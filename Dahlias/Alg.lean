import Mathlib

/-!
# Deterministic oracle algorithms

`Alg Q R α` is a deterministic algorithm that makes queries `q : Q`, receives
answers in `R q` and returns a value in `α`. Randomized algorithms are
functions from a type of coins to `Alg`.

* `Alg.run` answers the queries with a handler that carries a state.
* `Alg.interp` answers them with a handler that is itself an algorithm for
  other queries. This is how a reduction runs an adversary.
-/

namespace Dahlias

/-- A deterministic algorithm with queries `q : Q` answered in `R q`. -/
inductive Alg (Q : Type) (R : Q → Type) (α : Type) where
  | done : α → Alg Q R α
  | ask : (q : Q) → (R q → Alg Q R α) → Alg Q R α

namespace Alg

variable {Q : Type} {R : Q → Type} {α β σ : Type}

/-- Sequential composition. -/
def bind : Alg Q R α → (α → Alg Q R β) → Alg Q R β
  | done a, g => g a
  | ask q f, g => ask q fun r => bind (f r) g

instance : Monad (Alg Q R) where
  pure := done
  bind := bind

/-- A single query. -/
def query (q : Q) : Alg Q R (R q) := ask q done

@[simp] theorem pure_eq (a : α) : (pure a : Alg Q R α) = done a := rfl

@[simp] theorem done_bind (a : α) (g : α → Alg Q R β) : (done a : Alg Q R α) >>= g = g a := rfl

@[simp] theorem ask_bind (q : Q) (f : R q → Alg Q R α) (g : α → Alg Q R β) :
    ask q f >>= g = ask q fun r => f r >>= g := rfl

@[simp] theorem query_bind (q : Q) (g : R q → Alg Q R β) : query q >>= g = ask q g := rfl

/-- Run with a stateful handler for the queries. -/
def run (h : (q : Q) → σ → R q × σ) : Alg Q R α → σ → α × σ
  | done a, s => (a, s)
  | ask q f, s => run h (f (h q s).1) (h q s).2

@[simp] theorem run_done (h : (q : Q) → σ → R q × σ) (a : α) (s : σ) :
    run h (done a : Alg Q R α) s = (a, s) := rfl

@[simp] theorem run_ask (h : (q : Q) → σ → R q × σ) (q : Q) (f : R q → Alg Q R α) (s : σ) :
    run h (ask q f) s = run h (f (h q s).1) (h q s).2 := rfl

theorem run_bind (h : (q : Q) → σ → R q × σ) (t : Alg Q R α) (g : α → Alg Q R β) (s : σ) :
    run h (t >>= g) s = run h (g (run h t s).1) (run h t s).2 := by
  induction t generalizing s with
  | done a => rfl
  | ask q f ih => exact ih _ _

variable {Q' : Type} {R' : Q' → Type}

/-- Run with a stateful handler that answers each query by an algorithm for
other queries. -/
def interp (h : (q : Q) → σ → Alg Q' R' (R q × σ)) : Alg Q R α → σ → Alg Q' R' (α × σ)
  | done a, s => done (a, s)
  | ask q f, s => h q s >>= fun p => interp h (f p.1) p.2

@[simp] theorem interp_done (h : (q : Q) → σ → Alg Q' R' (R q × σ)) (a : α) (s : σ) :
    interp h (done a : Alg Q R α) s = done (a, s) := rfl

@[simp] theorem interp_ask (h : (q : Q) → σ → Alg Q' R' (R q × σ)) (q : Q) (f : R q → Alg Q R α)
    (s : σ) : interp h (ask q f) s = h q s >>= fun p => interp h (f p.1) p.2 := rfl

/-- Running an interpreted algorithm is running the original one with the
composed handler. -/
theorem run_interp {τ : Type} (h : (q : Q) → σ → Alg Q' R' (R q × σ))
    (h' : (q : Q') → τ → R' q × τ) (t : Alg Q R α) (s : σ) (u : τ) :
    run h' (interp h t s) u =
      let r := run (fun q (p : σ × τ) =>
        let a := run h' (h q p.1) p.2
        (a.1.1, (a.1.2, a.2))) t (s, u)
      ((r.1, r.2.1), r.2.2) := by
  induction t generalizing s u with
  | done a => rfl
  | ask q f ih =>
    simp only [interp_ask, run_bind, run_ask]
    exact ih _ _ _

end Alg

end Dahlias
