import Dahlias.Proofs.Records

/-!
# Running the reduction's queries in the AOMDL game

How the challenge queries and the discrete logarithm queries of the reduction
evaluate, and the arrangement `merge` of the secret key and the session nonces
as the challenges `P, U₀.1, U₀.2, U₁.1, …`.
-/

set_option linter.unusedSectionVars false

namespace Dahlias.Security

open Taproot Function

variable {n : ℕ} [Fact n.Prime] {E X M : Type} [AddCommGroup E] [DecidableEq E] [DecidableEq X]
  [DecidableEq M] (C : Curve n E X)

/-- The discrete logarithm of challenge `i`, zero beyond the last one. -/
def logAt {c : ℕ} (xs : Fin c → (ZMod n)ˣ) (i : ℕ) : ZMod n :=
  if h : i < c then ((xs ⟨i, h⟩ : (ZMod n)ˣ) : ZMod n) else 0

theorem chalLogs_eq {c : ℕ} (xs : Fin c → (ZMod n)ˣ) (ℓ : ℕ) :
    chalLogs xs ℓ = (List.range ℓ).map (logAt xs) := rfl

theorem run_getChals {c : ℕ} (xs : Fin c → (ZMod n)ˣ) (k ℓ d : ℕ) (h : ℓ + k ≤ c) :
    (getChals (n := n) (E := E) k).run (omdlChallenger C xs) (ℓ, d) =
      ((List.range k).map fun i => C.mulG (logAt xs (ℓ + i)), (ℓ + k, d)) := by
  induction k generalizing ℓ with
  | zero => rfl
  | succ k ih =>
    have hℓ : ℓ < c := by omega
    simp only [getChals, Alg.run_ask, omdlChallenger, hℓ, ↓reduceDIte, Alg.run_bind,
      ih (ℓ + 1) (by omega), Alg.run_done, Option.getD_some, List.range_succ_eq_map,
      List.map_cons, List.map_map, add_zero]
    refine Prod.ext ?_ (by simp only [Prod.mk.injEq, and_true]; omega)
    simp only [logAt, hℓ, ↓reduceDIte, List.cons.injEq, true_and]
    refine List.map_congr_left fun i _ => ?_
    have e : ℓ + 1 + i = ℓ + i.succ := by omega
    simp only [Function.comp_apply, e]

theorem run_dlog {c : ℕ} (xs : Fin c → (ZMod n)ˣ) (a : ZMod n) (bs : List (ZMod n)) (ℓ d : ℕ)
    {α : Type} (f : ZMod n → Alg (OmdlQ n) (OmdlR E) α) :
    (Alg.ask (.dlog a bs) f).run (omdlChallenger C xs) (ℓ, d) =
      (f (a + (List.zipWith (· * ·) bs (chalLogs xs ℓ)).sum)).run (omdlChallenger C xs)
        (ℓ, d + 1) := rfl

/-- The value of a coefficient list on the challenges. -/
theorem coefVec_eval (L : ℕ) (g : ℕ → ZMod n) (l : List (ℕ × ZMod n)) (hl : ∀ p ∈ l, p.1 < L) :
    (List.zipWith (· * ·) (coefVec L l) ((List.range L).map g)).sum =
      (l.map fun p => p.2 * g p.1).sum := by
  unfold coefVec
  rw [List.zipWith_map, List.zipWith_self]
  induction l with
  | nil => simp
  | cons p l ih =>
    have hp : p.1 < L := hl p List.mem_cons_self
    have hsplit : ((List.range L).map fun j =>
        (((p :: l).filter fun q => decide (q.1 = j)).map (·.2)).sum * g j) =
        (List.range L).map fun j => (if p.1 = j then p.2 * g j else 0) +
          ((l.filter fun q => decide (q.1 = j)).map (·.2)).sum * g j := by
      refine List.map_congr_left fun j _ => ?_
      by_cases h : p.1 = j <;> simp [h, add_mul]
    rw [hsplit, List.sum_map_add, ih fun q hq => hl q (List.mem_cons_of_mem _ hq), List.map_cons,
      List.sum_cons]
    congr 1
    rw [List.sum_map_eq_nsmul_single p.1 _ fun j hj _ => by simp [Ne.symm hj],
      List.count_eq_one_of_mem List.nodup_range (List.mem_range.mpr hp)]
    simp

/-! ## The challenges of a sample of the unforgeability game -/

variable {qs : ℕ}

/-- The secret key and the session nonces as challenges. -/
def merge (x : (ZMod n)ˣ) (ν : Fin qs → (ZMod n)ˣ × (ZMod n)ˣ) : Fin (2 * qs + 1) → (ZMod n)ˣ :=
  fun i =>
    if i.val = 0 then x
    else if h : (i.val - 1) / 2 < qs then
      if (i.val - 1) % 2 = 0 then (ν ⟨(i.val - 1) / 2, h⟩).1 else (ν ⟨(i.val - 1) / 2, h⟩).2
    else x

theorem logAt_merge_zero (x : (ZMod n)ˣ) (ν : Fin qs → (ZMod n)ˣ × (ZMod n)ˣ) :
    logAt (merge x ν) 0 = x := by
  simp [logAt, merge]

theorem logAt_merge_odd (x : (ZMod n)ˣ) (ν : Fin qs → (ZMod n)ˣ × (ZMod n)ˣ) {k : ℕ}
    (hk : k < qs) : logAt (merge x ν) (2 * k + 1) = (ν ⟨k, hk⟩).1 := by
  have h1 : 2 * k + 1 < 2 * qs + 1 := by omega
  simp [logAt, merge, h1, hk]

theorem logAt_merge_even (x : (ZMod n)ˣ) (ν : Fin qs → (ZMod n)ˣ × (ZMod n)ˣ) {k : ℕ}
    (hk : k < qs) : logAt (merge x ν) (2 * k + 2) = (ν ⟨k, hk⟩).2 := by
  have h1 : 2 * k + 2 < 2 * qs + 1 := by omega
  have h2 : (2 * k + 1) / 2 = k := by omega
  simp [logAt, merge, h1, h2, hk]

end Dahlias.Security
