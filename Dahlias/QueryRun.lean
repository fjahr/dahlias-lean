import Mathlib

/-!
# Deterministic algorithms that query a function

A `QTree D S α` is a deterministic algorithm that adaptively queries a
function `D → S` and returns a value in `α`. `eval T t` runs it on the function
`T`, and `fresh T t` lists the points it queries, in order and without
repetitions.

The main result is `fresh_update`: changing the function at the `j`-th fresh
query leaves the `j`-th fresh query where it is. This is the property the
local forking lemma (`Dahlias.LocalFork`) asks of the query points.
-/

namespace Dahlias

/-- A deterministic algorithm with adaptive queries to a function `D → S`. -/
inductive QTree (D S α : Type*) where
  | done : α → QTree D S α
  | ask : D → (S → QTree D S α) → QTree D S α

namespace QTree

open Function

variable {D S α : Type*} [DecidableEq D]

/-- The output on the function `T`. -/
def eval (T : D → S) : QTree D S α → α
  | done a => a
  | ask d f => eval T (f (T d))

/-- The fresh queries on the function `T`, appended to the points `l` that
count as queried already. -/
def flog (T : D → S) : List D → QTree D S α → List D
  | l, done _ => l
  | l, ask d f => flog T (if d ∈ l then l else l ++ [d]) (f (T d))

/-- The points queried on the function `T`, in order, each once. -/
def fresh (T : D → S) (t : QTree D S α) : List D := flog T [] t

omit [DecidableEq D] in
theorem nodup_snoc {l : List D} (hl : l.Nodup) {d : D} (h : d ∉ l) : (l ++ [d]).Nodup := by
  rw [List.nodup_append_comm]
  exact List.nodup_cons.mpr ⟨h, hl⟩

theorem prefix_flog (T : D → S) (l : List D) (t : QTree D S α) : l <+: flog T l t := by
  induction t generalizing l with
  | done a => exact List.prefix_refl l
  | ask d f ih =>
    refine List.IsPrefix.trans ?_ (ih (T d) _)
    split_ifs
    · exact List.prefix_refl l
    · exact List.prefix_append l [d]

theorem nodup_flog (T : D → S) {l : List D} (hl : l.Nodup) (t : QTree D S α) :
    (flog T l t).Nodup := by
  induction t generalizing l with
  | done a => exact hl
  | ask d f ih =>
    refine ih (T d) ?_
    split_ifs with h
    · exact hl
    · exact nodup_snoc hl h

theorem nodup_fresh (T : D → S) (t : QTree D S α) : (fresh T t).Nodup :=
  nodup_flog T List.nodup_nil t

/-- A point that is never queried does not matter. -/
theorem eval_flog_update (T : D → S) (x : D) (s : S) (l : List D) (t : QTree D S α)
    (hx : x ∉ flog T l t) :
    eval (update T x s) t = eval T t ∧ flog (update T x s) l t = flog T l t := by
  induction t generalizing l with
  | done a => exact ⟨rfl, rfl⟩
  | ask d f ih =>
    have hd : d ≠ x := by
      rintro rfl
      refine hx ((prefix_flog T _ (f (T d))).subset ?_)
      split_ifs with h
      · exact h
      · simp
    simp only [eval, flog, update_of_ne hd]
    exact ih (T d) _ hx

/-- **The `j`-th fresh query does not depend on the value at the `j`-th fresh
query.** -/
theorem flog_update (T : D → S) (x : D) (s : S) {l : List D} (hl : l.Nodup) (hxl : x ∉ l)
    (t : QTree D S α) {j : ℕ} (hj : (flog T l t)[j]? = some x) :
    (flog (update T x s) l t)[j]? = some x := by
  induction t generalizing l with
  | done a => exact absurd (List.mem_of_getElem? hj) hxl
  | ask d f ih =>
    by_cases hd : d = x
    · subst hd
      simp only [flog, hxl, ↓reduceIte] at hj ⊢
      have hat : ∀ (T' : D → S) (u : QTree D S α), (flog T' (l ++ [d]) u)[l.length]? = some d := by
        intro T' u
        obtain ⟨r, hr⟩ := prefix_flog T' (l ++ [d]) u
        rw [← hr]
        simp
      have hnd := nodup_flog T (nodup_snoc hl hxl) (f (T d))
      have hjl : j = l.length := by
        have h1 := hat T (f (T d))
        obtain ⟨hj1, hj2⟩ := List.getElem?_eq_some_iff.mp hj
        obtain ⟨hl1, hl2⟩ := List.getElem?_eq_some_iff.mp h1
        exact (List.Nodup.getElem_inj_iff hnd).mp (hj2.trans hl2.symm)
      rw [hjl]
      exact hat _ _
    · simp only [flog, update_of_ne hd] at hj ⊢
      refine ih (T d) ?_ ?_ hj
      · split_ifs with h
        · exact hl
        · exact nodup_snoc hl h
      · split_ifs with h
        · exact hxl
        · simpa using ⟨hxl, Ne.symm hd⟩

theorem fresh_update (T : D → S) (x : D) (s : S) (t : QTree D S α) {j : ℕ}
    (hj : (fresh T t)[j]? = some x) : (fresh (update T x s) t)[j]? = some x :=
  flog_update T x s List.nodup_nil (by simp) t hj

/-- A point outside the fresh queries does not matter. -/
theorem eval_update (T : D → S) (x : D) (s : S) (t : QTree D S α) (hx : x ∉ fresh T t) :
    eval (update T x s) t = eval T t :=
  (eval_flog_update T x s [] t hx).1

end QTree

end Dahlias
