import Dahlias.LocalFork
import Dahlias.QueryRun

/-!
# The local forking lemma for query algorithms

`QTree.localFork`: the local forking lemma for a deterministic algorithm with
adaptive queries (`QTree`) that makes at most `q` different queries. The
algorithm accepts on `T` if its output selects a point `z` that it queried.
The fork succeeds on `(T, s)` if it accepts on `T` with `z`, accepts with the
same `z` on the function that has `s` at `z`, and `s` differs from `T z`.
-/

namespace Dahlias.QTree

open Finset Function LocalFork

variable {D S α : Type} [Fintype D] [DecidableEq D] [Fintype S] [DecidableEq S]
  (t : QTree D S α) (sel : α → Option D)

/-- The algorithm accepts on `T`: its output selects one of its queries. -/
def Accepts (T : D → S) : Prop := ∃ z, sel (eval T t) = some z ∧ z ∈ fresh T t

/-- The fork succeeds on `(T, s)`. -/
def Forks (T : D → S) (s : S) : Prop :=
  ∃ z, sel (eval T t) = some z ∧ z ∈ fresh T t ∧ sel (eval (update T z s) t) = some z ∧ s ≠ T z

/-- The index of the selected query among the fresh queries. -/
def selIdx (q : ℕ) (T : D → S) : Option (Fin q) :=
  (sel (eval T t)).bind fun z =>
    if h : z ∈ fresh T t ∧ (fresh T t).idxOf z < q then some ⟨(fresh T t).idxOf z, h.2⟩ else none

omit [Fintype D] [Fintype S] [DecidableEq S] in
theorem selIdx_eq_some {q : ℕ} {T : D → S} {i : Fin q} (h : selIdx t sel q T = some i) :
    ∃ z, sel (eval T t) = some z ∧ z ∈ fresh T t ∧ (fresh T t)[(i : ℕ)]? = some z := by
  unfold selIdx at h
  obtain ⟨z, hz, h⟩ := Option.bind_eq_some_iff.mp h
  split_ifs at h with hm
  cases h
  exact ⟨z, hz, hm.1, by simp [List.getElem?_idxOf hm.1]⟩

open Classical in
/-- **The local forking lemma for query algorithms**, as a count over all
functions `T` and new values `s`. -/
theorem localFork {q : ℕ} (hq : ∀ T, (fresh T t).length ≤ q) :
    (Fintype.card S : ℝ) * (∑ T, if Accepts t sel T then (1 : ℝ) else 0) ^ 2 ≤
      q * Fintype.card (D → S) *
        ((∑ T, ∑ s, if Forks t sel T s then (1 : ℝ) else 0) +
          ∑ T, if Accepts t sel T then (1 : ℝ) else 0) := by
  have hacc : accCount (selIdx t sel q) = ∑ T, if Accepts t sel T then (1 : ℝ) else 0 := by
    refine Finset.sum_congr rfl fun T _ => ?_
    have : (selIdx t sel q T).isSome ↔ Accepts t sel T := by
      constructor
      · intro h
        obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp h
        obtain ⟨z, hz, hm, -⟩ := selIdx_eq_some t sel hi
        exact ⟨z, hz, hm⟩
      · rintro ⟨z, hz, hm⟩
        have hlt : (fresh T t).idxOf z < q := (List.idxOf_lt_length_of_mem hm).trans_le (hq T)
        simp [selIdx, hz, hm, hlt]
    simp only [this]
  have hfork : forkCount (selIdx t sel q) (fun i T => (fresh T t)[(i : ℕ)]?) ≤
      ∑ T, ∑ s, if Forks t sel T s then (1 : ℝ) else 0 := by
    refine Finset.sum_le_sum fun T _ => Finset.sum_le_sum fun s _ => ?_
    split_ifs with h1 h2 h2
    · exact le_rfl
    · exfalso
      obtain ⟨i, d, hi, hd, hi', hs⟩ := h1
      obtain ⟨z, hz, hm, hzi⟩ := selIdx_eq_some t sel hi
      obtain ⟨z', hz', -, hzi'⟩ := selIdx_eq_some t sel hi'
      have hdz : d = z := Option.some.inj (hd.symm.trans hzi)
      subst hdz
      have := fresh_update T d s t hzi
      have hzz : z' = d := Option.some.inj (hzi'.symm.trans this)
      subst hzz
      exact h2 ⟨z', hz, hm, hz', hs⟩
    · exact zero_le_one
    · exact le_rfl
  have h := LocalFork.localFork (selIdx t sel q) (fun i T => (fresh T t)[(i : ℕ)]?)
    (fun i T hi => by
      obtain ⟨z, -, -, hzi⟩ := selIdx_eq_some t sel hi
      simp [hzi])
    (fun i T d s hd => fresh_update T d s t hd)
  rw [hacc] at h
  refine h.trans ?_
  gcongr

end Dahlias.QTree
