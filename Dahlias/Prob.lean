import Mathlib

/-!
# Probability on a finite sample space

`prob p` is the fraction of the samples of a finite type that satisfy `p`:
the probability of `p` under the uniform distribution.
-/

namespace Dahlias

open Classical in
/-- The fraction of samples that satisfy `p`. -/
noncomputable def prob {Ω : Type} [Fintype Ω] (p : Ω → Prop) : ℝ :=
  ((Finset.univ.filter p).card : ℝ) / Fintype.card Ω

variable {Ω Ω' : Type} [Fintype Ω] [Fintype Ω']

open Classical in
theorem prob_eq_sum (p : Ω → Prop) :
    prob p = (∑ ω, if p ω then (1 : ℝ) else 0) / Fintype.card Ω := by
  unfold prob
  rw [Finset.card_filter]
  push_cast
  rfl

theorem prob_nonneg (p : Ω → Prop) : 0 ≤ prob p := by
  unfold prob
  positivity

theorem prob_mono {p q : Ω → Prop} (h : ∀ ω, p ω → q ω) : prob p ≤ prob q := by
  classical
  unfold prob
  gcongr
  exact h _

theorem prob_pos {p : Ω → Prop} (h : ∃ ω, p ω) : 0 < prob p := by
  classical
  obtain ⟨ω, hω⟩ := h
  have : Nonempty Ω := ⟨ω⟩
  unfold prob
  refine div_pos (Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨ω, by simp [hω]⟩)) ?_
  exact Nat.cast_pos.mpr Fintype.card_pos

/-- The union bound. -/
theorem prob_le_add {p q r : Ω → Prop} (h : ∀ ω, p ω → q ω ∨ r ω) :
    prob p ≤ prob q + prob r := by
  classical
  unfold prob
  rw [← add_div]
  gcongr
  have hsub : Finset.univ.filter p ⊆ Finset.univ.filter q ∪ Finset.univ.filter r := by
    intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hω ⊢
    exact h ω hω
  exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

/-- The union bound for finitely many events. -/
theorem prob_exists_le (q : ℕ) (p : ℕ → Ω → Prop) :
    prob (fun ω => ∃ j, j < q ∧ p j ω) ≤ ∑ j ∈ Finset.range q, prob (p j) := by
  induction q with
  | zero => simp [prob]
  | succ q ih =>
    rw [Finset.sum_range_succ]
    refine (prob_le_add (q := fun ω => ∃ j, j < q ∧ p j ω) (r := p q) ?_).trans (by gcongr)
    rintro ω ⟨j, hj, hp⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | rfl
    · exact Or.inl ⟨j, h, hp⟩
    · exact Or.inr hp

/-- Relabelling the samples does not change a probability. -/
theorem prob_equiv (e : Ω ≃ Ω') (p : Ω' → Prop) : prob (fun ω => p (e ω)) = prob p := by
  classical
  unfold prob
  rw [Fintype.card_congr e]
  congr 2
  exact Finset.card_bij (fun ω _ => e ω) (by simp) (by simp)
    fun ω' hω' => ⟨e.symm ω', by simpa using hω', by simp⟩

end Dahlias
