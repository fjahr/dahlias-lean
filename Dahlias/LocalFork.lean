import Mathlib

/-!
# The local forking lemma

The local forking lemma of Bellare, Dai and Li (ePrint 2019/1017, Lemma 1),
in the form the DahLIAS security proof uses (ePrint 2025/692, Lemma 2).

A deterministic algorithm runs with a random function `T : D → S`. It either
rejects or accepts with an index `i < q`. For every index there is at most one
point `pt i T` of the domain, the `i`-th query, and accepting with `i` requires
that it exists (`hsome`). The algorithm is run a second time on the function
that differs from `T` only at that point, where it gets a fresh uniform value
`s`. The fork succeeds if the second run accepts with the same index and `s`
differs from the old value.

The only other property of the query points the proof needs is that the `i`-th
query does not depend on the function's value at the `i`-th query (`hpt`).
An algorithm that queries its oracle adaptively, with `pt i T` its `i`-th new
query, has this property (`Dahlias.QueryRun`).

`localFork` states the lemma as a count over all `(T, s)`; `localFork_prob`
divides by the size of the sample space:

  `acc * (acc / q - 1 / |S|) ≤ fork`.
-/

set_option linter.unusedSectionVars false

namespace Dahlias.LocalFork

open Finset Function

variable {D S : Type*} [Fintype D] [DecidableEq D] [Fintype S] [DecidableEq S]

/-! ## One index -/

section OneIndex

variable (x : (D → S) → Option D)

/-- The function with the value at the query point replaced by `s`. -/
def upd (T : D → S) (s : S) : D → S :=
  match x T with
  | some d => update T d s
  | none => T

/-- The value at the query point; `s` if there is none. -/
def old (T : D → S) (s : S) : S :=
  match x T with
  | some d => T d
  | none => s

/-- Replace the value at the query point by `s` and return the old value. -/
def resample (p : (D → S) × S) : (D → S) × S := (upd x p.1 p.2, old x p.1 p.2)

variable {x} (hx : ∀ T d s, x T = some d → x (update T d s) = some d)
include hx

theorem resample_involutive : Involutive (resample x) := by
  rintro ⟨T, s⟩
  cases h : x T with
  | none => simp [resample, upd, old, h]
  | some d => simp [resample, upd, old, h, hx T d s h]

/-- **Resampling the value at the query point preserves the uniform
distribution.** -/
theorem sum_resample (f : (D → S) → ℝ) :
    ∑ T, ∑ s, f (upd x T s) = Fintype.card S * ∑ T, f T := by
  have h := Equiv.sum_comp (resample_involutive hx).toPerm fun p : (D → S) × S => f p.1
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type] at h
  calc ∑ T, ∑ s, f (upd x T s) = ∑ T, ∑ _s : S, f T := h
    _ = Fintype.card S * ∑ T, f T := by
      simp [Finset.sum_const, Finset.card_univ, Finset.mul_sum]

variable (g : (D → S) → ℝ)

omit hx in
/-- The sum of `g` over all values at the query point. -/
def cnt (x : (D → S) → Option D) (g : (D → S) → ℝ) (T : D → S) : ℝ := ∑ s, g (upd x T s)

theorem cnt_upd (T : D → S) (s : S) : cnt x g (upd x T s) = cnt x g T := by
  cases h : x T with
  | none => simp [cnt, upd, h]
  | some d => simp [cnt, upd, h, hx T d s h]

theorem sum_cnt : ∑ T, cnt x g T = Fintype.card S * ∑ T, g T := sum_resample hx g

theorem sum_mul_cnt : (Fintype.card S : ℝ) * ∑ T, g T * cnt x g T = ∑ T, cnt x g T ^ 2 := by
  rw [← sum_resample hx fun T => g T * cnt x g T]
  refine Finset.sum_congr rfl fun T _ => ?_
  simp only [cnt_upd hx]
  rw [← Finset.sum_mul, sq]
  rfl

omit hx in
/-- Both runs weighted by `g`, with a new value different from the old one. -/
theorem sum_fork (x : (D → S) → Option D) (T : D → S) (hg : x T = none → g T = 0) :
    ∑ s, (if s ≠ old x T s then g T * g (upd x T s) else 0) = g T * cnt x g T - g T ^ 2 := by
  cases hd : x T with
  | none => simp [old, hd, hg hd]
  | some d =>
    have h : ∀ s, (if s ≠ T d then g T * g (update T d s) else 0) =
        g T * g (update T d s) - if s = T d then g T * g (update T d s) else 0 := by
      intro s; split_ifs <;> simp_all
    simp only [old, upd, hd, h, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ,
      ↓reduceIte, update_eq_self, ← Finset.mul_sum, cnt, sq]

end OneIndex

/-! ## The lemma -/

variable {q : ℕ} (idx : (D → S) → Option (Fin q)) (pt : Fin q → (D → S) → Option D)

/-- The number of functions on which the algorithm accepts. -/
def accCount : ℝ := ∑ T, if (idx T).isSome then 1 else 0

/-- The number of pairs `(T, s)` on which the fork succeeds. -/
def forkCount : ℝ :=
  ∑ T, ∑ s, if ∃ i d, idx T = some i ∧ pt i T = some d ∧ idx (update T d s) = some i ∧ s ≠ T d
    then 1 else 0

/-- The indicator of accepting with index `i`. -/
def ind (i : Fin q) (T : D → S) : ℝ := if idx T = some i then 1 else 0

theorem ind_sq (i : Fin q) (T : D → S) : ind idx i T ^ 2 = ind idx i T := by
  unfold ind; split_ifs <;> simp

theorem accCount_eq : accCount idx = ∑ i, ∑ T, ind idx i T := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun T _ => ?_
  cases h : idx T with
  | none => simp [ind, h]
  | some j => simp [ind, h]

variable (hsome : ∀ i T, idx T = some i → (pt i T).isSome)
include hsome

theorem forkCount_eq : forkCount idx pt =
    ∑ i, ∑ T, ∑ s, (if s ≠ old (pt i) T s then ind idx i T * ind idx i (upd (pt i) T s)
      else 0) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  cases h : idx T with
  | none => simp [ind, h]
  | some j =>
    rw [Finset.sum_eq_single j (fun i _ hij => by simp [ind, h, Ne.symm hij]) (by simp)]
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp (hsome j T h)
    by_cases h1 : idx (update T d s) = some j <;> by_cases h2 : s = T d <;>
      simp [ind, h, h1, h2, hd, old, upd]

variable (hpt : ∀ i T d s, pt i T = some d → pt i (update T d s) = some d)
include hpt

/-- **The local forking lemma**, as a count over all functions `T` and new
values `s`. -/
theorem localFork :
    (Fintype.card S : ℝ) * accCount idx ^ 2 ≤
      q * Fintype.card (D → S) * (forkCount idx pt + accCount idx) := by
  set σ : ℝ := (Fintype.card S : ℝ)
  set c : Fin q × (D → S) → ℝ := fun p => cnt (pt p.1) (ind idx p.1) p.2
  -- the fork count in terms of the squares of `c`
  have hfork : σ * (forkCount idx pt + accCount idx) = ∑ p, c p ^ 2 := by
    rw [forkCount_eq idx pt hsome, accCount_eq, ← Finset.sum_add_distrib, Finset.mul_sum,
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hg : ∀ T, pt i T = none → ind idx i T = 0 := fun T hn => by
      unfold ind
      split_ifs with h
      · have := hsome i T h
        simp [hn] at this
      · rfl
    rw [Finset.sum_congr rfl fun T _ => sum_fork (ind idx i) (pt i) T (hg T)]
    simp only [ind_sq, Finset.sum_sub_distrib, sub_add_cancel]
    exact sum_mul_cnt (hpt i) _
  have hsum : ∑ p, c p = σ * accCount idx := by
    rw [accCount_eq, Finset.mul_sum, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun i _ => sum_cnt (hpt i) (ind idx i)
  have hcs := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin q × (D → S)))) (f := c)
  rw [hsum, ← hfork, Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at hcs
  have hσ : 0 ≤ σ := Nat.cast_nonneg _
  rcases hσ.eq_or_lt with h0 | hpos
  · rw [← h0]; simp only [zero_mul]
    have : 0 ≤ forkCount idx pt + accCount idx := by
      unfold forkCount accCount
      positivity
    positivity
  · have : σ * (σ * accCount idx ^ 2) ≤
        σ * (q * Fintype.card (D → S) * (forkCount idx pt + accCount idx)) := by
      push_cast at hcs
      nlinarith [hcs]
    exact le_of_mul_le_mul_left this hpos

/-- **The local forking lemma**, as probabilities: with `acc` the probability
of accepting and `fork` the probability that the fork succeeds,
`acc * (acc / q - 1 / |S|) ≤ fork`. -/
theorem localFork_prob [Nonempty S] (hq : 0 < q) :
    let N : ℝ := Fintype.card (D → S)
    let acc := accCount idx / N
    acc * (acc / q - 1 / Fintype.card S) ≤ forkCount idx pt / (N * Fintype.card S) := by
  intro N acc
  have h := localFork idx pt hsome hpt
  have hN : 0 < N := Nat.cast_pos.mpr Fintype.card_pos
  have hσ : (0 : ℝ) < Fintype.card S := Nat.cast_pos.mpr Fintype.card_pos
  have hq' : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have key : forkCount idx pt / (N * Fintype.card S) - acc * (acc / q - 1 / Fintype.card S) =
      (q * N * (forkCount idx pt + accCount idx) - Fintype.card S * accCount idx ^ 2) /
        (N ^ 2 * q * Fintype.card S) := by
    simp only [acc]
    field_simp
    ring
  rw [← sub_nonneg, key]
  exact div_nonneg (sub_nonneg.mpr h) (by positivity)

end Dahlias.LocalFork
