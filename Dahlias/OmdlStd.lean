import Dahlias.Unforgeability
import Dahlias.NonceProb

/-!
# The AOMDL game with uniform challenges

The AOMDL game of `Dahlias.Security` draws the discrete logarithms of its
challenges from the nonzero scalars, because the challenges stand for the
secret key and the nonces of the unforgeability game, which are nonzero. The
usual AOMDL game draws them from all scalars. This file has that game
(`omdlExperimentStd`) and the step between the two.

* `omdlAdvantage_mul_le_std`: an adversary's advantage against nonzero
  challenges, times `((n - 1) / n)^c`, is at most its advantage against
  uniform challenges. The samples of the first game are among the samples of
  the second, where the two games agree.
* `omdlAdvantage_le_std`: so the first advantage is at most the second plus
  `c / n`, for `c` challenges.
* `unforgeable_sqrt_std`: `unforgeable_sqrt` with the reduction's advantage in
  the game with uniform challenges. The reduction asks for `2⋅qs + 1`
  challenges, which adds `(2⋅qs + 1) / n` next to the AOMDL advantage.
-/

set_option linter.unusedSectionVars false

namespace Dahlias

section Prob

variable {Ω Ω' : Type} [Fintype Ω] [Fintype Ω']

/-- An event has at least as many samples as an event that maps into it by an
injection. -/
theorem prob_mul_card_le_of_injective (ι : Ω → Ω') (hι : Function.Injective ι) (p : Ω → Prop)
    (q : Ω' → Prop) (h : ∀ ω, p ω → q (ι ω)) :
    prob p * Fintype.card Ω ≤ prob q * Fintype.card Ω' := by
  classical
  rcases isEmpty_or_nonempty Ω with hΩ | hΩ
  · have h0 : prob p = 0 := by
      unfold prob
      simp
    rw [h0, zero_mul]
    exact mul_nonneg (prob_nonneg _) (Nat.cast_nonneg _)
  · have hΩ' : Nonempty Ω' := hΩ.map ι
    have h1 : (0 : ℝ) < Fintype.card Ω := Nat.cast_pos.mpr Fintype.card_pos
    have h2 : (0 : ℝ) < Fintype.card Ω' := Nat.cast_pos.mpr Fintype.card_pos
    unfold prob
    rw [div_mul_cancel₀ _ h1.ne', div_mul_cancel₀ _ h2.ne']
    have hle : (Finset.univ.filter p).card ≤ (Finset.univ.filter q).card :=
      Finset.card_le_card_of_injOn ι (fun ω hω => by simpa using h ω (by simpa using hω))
        hι.injOn
    exact_mod_cast hle

end Prob

namespace Security

open Taproot

variable {n : ℕ} [Fact n.Prime] {E X M : Type} [AddCommGroup E] [DecidableEq E] [DecidableEq X]
  [DecidableEq M] (C : Curve n E X)

/-! ## The game -/

/-- The discrete logarithms of the first `ℓ` challenges. -/
def chalLogsStd {c : ℕ} (xs : Fin c → ZMod n) (ℓ : ℕ) : List (ZMod n) :=
  (List.range ℓ).map fun i => if h : i < c then xs ⟨i, h⟩ else 0

/-- The game's answers, for challenges with the discrete logarithms `xs`. -/
def omdlChallengerStd {c : ℕ} (xs : Fin c → ZMod n) :
    (q : OmdlQ n) → ℕ × ℕ → OmdlR E q × (ℕ × ℕ)
  | .chal, (ℓ, d) =>
    if h : ℓ < c then (some (C.mulG (xs ⟨ℓ, h⟩)), (ℓ + 1, d)) else (none, (ℓ, d))
  | .dlog a bs, (ℓ, d) =>
    (a + (List.zipWith (· * ·) bs (chalLogsStd xs ℓ)).sum, (ℓ, d + 1))

/-- **The AOMDL game with uniform challenges** on one sample: at most `c`
challenges with the discrete logarithms `xs`, which may be zero. The adversary
wins if it outputs the discrete logarithms of all challenges it received and
made fewer discrete logarithm queries than it received challenges. -/
def omdlExperimentStd (c : ℕ) {Coins : Type} (B : OmdlAdversary n E Coins)
    (ω : (Fin c → ZMod n) × Coins) : Prop :=
  let out := (B ω.2).run (omdlChallengerStd C ω.1) (0, 0)
  out.1 = chalLogsStd ω.1 out.2.1 ∧ out.2.2 < out.2.1

/-- The adversary's probability of winning the AOMDL game with uniform
challenges. -/
noncomputable def omdlAdvantageStd (c : ℕ) {Coins : Type} [Fintype Coins]
    (B : OmdlAdversary n E Coins) : ℝ :=
  prob (omdlExperimentStd C c B)

/-! ## From nonzero challenges to uniform challenges -/

theorem omdlChallenger_eq_std {c : ℕ} (xs : Fin c → (ZMod n)ˣ) :
    omdlChallenger C xs = omdlChallengerStd C fun i => ((xs i : (ZMod n)ˣ) : ZMod n) := by
  funext q s
  obtain ⟨ℓ, d⟩ := s
  cases q <;> rfl

/-- On challenges with nonzero discrete logarithms the two games are the
same. -/
theorem omdlExperiment_iff_std (c : ℕ) {Coins : Type} (B : OmdlAdversary n E Coins)
    (ω : (Fin c → (ZMod n)ˣ) × Coins) :
    omdlExperiment C c B ω ↔
      omdlExperimentStd C c B (fun i => ((ω.1 i : (ZMod n)ˣ) : ZMod n), ω.2) := by
  unfold omdlExperiment omdlExperimentStd
  rw [omdlChallenger_eq_std]
  rfl

variable {Coins : Type} [Fintype Coins]

/-- **Nonzero challenges cost a factor.** An adversary's advantage against
challenges with nonzero discrete logarithms, times `((n - 1) / n)^c`, is at
most its advantage against uniform challenges. -/
theorem omdlAdvantage_mul_le_std (c : ℕ) (B : OmdlAdversary n E Coins) :
    omdlAdvantage C c B * (((n : ℝ) - 1) / n) ^ c ≤ omdlAdvantageStd C c B := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Fact.out : n.Prime).pos
  have h := prob_mul_card_le_of_injective
    (fun ω : (Fin c → (ZMod n)ˣ) × Coins => ((fun i => ((ω.1 i : (ZMod n)ˣ) : ZMod n)), ω.2))
    (fun ω ω' he => by
      simp only [Prod.mk.injEq] at he
      exact Prod.ext (funext fun i => Units.ext (congrFun he.1 i)) he.2)
    (omdlExperiment C c B) (omdlExperimentStd C c B)
    fun ω hω => (omdlExperiment_iff_std C c B ω).mp hω
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, Fintype.card_fin,
    ZMod.card_units, ZMod.card] at h
  rcases isEmpty_or_nonempty Coins with hC | hC
  · have h0 : omdlAdvantage C c B = 0 := by
      unfold omdlAdvantage prob
      simp
    rw [h0, zero_mul]
    exact prob_nonneg _
  · have hK : (0 : ℝ) < Fintype.card Coins := Nat.cast_pos.mpr Fintype.card_pos
    have hsub : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := Nat.cast_pred (Fact.out : n.Prime).pos
    push_cast at h
    rw [hsub] at h
    have h' : omdlAdvantage C c B * ((n : ℝ) - 1) ^ c ≤ omdlAdvantageStd C c B * (n : ℝ) ^ c := by
      refine le_of_mul_le_mul_right ?_ hK
      calc omdlAdvantage C c B * ((n : ℝ) - 1) ^ c * Fintype.card Coins
          = omdlAdvantage C c B * (((n : ℝ) - 1) ^ c * Fintype.card Coins) := by ring
        _ ≤ omdlAdvantageStd C c B * ((n : ℝ) ^ c * Fintype.card Coins) := h
        _ = omdlAdvantageStd C c B * (n : ℝ) ^ c * Fintype.card Coins := by ring
    rw [div_pow, ← mul_div_assoc, div_le_iff₀ (pow_pos hn c)]
    exact h'

/-- **Nonzero challenges cost at most `c / n`.** -/
theorem omdlAdvantage_le_std (c : ℕ) (B : OmdlAdversary n E Coins) :
    omdlAdvantage C c B ≤ omdlAdvantageStd C c B + c / n := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Fact.out : n.Prime).pos
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Fact.out : n.Prime).one_le
  have h := omdlAdvantage_mul_le_std C c B
  have hA0 : 0 ≤ omdlAdvantage C c B := prob_nonneg _
  have hA1 : omdlAdvantage C c B ≤ 1 := prob_le_one _
  have hcn : 0 ≤ (c : ℝ) / n := by positivity
  -- Bernoulli: `((n - 1) / n)^c ≥ 1 - c / n`
  have hb : 1 - (c : ℝ) / n ≤ (((n : ℝ) - 1) / n) ^ c := by
    have hrw : ((n : ℝ) - 1) / n = 1 + -(1 / n) := by
      field_simp
      ring
    have h2 : (-2 : ℝ) ≤ -(1 / n) := by
      have : (1 : ℝ) / n ≤ 1 := by
        rw [div_le_one hn]
        exact hn1
      linarith
    have hbern := one_add_mul_le_pow h2 c
    rw [hrw]
    have he : 1 + (c : ℝ) * -(1 / n) = 1 - c / n := by ring
    linarith
  have h1 := mul_le_mul_of_nonneg_left hb hA0
  have h2 := mul_le_mul_of_nonneg_right hA1 hcn
  nlinarith

/-! ## Unforgeability under the AOMDL assumption with uniform challenges -/

variable (nonceCoef : E → E → List (X × M × E) → ZMod n) (N qs : ℕ)
  (A : Adversary n N E X M Coins) [Fintype (SigIn N X M)]

/-- **BIP 459 is unforgeable under AOMDL with uniform challenges.** This is
`unforgeable_sqrt` with the advantage of `reduction A` in the game whose
challenges have uniform discrete logarithms. The `2⋅qs + 1` challenges that
the reduction asks for add `(2⋅qs + 1) / n`. -/
theorem unforgeable_sqrt_std (hN : N < n) (qh : ℕ) (hA : ∀ coins P, HashBound (A coins P) qh) :
    forgeAdvantage C nonceCoef N qs A ≤
      Real.sqrt ((qh + qs + 1 : ℕ) *
        (omdlAdvantageStd C (2 * qs + 1) (reduction C nonceCoef N qs A) + (2 * qs + 1 : ℕ) / n +
          collisionAdvantage C nonceCoef N qs A)) + (qh + qs + 1 : ℕ) / n + qs / (n - 1 : ℝ) := by
  refine (unforgeable_sqrt C nonceCoef N qs A hN qh hA).trans ?_
  have hle := omdlAdvantage_le_std C (2 * qs + 1) (reduction C nonceCoef N qs A)
  gcongr

end Security

end Dahlias
