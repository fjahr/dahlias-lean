import Dahlias.Proofs.Main

/-!
# BIP 459 is unforgeable under AOMDL

`unforgeable`: for every forger `A` against the game of `Dahlias.Security`
that makes at most `qh` random oracle queries and opens at most `qs` signing
sessions,

  `adv * (adv / (qh + qs + 1) - 1 / n) ≤ omdl + coll`

where `adv` is the forger's success probability, `omdl` is the probability
that the AOMDL adversary `reduction A` wins with `2⋅qs + 1` challenges, and
`coll` is the probability that `collider A` outputs a collision of
`hash_BIP0459/noncecoef`.

This is Theorem 2 of the DahLIAS paper (ePrint 2025/692) for the algorithms of
BIP 459, in the form before solving for `adv`. `unforgeable_sqrt` is the
solved form: `adv ≤ sqrt (q * (omdl + coll)) + q / n` for `q = qh + qs + 1`.
The challenge hash is a random oracle; the nonce coefficient hash is a fixed
function and only has to be collision resistant.

The statement has no running times. `reduction A` runs `A` twice and makes at
most `2⋅qs` discrete logarithm queries (it could not win otherwise).
`collider A` runs `A` twice with a key and nonces it knows.
-/

set_option linter.unusedSectionVars false
set_option linter.deprecated false

namespace Dahlias.Security

open Taproot Function

variable {n : ℕ} [Fact n.Prime] {E X M : Type} [AddCommGroup E] [DecidableEq E] [DecidableEq X]
  [DecidableEq M] (C : Curve n E X) (nonceCoef : E → E → List (X × M × E) → ZMod n) (N qs : ℕ)
  {Coins : Type} (A : Adversary n N E X M Coins)

/-! ## The sample spaces of the two games -/

/-- The secret key and the session nonces are `2⋅qs + 1` challenges. -/
def mergeEquiv : (ZMod n)ˣ × (Fin qs → (ZMod n)ˣ × (ZMod n)ˣ) ≃ (Fin (2 * qs + 1) → (ZMod n)ˣ) where
  toFun p := merge p.1 p.2
  invFun xs := (xs ⟨0, by omega⟩, fun k => (xs ⟨2 * k + 1, by omega⟩, xs ⟨2 * k + 2, by omega⟩))
  left_inv := by
    rintro ⟨x, ν⟩
    refine Prod.ext (by simp [merge]) ?_
    funext k
    have hk := k.isLt
    have h1 : (2 * (k : ℕ) + 1 - 1) / 2 = k := by omega
    have h2 : (2 * (k : ℕ) + 2 - 1) / 2 = k := by omega
    have h3 : ¬(2 * (k : ℕ) + 2 - 1) % 2 = 0 := by omega
    refine Prod.ext ?_ ?_
    · simp [merge, hk]
    · simp only [merge]
      rw [if_neg (by simp), dif_pos (by omega), if_neg h3]
      congr 2
      exact Fin.ext h2
  right_inv := by
    intro xs
    funext i
    have hi := i.isLt
    simp only [merge]
    by_cases h0 : i.val = 0
    · rw [if_pos h0]
      exact congrArg xs (Fin.ext h0.symm)
    · rw [if_neg h0, dif_pos (by omega)]
      by_cases hp : (i.val - 1) % 2 = 0
      · rw [if_pos hp]
        exact congrArg xs (Fin.ext (by simp only; omega))
      · rw [if_neg hp]
        exact congrArg xs (Fin.ext (by simp only; omega))

/-- A sample of the forked unforgeability game is a sample of the AOMDL game
for the reduction. -/
def forkSampleEquiv :
    ForgeSample n N qs X M Coins × ZMod n ≃
      (Fin (2 * qs + 1) → (ZMod n)ˣ) × (Coins × (SigIn N X M → ZMod n) × ZMod n) where
  toFun p := (merge p.1.1 p.1.2.1, (p.1.2.2.1, p.1.2.2.2, p.2))
  invFun q := ((((mergeEquiv qs).symm q.1).1, ((mergeEquiv qs).symm q.1).2, q.2.1, q.2.2.1),
    q.2.2.2)
  left_inv := by
    rintro ⟨⟨x, ν, c, T⟩, s⟩
    have h : (mergeEquiv qs).symm (merge x ν) = (x, ν) := (mergeEquiv qs).left_inv (x, ν)
    change ((((mergeEquiv qs).symm (merge x ν)).1, ((mergeEquiv qs).symm (merge x ν)).2, c, T),
      s) = _
    rw [h]
  right_inv := by
    rintro ⟨xs, c, T, s⟩
    have h : merge ((mergeEquiv qs).symm xs).1 ((mergeEquiv qs).symm xs).2 = xs :=
      (mergeEquiv qs).right_inv xs
    change (merge ((mergeEquiv qs).symm xs).1 ((mergeEquiv qs).symm xs).2, (c, T, s)) = _
    rw [h]

variable [Fintype Coins] [Fintype (SigIn N X M)]

noncomputable instance : Fintype (Coins × (SigIn N X M → ZMod n) × ZMod n) := instFintypeProd _ _

/-- The probability that `collider A` outputs a collision of the nonce
coefficient hash. -/
noncomputable def collisionAdvantage : ℝ :=
  prob fun p : ForgeSample n N qs X M Coins × ZMod n =>
    IsCollision nonceCoef (collider C nonceCoef N qs A p)

/-- **BIP 459 is unforgeable under AOMDL**, with the challenge hash as a random
oracle and a collision resistant nonce coefficient hash. -/
theorem unforgeable (hN : N < n) (qh : ℕ) (hA : ∀ coins P, HashBound (A coins P) qh) :
    forgeAdvantage C nonceCoef N qs A *
        (forgeAdvantage C nonceCoef N qs A / (qh + qs + 1 : ℕ) - 1 / n) ≤
      omdlAdvantage C (2 * qs + 1) (reduction C nonceCoef N qs A) +
        collisionAdvantage C nonceCoef N qs A := by
  refine (forge_fork C nonceCoef N qs A qh hA).trans ?_
  have h := prob_le_add (fork_to_omdl C nonceCoef N qs A hN)
  have he := prob_equiv (forkSampleEquiv (n := n) (X := X) (M := M) (Coins := Coins) N qs)
    (omdlExperiment C (2 * qs + 1) (reduction C nonceCoef N qs A))
  unfold omdlAdvantage collisionAdvantage
  rw [← he]
  exact h

/-- From the product form of a forking bound to the square root form. -/
theorem le_sqrt_of_fork_bound {adv q N ε : ℝ} (hq : 0 < q) (hN : 0 < N)
    (h : adv * (adv / q - 1 / N) ≤ ε) : adv ≤ Real.sqrt (q * ε) + q / N := by
  by_contra hlt
  push Not at hlt
  have hs : 0 ≤ Real.sqrt (q * ε) := Real.sqrt_nonneg _
  have hqN : 0 < q / N := div_pos hq hN
  have h1 : Real.sqrt (q * ε) < adv - q / N := by linarith
  have h2 : Real.sqrt (q * ε) < adv := by linarith
  have hprod : q * ε < adv * (adv - q / N) := by
    have hsq : q * ε ≤ Real.sqrt (q * ε) * Real.sqrt (q * ε) := by
      by_cases hε : 0 ≤ q * ε
      · rw [Real.mul_self_sqrt hε]
      · have := Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hε)
        rw [this]; nlinarith
    nlinarith
  have heq : adv * (adv / q - 1 / N) = adv * (adv - q / N) / q := by
    field_simp
  rw [heq, div_le_iff₀ hq] at h
  linarith

/-- **BIP 459 is unforgeable under AOMDL**, in the form of the paper's Theorem 2:
with `q = qh + qs + 1`, the forger's success probability is at most
`sqrt (q * (omdl + coll)) + q / n`. -/
theorem unforgeable_sqrt (hN : N < n) (qh : ℕ) (hA : ∀ coins P, HashBound (A coins P) qh) :
    forgeAdvantage C nonceCoef N qs A ≤
      Real.sqrt ((qh + qs + 1 : ℕ) * (omdlAdvantage C (2 * qs + 1) (reduction C nonceCoef N qs A) +
        collisionAdvantage C nonceCoef N qs A)) + (qh + qs + 1 : ℕ) / n :=
  le_sqrt_of_fork_bound (Nat.cast_pos.mpr (Nat.succ_pos _))
    (Nat.cast_pos.mpr (Fact.out : n.Prime).pos) (unforgeable C nonceCoef N qs A hN qh hA)

end Dahlias.Security
