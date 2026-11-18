import Dahlias.Proofs.GameBound

/-!
# Forking the unforgeability game

`forge_fork`: if the adversary forges with probability `adv`, then with
probability at least `adv * (adv / q - 1 / n)`, `q = qh + qs + 1`, it forges
twice at the same fork point: once with the table `T` and once with the table
that has a fresh value `s ≠ T z` at the fork point `z`, everything else being
equal (`ForkEvent`).
-/

set_option linter.unusedSectionVars false

namespace Dahlias.Security

open Taproot QTree

variable {n : ℕ} [Fact n.Prime] {E X M : Type} [AddCommGroup E] [DecidableEq E] [DecidableEq X]
  [DecidableEq M] (C : Curve n E X) (nonceCoef : E → E → List (X × M × E) → ZMod n) (N qs : ℕ)
  {Coins : Type} (A : Adversary n N E X M Coins)

/-- The nonces of a sample as scalars. -/
def noncesOf (ν : Fin qs → (ZMod n)ˣ × (ZMod n)ˣ) : Fin qs → SecNonce n :=
  fun k => ((ν k).1, (ν k).2)

/-- The game algorithm of a sample without its table. -/
def sampleTree (ω : (ZMod n)ˣ × (Fin qs → (ZMod n)ˣ × (ZMod n)ˣ) × Coins) :
    QTree (SigIn N X M) (ZMod n) (Forgery n X M × SignerState X M) :=
  gameTree C nonceCoef N qs (ω.1 : ZMod n) (noncesOf qs ω.2.1) A ω.2.2

/-- **The fork event**: the adversary forges on the sample, and forges again
with the same fork point when the table gets the new value `s` there. -/
def ForkEvent (p : ForgeSample n N qs X M Coins × ZMod n) : Prop :=
  Forks (sampleTree C nonceCoef N qs A (p.1.1, p.1.2.1, p.1.2.2.1))
    (gameSel C nonceCoef N (p.1.1 : ZMod n)) p.1.2.2.2 p.2

theorem forgeExperiment_iff (ω : ForgeSample n N qs X M Coins) :
    forgeExperiment C nonceCoef N qs A ω ↔
      Accepts (sampleTree C nonceCoef N qs A (ω.1, ω.2.1, ω.2.2.1))
        (gameSel C nonceCoef N (ω.1 : ZMod n)) ω.2.2.2 :=
  wins_iff_accepts C nonceCoef N qs (ω.1 : ZMod n) (noncesOf qs ω.2.1) A ω.2.2.1 ω.2.2.2

variable [Fintype Coins] [Fintype (SigIn N X M)]

/- Instance search does not find these by itself. -/
noncomputable instance : Fintype (ForgeSample n N qs X M Coins × ZMod n) := instFintypeProd _ _

noncomputable instance : Fintype ((((ZMod n)ˣ × (Fin qs → (ZMod n)ˣ × (ZMod n)ˣ) × Coins) ×
    (SigIn N X M → ZMod n)) × ZMod n) := instFintypeProd _ _

/-- Samples with the table split off. -/
def splitTable :
    ((ZMod n)ˣ × (Fin qs → (ZMod n)ˣ × (ZMod n)ˣ) × Coins) × (SigIn N X M → ZMod n) ≃
      ForgeSample n N qs X M Coins where
  toFun p := (p.1.1, p.1.2.1, p.1.2.2, p.2)
  invFun ω := ((ω.1, ω.2.1, ω.2.2.1), ω.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Forking the unforgeability game.** -/
theorem forge_fork (qh : ℕ) (hA : ∀ coins P, HashBound (A coins P) qh) :
    forgeAdvantage C nonceCoef N qs A *
        (forgeAdvantage C nonceCoef N qs A / (qh + qs + 1 : ℕ) - 1 / n) ≤
      prob (ForkEvent C nonceCoef N qs A) := by
  have h := localFork_prob (S := ZMod n) (q := qh + qs + 1) (Nat.succ_pos _)
    (sampleTree C nonceCoef N qs A) (fun ω => gameSel C nonceCoef N (ω.1 : ZMod n))
    (fun ω T => length_fresh_gameTree C nonceCoef N qs (ω.1 : ZMod n) (noncesOf qs ω.2.1) A
      ω.2.2 T qh (hA _ _))
  have hadv : forgeAdvantage C nonceCoef N qs A =
      prob fun p : ((ZMod n)ˣ × (Fin qs → (ZMod n)ˣ × (ZMod n)ˣ) × Coins) ×
        (SigIn N X M → ZMod n) =>
          Accepts (sampleTree C nonceCoef N qs A p.1)
            (gameSel C nonceCoef N (p.1.1 : ZMod n)) p.2 := by
    unfold forgeAdvantage
    rw [← prob_equiv (splitTable N qs)]
    congr 1
    funext p
    exact propext (forgeExperiment_iff C nonceCoef N qs A _)
  have hfork : prob (ForkEvent C nonceCoef N qs A) =
      prob fun p : (((ZMod n)ˣ × (Fin qs → (ZMod n)ˣ × (ZMod n)ˣ) × Coins) ×
        (SigIn N X M → ZMod n)) × ZMod n =>
          Forks (sampleTree C nonceCoef N qs A p.1.1)
            (gameSel C nonceCoef N (p.1.1.1 : ZMod n)) p.1.2 p.2 := by
    rw [← prob_equiv ((splitTable N qs).prodCongr (Equiv.refl (ZMod n)))]
    rfl
  rw [hadv, hfork]
  simpa [ZMod.card] using h

end Dahlias.Security
