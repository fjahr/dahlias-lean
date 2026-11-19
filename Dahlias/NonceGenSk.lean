import Dahlias.NonceGen

/-!
# `NonceGen` with the optional secret key argument

With the argument `sk`, BIP 459's `NonceGen` draws `rand'` and uses
`rand = sk xor hash_BIP0459/aux(rand')` in place of a uniform `rand`.

Here `hash_BIP0459/aux` is a third random oracle `Aux`, which the adversary
may query, and `mask x` is the map `r ↦ bytes(x) xor r`, any family of
bijections. `nonceGenSk_advantage`: an adversary that makes at most `qa`
queries to `Aux` wins this game at most `qs² / |Rp| + qs⋅qa / |Rp|` more often
than the adversary that answers those queries itself wins the game of
`Dahlias.NonceGen`, where `rand` is uniform. The two terms: two slots draw the
same `rand'`, the adversary queries `Aux` on a `rand'` of the signer.

So the optional argument costs nothing when `rand'` is uniform. What it is
for, protection when `rand'` is not uniform, is outside the model.
-/

set_option linter.unusedSectionVars false

namespace Dahlias.Security

open Taproot Function QTree

variable {n : ℕ} [Fact n.Prime] {E X M : Type} [AddCommGroup E] [DecidableEq E] [DecidableEq X]
  [DecidableEq M]

/-! ## Answering a second oracle inside the handler -/

section Second

variable {Q : Type} {R : Q → Type} {D W α σ : Type}

/-- A handler for the queries `Q` extended by a table for the queries of `G`. -/
def handG (G : D → W) (h : (q : Q) → σ → R q × σ) : (q : Q ⊕ D) → σ → SumR R W q × σ
  | .inl q, s => h q s
  | .inr z, s => (G z, s)

theorem run_answerG (G : D → W) (h : (q : Q) → σ → R q × σ)
    (t : Alg (Q ⊕ D) (SumR R W) α) (s : σ) :
    (answerG G t).run h s = t.run (handG G h) s := by
  induction t generalizing s with
  | done a => rfl
  | ask x f ih =>
    cases x with
    | inl x => exact ih _ _
    | inr z => exact ih _ _

end Second

/-! ## The game -/

variable (C : Curve n E X) (nonceCoef : E → E → List (X × M × E) → ZMod n) (N qs : ℕ)
  {Rnd Rp Ex W Coins : Type}

/-- An adversary that may also query `hash_BIP0459/aux`. -/
abbrev SkAdversary (n N : ℕ) (E X M Rnd Rp Ex W Coins : Type) :=
  Coins → E → Alg (((AdvQ n N E X M ⊕ Ex) ⊕ (Rnd × Ex × Bool)) ⊕ Rp)
    (SumR (SumR (SumR AdvR Unit) W) Rnd) (Forgery n X M)

/-- The adversary for the game of `Dahlias.NonceGen` that answers the queries
to `hash_BIP0459/aux` from a table in its coins. -/
def withAux (A : SkAdversary n N E X M Rnd Rp Ex W Coins) :
    NAdversary n N E X M Rnd Ex W (Coins × (Rp → Rnd)) :=
  fun c P => answerG c.2 (A c.1 P)

variable (A : SkAdversary n N E X M Rnd Rp Ex W Coins) (ρ : W → ZMod n) (e₀ : Ex)
  (mask : (ZMod n)ˣ → Rnd ≃ Rnd)

/-- The game with the `rand` of every slot given by `v`, masked with the
secret key, and the table `Aux` for the adversary's queries. -/
def winSk (θ : Rest n N X M Coins × (Rnd × Ex × Bool → W)) (Aux : Rp → Rnd)
    (v : Fin qs → Rnd) : Prop :=
  nonceGenExperiment C nonceCoef N qs (fun c P => answerG Aux (A c P)) ρ e₀
    ((θ.1, fun k => mask θ.1.1 (v k)), θ.2)

/-- **The unforgeability game with `NonceGen` and its `sk` argument** on one
sample: the `rand` of slot `k` is `mask x (Aux (rand' k))`. -/
def nonceGenSkExperiment
    (ω : ((Rest n N X M Coins × (Rnd × Ex × Bool → W)) × (Fin qs → Rp)) × (Rp → Rnd)) : Prop :=
  winSk C nonceCoef N qs A ρ e₀ mask ω.1.1 ω.2 fun k => ω.2 (ω.1.2 k)

variable [Fintype Coins] [Fintype (SigIn N X M)] [Fintype Rnd] [DecidableEq Rnd] [Nonempty Rnd]
  [Fintype Rp] [DecidableEq Rp] [Nonempty Rp] [Fintype Ex] [DecidableEq Ex] [Fintype W]
  [Nonempty W]

/-- The adversary's advantage in the game with `NonceGen` and its `sk`
argument. -/
noncomputable def nonceGenSkAdvantage : ℝ :=
  prob (nonceGenSkExperiment C nonceCoef N qs A ρ e₀ mask)

/-- The samples of the game of `Dahlias.NonceGen` for `withAux A`, from the
parts used here. -/
def toNonceGenSample :
    (((Rest n N X M Coins × (Rnd × Ex × Bool → W)) × (Rp → Rnd)) × (Fin qs → Rnd)) ≃
      (Rest n N X M (Coins × (Rp → Rnd)) × (Fin qs → Rnd)) × (Rnd × Ex × Bool → W) where
  toFun s := (((s.1.1.1.1, (s.1.1.1.2.1, s.1.2), s.1.1.1.2.2), s.2), s.1.1.2)
  invFun t := ((((t.1.1.1, t.1.1.2.1.1, t.1.1.2.2), t.2), t.1.1.2.1.2), t.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

set_option synthInstance.maxSize 4000 in
/-- **The `sk` argument of `NonceGen` costs at most two error terms** over
`NonceGen` with a uniform `rand`. -/
theorem nonceGenSk_le (qa : ℕ) (hA : ∀ c P, NBound (A c P) qa) :
    nonceGenSkAdvantage C nonceCoef N qs A ρ e₀ mask ≤
      nonceGenAdvantage C nonceCoef N qs (withAux N A) ρ e₀ +
        (qs : ℝ) ^ 2 / Fintype.card Rp + qs * (qa / Fintype.card Rp) := by
  have H := oracle_hop (Θ := Rest n N X M Coins × (Rnd × Ex × Bool → W)) (D := Rp) (W := Rnd)
    (ι := Fin qs) (fun r => r) (fun r hr => hr) id (fun r i => ⟨i, rfl⟩)
    (winSk C nonceCoef N qs A ρ e₀ mask)
    (fun θ Aux v => gLog Aux
      (handG θ.2 (challengerE C nonceCoef N qs
        (nvOf qs ρ fun i => θ.2 (noncePt qs (fun k => mask θ.1.1 (v k)) i))
        (θ.1.1 : ZMod n) θ.1.2.2))
      (A θ.1.2.1 (C.mulG (θ.1.1 : ZMod n))) (⟨0, [], []⟩, fun _ => e₀))
    (fun θ Aux Aux' v h => by
      unfold winSk nonceGenExperiment winE
      dsimp only
      simp only [run_answerG]
      rw [← run_answerG Aux' (handG θ.2 _), ← run_answerG Aux (handG θ.2 _),
        answerG_congr Aux Aux' _ _ _ h])
    qa (fun θ Aux v => length_gLog _ _ _ _ _ (hA _ _))
  have hid : prob (fun s : ((Rest n N X M Coins × (Rnd × Ex × Bool → W)) × (Rp → Rnd)) ×
      (Fin qs → Rnd) => winSk C nonceCoef N qs A ρ e₀ mask s.1.1 s.1.2 s.2) =
      nonceGenAdvantage C nonceCoef N qs (withAux N A) ρ e₀ := by
    -- the masked values are uniform
    have hmask : ∀ a : (Rest n N X M Coins × (Rnd × Ex × Bool → W)) × (Rp → Rnd),
        prob (fun u : Fin qs → Rnd => winSk C nonceCoef N qs A ρ e₀ mask a.1 a.2 u) =
          prob (fun r : Fin qs → Rnd => nonceGenExperiment C nonceCoef N qs
            (fun c P => answerG a.2 (A c P)) ρ e₀ ((a.1.1, r), a.1.2)) := by
      intro a
      have h := prob_equiv (Equiv.piCongrRight fun _ : Fin qs => mask a.1.1.1)
        (fun r : Fin qs → Rnd => nonceGenExperiment C nonceCoef N qs
          (fun c P => answerG a.2 (A c P)) ρ e₀ ((a.1.1, r), a.1.2))
      rw [← h]
      rfl
    have hstep := prob_prod_congr
      (fun s : ((Rest n N X M Coins × (Rnd × Ex × Bool → W)) × (Rp → Rnd)) × (Fin qs → Rnd) =>
        winSk C nonceCoef N qs A ρ e₀ mask s.1.1 s.1.2 s.2)
      (fun s : ((Rest n N X M Coins × (Rnd × Ex × Bool → W)) × (Rp → Rnd)) × (Fin qs → Rnd) =>
        nonceGenExperiment C nonceCoef N qs (fun c P => answerG s.1.2 (A c P)) ρ e₀
          ((s.1.1.1, s.2), s.1.1.2)) hmask
    rw [hstep]
    unfold nonceGenAdvantage
    rw [← prob_equiv (toNonceGenSample (n := n) (N := N) (X := X) (M := M) (Coins := Coins)
      (Rnd := Rnd) (Rp := Rp) (Ex := Ex) (W := W) qs)
      (nonceGenExperiment C nonceCoef N qs (withAux N A) ρ e₀)]
    rfl
  unfold nonceGenSkAdvantage nonceGenSkExperiment
  rw [hid] at H
  exact H

set_option synthInstance.maxSize 4000 in
/-- **`NonceGen` with its `sk` argument**, against the game with uniform
nonces: the error terms of the two random oracles and of the reduction modulo
the group order. -/
theorem nonceGenSk_advantage (g : (ZMod n)ˣ → W) (hg : Injective g) (hρ : ∀ u, ρ (g u) = u)
    (qn qa : ℕ) (hA : ∀ c P, NBound (A c P) qa)
    (hG : ∀ c P (Aux : Rp → Rnd), NBound (answerG Aux (A c P)) qn) :
    nonceGenSkAdvantage C nonceCoef N qs A ρ e₀ mask ≤
      forgeAdvantage C nonceCoef N qs (withTable N (withAux N A)) +
        (qs : ℝ) ^ 2 / Fintype.card Rnd + qs * (qn / Fintype.card Rnd) +
        (2 * qs : ℕ) * ((Fintype.card W - Fintype.card (ZMod n)ˣ : ℝ) / Fintype.card W) +
        (qs : ℝ) ^ 2 / Fintype.card Rp + qs * (qa / Fintype.card Rp) := by
  have h1 := nonceGenSk_le C nonceCoef N qs A ρ e₀ mask qa hA
  have h2 := nonceGen_advantage C nonceCoef N qs (withAux N A) ρ e₀ g hg hρ qn
    fun c P => hG c.1 P c.2
  linarith

end Dahlias.Security
