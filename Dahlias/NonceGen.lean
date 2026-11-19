import Dahlias.NonceProb
import Dahlias.Unforgeability

/-!
# `NonceGen`: nonces derived with a hash function

The unforgeability game of `Dahlias.Security` gives the honest signer uniform
nonzero nonces. BIP 459's `NonceGen` instead draws `rand` and lets
`rᵢ = int(hash_BIP0459/nonce(rand ‖ extra_in ‖ i)) mod n`.

Here `hash_BIP0459/nonce` is a second random oracle `G`, which the adversary
may query, with inputs `(rand, extra_in, i)` and outputs in a type `W` that
`ρ` maps to scalars. In session `k` the signer draws a uniform `rand` and uses
the fixed value `ex k` as `extra_in`.

`nonceGen_advantage`: an adversary that makes at most `qn` queries to `G`
wins this game with at most the probability with which the adversary
`withTable A`, which answers those queries itself, wins the game with uniform
nonces, plus

  `qs² / |Rnd| + qs⋅qn / |Rnd| + 2⋅qs⋅(|W| - (n - 1)) / |W|`.

The three terms: two sessions draw the same `rand`, the adversary queries `G`
on a `rand` of the signer, a derived nonce is zero or in the part of `W` where
`mod n` is not uniform.

Not modelled: the optional `sk` argument (`rand = sk xor hash(rand')`), an
`extra_in` that the adversary chooses, and `rand` that is not uniform.
-/

set_option linter.unusedSectionVars false

namespace Dahlias.Security

open Taproot Function

variable {n : ℕ} [Fact n.Prime] {E X M : Type} [AddCommGroup E] [DecidableEq E] [DecidableEq X]
  [DecidableEq M]

/-! ## Algorithms with a second oracle -/

section Second

variable {Q : Type} {R : Q → Type} {D W α σ : Type}

/-- The answers to the queries `Q` and to the queries of `G`. -/
def SumR (R : Q → Type) (W : Type) : Q ⊕ D → Type
  | .inl q => R q
  | .inr _ => W

/-- Answer the queries of `G` from a table. -/
def answerG (G : D → W) : Alg (Q ⊕ D) (SumR R W) α → Alg Q R α
  | .done a => .done a
  | .ask (.inl q) f => .ask q fun r => answerG G (f r)
  | .ask (.inr z) f => answerG G (f (G z))

/-- The queries to `G` in a run. -/
def gLog (G : D → W) (h : (q : Q) → σ → R q × σ) : Alg (Q ⊕ D) (SumR R W) α → σ → List D
  | .done _, _ => []
  | .ask (.inl q) f, s => gLog G h (f (h q s).1) (h q s).2
  | .ask (.inr z) f, s => z :: gLog G h (f (G z)) s

/-- At most `q` queries to `G`, whatever the answers. -/
def NBound : Alg (Q ⊕ D) (SumR R W) α → ℕ → Prop
  | .done _, _ => True
  | .ask (.inl _) f, q => ∀ r, NBound (f r) q
  | .ask (.inr _) f, q => 0 < q ∧ ∀ r, NBound (f r) (q - 1)

theorem length_gLog (G : D → W) (h : (q : Q) → σ → R q × σ)
    (t : Alg (Q ⊕ D) (SumR R W) α) (s : σ) (q : ℕ) (ht : NBound t q) :
    (gLog G h t s).length ≤ q := by
  induction t generalizing s q with
  | done a => simp [gLog]
  | ask x f ih =>
    cases x with
    | inl x => exact ih _ _ _ (ht _)
    | inr z =>
      obtain ⟨hq, hr⟩ : 0 < q ∧ ∀ r, NBound (f r) (q - 1) := ht
      have := ih (G z) s (q - 1) (hr _)
      simp only [gLog, List.length_cons]
      omega

/-- A run depends on `G` only at the points it queries. -/
theorem answerG_congr (G G' : D → W) (h : (q : Q) → σ → R q × σ)
    (t : Alg (Q ⊕ D) (SumR R W) α) (s : σ) (hG : ∀ z ∈ gLog G h t s, G' z = G z) :
    (answerG G' t).run h s = (answerG G t).run h s := by
  induction t generalizing s with
  | done a => rfl
  | ask x f ih =>
    cases x with
    | inl x => exact ih _ _ hG
    | inr z =>
      have hz : G' z = G z := hG z (by simp [gLog])
      change (answerG G' (f (G' z))).run h s = (answerG G (f (G z))).run h s
      rw [hz]
      exact ih _ _ fun y hy => hG y (by simp [gLog, hy])

end Second

/-! ## The game -/

variable (C : Curve n E X) (nonceCoef : E → E → List (X × M × E) → ZMod n) (N qs : ℕ)
  {Rnd Ex W Coins : Type}

/-- An adversary that may also query `hash_BIP0459/nonce`. -/
abbrev NAdversary (n N : ℕ) (E X M Rnd Ex W Coins : Type) :=
  Coins → E → Alg (AdvQ n N E X M ⊕ (Rnd × Ex × Bool)) (SumR AdvR W) (Forgery n X M)

/-- The adversary for the game with uniform nonces that answers the queries to
`hash_BIP0459/nonce` from a table in its coins. -/
def withTable (A : NAdversary n N E X M Rnd Ex W Coins) :
    Adversary n N E X M (Coins × (Rnd × Ex × Bool → W)) :=
  fun c P => answerG c.2 (A c.1 P)

variable (A : NAdversary n N E X M Rnd Ex W Coins)

/-- The part of the sample that the nonces do not depend on: the secret key,
the adversary's coins and the challenge hash. -/
abbrev Rest (n N : ℕ) (X M Coins : Type) := (ZMod n)ˣ × Coins × (SigIn N X M → ZMod n)

/-- The game for given nonces `v` and a given table `G`. -/
def winOf (θ : Rest n N X M Coins) (G : Rnd × Ex × Bool → W) (v : Fin qs × Bool → ZMod n) :
    Prop :=
  let x : ZMod n := θ.1
  let out := (answerG G (A θ.2.1 (C.mulG x))).run
    (challenger C nonceCoef N qs x (fun k => (v (k, false), v (k, true))) θ.2.2) ⟨0, [], []⟩
  Wins C nonceCoef N x θ.2.2 out.1 out.2

/-- The input of `hash_BIP0459/nonce` for nonce `i` of a session. -/
def noncePt (ex : Fin qs → Ex) (rands : Fin qs → Rnd) (i : Fin qs × Bool) : Rnd × Ex × Bool :=
  (rands i.1, ex i.1, i.2)

theorem noncePt_injective (ex : Fin qs → Ex) {rands : Fin qs → Rnd} (h : Injective rands) :
    Injective (noncePt qs ex rands) := by
  rintro ⟨k, b⟩ ⟨k', b'⟩ heq
  simp only [noncePt, Prod.mk.injEq] at heq
  rw [h heq.1, heq.2.2]

variable (ρ : W → ZMod n) (ex : Fin qs → Ex)

/-- **The unforgeability game with `NonceGen`** on one sample: the nonces of
session `k` are `ρ (G (rand k, ex k, i))`. -/
def nonceGenExperiment
    (ω : (Rest n N X M Coins × (Fin qs → Rnd)) × (Rnd × Ex × Bool → W)) : Prop :=
  winOf C nonceCoef N qs A ω.1.1 ω.2 fun i => ρ (ω.2 (noncePt qs ex ω.1.2 i))

/-- The queries to `hash_BIP0459/nonce` in a run of the game. -/
def nLog (θ : Rest n N X M Coins) (G : Rnd × Ex × Bool → W) (v : Fin qs × Bool → ZMod n) :
    List (Rnd × Ex × Bool) :=
  gLog G (challenger C nonceCoef N qs (θ.1 : ZMod n) (fun k => (v (k, false), v (k, true))) θ.2.2)
    (A θ.2.1 (C.mulG (θ.1 : ZMod n))) ⟨0, [], []⟩

theorem winOf_congr (θ : Rest n N X M Coins) (G G' : Rnd × Ex × Bool → W)
    (v : Fin qs × Bool → ZMod n) (h : ∀ z ∈ nLog C nonceCoef N qs A θ G v, G' z = G z) :
    winOf C nonceCoef N qs A θ G' v ↔ winOf C nonceCoef N qs A θ G v := by
  unfold winOf
  simp only
  rw [answerG_congr G G' _ _ _ h]

variable [Fintype Coins] [Fintype (SigIn N X M)] [Fintype Rnd] [Fintype Ex] [Fintype W]
  [DecidableEq Rnd] [DecidableEq Ex]

/-- The adversary's advantage in the game with `NonceGen`. -/
noncomputable def nonceGenAdvantage : ℝ := prob (nonceGenExperiment C nonceCoef N qs A ρ ex)

variable [Nonempty W] [Nonempty Rnd]

/-- For distinct `rand`s: the game with nonces from `G` is the game with
independent nonces, unless the adversary queries `G` on a `rand`. -/
theorem prob_real_le (θ : Rest n N X M Coins) (rands : Fin qs → Rnd) (hinj : Injective rands) :
    prob (fun G : Rnd × Ex × Bool → W =>
        winOf C nonceCoef N qs A θ G fun i => ρ (G (noncePt qs ex rands i))) ≤
      prob (fun y : (Rnd × Ex × Bool → W) × (Fin qs × Bool → W) =>
        winOf C nonceCoef N qs A θ y.1 (fun i => ρ (y.2 i)) ∨
          ∃ k, rands k ∈ (nLog C nonceCoef N qs A θ y.1 fun i => ρ (y.2 i)).map Prod.fst) := by
  have hp := noncePt_injective qs ex hinj
  rw [← prob_fst (B := Fin qs × Bool → W) (fun G : Rnd × Ex × Bool → W =>
    winOf C nonceCoef N qs A θ G fun i => ρ (G (noncePt qs ex rands i)))]
  rw [← prob_equiv (Involutive.toPerm _ (swapAt_involutive (W := W) hp))
    (fun y : (Rnd × Ex × Bool → W) × (Fin qs × Bool → W) =>
        winOf C nonceCoef N qs A θ y.1 (fun i => ρ (y.2 i)) ∨
          ∃ k, rands k ∈ (nLog C nonceCoef N qs A θ y.1 fun i => ρ (y.2 i)).map Prod.fst)]
  refine prob_mono ?_
  rintro ⟨G, w⟩ hR
  change winOf C nonceCoef N qs A θ (overwrite (noncePt qs ex rands) G w)
      (fun i => ρ (G (noncePt qs ex rands i))) ∨
    ∃ k, rands k ∈ (nLog C nonceCoef N qs A θ (overwrite (noncePt qs ex rands) G w)
      fun i => ρ (G (noncePt qs ex rands i))).map Prod.fst
  by_cases hb : ∃ k, rands k ∈ (nLog C nonceCoef N qs A θ (overwrite (noncePt qs ex rands) G w)
      fun i => ρ (G (noncePt qs ex rands i))).map Prod.fst
  · exact Or.inr hb
  · refine Or.inl ((winOf_congr C nonceCoef N qs A θ _ G _ fun z hz => ?_).mp hR)
    refine (overwrite_of_ne G w fun i hi => hb ⟨i.1, ?_⟩).symm
    exact List.mem_map.mpr ⟨z, hz, by rw [← hi]; rfl⟩

/-- The samples with the `rand`s moved to the end. -/
def moveRands {Θ Rs Gt Ws : Type} : (Θ × Rs) × (Gt × Ws) ≃ ((Θ × Gt) × Ws) × Rs where
  toFun s := (((s.1.1, s.2.1), s.2.2), s.1.2)
  invFun t := ((t.1.1.1, t.2), (t.1.1.2, t.1.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The sample of the game with uniform nonces, from the parts used here. -/
def toForgeSample : (Rest n N X M Coins × (Rnd × Ex × Bool → W)) × (Fin qs × Bool → (ZMod n)ˣ) ≃
    ForgeSample n N qs X M (Coins × (Rnd × Ex × Bool → W)) where
  toFun s := (s.1.1.1, (fun k => (s.2 (k, false), s.2 (k, true))), (s.1.1.2.1, s.1.2), s.1.1.2.2)
  invFun f := (((f.1, f.2.2.1.1, f.2.2.2), f.2.2.1.2),
    fun i => if i.2 then (f.2.1 i.1).2 else (f.2.1 i.1).1)
  left_inv := by
    rintro ⟨⟨⟨x, c, T⟩, G⟩, u⟩
    refine Prod.ext rfl ?_
    funext ⟨k, b⟩
    cases b <;> rfl
  right_inv _ := rfl

/-- The game with independent nonces `ρ (w i)`. -/
def idealExperiment
    (s : (Rest n N X M Coins × (Rnd × Ex × Bool → W)) × (Fin qs × Bool → W)) : Prop :=
  winOf C nonceCoef N qs A s.1.1 s.1.2 fun i => ρ (s.2 i)

/-- In the game with independent nonces the adversary queries
`hash_BIP0459/nonce` on one of the `rand`s. -/
def badQuery (t : ((Rest n N X M Coins × (Rnd × Ex × Bool → W)) × (Fin qs × Bool → W)) ×
    (Fin qs → Rnd)) : Prop :=
  ∃ k, t.2 k ∈ (nLog C nonceCoef N qs A t.1.1.1 t.1.1.2 fun i => ρ (t.1.2 i)).map Prod.fst

set_option synthInstance.maxSize 4000 in
/-- **`NonceGen` costs at most the three error terms.** -/
theorem nonceGen_advantage (g : (ZMod n)ˣ → W) (hg : Injective g) (hρ : ∀ u, ρ (g u) = u)
    (qn : ℕ) (hA : ∀ c P, NBound (A c P) qn) :
    nonceGenAdvantage C nonceCoef N qs A ρ ex ≤
      forgeAdvantage C nonceCoef N qs (withTable N A) +
        (qs : ℝ) ^ 2 / Fintype.card Rnd + qs * (qn / Fintype.card Rnd) +
        (2 * qs : ℕ) * ((Fintype.card W - Fintype.card (ZMod n)ˣ : ℝ) / Fintype.card W) := by
  have hRnd : (0 : ℝ) < Fintype.card Rnd := Nat.cast_pos.mpr Fintype.card_pos
  -- colliding `rand`s
  have h1 := prob_le_add (p := nonceGenExperiment C nonceCoef N qs A ρ ex)
    (q := fun ω => ¬Injective ω.1.2)
    (r := fun ω => Injective ω.1.2 ∧ nonceGenExperiment C nonceCoef N qs A ρ ex ω)
    fun ω hω => by
      by_cases h : Injective ω.1.2
      · exact Or.inr ⟨h, hω⟩
      · exact Or.inl h
  have h2 : prob (fun ω : (Rest n N X M Coins × (Fin qs → Rnd)) × (Rnd × Ex × Bool → W) =>
      ¬Injective ω.1.2) ≤ (qs : ℝ) ^ 2 / Fintype.card Rnd :=
    prob_prod_le _ _ (by positivity) fun G =>
      prob_prod_le' (fun a : Rest n N X M Coins × (Fin qs → Rnd) => ¬Injective a.2) _
        (by positivity) fun θ => prob_not_injective
  -- distinct `rand`s
  have h3 : prob (fun ω : (Rest n N X M Coins × (Fin qs → Rnd)) × (Rnd × Ex × Bool → W) =>
      Injective ω.1.2 ∧ nonceGenExperiment C nonceCoef N qs A ρ ex ω) ≤
      prob (fun s : (Rest n N X M Coins × (Fin qs → Rnd)) ×
          ((Rnd × Ex × Bool → W) × (Fin qs × Bool → W)) =>
        (idealExperiment C nonceCoef N qs A ρ) (moveRands s).1 ∨
          (badQuery C nonceCoef N qs A ρ) (moveRands s)) + 0 := by
    refine prob_prod_mono _ _ 0 le_rfl fun a => ?_
    rw [add_zero]
    by_cases hinj : Injective a.2
    · refine le_trans (prob_mono ?_) (prob_real_le C nonceCoef N qs A ρ ex a.1 a.2 hinj)
      intro G h
      exact h.2
    · have h0 : prob (fun _ : Rnd × Ex × Bool → W => False) = 0 := by
        unfold prob
        simp
      refine le_trans (prob_mono (q := fun _ => False) ?_) (h0.le.trans (prob_nonneg _))
      intro G h
      exact hinj h.1
  rw [add_zero] at h3
  have h4 := prob_le_add (p := fun s : (Rest n N X M Coins × (Fin qs → Rnd)) ×
          ((Rnd × Ex × Bool → W) × (Fin qs × Bool → W)) =>
        (idealExperiment C nonceCoef N qs A ρ) (moveRands s).1 ∨
          (badQuery C nonceCoef N qs A ρ) (moveRands s))
    (q := fun s => (idealExperiment C nonceCoef N qs A ρ) (moveRands s).1)
    (r := fun s => (badQuery C nonceCoef N qs A ρ) (moveRands s)) fun s h => h
  have h5 : prob (fun s : (Rest n N X M Coins × (Fin qs → Rnd)) ×
      ((Rnd × Ex × Bool → W) × (Fin qs × Bool → W)) =>
        (idealExperiment C nonceCoef N qs A ρ) (moveRands s).1) =
      prob (idealExperiment C nonceCoef N qs A ρ) := by
    rw [prob_equiv moveRands (fun t => (idealExperiment C nonceCoef N qs A ρ) t.1)]
    exact prob_fst (idealExperiment C nonceCoef N qs A ρ)
  have h6 : prob (fun s : (Rest n N X M Coins × (Fin qs → Rnd)) ×
      ((Rnd × Ex × Bool → W) × (Fin qs × Bool → W)) =>
        (badQuery C nonceCoef N qs A ρ) (moveRands s)) ≤
      qs * (qn / Fintype.card Rnd) := by
    rw [prob_equiv moveRands (badQuery C nonceCoef N qs A ρ)]
    refine prob_prod_le' (badQuery C nonceCoef N qs A ρ) _ (by positivity) fun a => ?_
    have hh := prob_hit (qs := qs)
      ((nLog C nonceCoef N qs A a.1.1 a.1.2 fun i => ρ (a.2 i)).map Prod.fst)
    have hl : ((nLog C nonceCoef N qs A a.1.1 a.1.2 fun i => ρ (a.2 i)).map Prod.fst).length ≤
        qn := by
      rw [List.length_map]
      exact length_gLog _ _ _ _ _ (hA _ _)
    refine le_trans (le_of_eq ?_) (hh.trans ?_)
    · unfold badQuery
      rfl
    · gcongr
  -- from derived nonces to uniform nonzero scalars
  have h7 : prob (idealExperiment C nonceCoef N qs A ρ) ≤
      forgeAdvantage C nonceCoef N qs (withTable N A) +
      (2 * qs : ℕ) * ((Fintype.card W - Fintype.card (ZMod n)ˣ : ℝ) / Fintype.card W) := by
    have hle : Fintype.card (ZMod n)ˣ ≤ Fintype.card W := Fintype.card_le_of_injective g hg
    have hc : (0 : ℝ) ≤ (2 * qs : ℕ) *
        ((Fintype.card W - Fintype.card (ZMod n)ˣ : ℝ) / Fintype.card W) := by
      have : (0 : ℝ) ≤ Fintype.card W - Fintype.card (ZMod n)ˣ :=
        sub_nonneg.mpr (Nat.cast_le.mpr hle)
      positivity
    have hs := prob_prod_mono (idealExperiment C nonceCoef N qs A ρ)
      (fun s : (Rest n N X M Coins × (Rnd × Ex × Bool → W)) × (Fin qs × Bool → (ZMod n)ˣ) =>
        winOf C nonceCoef N qs A s.1.1 s.1.2 fun i => ρ (g (s.2 i))) _ hc fun a => by
          have := prob_section (ι := Fin qs × Bool) g hg
            (fun w => winOf C nonceCoef N qs A a.1 a.2 fun i => ρ (w i))
          rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool] at this
          rw [show (2 * qs : ℕ) = qs * 2 from mul_comm 2 qs]
          exact this
    refine hs.trans (add_le_add (le_of_eq ?_) le_rfl)
    unfold forgeAdvantage forgeAdvantageG
    rw [← prob_equiv (toForgeSample (n := n) (N := N) (X := X) (M := M) (Coins := Coins)
      (Rnd := Rnd) (Ex := Ex) (W := W) qs) (forgeExperiment C nonceCoef N qs (withTable N A))]
    congr 1
    funext s
    simp only [hρ]
    rfl
  calc nonceGenAdvantage C nonceCoef N qs A ρ ex
      ≤ (qs : ℝ) ^ 2 / Fintype.card Rnd +
          (prob (idealExperiment C nonceCoef N qs A ρ) + qs * (qn / Fintype.card Rnd)) :=
        h1.trans (add_le_add h2 (h3.trans (h4.trans (add_le_add (le_of_eq h5) h6))))
    _ ≤ _ := by linarith

/-- **Unforgeability with `NonceGen`**, under AOMDL with both
`hash_BIP0459/sig` and `hash_BIP0459/nonce` as random oracles. -/
theorem nonceGen_unforgeable (g : (ZMod n)ˣ → W) (hg : Injective g) (hρ : ∀ u, ρ (g u) = u)
    (hN : N < n) (qh qn : ℕ) (hA : ∀ c P, NBound (A c P) qn)
    (hH : ∀ c P G, HashBound (answerG G (A c P)) qh) :
    nonceGenAdvantage C nonceCoef N qs A ρ ex ≤
      Real.sqrt ((qh + qs + 1 : ℕ) *
          (omdlAdvantage C (2 * qs + 1) (reduction C nonceCoef N qs (withTable N A)) +
            collisionAdvantage C nonceCoef N qs (withTable N A))) + (qh + qs + 1 : ℕ) / n +
        qs / (n - 1 : ℝ) +
        (qs : ℝ) ^ 2 / Fintype.card Rnd + qs * (qn / Fintype.card Rnd) +
        (2 * qs : ℕ) * ((Fintype.card W - Fintype.card (ZMod n)ˣ : ℝ) / Fintype.card W) := by
  have h1 := nonceGen_advantage C nonceCoef N qs A ρ ex g hg hρ qn hA
  have h2 := unforgeable_sqrt C nonceCoef N qs (withTable N A) hN qh fun c P => hH c.1 P c.2
  linarith

omit [Nonempty W] [Fintype W] in
/-- **`NonceGen` with hash outputs `0, …, m - 1` reduced modulo `n`**, as in
BIP 459 with `m = 2²⁵⁶`. -/
theorem nonceGen_advantage_fin {m : ℕ} (hm : n ≤ m)
    (A : NAdversary n N E X M Rnd Ex (Fin m) Coins) (qn : ℕ) (hA : ∀ c P, NBound (A c P) qn) :
    nonceGenAdvantage C nonceCoef N qs A (fun w => (w.val : ZMod n)) ex ≤
      forgeAdvantage C nonceCoef N qs (withTable N A) +
        (qs : ℝ) ^ 2 / Fintype.card Rnd + qs * (qn / Fintype.card Rnd) +
        (2 * qs : ℕ) * ((m - (n - 1) : ℝ) / m) := by
  have hn : 0 < n := (Fact.out : n.Prime).pos
  have : Nonempty (Fin m) := ⟨⟨0, lt_of_lt_of_le hn hm⟩⟩
  have h := nonceGen_advantage C nonceCoef N qs A (fun w : Fin m => (w.val : ZMod n)) ex
    (fun u => ⟨(u : ZMod n).val, lt_of_lt_of_le (ZMod.val_lt _) hm⟩)
    (fun u u' h => Units.ext (ZMod.val_injective n (Fin.mk.inj h)))
    (fun u => ZMod.natCast_zmod_val _) qn hA
  rw [ZMod.card_units_eq_totient, Nat.totient_prime Fact.out, Fintype.card_fin,
    Nat.cast_sub hn, Nat.cast_one] at h
  exact h

end Dahlias.Security
