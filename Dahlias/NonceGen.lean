import Dahlias.NonceProb
import Dahlias.Unforgeability
import Dahlias.Second

/-!
# `NonceGen`: nonces derived with a hash function

The unforgeability game of `Dahlias.Security` gives the honest signer uniform
nonzero nonces. BIP 459's `NonceGen` instead draws `rand` and lets
`rᵢ = int(hash_BIP0459/nonce(rand ‖ extra_in ‖ i)) mod n`.

Here `hash_BIP0459/nonce` is a second random oracle `G`, which the adversary
may query, with inputs `(rand, extra_in, i)` and outputs in a type `W` that
`ρ` maps to scalars. For every nonce slot the signer draws a uniform `rand`.
The adversary chooses the `extra_in` of the next slot (`setExtra`), whenever
and as often as it likes before the slot is used.

`nonceGen_advantage`: an adversary that makes at most `qn` queries to `G`
wins this game with at most the probability with which the adversary
`withTable A`, which answers those queries itself, wins the game with uniform
nonces, plus

  `qs² / |Rnd| + qs⋅qn / |Rnd| + 2⋅qs⋅(|W| - (n - 1)) / |W|`.

The three terms: two sessions draw the same `rand`, the adversary queries `G`
on a `rand` of the signer, a derived nonce is zero or in the part of `W` where
`mod n` is not uniform.

`Dahlias.NonceGenSk` adds the optional `sk` argument. A `rand` that is not
uniform is outside the model: the theorem assumes it is.
-/

set_option linter.unusedSectionVars false

namespace Dahlias.Security

open Taproot Function QTree

variable {n : ℕ} [Fact n.Prime] {E X M : Type} [AddCommGroup E] [DecidableEq E] [DecidableEq X]
  [DecidableEq M]

/-! ## The game -/

variable (C : Curve n E X) (nonceCoef : E → E → List (X × M × E) → ZMod n) (N qs : ℕ)
  {Rnd Ex W Coins : Type}

/-- An adversary that may also set the `extra_in` of the next nonce slot and
query `hash_BIP0459/nonce`. -/
abbrev NAdversary (n N : ℕ) (E X M Rnd Ex W Coins : Type) :=
  Coins → E → Alg ((AdvQ n N E X M ⊕ Ex) ⊕ (Rnd × Ex × Bool)) (SumR (SumR AdvR Unit) W)
    (Forgery n X M)

/-- The adversary for the game with uniform nonces: it answers the queries to
`hash_BIP0459/nonce` from a table in its coins and drops the `extra_in`. -/
def withTable (A : NAdversary n N E X M Rnd Ex W Coins) :
    Adversary n N E X M (Coins × (Rnd × Ex × Bool → W)) :=
  fun c P => answerG (fun _ : Ex => ()) (answerG c.2 (A c.1 P))

/-- The game's answers when the nonces of a slot depend on its `extra_in`.
The state has the `extra_in` chosen for every slot. -/
def challengerE (nv : Fin qs → Ex → SecNonce n) (x : ZMod n) (T : SigIn N X M → ZMod n) :
    (q : AdvQ n N E X M ⊕ Ex) → SignerState X M × (ℕ → Ex) →
      SumR AdvR Unit q × (SignerState X M × (ℕ → Ex))
  | .inl q, s =>
    ((challenger C nonceCoef N qs x (fun k => nv k (s.2 k)) T q s.1).1,
      ((challenger C nonceCoef N qs x (fun k => nv k (s.2 k)) T q s.1).2, s.2))
  | .inr e, s => ((), (s.1, update s.2 s.1.opened e))

variable (A : NAdversary n N E X M Rnd Ex W Coins)

/-- The part of the sample that the nonces do not depend on: the secret key,
the adversary's coins and the challenge hash. -/
abbrev Rest (n N : ℕ) (X M Coins : Type) := (ZMod n)ˣ × Coins × (SigIn N X M → ZMod n)

variable (ρ : W → ZMod n) (e₀ : Ex)

/-- The nonces of a slot from the values of `hash_BIP0459/nonce`. -/
def nvOf (v : Fin qs × Ex × Bool → W) : Fin qs → Ex → SecNonce n :=
  fun k e => (ρ (v (k, e, false)), ρ (v (k, e, true)))

/-- The game for nonces that depend on the `extra_in`, with the table `G`. -/
def winE (θ : Rest n N X M Coins) (G : Rnd × Ex × Bool → W) (nv : Fin qs → Ex → SecNonce n) :
    Prop :=
  let out := (answerG G (A θ.2.1 (C.mulG (θ.1 : ZMod n)))).run
    (challengerE C nonceCoef N qs nv (θ.1 : ZMod n) θ.2.2) (⟨0, [], []⟩, fun _ => e₀)
  Wins C nonceCoef N (θ.1 : ZMod n) θ.2.2 out.1 out.2.1

/-- The game for given nonces `v`, with the table `G`. -/
def winOf (θ : Rest n N X M Coins) (G : Rnd × Ex × Bool → W) (v : Fin qs × Bool → ZMod n) :
    Prop :=
  let x : ZMod n := θ.1
  let out := (answerG (fun _ : Ex => ()) (answerG G (A θ.2.1 (C.mulG x)))).run
    (challenger C nonceCoef N qs x (fun k => (v (k, false), v (k, true))) θ.2.2) ⟨0, [], []⟩
  Wins C nonceCoef N x θ.2.2 out.1 out.2

/-- The input of `hash_BIP0459/nonce` for a slot, an `extra_in` and a nonce
index. -/
def noncePt (rands : Fin qs → Rnd) (i : Fin qs × Ex × Bool) : Rnd × Ex × Bool :=
  (rands i.1, i.2.1, i.2.2)

theorem noncePt_injective {rands : Fin qs → Rnd} (h : Injective rands) :
    Injective (noncePt (Ex := Ex) qs rands) := by
  rintro ⟨k, e, b⟩ ⟨k', e', b'⟩ heq
  simp only [noncePt, Prod.mk.injEq] at heq
  rw [h heq.1, heq.2.1, heq.2.2]

/-- **The unforgeability game with `NonceGen`** on one sample: the nonces of
slot `k` are `ρ (G (rand k, extra_in, i))`. -/
def nonceGenExperiment
    (ω : (Rest n N X M Coins × (Fin qs → Rnd)) × (Rnd × Ex × Bool → W)) : Prop :=
  winE C nonceCoef N qs A e₀ ω.1.1 ω.2 (nvOf qs ρ fun i => ω.2 (noncePt qs ω.1.2 i))

/-! ## The choice of `extra_in` does not matter for fresh nonces -/

/-- `challengerE` with the nonce values as an oracle, queried at `pt`. -/
def nonceTreeE {D : Type} (pt : Fin qs → Ex → Bool → D) (x : ZMod n) (T : SigIn N X M → ZMod n) :
    (q : AdvQ n N E X M ⊕ Ex) → SignerState X M × (ℕ → Ex) →
      QTree D W (SumR AdvR Unit q × (SignerState X M × (ℕ → Ex)))
  | .inl q, s =>
    match needs N qs q s.1 with
    | some k =>
      .ask (pt k (s.2 k) false) fun a => .ask (pt k (s.2 k) true) fun b =>
        .done ((challenger C nonceCoef N qs x (fun _ => (ρ a, ρ b)) T q s.1).1,
          ((challenger C nonceCoef N qs x (fun _ => (ρ a, ρ b)) T q s.1).2, s.2))
    | none =>
      .done ((challenger C nonceCoef N qs x (fun _ => (0, 0)) T q s.1).1,
        ((challenger C nonceCoef N qs x (fun _ => (0, 0)) T q s.1).2, s.2))
  | .inr e, s => .done ((), (s.1, update s.2 s.1.opened e))

theorem eval_nonceTreeE {D : Type} (pt : Fin qs → Ex → Bool → D) (x : ZMod n)
    (T : SigIn N X M → ZMod n) (v : D → W) (q : AdvQ n N E X M ⊕ Ex)
    (s : SignerState X M × (ℕ → Ex)) :
    eval v (nonceTreeE C nonceCoef N qs ρ pt x T q s) =
      challengerE C nonceCoef N qs (fun k e => (ρ (v (pt k e false)), ρ (v (pt k e true)))) x T
        q s := by
  cases q with
  | inr e => rfl
  | inl q =>
    cases hn : needs N qs q s.1 with
    | none =>
      have h := (challengerG_of_needs_none false C nonceCoef N qs x T
        (fun k => (ρ (v (pt k (s.2 k) false)), ρ (v (pt k (s.2 k) true)))) (fun _ => (0, 0)) q
        s.1 hn).1
      simp only [nonceTreeE, challengerE, hn, QTree.eval, challenger]
      rw [h]
    | some k =>
      have h := challengerG_of_needs_some false C nonceCoef N qs x T
        (fun _ => (ρ (v (pt k (s.2 k) false)), ρ (v (pt k (s.2 k) true))))
        (fun k => (ρ (v (pt k (s.2 k) false)), ρ (v (pt k (s.2 k) true)))) q s.1 hn rfl
      simp only [nonceTreeE, challengerE, hn, QTree.eval, challenger]
      rw [h]

/-- Dropping the `extra_in` queries is running with nonces that do not depend
on the `extra_in`. -/
theorem run_dropExtra (x : ZMod n) (T : SigIn N X M → ZMod n) (nonces : Fin qs → SecNonce n)
    {α : Type} (t : Alg (AdvQ n N E X M ⊕ Ex) (SumR AdvR Unit) α) (st : SignerState X M)
    (rec : ℕ → Ex) :
    (answerG (fun _ : Ex => ()) t).run (challenger C nonceCoef N qs x nonces T) st =
      ((t.run (challengerE C nonceCoef N qs (fun k _ => nonces k) x T) (st, rec)).1,
        (t.run (challengerE C nonceCoef N qs (fun k _ => nonces k) x T) (st, rec)).2.1) := by
  induction t generalizing st rec with
  | done a => rfl
  | ask q f ih =>
    cases q with
    | inl q => exact ih _ _ _
    | inr e => exact ih _ _ _

variable [DecidableEq Ex]

/-- The memories of the two oracle versions: an open session has the same
nonce values in both, under its `extra_in` in the first; slots that are not
opened yet have none. -/
def SRel (s : SignerState X M × (ℕ → Ex)) (μ₁ : List ((Fin qs × Ex × Bool) × W))
    (μ₂ : List ((Fin qs × Bool) × W)) : Prop :=
  s.1.opened ≤ qs ∧ (∀ j ∈ s.1.closed, j < s.1.opened) ∧
    (∀ k : Fin qs, k.val < s.1.opened → k.val ∉ s.1.closed → ∀ b,
      ∃ y, memo μ₁ (k, s.2 k, b) = some y ∧ memo μ₂ (k, b) = some y) ∧
    ∀ k : Fin qs, s.1.opened ≤ k.val → ∀ e b,
      memo μ₁ (k, e, b) = none ∧ memo μ₂ (k, b) = none

variable [Fintype W] [Nonempty W] [Fintype Ex]

set_option maxHeartbeats 1000000 in
-- the case analysis over the queries is long
/-- **Fresh nonces do not depend on the `extra_in`**: the oracle version that
reads the nonce values at `(slot, extra_in, i)` and the one that reads them at
`(slot, i)` have the same lazily sampled expectation. -/
theorem sel_couple {α : Type} (F : α × (SignerState X M × (ℕ → Ex)) → ℝ) (x : ZMod n)
    (T : SigIn N X M → ZMod n) (t : Alg (AdvQ n N E X M ⊕ Ex) (SumR AdvR Unit) α)
    (s : SignerState X M × (ℕ → Ex)) (μ₁ : List ((Fin qs × Ex × Bool) × W))
    (μ₂ : List ((Fin qs × Bool) × W)) (h : SRel qs s μ₁ μ₂) :
    exL (fun _ p => F p) μ₁
        (Alg.interp (nonceTreeE C nonceCoef N qs ρ (fun k e b => (k, e, b)) x T) t s) =
      exL (fun _ p => F p) μ₂
        (Alg.interp (nonceTreeE C nonceCoef N qs ρ (fun k _ b => (k, b)) x T) t s) := by
  classical
  have : Inhabited W := Classical.inhabited_of_nonempty inferInstance
  induction t generalizing s μ₁ μ₂ with
  | done a => rw [Alg.interp_done, Alg.interp_done, exL_done, exL_done]
  | ask q f ih =>
    rw [Alg.interp_ask, Alg.interp_ask, exL_bind, exL_bind]
    obtain ⟨hq, hcl, hopen, hnew⟩ := h
    cases q with
    | inr e =>
      simp only [nonceTreeE, exL_done]
      refine ih _ _ _ _ ⟨hq, hcl, fun k hk hkc b => ?_, hnew⟩
      have hk0 : k.val < s.1.opened := hk
      have hu : update s.2 s.1.opened e k.val = s.2 k.val := update_of_ne (by omega) _ _
      simp only [hu]
      exact hopen k hk hkc b
    | inl q =>
      cases hn : needs N qs q s.1 with
      | none =>
        simp only [nonceTreeE, hn, exL_done]
        have e2 := (challengerG_of_needs_none false C nonceCoef N qs x T (fun _ => (0, 0))
          (fun _ => (0, 0)) q s.1 hn).2
        refine ih _ _ _ _ ?_
        simp only [challenger, e2]
        exact ⟨hq, hcl, hopen, hnew⟩
      | some k =>
        simp only [nonceTreeE, hn]
        rcases needs_some_cases false C nonceCoef N qs x T (fun _ => (0, 0)) q s.1 hn with
          ⟨hk, -, -⟩ | ⟨hlt, hkc, -, -⟩
        · -- the slot is opened by this query
          have hm1f : memo μ₁ (k, s.2 k, false) = none := (hnew k (le_of_eq hk.symm) _ _).1
          have hm2f : memo μ₂ (k, false) = none := (hnew k (le_of_eq hk.symm) (s.2 k) false).2
          rw [exL_ask_none _ hm1f, exL_ask_none _ hm2f]
          congr 1
          refine Finset.sum_congr rfl fun a _ => ?_
          have hm1t : memo (μ₁ ++ [((k, s.2 k, false), a)]) (k, s.2 k, true) = none := by
            rw [memo_append_ne (by simp)]
            exact (hnew k (le_of_eq hk.symm) _ _).1
          have hm2t : memo (μ₂ ++ [((k, false), a)]) (k, true) = none := by
            rw [memo_append_ne (by simp)]
            exact (hnew k (le_of_eq hk.symm) (s.2 k) true).2
          rw [exL_ask_none _ hm1t, exL_ask_none _ hm2t]
          congr 1
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [exL_done, exL_done]
          refine ih _ _ _ _ ?_
          rcases needs_some_cases false C nonceCoef N qs x T (fun _ => (ρ a, ρ b)) q s.1 hn with
            ⟨-, ho, hc⟩ | ⟨hlt, -⟩
          · have hkq := k.isLt
            refine ⟨by simp only [challenger, ho]; omega, ?_, ?_, ?_⟩
            · intro j hj
              simp only [challenger, ho] at hj ⊢
              rcases hc with hc | hc <;> rw [hc] at hj
              · have := hcl j hj
                omega
              · rcases List.mem_cons.mp hj with rfl | hj
                · omega
                · have := hcl j hj
                  omega
            · intro k' hk' hkc' b'
              simp only [challenger, ho] at hk' hkc'
              by_cases hkk : k' = k
              · subst hkk
                cases b' with
                | false =>
                  refine ⟨a, ?_, ?_⟩
                  · rw [memo_append_ne (by simp)]
                    exact memo_append_self hm1f a
                  · rw [memo_append_ne (by simp)]
                    exact memo_append_self hm2f a
                | true => exact ⟨b, memo_append_self hm1t b, memo_append_self hm2t b⟩
              · have hval : k'.val ≠ k.val := fun h => hkk (Fin.ext h)
                have hnc : k'.val ∉ s.1.closed := fun hm => hkc' (by
                  rcases hc with hc | hc <;> rw [hc]
                  · exact hm
                  · exact List.mem_cons_of_mem _ hm)
                obtain ⟨y, h1, h2⟩ := hopen k' (by omega) hnc b'
                have hne1 : ∀ (e : Ex) (c : Bool), ((k, e, c) : Fin qs × Ex × Bool) ≠
                    (k', s.2 k', b') := fun e c h => hkk (congrArg Prod.fst h).symm
                have hne2 : ∀ c : Bool, ((k, c) : Fin qs × Bool) ≠ (k', b') :=
                  fun c h => hkk (congrArg Prod.fst h).symm
                exact ⟨y, by rw [memo_append_ne (hne1 _ _), memo_append_ne (hne1 _ _)]; exact h1,
                  by rw [memo_append_ne (hne2 _), memo_append_ne (hne2 _)]; exact h2⟩
            · intro k' hk' e b'
              simp only [challenger, ho] at hk'
              have hkk : k ≠ k' := fun h => by
                have := congrArg Fin.val h
                omega
              have hne1 : ∀ (e' : Ex) (c : Bool), ((k, e', c) : Fin qs × Ex × Bool) ≠
                  (k', e, b') := fun e' c h => hkk (congrArg Prod.fst h)
              have hne2 : ∀ c : Bool, ((k, c) : Fin qs × Bool) ≠ (k', b') :=
                fun c h => hkk (congrArg Prod.fst h)
              obtain ⟨h1, h2⟩ := hnew k' (by omega) e b'
              exact ⟨by rw [memo_append_ne (hne1 _ _), memo_append_ne (hne1 _ _)]; exact h1,
                by rw [memo_append_ne (hne2 _), memo_append_ne (hne2 _)]; exact h2⟩
          · omega
        · -- the slot is an open session
          obtain ⟨a, h1a, h2a⟩ := hopen k hlt hkc false
          obtain ⟨b, h1b, h2b⟩ := hopen k hlt hkc true
          rw [exL_ask_some _ h1a, exL_ask_some _ h2a, exL_ask_some _ h1b, exL_ask_some _ h2b,
            exL_done, exL_done]
          refine ih _ _ _ _ ?_
          rcases needs_some_cases false C nonceCoef N qs x T (fun _ => (ρ a, ρ b)) q s.1 hn with
            ⟨hk, -⟩ | ⟨-, -, ho, hc⟩
          · omega
          · refine ⟨by simp only [challenger, ho]; exact hq, ?_, ?_, ?_⟩
            · intro j hj
              simp only [challenger, ho] at hj ⊢
              rcases hc with hc | hc <;> rw [hc] at hj
              · exact hcl j hj
              · rcases List.mem_cons.mp hj with rfl | hj
                · exact hlt
                · exact hcl j hj
            · intro k' hk' hkc' b'
              simp only [challenger, ho] at hk' hkc'
              refine hopen k' hk' (fun hm => hkc' ?_) b'
              rcases hc with hc | hc <;> rw [hc]
              · exact hm
              · exact List.mem_cons_of_mem _ hm
            · intro k' hk' e b'
              simp only [challenger, ho] at hk'
              exact hnew k' hk' e b'

open Classical in
/-- With independent nonce values for every slot and every `extra_in`, the
game is the game with independent nonce values for every slot. -/
theorem prob_winE_eq (θ : Rest n N X M Coins) (G : Rnd × Ex × Bool → W) :
    prob (fun w : Fin qs × Ex × Bool → W => winE C nonceCoef N qs A e₀ θ G (nvOf qs ρ w)) =
      prob (fun ν : Fin qs × Bool → W => winOf C nonceCoef N qs A θ G fun i => ρ (ν i)) := by
  have : Inhabited W := Classical.inhabited_of_nonempty inferInstance
  let P : Forgery n X M × (SignerState X M × (ℕ → Ex)) → Prop :=
    fun p => Wins C nonceCoef N (θ.1 : ZMod n) θ.2.2 p.1 p.2.1
  have h1 : (fun w : Fin qs × Ex × Bool → W =>
      winE C nonceCoef N qs A e₀ θ G (nvOf qs ρ w)) =
      fun w => P (eval w (Alg.interp
        (nonceTreeE C nonceCoef N qs ρ (fun k e b => (k, e, b)) (θ.1 : ZMod n) θ.2.2)
        (answerG G (A θ.2.1 (C.mulG (θ.1 : ZMod n)))) (⟨0, [], []⟩, fun _ => e₀))) := by
    funext w
    rw [eval_interp_of _ _ w (eval_nonceTreeE C nonceCoef N qs ρ _ (θ.1 : ZMod n) θ.2.2 w)]
    rfl
  have h2 : (fun ν : Fin qs × Bool → W => winOf C nonceCoef N qs A θ G fun i => ρ (ν i)) =
      fun ν => P (eval ν (Alg.interp
        (nonceTreeE C nonceCoef N qs ρ (fun k _ b => (k, b)) (θ.1 : ZMod n) θ.2.2)
        (answerG G (A θ.2.1 (C.mulG (θ.1 : ZMod n)))) (⟨0, [], []⟩, fun _ => e₀))) := by
    funext ν
    rw [eval_interp_of _ _ ν (eval_nonceTreeE C nonceCoef N qs ρ _ (θ.1 : ZMod n) θ.2.2 ν)]
    unfold winOf
    dsimp only
    rw [run_dropExtra C nonceCoef N qs (θ.1 : ZMod n) θ.2.2 _ _ _ fun _ => e₀]
  rw [h1, h2, prob_eval_eq_exL, prob_eval_eq_exL]
  exact sel_couple C nonceCoef N qs ρ _ (θ.1 : ZMod n) θ.2.2 _ _ [] []
    ⟨Nat.zero_le _, by simp, fun k hk => absurd hk (Nat.not_lt_zero _), fun k _ e b => ⟨rfl, rfl⟩⟩

variable [Fintype Coins] [Fintype (SigIn N X M)] [Fintype Rnd] [DecidableEq Rnd] [Nonempty Rnd]

/-- The adversary's advantage in the game with `NonceGen`. -/
noncomputable def nonceGenAdvantage : ℝ := prob (nonceGenExperiment C nonceCoef N qs A ρ e₀)

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

set_option synthInstance.maxSize 4000 in
/-- **`NonceGen` costs at most the three error terms.** -/
theorem nonceGen_advantage (g : (ZMod n)ˣ → W) (hg : Injective g) (hρ : ∀ u, ρ (g u) = u)
    (qn : ℕ) (hA : ∀ c P, NBound (A c P) qn) :
    nonceGenAdvantage C nonceCoef N qs A ρ e₀ ≤
      forgeAdvantage C nonceCoef N qs (withTable N A) +
        (qs : ℝ) ^ 2 / Fintype.card Rnd + qs * (qn / Fintype.card Rnd) +
        (2 * qs : ℕ) * ((Fintype.card W - Fintype.card (ZMod n)ˣ : ℝ) / Fintype.card W) := by
  -- from the table's values to independent values
  have H := oracle_hop (Θ := Rest n N X M Coins) (noncePt (Ex := Ex) qs)
    (fun r hr => noncePt_injective qs hr) Prod.fst (fun r i => ⟨i.1, rfl⟩)
    (fun θ G v => winE C nonceCoef N qs A e₀ θ G (nvOf qs ρ v))
    (fun θ G v => gLog G (challengerE C nonceCoef N qs (nvOf qs ρ v) (θ.1 : ZMod n) θ.2.2)
      (A θ.2.1 (C.mulG (θ.1 : ZMod n))) (⟨0, [], []⟩, fun _ => e₀))
    (fun θ G G' v h => by
      unfold winE
      dsimp only
      rw [answerG_congr G G' _ _ _ h])
    qn (fun θ G v => length_gLog _ _ _ _ _ (hA _ _))
  -- the `extra_in` does not matter
  have hsel : prob (fun s : (Rest n N X M Coins × (Rnd × Ex × Bool → W)) ×
      (Fin qs × Ex × Bool → W) => winE C nonceCoef N qs A e₀ s.1.1 s.1.2 (nvOf qs ρ s.2)) =
      prob (fun s : (Rest n N X M Coins × (Rnd × Ex × Bool → W)) × (Fin qs × Bool → W) =>
        winOf C nonceCoef N qs A s.1.1 s.1.2 fun i => ρ (s.2 i)) :=
    prob_prod_congr _ _ fun a => prob_winE_eq C nonceCoef N qs A ρ e₀ a.1 a.2
  -- from derived nonces to uniform nonzero scalars
  have h7 : prob (fun s : (Rest n N X M Coins × (Rnd × Ex × Bool → W)) × (Fin qs × Bool → W) =>
        winOf C nonceCoef N qs A s.1.1 s.1.2 fun i => ρ (s.2 i)) ≤
      forgeAdvantage C nonceCoef N qs (withTable N A) +
      (2 * qs : ℕ) * ((Fintype.card W - Fintype.card (ZMod n)ˣ : ℝ) / Fintype.card W) := by
    have hle : Fintype.card (ZMod n)ˣ ≤ Fintype.card W := Fintype.card_le_of_injective g hg
    have hc : (0 : ℝ) ≤ (2 * qs : ℕ) *
        ((Fintype.card W - Fintype.card (ZMod n)ˣ : ℝ) / Fintype.card W) := by
      have : (0 : ℝ) ≤ Fintype.card W - Fintype.card (ZMod n)ˣ :=
        sub_nonneg.mpr (Nat.cast_le.mpr hle)
      positivity
    have hs := prob_prod_mono
      (fun s : (Rest n N X M Coins × (Rnd × Ex × Bool → W)) × (Fin qs × Bool → W) =>
        winOf C nonceCoef N qs A s.1.1 s.1.2 fun i => ρ (s.2 i))
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
  unfold nonceGenAdvantage nonceGenExperiment
  rw [hsel] at H
  linarith

/-- **Unforgeability with `NonceGen`**, under AOMDL with both
`hash_BIP0459/sig` and `hash_BIP0459/nonce` as random oracles. -/
theorem nonceGen_unforgeable (g : (ZMod n)ˣ → W) (hg : Injective g) (hρ : ∀ u, ρ (g u) = u)
    (hN : N < n) (qh qn : ℕ) (hA : ∀ c P, NBound (A c P) qn)
    (hH : ∀ c P G, HashBound (answerG (fun _ : Ex => ()) (answerG G (A c P))) qh) :
    nonceGenAdvantage C nonceCoef N qs A ρ e₀ ≤
      Real.sqrt ((qh + qs + 1 : ℕ) *
          (omdlAdvantage C (2 * qs + 1) (reduction C nonceCoef N qs (withTable N A)) +
            collisionAdvantage C nonceCoef N qs (withTable N A))) + (qh + qs + 1 : ℕ) / n +
        qs / (n - 1 : ℝ) +
        (qs : ℝ) ^ 2 / Fintype.card Rnd + qs * (qn / Fintype.card Rnd) +
        (2 * qs : ℕ) * ((Fintype.card W - Fintype.card (ZMod n)ˣ : ℝ) / Fintype.card W) := by
  have h1 := nonceGen_advantage C nonceCoef N qs A ρ e₀ g hg hρ qn hA
  have h2 := unforgeable_sqrt C nonceCoef N qs (withTable N A) hN qh fun c P => hH c.1 P c.2
  linarith

omit [Nonempty W] [Fintype W] in
/-- **`NonceGen` with hash outputs `0, …, m - 1` reduced modulo `n`**, as in
BIP 459 with `m = 2²⁵⁶`. -/
theorem nonceGen_advantage_fin {m : ℕ} (hm : n ≤ m)
    (A : NAdversary n N E X M Rnd Ex (Fin m) Coins) (qn : ℕ) (hA : ∀ c P, NBound (A c P) qn) :
    nonceGenAdvantage C nonceCoef N qs A (fun w => (w.val : ZMod n)) e₀ ≤
      forgeAdvantage C nonceCoef N qs (withTable N A) +
        (qs : ℝ) ^ 2 / Fintype.card Rnd + qs * (qn / Fintype.card Rnd) +
        (2 * qs : ℕ) * ((m - (n - 1) : ℝ) / m) := by
  have hn : 0 < n := (Fact.out : n.Prime).pos
  have : Nonempty (Fin m) := ⟨⟨0, lt_of_lt_of_le hn hm⟩⟩
  have h := nonceGen_advantage C nonceCoef N qs A (fun w : Fin m => (w.val : ZMod n)) e₀
    (fun u => ⟨(u : ZMod n).val, lt_of_lt_of_le (ZMod.val_lt _) hm⟩)
    (fun u u' h => Units.ext (ZMod.val_injective n (Fin.mk.inj h)))
    (fun u => ZMod.natCast_zmod_val _) qn hA
  rw [ZMod.card_units_eq_totient, Nat.totient_prime Fact.out, Fintype.card_fin,
    Nat.cast_sub hn, Nat.cast_one] at h
  exact h

end Dahlias.Security
