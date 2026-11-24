import Dahlias.NonceGenSk
import Dahlias.Hashed
import Dahlias.BindingHashed

/-!
# `NonceGen` and a challenge hash with outputs in a larger set, together

`Dahlias.NonceGen` and `Dahlias.NonceGenSk` derive the nonces as BIP 459's
`NonceGen` does, in a game where the challenge hash answers with a uniform
scalar. `Dahlias.Hashed` lets the challenge hash answer with an output in a
set `H` that signer and verifier reduce to a scalar, in a game with uniform
nonces. Here one game has both.

* `nonceGenExperimentH` is the game for `NonceGen` without its `sk` argument:
  the nonces come from `hash_BIP0459/nonce`, a random oracle, and the adversary
  sees the outputs in `H` of the challenge hash. `nonceGenSkExperimentH` is
  the game with the `sk` argument and `hash_BIP0459/aux` as a third random
  oracle.
* `nonceGenAdvantageH_le`, `nonceGenSkAdvantageH_le`: an adversary wins these
  games at most `(qh + qs + N)⋅(|H| - n) / |H|` more often than the adversary
  `liftHashN g A` or `liftHashSk g A` wins the game with scalar answers.
* `nonceGen_unforgeable_hashed`, `nonceGenSk_unforgeable_hashed`: the bound of
  `unforgeable_sqrt` with the error terms of all oracles. `Dahlias.NonceGenLazy`
  states them with lazily sampled oracles.
-/

set_option linter.unusedSectionVars false

namespace Dahlias.Security

open Taproot Function QTree

/-! ## Changing the answers an algorithm gets -/

section MapAns

variable {Q : Type} {R R' : Q → Type} {D W α σ : Type}

/-- The algorithm that gets answers in `R'` and continues as `t` does on their
images under `f`. -/
def mapAns (f : (q : Q) → R' q → R q) : Alg Q R α → Alg Q R' α
  | .done a => .done a
  | .ask q k => .ask q fun r => mapAns f (k (f q r))

/-- If the handler `h` answers with the image under `f` of what `h'` answers,
`mapAns f t` runs with `h'` as `t` runs with `h`. -/
theorem run_mapAns (f : (q : Q) → R' q → R q) (h : (q : Q) → σ → R q × σ)
    (h' : (q : Q) → σ → R' q × σ) (hh : ∀ q s, h q s = (f q (h' q s).1, (h' q s).2))
    (t : Alg Q R α) (s : σ) : (mapAns f t).run h' s = t.run h s := by
  induction t generalizing s with
  | done a => rfl
  | ask q k ih =>
    rw [Alg.run_ask, hh]
    exact ih _ _

/-- `f` on the answers of the game, nothing on the answers of the table. -/
def sumAns (f : (q : Q) → R' q → R q) : (q : Q ⊕ D) → SumR R' W q → SumR R W q
  | .inl q, r => f q r
  | .inr _, w => w

theorem answerG_mapAns (G : D → W) (f : (q : Q) → R' q → R q)
    (t : Alg (Q ⊕ D) (SumR R W) α) :
    answerG G (mapAns (sumAns f) t) = mapAns f (answerG G t) := by
  induction t with
  | done a => rfl
  | ask x k ih =>
    cases x with
    | inl q =>
      change Alg.ask q (fun r => answerG G (mapAns (sumAns f) (k (f q r)))) =
        Alg.ask q fun r => mapAns f (answerG G (k (f q r)))
      congr 1
      funext r
      exact ih _
    | inr z => exact ih _

theorem nbound_mapAns (f : (q : Q) → R' q → R q) (t : Alg (Q ⊕ D) (SumR R W) α) (q : ℕ)
    (h : NBound t q) : NBound (mapAns (sumAns f) t) q := by
  induction t generalizing q with
  | done a => trivial
  | ask x k ih =>
    cases x with
    | inl x => exact fun r => ih _ _ (h _)
    | inr z => exact ⟨h.1, fun r => ih _ _ (h.2 _)⟩

end MapAns

variable {n : ℕ} [Fact n.Prime] {E X M : Type} [AddCommGroup E] [DecidableEq E] [DecidableEq X]
  [DecidableEq M]

/-! ## The game -/

variable (C : Curve n E X) (nonceCoef : E → E → List (X × M × E) → ZMod n) (N qs : ℕ)
  {H Rnd Rp Ex W Coins : Type} (red : H → ZMod n)

/-- An adversary of the game with `NonceGen` that sees the outputs of the
challenge hash. -/
abbrev NAdversaryH (n N : ℕ) (E X M Rnd Ex W H Coins : Type) :=
  Coins → E → Alg ((AdvQ n N E X M ⊕ Ex) ⊕ (Rnd × Ex × Bool)) (SumR (SumR (AdvRH H) Unit) W)
    (Forgery n X M)

/-- An adversary of the game with `NonceGen` and its `sk` argument that sees
the outputs of the challenge hash. -/
abbrev SkAdversaryH (n N : ℕ) (E X M Rnd Rp Ex W H Coins : Type) :=
  Coins → E → Alg (((AdvQ n N E X M ⊕ Ex) ⊕ (Rnd × Ex × Bool)) ⊕ Rp)
    (SumR (SumR (SumR (AdvRH H) Unit) W) Rnd) (Forgery n X M)

/-- `challengerE` for a table `Tab` of hash outputs: a hash query returns the
output, the signer reduces it with `red`. -/
def challengerEH (nv : Fin qs → Ex → SecNonce n) (x : ZMod n) (Tab : SigIn N X M → H) :
    (q : AdvQ n N E X M ⊕ Ex) → SignerState X M × (ℕ → Ex) →
      SumR (AdvRH H) Unit q × (SignerState X M × (ℕ → Ex))
  | .inl q, s =>
    ((challengerH C nonceCoef N qs red x (fun k => nv k (s.2 k)) Tab q s.1).1,
      ((challengerH C nonceCoef N qs red x (fun k => nv k (s.2 k)) Tab q s.1).2, s.2))
  | .inr e, s => ((), (s.1, update s.2 s.1.opened e))

/-- The part of the sample that the nonces do not depend on: the secret key,
the adversary's coins and the table of hash outputs. -/
abbrev RestH (n N : ℕ) (X M H Coins : Type) := (ZMod n)ˣ × Coins × (SigIn N X M → H)

/-- **The unforgeability game with `NonceGen` and hash outputs in `H`** on one
sample: the nonces of slot `k` are `ρ (G (rand k, extra_in, i))`, and the
verifier reduces the outputs of the challenge hash with `red` as the signer
does. -/
def nonceGenExperimentH (A : NAdversaryH n N E X M Rnd Ex W H Coins) (ρ : W → ZMod n) (e₀ : Ex)
    (ω : (RestH n N X M H Coins × (Fin qs → Rnd)) × (Rnd × Ex × Bool → W)) : Prop :=
  let x : ZMod n := ω.1.1.1
  let Tab := ω.1.1.2.2
  let out := (answerG ω.2 (A ω.1.1.2.1 (C.mulG x))).run
    (challengerEH C nonceCoef N qs red (nvOf qs ρ fun i => ω.2 (noncePt qs ω.1.2 i)) x Tab)
    (⟨0, [], []⟩, fun _ => e₀)
  Wins C nonceCoef N x (fun z => red (Tab z)) out.1 out.2.1

/-- **The unforgeability game with `NonceGen`, its `sk` argument and hash
outputs in `H`** on one sample: the `rand` of slot `k` is
`mask x k (Aux (rand' k))`. -/
def nonceGenSkExperimentH (A : SkAdversaryH n N E X M Rnd Rp Ex W H Coins) (ρ : W → ZMod n)
    (e₀ : Ex) (mask : (ZMod n)ˣ → Fin qs → Rnd ≃ Rnd)
    (ω : ((RestH n N X M H Coins × (Rnd × Ex × Bool → W)) × (Fin qs → Rp)) × (Rp → Rnd)) :
    Prop :=
  nonceGenExperimentH C nonceCoef N qs red (fun c P => answerG ω.2 (A c P)) ρ e₀
    ((ω.1.1.1, fun k => mask ω.1.1.1.1 k (ω.2 (ω.1.2 k))), ω.1.1.2)

/-- The adversary's advantage in the game with `NonceGen` and hash outputs in
`H`. -/
noncomputable def nonceGenAdvantageH [Fintype Coins] [Fintype (SigIn N X M)] [Fintype H]
    [Fintype Rnd] [DecidableEq Rnd] [Fintype Ex] [DecidableEq Ex] [Fintype W]
    (A : NAdversaryH n N E X M Rnd Ex W H Coins) (ρ : W → ZMod n) (e₀ : Ex) : ℝ :=
  prob (nonceGenExperimentH C nonceCoef N qs red A ρ e₀)

/-- The adversary's advantage in the game with `NonceGen`, its `sk` argument
and hash outputs in `H`. -/
noncomputable def nonceGenSkAdvantageH [Fintype Coins] [Fintype (SigIn N X M)] [Fintype H]
    [Fintype Rnd] [Fintype Rp] [DecidableEq Rp] [Fintype Ex] [DecidableEq Ex] [DecidableEq Rnd]
    [Fintype W] (A : SkAdversaryH n N E X M Rnd Rp Ex W H Coins) (ρ : W → ZMod n) (e₀ : Ex)
    (mask : (ZMod n)ˣ → Fin qs → Rnd ≃ Rnd) : ℝ :=
  prob (nonceGenSkExperimentH C nonceCoef N qs red A ρ e₀ mask)

/-! ## From hash outputs to scalars -/

/-- The game's answers with the scalar answer of the challenge hash replaced
by the output `g c`. -/
def hashAns (g : ZMod n → H) : (q : AdvQ n N E X M) → AdvR q → AdvRH H q
  | .hash _, c => g c
  | .openSession, r => r
  | .close .., r => r
  | .single _, r => r

omit [Fact n.Prime] [AddCommGroup E] [DecidableEq E] [DecidableEq X] [DecidableEq M] in
theorem hashBound_mapAns (g : ZMod n → H) {α : Type} (t : Alg (AdvQ n N E X M) (AdvRH H) α)
    (qh : ℕ) (h : HashBound t qh) : HashBound (mapAns (hashAns N g) t) qh := by
  induction t generalizing qh with
  | done a => trivial
  | ask q f ih =>
    cases q with
    | hash z => exact ⟨h.1, fun r => ih _ _ (h.2 _)⟩
    | openSession => exact fun r => ih _ _ (h _)
    | close k τ m agg pm pubnonces => exact fun r => ih _ _ (h _)
    | single items => exact ⟨h.1, fun r => ih _ _ (h.2 _)⟩

/-- The adversary for the game of `Dahlias.NonceGen`: when the challenge hash
answers `c`, it continues with the output `g c`. -/
def liftHashN (g : ZMod n → H) (A : NAdversaryH n N E X M Rnd Ex W H Coins) :
    NAdversary n N E X M Rnd Ex W Coins :=
  fun c P => mapAns (sumAns (sumAns (hashAns N g))) (A c P)

/-- The adversary for the game of `Dahlias.NonceGenSk`: when the challenge
hash answers `c`, it continues with the output `g c`. -/
def liftHashSk (g : ZMod n → H) (A : SkAdversaryH n N E X M Rnd Rp Ex W H Coins) :
    SkAdversary n N E X M Rnd Rp Ex W Coins :=
  fun c P => mapAns (sumAns (sumAns (sumAns (hashAns N g)))) (A c P)

/-- On the table `g ∘ T` the game's answers are the images of the answers on
the table `T` of scalars. -/
theorem challengerEH_lift (g : ZMod n → H) (hg : ∀ c, red (g c) = c)
    (nv : Fin qs → Ex → SecNonce n) (x : ZMod n) (T : SigIn N X M → ZMod n)
    (q : AdvQ n N E X M ⊕ Ex) (s : SignerState X M × (ℕ → Ex)) :
    challengerEH C nonceCoef N qs red nv x (fun z => g (T z)) q s =
      (sumAns (hashAns N g) q (challengerE C nonceCoef N qs nv x T q s).1,
        (challengerE C nonceCoef N qs nv x T q s).2) := by
  have hT : (fun z => red (g (T z))) = T := funext fun z => hg _
  cases q with
  | inr e => rfl
  | inl q =>
    cases q with
    | hash z => rfl
    | openSession =>
      simp only [challengerEH, challengerE, challengerH, hT]
      rfl
    | close k τ m agg pm pubnonces =>
      simp only [challengerEH, challengerE, challengerH, hT]
      rfl
    | single items =>
      simp only [challengerEH, challengerE, challengerH, hT]
      rfl

/-- On the table `g ∘ T` the game with hash outputs is the game of
`Dahlias.NonceGen` for `liftHashN g A`. -/
theorem nonceGenExperimentH_lift (g : ZMod n → H) (hg : ∀ c, red (g c) = c)
    (A : NAdversaryH n N E X M Rnd Ex W H Coins) (ρ : W → ZMod n) (e₀ : Ex) (x : (ZMod n)ˣ)
    (c : Coins) (T : SigIn N X M → ZMod n) (rands : Fin qs → Rnd) (G : Rnd × Ex × Bool → W) :
    nonceGenExperimentH C nonceCoef N qs red A ρ e₀ (((x, c, fun z => g (T z)), rands), G) ↔
      nonceGenExperiment C nonceCoef N qs (liftHashN N g A) ρ e₀ (((x, c, T), rands), G) := by
  have hT : (fun z => red (g (T z))) = T := funext fun z => hg _
  unfold nonceGenExperimentH nonceGenExperiment winE liftHashN
  dsimp only
  rw [answerG_mapAns, run_mapAns _ _ _ (challengerEH_lift C nonceCoef N qs red g hg _ _ T), hT]

/-! ## The game as a query algorithm -/

/-- `challengerEH`, with the table as an oracle. -/
def treeChallengerEH (nv : Fin qs → Ex → SecNonce n) (x : ZMod n) :
    (q : AdvQ n N E X M ⊕ Ex) → SignerState X M × (ℕ → Ex) →
      QTree (SigIn N X M) H (SumR (AdvRH H) Unit q × (SignerState X M × (ℕ → Ex)))
  | .inl q, s =>
    treeChallengerH C nonceCoef N qs red x (fun k => nv k (s.2 k)) q s.1 >>= fun p =>
      .done (p.1, (p.2, s.2))
  | .inr e, s => .done ((), (s.1, update s.2 s.1.opened e))

theorem eval_treeChallengerEH (nv : Fin qs → Ex → SecNonce n) (x : ZMod n)
    (Tab : SigIn N X M → H) (q : AdvQ n N E X M ⊕ Ex) (s : SignerState X M × (ℕ → Ex)) :
    eval Tab (treeChallengerEH C nonceCoef N qs red nv x q s) =
      challengerEH C nonceCoef N qs red nv x Tab q s := by
  cases q with
  | inl q =>
    simp only [treeChallengerEH, eval_bind, eval_treeChallengerH]
    rfl
  | inr e => rfl

theorem length_flog_interpEH (nv : Fin qs → Ex → SecNonce n) (x : ZMod n)
    (Tab : SigIn N X M → H) {α : Type}
    (t : Alg (AdvQ n N E X M ⊕ Ex) (SumR (AdvRH H) Unit) α) (qh : ℕ)
    (ht : HashBound (answerG (fun _ : Ex => ()) t) qh) (s : SignerState X M × (ℕ → Ex))
    (l : List (SigIn N X M)) (hst : ClosedOk qs s.1) :
    (flog Tab l (Alg.interp (treeChallengerEH C nonceCoef N qs red nv x) t s)).length ≤
      l.length + qh + (qs - s.1.closed.length) := by
  induction t generalizing s l qh with
  | done a =>
    change l.length ≤ _
    omega
  | ask q f ih =>
    cases q with
    | inl q =>
      have ht' : HashBound (.ask q fun r => answerG (fun _ : Ex => ()) (f r)) qh := ht
      obtain ⟨hc, hf⟩ := hashBound_ask ht'
      obtain ⟨hst', hstep⟩ := step_boundH C nonceCoef N qs red x (fun k => nv k (s.2 k)) Tab q
        s.1 l hst
      have hfl : flog Tab l (treeChallengerEH C nonceCoef N qs red nv x (.inl q) s) =
          flog Tab l (treeChallengerH C nonceCoef N qs red x (fun k => nv k (s.2 k)) q s.1) := by
        simp only [treeChallengerEH, flog_bind]
        rfl
      have hev : eval Tab (treeChallengerEH C nonceCoef N qs red nv x (.inl q) s) =
          ((eval Tab (treeChallengerH C nonceCoef N qs red x (fun k => nv k (s.2 k)) q s.1)).1,
            ((eval Tab (treeChallengerH C nonceCoef N qs red x (fun k => nv k (s.2 k)) q s.1)).2,
              s.2)) := by
        simp only [treeChallengerEH, eval_bind]
        rfl
      rw [Alg.interp_ask, flog_bind, hev, hfl]
      have h := ih (eval Tab (treeChallengerH C nonceCoef N qs red x (fun k => nv k (s.2 k)) q
          s.1)).1 (qh - hashCost q) (hf _)
        ((eval Tab (treeChallengerH C nonceCoef N qs red x (fun k => nv k (s.2 k)) q s.1)).2, s.2)
        (flog Tab l (treeChallengerH C nonceCoef N qs red x (fun k => nv k (s.2 k)) q s.1)) hst'
      dsimp only at h ⊢
      omega
    | inr e =>
      rw [Alg.interp_ask, flog_bind]
      exact ih () qh ht _ _ hst

variable {Coins : Type} (nv : Fin qs → Ex → SecNonce n) (x : ZMod n)
  (B : Alg (AdvQ n N E X M ⊕ Ex) (SumR (AdvRH H) Unit) (Forgery n X M)) (e₀ : Ex)

/-- The whole game with hash outputs, for given nonce values, as one
algorithm. -/
noncomputable def winTreeEH : QTree (SigIn N X M) H Bool :=
  Alg.interp (treeChallengerEH C nonceCoef N qs red nv x) B (⟨0, [], []⟩, fun _ => e₀) >>=
    fun out => mapTree red (winTail C N x (out.1, out.2.1))

theorem eval_winTreeEH (Tab : SigIn N X M → H) :
    eval Tab (winTreeEH C nonceCoef N qs red nv x B e₀) = true ↔
      Wins C nonceCoef N x (fun z => red (Tab z))
        (B.run (challengerEH C nonceCoef N qs red nv x Tab) (⟨0, [], []⟩, fun _ => e₀)).1
        (B.run (challengerEH C nonceCoef N qs red nv x Tab) (⟨0, [], []⟩, fun _ => e₀)).2.1 := by
  unfold winTreeEH
  rw [eval_bind, eval_interp_of _ _ Tab (eval_treeChallengerEH C nonceCoef N qs red nv x Tab),
    eval_mapTree]
  exact eval_winTail C nonceCoef N x _ _

theorem length_fresh_winTreeEH (Tab : SigIn N X M → H) (qh : ℕ)
    (hB : HashBound (answerG (fun _ : Ex => ()) B) qh) :
    (fresh Tab (winTreeEH C nonceCoef N qs red nv x B e₀)).length ≤ qh + qs + N := by
  unfold winTreeEH
  rw [fresh_bind, flog_mapTree]
  have h := length_flog_interpEH C nonceCoef N qs red nv x Tab B qh hB (⟨0, [], []⟩, fun _ => e₀)
    [] ⟨List.nodup_nil, by simp, Nat.zero_le _⟩
  simp only [List.length_nil, zero_add, Nat.sub_zero] at h
  exact (length_flog_winTail C N x _ _ _).trans (Nat.add_le_add_right h N)

/-! ## The bound -/

variable [Fintype (SigIn N X M)] [Fintype H] [DecidableEq H]

/-- **A hash output reduced to a scalar costs `(|H| - n) / |H|` for every
value of the oracle that the game with `NonceGen` reads**, for every secret
key, all coins and all values of `hash_BIP0459/nonce`. -/
theorem nonceGenExperimentH_le (g : ZMod n → H) (hg : ∀ c, red (g c) = c)
    (A : NAdversaryH n N E X M Rnd Ex W H Coins) (ρ : W → ZMod n) (qh : ℕ) (u : (ZMod n)ˣ)
    (c : Coins) (rands : Fin qs → Rnd) (G : Rnd × Ex × Bool → W)
    (hA : HashBound (answerG (fun _ : Ex => ()) (answerG G (A c (C.mulG (u : ZMod n))))) qh) :
    prob (fun Tab : SigIn N X M → H =>
        nonceGenExperimentH C nonceCoef N qs red A ρ e₀ (((u, c, Tab), rands), G)) ≤
      prob (fun T : SigIn N X M → ZMod n =>
        nonceGenExperiment C nonceCoef N qs (liftHashN N g A) ρ e₀ (((u, c, T), rands), G)) +
        (qh + qs + N : ℕ) * ((Fintype.card H - n : ℝ) / Fintype.card H) := by
  have hinj : Injective g := fun a b h => by rw [← hg a, ← hg b, h]
  set t := winTreeEH C nonceCoef N qs red (nvOf qs ρ fun i => G (noncePt qs rands i))
    (u : ZMod n) (answerG G (A c (C.mulG (u : ZMod n)))) e₀ with ht
  have h := prob_eval_le_mapTree g hinj (qh + qs + N) t fun Tab =>
    length_fresh_winTreeEH C nonceCoef N qs red _ _ _ e₀ Tab qh hA
  have h0 : (fun Tab : SigIn N X M → H =>
      nonceGenExperimentH C nonceCoef N qs red A ρ e₀ (((u, c, Tab), rands), G)) =
      fun Tab => eval Tab t = true := by
    funext Tab
    exact propext (eval_winTreeEH C nonceCoef N qs red _ _ _ e₀ Tab).symm
  have h1 : (fun T : SigIn N X M → ZMod n => eval T (mapTree g t) = true) =
      fun T => nonceGenExperiment C nonceCoef N qs (liftHashN N g A) ρ e₀
        (((u, c, T), rands), G) := by
    funext T
    rw [eval_mapTree]
    exact propext ((eval_winTreeEH C nonceCoef N qs red _ _ _ e₀ fun z => g (T z)).trans
      (nonceGenExperimentH_lift C nonceCoef N qs red g hg A ρ e₀ u c T rands G))
  rw [h0, ← h1]
  rwa [ZMod.card] at h

omit [DecidableEq H] in
/-- The error term of the reduction to a scalar is not negative. -/
theorem hashGap_nonneg (g : ZMod n → H) (hg : ∀ c, red (g c) = c) (q : ℕ) :
    (0 : ℝ) ≤ q * ((Fintype.card H - n : ℝ) / Fintype.card H) := by
  have hinj : Injective g := fun a b h => by rw [← hg a, ← hg b, h]
  have hle : n ≤ Fintype.card H := by
    simpa [ZMod.card] using Fintype.card_le_of_injective g hinj
  have : (0 : ℝ) ≤ Fintype.card H - n := sub_nonneg.mpr (Nat.cast_le.mpr hle)
  positivity

/-- Samples of the game with `NonceGen`, with the table of the challenge hash
last. -/
def tabLastN {U K Tb B₁ B₂ : Type} : (((U × K) × B₁) × B₂) × Tb ≃ ((U × K × Tb) × B₁) × B₂ where
  toFun p := (((p.1.1.1.1, p.1.1.1.2, p.2), p.1.1.2), p.1.2)
  invFun ω := ((((ω.1.1.1, ω.1.1.2.1), ω.1.2), ω.2), ω.1.1.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Samples of the game with `NonceGen` and its `sk` argument, with the table
of the challenge hash last. -/
def tabLastSk {U K Tb B₁ B₂ B₃ : Type} :
    ((((U × K) × B₁) × B₂) × B₃) × Tb ≃ (((U × K × Tb) × B₁) × B₂) × B₃ where
  toFun p := ((((p.1.1.1.1.1, p.1.1.1.1.2, p.2), p.1.1.1.2), p.1.1.2), p.1.2)
  invFun ω := (((((ω.1.1.1.1, ω.1.1.1.2.1), ω.1.1.2), ω.1.2), ω.2), ω.1.1.1.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

variable [Fintype Coins] [Fintype Rnd] [DecidableEq Rnd] [Nonempty Rnd] [Fintype Rp]
  [DecidableEq Rp] [Nonempty Rp] [Fintype Ex] [DecidableEq Ex] [Fintype W] [Nonempty W]

/-! ### `NonceGen` without the `sk` argument -/

set_option synthInstance.maxSize 4000 in
/-- **A hash output reduced to a scalar costs `(|H| - n) / |H|` for every
value of the oracle that the game reads**, in the game with `NonceGen`. -/
theorem nonceGenAdvantageH_le (A : NAdversaryH n N E X M Rnd Ex W H Coins) (ρ : W → ZMod n)
    (g : ZMod n → H) (hg : ∀ c, red (g c) = c) (qh : ℕ)
    (hH : ∀ c P G, HashBound (answerG (fun _ : Ex => ()) (answerG G (A c P))) qh) :
    nonceGenAdvantageH C nonceCoef N qs red A ρ e₀ ≤
      nonceGenAdvantage C nonceCoef N qs (liftHashN N g A) ρ e₀ +
        (qh + qs + N : ℕ) * ((Fintype.card H - n : ℝ) / Fintype.card H) := by
  unfold nonceGenAdvantageH nonceGenAdvantage
  rw [← prob_equiv (tabLastN (Tb := SigIn N X M → H))
      (nonceGenExperimentH C nonceCoef N qs red A ρ e₀),
    ← prob_equiv (tabLastN (Tb := SigIn N X M → ZMod n))
      (nonceGenExperiment C nonceCoef N qs (liftHashN N g A) ρ e₀)]
  refine prob_prod_mono _ _ _ (hashGap_nonneg red g hg _) fun a => ?_
  exact nonceGenExperimentH_le C nonceCoef N qs red e₀ g hg A ρ qh a.1.1.1 a.1.1.2 a.1.2 a.2
    (hH _ _ _)

set_option synthInstance.maxSize 4000 in
/-- **Unforgeability with `NonceGen` and the challenge hash reduced to a
scalar**, under AOMDL with `hash_BIP0459/sig` and `hash_BIP0459/nonce` as
random oracles: the bound of `unforgeable_sqrt` and the error terms of the two
oracles. -/
theorem nonceGen_unforgeable_hashed (A : NAdversaryH n N E X M Rnd Ex W H Coins)
    (ρ : W → ZMod n) (g : ZMod n → H) (hg : ∀ c, red (g c) = c) (gW : (ZMod n)ˣ → W)
    (hgW : Injective gW) (hρ : ∀ u, ρ (gW u) = u) (hN : N < n) (qh qn : ℕ)
    (hA : ∀ c P, NBound (A c P) qn)
    (hH : ∀ c P G, HashBound (answerG (fun _ : Ex => ()) (answerG G (A c P))) qh) :
    nonceGenAdvantageH C nonceCoef N qs red A ρ e₀ ≤
      Real.sqrt ((qh + qs + 1 : ℕ) *
          (omdlAdvantage C (2 * qs + 1)
              (reduction C nonceCoef N qs (withTable N (liftHashN N g A))) +
            collisionAdvantage C nonceCoef N qs (withTable N (liftHashN N g A)))) +
        (qh + qs + 1 : ℕ) / n + qs / (n - 1 : ℝ) +
        (qh + qs + N : ℕ) * ((Fintype.card H - n : ℝ) / Fintype.card H) +
        (qs : ℝ) ^ 2 / Fintype.card Rnd + qs * (qn / Fintype.card Rnd) +
        (2 * qs : ℕ) * ((Fintype.card W - Fintype.card (ZMod n)ˣ : ℝ) / Fintype.card W) := by
  have h1 := nonceGenAdvantageH_le C nonceCoef N qs red e₀ A ρ g hg qh hH
  have h2 := nonceGen_unforgeable C nonceCoef N qs (liftHashN N g A) ρ e₀ gW hgW hρ hN qh qn
    (fun c P => nbound_mapAns _ _ _ (hA c P))
    (fun c P G => by
      change HashBound (answerG (fun _ : Ex => ()) (answerG G
        (mapAns (sumAns (sumAns (hashAns N g))) (A c P)))) qh
      rw [answerG_mapAns, answerG_mapAns]
      exact hashBound_mapAns N g _ qh (hH _ _ _))
  linarith

/-! ### `NonceGen` with the `sk` argument -/

variable (A : SkAdversaryH n N E X M Rnd Rp Ex W H Coins) (ρ : W → ZMod n)
  (mask : (ZMod n)ˣ → Fin qs → Rnd ≃ Rnd)

set_option synthInstance.maxSize 4000 in
/-- **A hash output reduced to a scalar costs `(|H| - n) / |H|` for every
value of the oracle that the game reads**, in the game with `NonceGen` and its
`sk` argument. -/
theorem nonceGenSkAdvantageH_le (g : ZMod n → H) (hg : ∀ c, red (g c) = c) (qh : ℕ)
    (hH : ∀ c P G (Aux : Rp → Rnd),
      HashBound (answerG (fun _ : Ex => ()) (answerG G (answerG Aux (A c P)))) qh) :
    nonceGenSkAdvantageH C nonceCoef N qs red A ρ e₀ mask ≤
      nonceGenSkAdvantage C nonceCoef N qs (liftHashSk N g A) ρ e₀ mask +
        (qh + qs + N : ℕ) * ((Fintype.card H - n : ℝ) / Fintype.card H) := by
  unfold nonceGenSkAdvantageH nonceGenSkAdvantage
  rw [← prob_equiv (tabLastSk (Tb := SigIn N X M → H))
      (nonceGenSkExperimentH C nonceCoef N qs red A ρ e₀ mask),
    ← prob_equiv (tabLastSk (Tb := SigIn N X M → ZMod n))
      (nonceGenSkExperiment C nonceCoef N qs (liftHashSk N g A) ρ e₀ mask)]
  refine prob_prod_mono _ _ _ (hashGap_nonneg red g hg _) fun a => ?_
  have h := nonceGenExperimentH_le C nonceCoef N qs red e₀ g hg (fun c P => answerG a.2 (A c P)) ρ
    qh a.1.1.1.1 a.1.1.1.2 (fun k => mask a.1.1.1.1 k (a.2 (a.1.2 k))) a.1.1.2 (hH _ _ _ _)
  have hl : liftHashN N g (fun c P => answerG a.2 (A c P)) =
      fun c P => answerG a.2 (liftHashSk N g A c P) := by
    funext c P
    exact (answerG_mapAns a.2 _ _).symm
  rw [hl] at h
  exact h

set_option synthInstance.maxSize 4000 in
/-- **Unforgeability with `NonceGen`, its `sk` argument and the challenge hash
reduced to a scalar**, under AOMDL with `hash_BIP0459/sig`,
`hash_BIP0459/nonce` and `hash_BIP0459/aux` as random oracles: the bound of
`unforgeable_sqrt` and the error terms of the three oracles. -/
theorem nonceGenSk_unforgeable_hashed (g : ZMod n → H) (hg : ∀ c, red (g c) = c)
    (gW : (ZMod n)ˣ → W) (hgW : Injective gW) (hρ : ∀ u, ρ (gW u) = u) (hN : N < n)
    (qh qn qa : ℕ) (hA : ∀ c P, NBound (A c P) qa)
    (hG : ∀ c P (Aux : Rp → Rnd), NBound (answerG Aux (A c P)) qn)
    (hH : ∀ c P G (Aux : Rp → Rnd),
      HashBound (answerG (fun _ : Ex => ()) (answerG G (answerG Aux (A c P)))) qh) :
    nonceGenSkAdvantageH C nonceCoef N qs red A ρ e₀ mask ≤
      Real.sqrt ((qh + qs + 1 : ℕ) *
          (omdlAdvantage C (2 * qs + 1)
              (reduction C nonceCoef N qs (withTable N (withAux N (liftHashSk N g A)))) +
            collisionAdvantage C nonceCoef N qs
              (withTable N (withAux N (liftHashSk N g A))))) +
        (qh + qs + 1 : ℕ) / n + qs / (n - 1 : ℝ) +
        (qh + qs + N : ℕ) * ((Fintype.card H - n : ℝ) / Fintype.card H) +
        (qs : ℝ) ^ 2 / Fintype.card Rnd + qs * (qn / Fintype.card Rnd) +
        (2 * qs : ℕ) * ((Fintype.card W - Fintype.card (ZMod n)ˣ : ℝ) / Fintype.card W) +
        (qs : ℝ) ^ 2 / Fintype.card Rp + qs * (qa / Fintype.card Rp) := by
  have h1 := nonceGenSkAdvantageH_le C nonceCoef N qs red e₀ A ρ mask g hg qh hH
  have h2 := nonceGenSk_advantage C nonceCoef N qs (liftHashSk N g A) ρ e₀ mask gW hgW hρ qn qa
    (fun c P => nbound_mapAns _ _ _ (hA c P))
    (fun c P Aux => by
      change NBound (answerG Aux (mapAns (sumAns (sumAns (sumAns (hashAns N g)))) (A c P))) qn
      rw [answerG_mapAns]
      exact nbound_mapAns _ _ _ (hG c P Aux))
  have h3 := unforgeable_sqrt C nonceCoef N qs (withTable N (withAux N (liftHashSk N g A))) hN qh
    fun c P => by
      change HashBound (answerG (fun _ : Ex => ()) (answerG c.2 (answerG c.1.2
        (mapAns (sumAns (sumAns (sumAns (hashAns N g)))) (A c.1.1 P))))) qh
      rw [answerG_mapAns, answerG_mapAns, answerG_mapAns]
      exact hashBound_mapAns N g _ qh (hH _ _ _ _)
  linarith

end Dahlias.Security
