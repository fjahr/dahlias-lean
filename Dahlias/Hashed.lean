import Dahlias.LazyGame
import Dahlias.NonceProb
import Dahlias.Unforgeability

/-!
# The challenge hash as an output reduced to a scalar

In the game of `Dahlias.Security` the random oracle for `hash_BIP0459/sig`
answers with a uniform scalar. BIP 459 computes
`c = int(hash_BIP0459/sig(…)) mod n` from a 256-bit hash.

Here the oracle answers with a uniform element of a type `H`, the outputs of
the hash function. The adversary sees them. `Sign` and `Verify` turn an
output into a scalar with `red` (`forgeExperimentH`).

`forgeAdvantageH_le`: if every scalar `c` has an output `g c` with
`red (g c) = c`, an adversary with at most `qh` hash queries wins this game at
most

  `(qh + qs + N) ⋅ (|H| - n) / |H|`

more often than the adversary `liftHash g A` wins the game with scalar
answers. That adversary passes `g c` on when the oracle answers `c`. The game
reads at most `qh + qs + N` values of the oracle, and each is in the range of
`g` except with probability `(|H| - n) / |H|`.

`unforgeable_sqrt_fin` is the security theorem for `H = {0, …, m - 1}` and
`red h = h mod n`, which is BIP 459 for `m = 2²⁵⁶`. There
`(m - n) / m` is about `2^-127.7`.

The nonce coefficient hash needs no such step: it is a fixed function into the
scalars, and BIP 459's `int(hash_BIP0459/noncecoef(…)) mod n` is one.
-/

set_option linter.unusedSectionVars false

namespace Dahlias.Security

open Taproot QTree Function

variable {n : ℕ} [Fact n.Prime] {E X M : Type} [AddCommGroup E] [DecidableEq E] [DecidableEq X]
  [DecidableEq M]

/-! ## The game -/

/-- The game's answers when the random oracle returns outputs in `H`. -/
def AdvRH (H : Type) {N : ℕ} : AdvQ n N E X M → Type
  | .hash _ => H
  | .openSession => Option (PubNonce E)
  | .close .. => Option (ZMod n)
  | .single _ => Option (X × ZMod n)

/-- An adversary that sees the outputs of the hash function. -/
abbrev AdversaryH (n N : ℕ) (E X M H Coins : Type) :=
  Coins → E → Alg (AdvQ n N E X M) (AdvRH H) (Forgery n X M)

variable (C : Curve n E X) (nonceCoef : E → E → List (X × M × E) → ZMod n) (N qs : ℕ)
  {H : Type} (red : H → ZMod n)

/-- The game's answers for the table `Tab` of hash outputs: a hash query
returns the output, the signer reduces it with `red`. -/
def challengerH (x : ZMod n) (nonces : Fin qs → SecNonce n) (Tab : SigIn N X M → H) :
    (q : AdvQ n N E X M) → SignerState X M → AdvRH H q × SignerState X M
  | .hash z, st => (Tab z, st)
  | .openSession, st =>
    challenger C nonceCoef N qs x nonces (fun z => red (Tab z)) .openSession st
  | .close k τ m agg pm pubnonces, st =>
    challenger C nonceCoef N qs x nonces (fun z => red (Tab z)) (.close k τ m agg pm pubnonces) st
  | .single items, st =>
    challenger C nonceCoef N qs x nonces (fun z => red (Tab z)) (.single items) st

/-- The sample of the game: the secret key, the nonces, the adversary's coins
and the table of hash outputs. -/
abbrev ForgeSampleH (n N qs : ℕ) (X M H Coins : Type) :=
  (ZMod n)ˣ × (Fin qs → (ZMod n)ˣ × (ZMod n)ˣ) × Coins × (SigIn N X M → H)

variable {Coins : Type}

/-- **The unforgeability game with hash outputs in `H`** on one sample. The
verifier reduces the outputs with `red` as the signer does. -/
def forgeExperimentH (A : AdversaryH n N E X M H Coins) (ω : ForgeSampleH n N qs X M H Coins) :
    Prop :=
  let x : ZMod n := ω.1
  let nonces : Fin qs → SecNonce n := fun k => ((ω.2.1 k).1, (ω.2.1 k).2)
  let Tab := ω.2.2.2
  let out := (A ω.2.2.1 (C.mulG x)).run (challengerH C nonceCoef N qs red x nonces Tab)
    ⟨0, [], []⟩
  Wins C nonceCoef N x (fun z => red (Tab z)) out.1 out.2

/-- The adversary's probability of forging in the game with hash outputs. -/
noncomputable def forgeAdvantageH [Fintype Coins] [Fintype (SigIn N X M)] [Fintype H]
    (A : AdversaryH n N E X M H Coins) : ℝ :=
  prob (forgeExperimentH C nonceCoef N qs red A)

/-! ## From hash outputs to scalars -/

/-- The adversary for the game with scalar answers: when the oracle answers
`c`, it continues with the output `g c`. -/
def liftHash (g : ZMod n → H) {α : Type} :
    Alg (AdvQ n N E X M) (AdvRH H) α → Alg (AdvQ n N E X M) AdvR α
  | .done a => .done a
  | .ask (.hash z) f => .ask (.hash z) fun c => liftHash g (f (g c))
  | .ask .openSession f => .ask .openSession fun r => liftHash g (f r)
  | .ask (.close k τ m agg pm pubnonces) f =>
    .ask (.close k τ m agg pm pubnonces) fun r => liftHash g (f r)
  | .ask (.single items) f => .ask (.single items) fun r => liftHash g (f r)

/-- On the table `g ∘ T` the game with hash outputs is the game with scalar
answers for `liftHash g`. -/
theorem run_liftHash (g : ZMod n → H) (hg : ∀ c, red (g c) = c) (x : ZMod n)
    (nonces : Fin qs → SecNonce n) (T : SigIn N X M → ZMod n) {α : Type}
    (t : Alg (AdvQ n N E X M) (AdvRH H) α) (st : SignerState X M) :
    (liftHash N g t).run (challenger C nonceCoef N qs x nonces T) st =
      t.run (challengerH C nonceCoef N qs red x nonces fun z => g (T z)) st := by
  have hT : (fun z => red (g (T z))) = T := funext fun z => hg _
  induction t generalizing st with
  | done a => rfl
  | ask q f ih =>
    cases q with
    | hash z => exact ih _ _
    | openSession =>
      simp only [liftHash, Alg.run_ask, challengerH, hT]
      exact ih _ _
    | close k τ m agg pm pubnonces =>
      simp only [liftHash, Alg.run_ask, challengerH, hT]
      exact ih _ _
    | single items =>
      simp only [liftHash, Alg.run_ask, challengerH, hT]
      exact ih _ _

omit [Fact n.Prime] [AddCommGroup E] [DecidableEq E] [DecidableEq X] [DecidableEq M] in
theorem hashBound_liftHash (g : ZMod n → H) {α : Type} (t : Alg (AdvQ n N E X M) (AdvRH H) α)
    (qh : ℕ) (h : HashBound t qh) : HashBound (liftHash N g t) qh := by
  induction t generalizing qh with
  | done a => trivial
  | ask q f ih =>
    cases q with
    | hash z => exact ⟨h.1, fun r => ih _ _ (h.2 _)⟩
    | openSession => exact fun r => ih _ _ (h _)
    | close k τ m agg pm pubnonces => exact fun r => ih _ _ (h _)
    | single items => exact ⟨h.1, fun r => ih _ _ (h.2 _)⟩

/-! ## The game as a query algorithm -/

variable (x : ZMod n) (nonces : Fin qs → SecNonce n)

/-- `challengerH`, with the table as an oracle. -/
def treeChallengerH : (q : AdvQ n N E X M) → SignerState X M →
    QTree (SigIn N X M) H (AdvRH H q × SignerState X M)
  | .hash z, st => .ask z fun h => .done (h, st)
  | .openSession, st => mapTree red (treeChallenger false C nonceCoef N qs x nonces .openSession st)
  | .close k τ m agg pm pubnonces, st =>
    mapTree red (treeChallenger false C nonceCoef N qs x nonces (.close k τ m agg pm pubnonces) st)
  | .single items, st =>
    mapTree red (treeChallenger false C nonceCoef N qs x nonces (.single items) st)

theorem eval_treeChallengerH (Tab : SigIn N X M → H) (q : AdvQ n N E X M)
    (st : SignerState X M) :
    eval Tab (treeChallengerH C nonceCoef N qs red x nonces q st) =
      challengerH C nonceCoef N qs red x nonces Tab q st := by
  cases q with
  | hash z => rfl
  | openSession =>
    exact (eval_mapTree red Tab _).trans
      (eval_treeChallenger false C nonceCoef N qs x nonces _ _ st)
  | close k τ m agg pm pubnonces =>
    exact (eval_mapTree red Tab _).trans
      (eval_treeChallenger false C nonceCoef N qs x nonces _ _ st)
  | single items =>
    exact (eval_mapTree red Tab _).trans
      (eval_treeChallenger false C nonceCoef N qs x nonces _ _ st)

theorem step_boundH (Tab : SigIn N X M → H) (q : AdvQ n N E X M) (st : SignerState X M)
    (l : List (SigIn N X M)) (hst : ClosedOk qs st) :
    ClosedOk qs (eval Tab (treeChallengerH C nonceCoef N qs red x nonces q st)).2 ∧
      (flog Tab l (treeChallengerH C nonceCoef N qs red x nonces q st)).length +
          (qs - (eval Tab (treeChallengerH C nonceCoef N qs red x nonces q st)).2.closed.length) ≤
        l.length + (qs - st.closed.length) + hashCost q := by
  cases q with
  | hash z =>
    refine ⟨hst, ?_⟩
    simp only [treeChallengerH, QTree.eval, hashCost]
    refine le_trans (Nat.add_le_add_right (length_flog_ask_done Tab l z _) _) ?_
    omega
  | openSession =>
    have h := step_bound false C nonceCoef N qs x nonces (fun z => red (Tab z)) .openSession st l
      hst
    rw [← eval_mapTree red Tab, ← flog_mapTree red Tab] at h
    exact h
  | close k τ m agg pm pubnonces =>
    have h := step_bound false C nonceCoef N qs x nonces (fun z => red (Tab z))
      (.close k τ m agg pm pubnonces) st l hst
    rw [← eval_mapTree red Tab, ← flog_mapTree red Tab] at h
    exact h
  | single items =>
    have h := step_bound false C nonceCoef N qs x nonces (fun z => red (Tab z)) (.single items)
      st l hst
    rw [← eval_mapTree red Tab, ← flog_mapTree red Tab] at h
    exact h

theorem length_flog_interpH (Tab : SigIn N X M → H) {α : Type}
    (t : Alg (AdvQ n N E X M) (AdvRH H) α) (qh : ℕ) (ht : HashBound t qh)
    (st : SignerState X M) (l : List (SigIn N X M)) (hst : ClosedOk qs st) :
    (flog Tab l (Alg.interp (treeChallengerH C nonceCoef N qs red x nonces) t st)).length ≤
      l.length + qh + (qs - st.closed.length) := by
  induction t generalizing st l qh with
  | done a =>
    change l.length ≤ _
    omega
  | ask q f ih =>
    rw [Alg.interp_ask, flog_bind]
    obtain ⟨hst', hstep⟩ := step_boundH C nonceCoef N qs red x nonces Tab q st l hst
    obtain ⟨hc, hf⟩ := hashBound_ask ht
    have := ih (eval Tab (treeChallengerH C nonceCoef N qs red x nonces q st)).1
      (qh - hashCost q) (hf _) (eval Tab (treeChallengerH C nonceCoef N qs red x nonces q st)).2
      (flog Tab l (treeChallengerH C nonceCoef N qs red x nonces q st)) hst'
    omega

variable (A : AdversaryH n N E X M H Coins) (coins : Coins)

/-- The whole game with hash outputs as one algorithm. -/
noncomputable def winTreeH : QTree (SigIn N X M) H Bool :=
  Alg.interp (treeChallengerH C nonceCoef N qs red x nonces) (A coins (C.mulG x)) ⟨0, [], []⟩ >>=
    fun out => mapTree red (winTail C N x out)

theorem eval_winTreeH (Tab : SigIn N X M → H) :
    eval Tab (winTreeH C nonceCoef N qs red x nonces A coins) = true ↔
      Wins C nonceCoef N x (fun z => red (Tab z))
        ((A coins (C.mulG x)).run (challengerH C nonceCoef N qs red x nonces Tab) ⟨0, [], []⟩).1
        ((A coins (C.mulG x)).run (challengerH C nonceCoef N qs red x nonces Tab)
          ⟨0, [], []⟩).2 := by
  unfold winTreeH
  rw [eval_bind, eval_interp_of _ _ Tab (eval_treeChallengerH C nonceCoef N qs red x nonces Tab),
    eval_mapTree]
  exact eval_winTail C nonceCoef N x _ _

theorem length_fresh_winTreeH (Tab : SigIn N X M → H) (qh : ℕ)
    (hA : HashBound (A coins (C.mulG x)) qh) :
    (fresh Tab (winTreeH C nonceCoef N qs red x nonces A coins)).length ≤ qh + qs + N := by
  unfold winTreeH
  rw [fresh_bind, flog_mapTree]
  have h := length_flog_interpH C nonceCoef N qs red x nonces Tab (A coins (C.mulG x)) qh hA
    ⟨0, [], []⟩ [] ⟨List.nodup_nil, by simp, Nat.zero_le _⟩
  simp only [List.length_nil, zero_add, Nat.sub_zero] at h
  exact (length_flog_winTail C N x _ _ _).trans (Nat.add_le_add_right h N)

/-! ## The bound -/

variable [Fintype Coins] [Fintype (SigIn N X M)] [Fintype H] [DecidableEq H]

set_option synthInstance.maxSize 2000 in
/-- **A hash output reduced to a scalar costs `(|H| - n) / |H|` for every
value of the oracle that the game reads.** -/
theorem forgeAdvantageH_le (g : ZMod n → H) (hg : ∀ c, red (g c) = c) (qh : ℕ)
    (hA : ∀ coins P, HashBound (A coins P) qh) :
    forgeAdvantageH C nonceCoef N qs red A ≤
      forgeAdvantage C nonceCoef N qs (fun coins P => liftHash N g (A coins P)) +
        (qh + qs + N : ℕ) * ((Fintype.card H - n : ℝ) / Fintype.card H) := by
  have hinj : Injective g := fun a b h => by rw [← hg a, ← hg b, h]
  have hle : n ≤ Fintype.card H := by
    simpa [ZMod.card] using Fintype.card_le_of_injective g hinj
  have hc : (0 : ℝ) ≤ (qh + qs + N : ℕ) * ((Fintype.card H - n : ℝ) / Fintype.card H) := by
    have : (0 : ℝ) ≤ Fintype.card H - n := sub_nonneg.mpr (Nat.cast_le.mpr hle)
    positivity
  change prob (forgeExperimentH C nonceCoef N qs red A) ≤
    prob (forgeExperimentG false C nonceCoef N qs fun coins P => liftHash N g (A coins P)) + _
  refine prob_prod_mono _ _ _ hc fun u => prob_prod_mono _ _ _ hc fun ν =>
    prob_prod_mono _ _ _ hc fun c => ?_
  -- the game for this key, these nonces and these coins, as a query algorithm
  let _ : Inhabited H := ⟨g default⟩
  set t := winTreeH C nonceCoef N qs red (u : ZMod n) (fun k => ((ν k).1, (ν k).2)) A c with ht
  have hfresh : ∀ Tab : SigIn N X M → H, (fresh Tab t).length ≤ qh + qs + N := fun Tab =>
    length_fresh_winTreeH C nonceCoef N qs red _ _ A c Tab qh (hA c _)
  -- a uniform table is a lazily sampled one
  have h1 := prob_eval_eq_lazy (fun b : Bool => b = true) (qh + qs + N) t hfresh
  -- the sampled outputs are in the range of `g`, up to the error term
  have h2 := prob_section (ι := Fin (qh + qs + N)) g hinj
    (fun v => evalLazy (stream v) 0 [] t = true)
  -- on outputs in the range of `g` the game is the one with scalar answers
  have hstream : ∀ w : Fin (qh + qs + N) → ZMod n,
      stream (g ∘ w) = fun i => g (stream w i) := by
    intro w
    funext i
    unfold stream
    split_ifs <;> rfl
  have h3 : (fun w : Fin (qh + qs + N) → ZMod n => evalLazy (stream (g ∘ w)) 0 [] t = true) =
      fun w => evalLazy (stream w) 0 [] (mapTree g t) = true := by
    funext w
    rw [evalLazy_mapTree, hstream]
    rfl
  have h4 := prob_eval_eq_lazy (fun b : Bool => b = true) (qh + qs + N) (mapTree g t)
    fun T => by
      rw [fresh, flog_mapTree]
      exact hfresh _
  have h5 : (fun T : SigIn N X M → ZMod n => eval T (mapTree g t) = true) =
      fun T => forgeExperimentG false C nonceCoef N qs
        (fun coins P => liftHash N g (A coins P)) (u, ν, c, T) := by
    funext T
    rw [eval_mapTree, ht]
    refine propext ((eval_winTreeH C nonceCoef N qs red _ _ A c _).trans ?_)
    unfold forgeExperimentG
    dsimp only
    rw [run_liftHash C nonceCoef N qs red g hg]
    have hT : (fun z => red (g (T z))) = T := funext fun z => hg _
    rw [hT]
  have h0 : (fun Tab : SigIn N X M → H => forgeExperimentH C nonceCoef N qs red A (u, ν, c, Tab)) =
      fun Tab => eval Tab t = true := by
    funext Tab
    exact propext (eval_winTreeH C nonceCoef N qs red _ _ A c Tab).symm
  rw [h0, h1, ← h5, h4, ← h3]
  refine h2.trans (le_of_eq ?_)
  rw [Fintype.card_fin, ZMod.card]

/-- **Unforgeability with the challenge hash reduced to a scalar**: the bound
of `unforgeable_sqrt` and the term for the reduction. -/
theorem unforgeable_sqrt_hashed (g : ZMod n → H) (hg : ∀ c, red (g c) = c) (hN : N < n)
    (qh : ℕ) (hA : ∀ coins P, HashBound (A coins P) qh) :
    forgeAdvantageH C nonceCoef N qs red A ≤
      Real.sqrt ((qh + qs + 1 : ℕ) *
          (omdlAdvantage C (2 * qs + 1)
              (reduction C nonceCoef N qs fun coins P => liftHash N g (A coins P)) +
            collisionAdvantage C nonceCoef N qs fun coins P => liftHash N g (A coins P))) +
        (qh + qs + 1 : ℕ) / n + qs / (n - 1 : ℝ) +
        (qh + qs + N : ℕ) * ((Fintype.card H - n : ℝ) / Fintype.card H) := by
  have h1 := forgeAdvantageH_le C nonceCoef N qs red A g hg qh hA
  have h2 := unforgeable_sqrt C nonceCoef N qs (fun coins P => liftHash N g (A coins P)) hN qh
    fun coins P => hashBound_liftHash N g _ qh (hA coins P)
  linarith

/-! ## Outputs `0, …, m - 1` reduced modulo `n` -/

/-- `h mod n`. -/
def redFin (m : ℕ) (h : Fin m) : ZMod n := (h.val : ZMod n)

/-- The smallest output that reduces to `c`. -/
def liftFin {m : ℕ} (hm : n ≤ m) (c : ZMod n) : Fin m :=
  ⟨c.val, lt_of_lt_of_le (ZMod.val_lt c) hm⟩

omit [DecidableEq H] [Fintype H] in
/-- **BIP 459's challenge hash**: an `m`-valued random oracle reduced modulo
`n`, for `m = 2²⁵⁶`. The adversary's advantage is at most the bound of
`unforgeable_sqrt` plus `(qh + qs + N) ⋅ (m - n) / m`. -/
theorem unforgeable_sqrt_fin {m : ℕ} (hm : n ≤ m) (A : AdversaryH n N E X M (Fin m) Coins)
    (hN : N < n) (qh : ℕ) (hA : ∀ coins P, HashBound (A coins P) qh) :
    forgeAdvantageH C nonceCoef N qs (redFin m) A ≤
      Real.sqrt ((qh + qs + 1 : ℕ) *
          (omdlAdvantage C (2 * qs + 1)
              (reduction C nonceCoef N qs fun coins P => liftHash N (liftFin hm) (A coins P)) +
            collisionAdvantage C nonceCoef N qs
              fun coins P => liftHash N (liftFin hm) (A coins P))) +
        (qh + qs + 1 : ℕ) / n + qs / (n - 1 : ℝ) +
        (qh + qs + N : ℕ) * ((m - n : ℝ) / m) := by
  have h := unforgeable_sqrt_hashed C nonceCoef N qs (redFin m) A (liftFin hm)
    (fun c => ZMod.natCast_zmod_val c) hN qh hA
  rwa [Fintype.card_fin] at h

end Dahlias.Security
