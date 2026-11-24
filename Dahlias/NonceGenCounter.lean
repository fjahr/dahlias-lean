import Dahlias.NonceGenLazy
import Dahlias.Single

/-!
# `NonceGen` with a counter in place of the random value

`secp256k1_fullagg_nonce_gen_counter` runs `NonceGen` with the signer's secret
key and a counter value in place of the random value `rand'`. The theorems of
`Dahlias.NonceGenSk` assume a uniform `rand'` and say nothing about this.

Here the `rand'` of slot `k` is a public value `ctr k`, and these values are
distinct. Then `rand = mask x k (Aux (ctr k))`, where the adversary can compute
`Aux (ctr k)` and only the secret key `x` hides `rand`. The nonces are still
fresh values of `hash_BIP0459/nonce`, unless the adversary queries it at a
`rand`. A `rand` gives the secret key (`unmask`), and the holder of the secret
key forges. So such a query is as unlikely as a forgery in the game with
uniform nonces.

* `nonceGenCtrExperiment` is the game.
* `keyForger A` is the forger. It runs `A`, looks for the secret key among the
  candidates that the queries of `A` to the nonce hash give, and signs a new
  message with it.
* `nonceGenCtr_advantage`: `A` wins at most as often as `A` and `keyForger A`
  together win the game with uniform nonces, plus `qs² / |Rnd|` for two equal
  values of the aux hash and the terms for the reduction modulo the group
  order.
* `nonceGenCtr_unforgeable`, `nonceGenCtr_unforgeable_hashed` and
  `nonceGenCtr_unforgeable_fin` are the security theorems. Their bound has
  `lazyBound` once for each of the two forgers.

The theorems assume that the counter values are distinct, that the secret key
can be read off a `rand` and the value of the aux hash, as for
`rand = bytes(x) xor Aux(rand')`, and that there are `qs + 1` distinct
messages. The key that `NonceGen` gets in slot `k` is `x` or a key tweaked
from it, as in `Dahlias.NonceGenSk`: `mask x k` is any bijection, but the
family is fixed before the game. The adversary does not choose the key of a
slot.
-/

set_option linter.unusedSectionVars false

namespace Dahlias.Security

open Taproot Function QTree

/-! ## Values of a random oracle at points that the game may hit -/

section Hit

variable {D W ι : Type} [Fintype D] [DecidableEq D] [Fintype W] [Nonempty W] [Fintype ι]
  [DecidableEq ι]

/-- **Oracle values at distinct points are fresh unless the game reads the
oracle at such a point.** A game uses the values of a uniform table `G` at the
distinct points `p i`, and it reads `G` elsewhere only at the points of `log`.
Every point `p i` has the property `S`. Then the game is won at most as often
as the game with independent uniform values `v` in place of the table's is
won or reads the table at a point with the property `S`. -/
theorem fresh_values_or_hit (p : ι → D) (hp : Injective p) (S : D → Prop) (hS : ∀ i, S (p i))
    (win : (D → W) → (ι → W) → Prop) (log : (D → W) → (ι → W) → List D)
    (hcongr : ∀ G G' v, (∀ z ∈ log G v, G' z = G z) → (win G' v ↔ win G v)) :
    prob (fun G : D → W => win G fun i => G (p i)) ≤
      prob (fun y : (D → W) × (ι → W) => win y.1 y.2 ∨ ∃ z ∈ log y.1 y.2, S z) := by
  rw [← prob_fst (B := ι → W) (fun G : D → W => win G fun i => G (p i))]
  rw [← prob_equiv (Involutive.toPerm _ (swapAt_involutive (W := W) hp))
    (fun y : (D → W) × (ι → W) => win y.1 y.2 ∨ ∃ z ∈ log y.1 y.2, S z)]
  refine prob_mono ?_
  rintro ⟨G, w⟩ hR
  change win (overwrite p G w) (fun i => G (p i)) ∨
    ∃ z ∈ log (overwrite p G w) (fun i => G (p i)), S z
  by_cases hb : ∃ z ∈ log (overwrite p G w) (fun i => G (p i)), S z
  · exact Or.inr hb
  · refine Or.inl ((hcongr _ G _ fun z hz => ?_).mp hR)
    refine (overwrite_of_ne G w fun i hi => ?_).symm
    exact hb ⟨z, hz, hi ▸ hS i⟩

/-- **The values of a uniform table at distinct points are independent
uniform values.** -/
theorem prob_comp_injective (c : ι → D) (hc : Injective c) (P : (ι → W) → Prop) :
    prob (fun G : D → W => P fun i => G (c i)) = prob P := by
  have h1 := prob_fst (B := ι → W) (fun G : D → W => P fun i => G (c i))
  have h2 := prob_equiv (Involutive.toPerm _ (swapAt_involutive (W := W) hc))
    (fun y : (D → W) × (ι → W) => P y.2)
  have h3 := prob_equiv (Equiv.prodComm (D → W) (ι → W)) (fun y : (ι → W) × (D → W) => P y.1)
  have h4 := prob_fst (B := D → W) P
  rw [← h1, ← h4, ← h3]
  exact h2

end Hit

/-! ## A tally of the queries of an algorithm -/

section Tally

variable {Q : Type} {R : Q → Type} {D W α σ : Type}

/-- The algorithm that also returns a tally of its queries and their
answers. -/
def tally (upd : (q : Q) → R q → σ → σ) : Alg Q R α → σ → Alg Q R (α × σ)
  | .done a, o => .done (a, o)
  | .ask q f, o => .ask q fun r => tally upd (f r) (upd q r o)

theorem tally_fst (upd : (q : Q) → R q → σ → σ) (t : Alg Q R α) (o : σ) :
    (tally upd t o >>= fun p => (.done p.1 : Alg Q R α)) = t := by
  induction t generalizing o with
  | done a => rfl
  | ask q f ih =>
    simp only [tally, Alg.ask_bind]
    congr 1
    funext r
    exact ih r _

/-- A tally that leaves the queries of the table out. -/
def liftUpd (upd : (q : Q) → R q → σ → σ) : (q : Q ⊕ D) → SumR R W q → σ → σ
  | .inl q, r, o => upd q r o
  | .inr _, _, o => o

theorem answerG_tally (G : D → W) (upd : (q : Q) → R q → σ → σ)
    (t : Alg (Q ⊕ D) (SumR R W) α) (o : σ) :
    answerG G (tally (liftUpd upd) t o) = tally upd (answerG G t) o := by
  induction t generalizing o with
  | done a => rfl
  | ask x f ih =>
    cases x with
    | inl q =>
      change Alg.ask q (fun r => answerG G (tally (liftUpd upd) (f r) (upd q r o))) =
        Alg.ask q fun r => tally upd (answerG G (f r)) (upd q r o)
      congr 1
      funext r
      exact ih r _
    | inr z => exact ih _ _

theorem nbound_tally (upd : (q : Q ⊕ D) → SumR R W q → σ → σ)
    (t : Alg (Q ⊕ D) (SumR R W) α) (o : σ) (q : ℕ) (h : NBound t q) :
    NBound (tally upd t o) q := by
  induction t generalizing o q with
  | done a => trivial
  | ask x f ih =>
    cases x with
    | inl x => exact fun r => ih r _ _ (h r)
    | inr z => exact ⟨h.1, fun r => ih r _ _ (h.2 r)⟩

/-- Query the table at the points `pt k` for the `k` of a list, and return
every `k` with the answer. -/
def askList {ι : Type} (pt : ι → D) : List ι → Alg (Q ⊕ D) (SumR R W) (List (ι × W))
  | [] => .done []
  | k :: l => .ask (.inr (pt k)) fun a => askList pt l >>= fun as => .done ((k, a) :: as)

theorem answerG_askList {ι : Type} (G : D → W) (pt : ι → D) (l : List ι) :
    answerG G (askList (Q := Q) (R := R) pt l) = .done (l.map fun k => (k, G (pt k))) := by
  induction l with
  | nil => rfl
  | cons k l ih =>
    change answerG G (askList pt l >>= fun as => .done ((k, G (pt k)) :: as)) = _
    rw [answerG_bind, ih]
    rfl

theorem nbound_askList {ι : Type} (pt : ι → D) (l : List ι) :
    NBound (askList (Q := Q) (R := R) (W := W) pt l) l.length := by
  induction l with
  | nil => trivial
  | cons k l ih =>
    refine ⟨Nat.succ_pos _, fun a => ?_⟩
    have := NBound.bind
      (g := fun as => (.done ((k, a) :: as) : Alg (Q ⊕ D) (SumR R W) (List (ι × W))))
      (b := 0) ih fun as => trivial
    simpa using this

end Tally

variable {n : ℕ} [Fact n.Prime] {E X M : Type} [AddCommGroup E] [DecidableEq E] [DecidableEq X]
  [DecidableEq M]

/-! ## Bounds on the hash queries of composed algorithms -/

section HashBounds

variable {N : ℕ} {R : AdvQ n N E X M → Type} {α β : Type}

omit [Fact n.Prime] [AddCommGroup E] [DecidableEq E] [DecidableEq X] [DecidableEq M] in
theorem hashBound_mono (t : Alg (AdvQ n N E X M) R α) (a b : ℕ) (h : HashBound t a)
    (hab : a ≤ b) : HashBound t b := by
  induction t generalizing a b with
  | done r => trivial
  | ask q f ih =>
    obtain ⟨hc, hf⟩ := (hashBound_ask_iff q f a).mp h
    exact (hashBound_ask_iff q f b).mpr
      ⟨hc.trans hab, fun r => ih r _ _ (hf r) (Nat.sub_le_sub_right hab _)⟩

omit [Fact n.Prime] [AddCommGroup E] [DecidableEq E] [DecidableEq X] [DecidableEq M] in
theorem hashBound_bind (t : Alg (AdvQ n N E X M) R α) (K : α → Alg (AdvQ n N E X M) R β)
    (a b : ℕ) (ht : HashBound t a) (hK : ∀ r, HashBound (K r) b) :
    HashBound (t >>= K) (a + b) := by
  induction t generalizing a with
  | done r => exact hashBound_mono _ _ _ (hK r) (Nat.le_add_left _ _)
  | ask q f ih =>
    obtain ⟨hc, hf⟩ := (hashBound_ask_iff q f a).mp ht
    refine (hashBound_ask_iff q (fun r => f r >>= K) (a + b)).mpr ⟨by omega, fun r => ?_⟩
    rw [Nat.sub_add_comm hc]
    exact ih r _ (hf r)

omit [Fact n.Prime] [AddCommGroup E] [DecidableEq E] [DecidableEq X] [DecidableEq M] in
theorem hashBound_of_map (g : α → β) (t : Alg (AdvQ n N E X M) R α) (b : ℕ)
    (h : HashBound (t >>= fun p => (.done (g p) : Alg (AdvQ n N E X M) R β)) b) :
    HashBound t b := by
  induction t generalizing b with
  | done r => trivial
  | ask q f ih =>
    obtain ⟨hc, hf⟩ := (hashBound_ask_iff q (fun r => f r >>= fun p => .done (g p)) b).mp h
    exact (hashBound_ask_iff q f b).mpr ⟨hc, fun r => ih r _ (hf r)⟩

end HashBounds

/-! ## A forger from a query at a secret point -/

variable (C : Curve n E X) (nonceCoef : E → E → List (X × M × E) → ZMod n) (N qs : ℕ)
  {Rnd Rp Ex W Coins : Type}

/-- What a successful signing query adds to the signer's record: the list of
a session, or the items of a single-party signature. -/
abbrev SignedQ (n : ℕ) (X M : Type) := List (X × M) ⊕ List (Tweak n × M)

/-- The successful signing queries, from a query and its answer. -/
def trackOf : (q : AdvQ n N E X M) → AdvR q → List (SignedQ n X M) → List (SignedQ n X M)
  | .hash _, _, tr => tr
  | .openSession, _, tr => tr
  | .close _ _ _ _ pm _, r, tr => if r.isSome then .inl pm :: tr else tr
  | .single items, r, tr => if r.isSome then .inr items :: tr else tr

/-- The list of public keys and messages of a successful signing query. -/
def signedList (x : ZMod n) : SignedQ n X M → List (X × M)
  | .inl pm => pm
  | .inr items => singleKeys C x items

/-- The tally of a forger: its queries to the nonce hash and its successful
signing queries. -/
def obsUpd {D₁ W₁ : Type} : (q : (AdvQ n N E X M ⊕ Ex) ⊕ D₁) → SumR (SumR AdvR Unit) W₁ q →
    List D₁ × List (SignedQ n X M) → List D₁ × List (SignedQ n X M)
  | .inl (.inl q), r, o => (o.1, trackOf N q r o.2)
  | .inl (.inr _), _, o => o
  | .inr z, _, o => (z :: o.1, o.2)

variable (unmask : Fin qs → Rnd → Rnd → Option (ZMod n)ˣ) (msgs : Fin (qs + 1) → M)
  (ctr : Fin qs → Rp)

/-- The secret key, from the queries to the nonce hash and the values of the
aux hash at the counters: the first candidate that matches the public key. -/
def findKey (P : E) (log : List (Rnd × Ex × Bool)) (as : List (Fin qs × Rnd)) :
    Option (ZMod n)ˣ :=
  (log.product as).findSome? fun za =>
    (unmask za.2.1 za.1.1 za.2.2).filter fun x' : (ZMod n)ˣ => decide (C.mulG (x' : ZMod n) = P)

/-- A forgery by the holder of the secret key `x'`: a signature with the nonce
`1` for the key itself and the first of the messages `msgs` whose list the
signer has not signed. -/
def forgeTail (x' : ZMod n) (tr : List (SignedQ n X M)) (fallback : Forgery n X M) :
    Alg (AdvQ n N E X M) AdvR (Forgery n X M) :=
  match (List.finRange (qs + 1)).find? fun j =>
      decide ([(C.x (C.mulG x'), msgs j)] ∉ tr.map (signedList C x')) with
  | none => .done fallback
  | some j =>
    if hN : [(C.x (C.mulG x'), msgs j)].length ≤ N then
      .ask (.hash (⟨[(C.x (C.mulG x'), msgs j)], hN⟩, C.x (C.mulG 1),
        (C.x (C.mulG x'), msgs j))) fun (c : ZMod n) =>
          .done ⟨[(C.x (C.mulG x'), msgs j)], (0, 1), (C.x (C.mulG 1),
            (if C.hasEvenY (C.mulG 1) then 1 else -1) + (c * C.ops.evenScalar x' + 0))⟩
    else .done fallback

variable [DecidableEq Rnd]

/-- **The forger from a query at a secret point.** It runs `A` and keeps a
tally of the queries to the nonce hash and of the successful signing queries.
Then it reads the aux hash at the counters and looks for the secret key among
the candidates that the queries to the nonce hash give. With the key it signs
a new message. -/
def keyForger (A : SkAdversary n N E X M Rnd Rp Ex W Coins) :
    SkAdversary n N E X M Rnd Rp Ex W Coins := fun c P =>
  tally (liftUpd (obsUpd N)) (A c P) ([], []) >>= fun out =>
    askList ctr (List.finRange qs) >>= fun as =>
      match findKey C qs unmask P out.2.1 as with
      | none => .done out.1
      | some x' => liftQ (liftQ (liftQ (forgeTail C N qs msgs (x' : ZMod n) out.2.2 out.1)))

/-! ### The tally along a run of the game -/

section Run

/-- The lists in the signer's record are among the lists of the successful
signing queries, and there are at most as many of these as closed slots. -/
def TrInv (x : ZMod n) (st : SignerState X M) (tr : List (SignedQ n X M)) : Prop :=
  tr.length ≤ st.closed.length ∧ ∀ e ∈ st.signed, e.1 ∈ tr.map (signedList C x)

theorem closedOk_challenger (x : ZMod n) (nonces : Fin qs → SecNonce n)
    (T : SigIn N X M → ZMod n) (q : AdvQ n N E X M) (st : SignerState X M)
    (hst : ClosedOk qs st) : ClosedOk qs (challenger C nonceCoef N qs x nonces T q st).2 := by
  have h := (step_bound false C nonceCoef N qs x nonces T q st [] hst).1
  rwa [eval_treeChallenger] at h

theorem trInv_step (x : ZMod n) (nonces : Fin qs → SecNonce n) (T : SigIn N X M → ZMod n)
    (q : AdvQ n N E X M) (st : SignerState X M) (tr : List (SignedQ n X M))
    (h : TrInv C x st tr) :
    TrInv C x (challenger C nonceCoef N qs x nonces T q st).2
      (trackOf N q (challenger C nonceCoef N qs x nonces T q st).1 tr) := by
  cases q with
  | hash z => exact h
  | openSession =>
    unfold challenger challengerG
    dsimp only
    split_ifs <;> exact h
  | close k τ m agg pm pubnonces =>
    unfold challenger challengerG
    dsimp only
    split_ifs with hc
    · cases sign C.ops (hashesOf N nonceCoef T) (nonces ⟨k, hc.1⟩) (τ.sk x) m agg pm pubnonces with
      | none => exact h
      | some s =>
        refine ⟨Nat.succ_le_succ h.1, fun e he => ?_⟩
        rcases List.mem_cons.mp he with rfl | he
        · exact List.mem_map.mpr ⟨.inl pm, List.mem_cons_self, rfl⟩
        · obtain ⟨a, ha, hae⟩ := List.mem_map.mp (h.2 e he)
          exact List.mem_map.mpr ⟨a, List.mem_cons_of_mem _ ha, hae⟩
    · exact h
  | single items =>
    unfold challenger challengerG
    dsimp only
    split_ifs with ho hc
    · refine ⟨Nat.succ_le_succ h.1, fun e he => ?_⟩
      rcases List.mem_append.mp he with he | he
      · obtain ⟨a, -, rfl⟩ := List.mem_map.mp he
        exact List.mem_map.mpr ⟨.inr items, List.mem_cons_self, rfl⟩
      · obtain ⟨a, ha, hae⟩ := List.mem_map.mp (h.2 e he)
        exact List.mem_map.mpr ⟨a, List.mem_cons_of_mem _ ha, hae⟩
    · exact ⟨h.1.trans (Nat.le_succ _), h.2⟩
    · exact h

/-- **The tally of a run.** With the queries to the nonce hash answered from
a table, the forger's tally has every such query of the run, and the lists of
its successful signing queries cover the signer's record. -/
theorem run_tally_obs {D₁ W₁ α : Type} (x : ZMod n) (nv : Fin qs → Ex → SecNonce n)
    (T : SigIn N X M → ZMod n) (G : D₁ → W₁)
    (t : Alg ((AdvQ n N E X M ⊕ Ex) ⊕ D₁) (SumR (SumR AdvR Unit) W₁) α)
    (o : List D₁ × List (SignedQ n X M)) (s : SignerState X M × (ℕ → Ex))
    (hc : ClosedOk qs s.1) (hi : TrInv C x s.1 o.2) :
    ∃ o', (answerG G (tally (obsUpd N) t o)).run (challengerE C nonceCoef N qs nv x T) s =
        ((((answerG G t).run (challengerE C nonceCoef N qs nv x T) s).1, o'),
          ((answerG G t).run (challengerE C nonceCoef N qs nv x T) s).2) ∧
      (∀ z, z ∈ o.1 ∨ z ∈ gLog G (challengerE C nonceCoef N qs nv x T) t s → z ∈ o'.1) ∧
      ClosedOk qs ((answerG G t).run (challengerE C nonceCoef N qs nv x T) s).2.1 ∧
      TrInv C x ((answerG G t).run (challengerE C nonceCoef N qs nv x T) s).2.1 o'.2 := by
  induction t generalizing o s with
  | done a =>
    exact ⟨o, rfl, fun z hz => hz.elim id fun h => absurd h (by simp [gLog]), hc, hi⟩
  | ask q f ih =>
    cases q with
    | inl y =>
      cases y with
      | inl q =>
        exact ih _ (o.1, trackOf N q _ o.2) _
          (closedOk_challenger C nonceCoef N qs x _ T q s.1 hc)
          (trInv_step C nonceCoef N qs x _ T q s.1 o.2 hi)
      | inr e => exact ih () o _ hc hi
    | inr z =>
      obtain ⟨o', h1, h2, h3⟩ := ih (G z) (z :: o.1, o.2) s hc hi
      refine ⟨o', h1, fun z' hz' => h2 z' ?_, h3⟩
      rcases hz' with h | h
      · exact Or.inl (List.mem_cons_of_mem _ h)
      · rcases List.mem_cons.mp h with rfl | h
        · exact Or.inl List.mem_cons_self
        · exact Or.inr h

/-- A run without queries to the nonce hash and without a new `extra_in` is a
run of the game with the nonces of the current `extra_in`. -/
theorem run_liftQ_challengerE {α : Type} (x : ZMod n) (nv : Fin qs → Ex → SecNonce n)
    (T : SigIn N X M → ZMod n) (t : Alg (AdvQ n N E X M) AdvR α)
    (s : SignerState X M × (ℕ → Ex)) :
    (liftQ t : Alg (AdvQ n N E X M ⊕ Ex) (SumR AdvR Unit) α).run
        (challengerE C nonceCoef N qs nv x T) s =
      ((t.run (challenger C nonceCoef N qs x (fun k => nv k (s.2 k)) T) s.1).1,
        ((t.run (challenger C nonceCoef N qs x (fun k => nv k (s.2 k)) T) s.1).2, s.2)) := by
  induction t generalizing s with
  | done a => rfl
  | ask q f ih => exact ih _ _

end Run

/-! ### The forger wins when the adversary queries the nonce hash at a secret point -/

variable (mask : (ZMod n)ˣ → Fin qs → Rnd ≃ Rnd)

omit [DecidableEq X] [DecidableEq M] in
/-- A candidate from a query at a secret point is the secret key. -/
theorem findKey_eq (hunmask : ∀ x k a, unmask k (mask x k a) a = some x) (x : (ZMod n)ˣ)
    (log : List (Rnd × Ex × Bool)) (as : List (Fin qs × Rnd)) (k : Fin qs) (a : Rnd)
    (ha : (k, a) ∈ as) (hz : mask x k a ∈ log.map Prod.fst) :
    findKey C qs unmask (C.mulG (x : ZMod n)) log as = some x := by
  obtain ⟨z, hz, hz1⟩ := List.mem_map.mp hz
  cases hf : findKey C qs unmask (C.mulG (x : ZMod n)) log as with
  | none =>
    unfold findKey at hf
    rw [List.findSome?_eq_none_iff] at hf
    have := hf (z, (k, a)) (List.pair_mem_product.mpr ⟨hz, ha⟩)
    simp [hz1, hunmask] at this
  | some y =>
    unfold findKey at hf
    obtain ⟨za, -, hy⟩ := List.exists_of_findSome?_eq_some hf
    cases hu : unmask za.2.1 za.1.1 za.2.2 with
    | none => simp [hu] at hy
    | some w =>
      simp only [hu, Option.filter_some] at hy
      split_ifs at hy with hd
      cases Option.some.inj hy
      exact congrArg some (Units.ext (C.mulG_injective (of_decide_eq_true hd)))

/-- Among `qs + 1` messages there is one whose list is not among `qs` lists. -/
theorem exists_fresh (hmsgs : Injective msgs) (x' : ZMod n) (tr : List (SignedQ n X M))
    (htr : tr.length ≤ qs) :
    ∃ j : Fin (qs + 1), [(C.x (C.mulG x'), msgs j)] ∉ tr.map (signedList C x') := by
  by_contra hcon
  push Not at hcon
  have hinj : Injective fun j : Fin (qs + 1) => [(C.x (C.mulG x'), msgs j)] :=
    fun j j' h => hmsgs (by simpa using h)
  have hsub : ((List.finRange (qs + 1)).map fun j => [(C.x (C.mulG x'), msgs j)]) ⊆
      tr.map (signedList C x') := by
    intro L hL
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hL
    exact hcon j
  have hnd : ((List.finRange (qs + 1)).map fun j => [(C.x (C.mulG x'), msgs j)]).Nodup :=
    (List.nodup_finRange _).map hinj
  have := (hnd.subperm hsub).length_le
  simp only [List.length_map, List.length_finRange] at this
  omega

/-- **The holder of the secret key forges.** -/
theorem forgeTail_wins (hmsgs : Injective msgs) (hN : 0 < N) (x : (ZMod n)ˣ)
    (T : SigIn N X M → ZMod n) (nonces : Fin qs → SecNonce n) (tr : List (SignedQ n X M))
    (fb : Forgery n X M) (st : SignerState X M) (htr : tr.length ≤ qs)
    (hinv : ∀ e ∈ st.signed, e.1 ∈ tr.map (signedList C (x : ZMod n))) :
    ((forgeTail C N qs msgs (x : ZMod n) tr fb).run
        (challenger C nonceCoef N qs (x : ZMod n) nonces T) st).2 = st ∧
      Wins C nonceCoef N (x : ZMod n) T
        ((forgeTail C N qs msgs (x : ZMod n) tr fb).run
          (challenger C nonceCoef N qs (x : ZMod n) nonces T) st).1 st := by
  have hx : (x : ZMod n) ≠ 0 := x.ne_zero
  unfold forgeTail
  cases hfind : (List.finRange (qs + 1)).find? fun j =>
      decide ([(C.x (C.mulG (x : ZMod n)), msgs j)] ∉ tr.map (signedList C (x : ZMod n))) with
  | none =>
    obtain ⟨j, hj⟩ := exists_fresh C qs msgs hmsgs (x : ZMod n) tr htr
    have := List.find?_eq_none.mp hfind j (List.mem_finRange j)
    simp [hj] at this
  | some j =>
    have hj : [(C.x (C.mulG (x : ZMod n)), msgs j)] ∉ tr.map (signedList C (x : ZMod n)) := by
      simpa using List.find?_some hfind
    have hNL : [(C.x (C.mulG (x : ZMod n)), msgs j)].length ≤ N := hN
    have hN1 : 1 ≤ N := hN
    dsimp only
    simp only [hNL, ↓reduceDIte]
    refine ⟨rfl, ?_⟩
    have hsig : signSingle C.ops (hashesOf N nonceCoef T) 1 [((x : ZMod n), msgs j)] =
        some (C.x (C.mulG 1), (if C.hasEvenY (C.mulG 1) then 1 else -1) +
          (T (⟨[(C.x (C.mulG (x : ZMod n)), msgs j)], hNL⟩, C.x (C.mulG 1),
            (C.x (C.mulG (x : ZMod n)), msgs j)) * C.ops.evenScalar (x : ZMod n) + 0)) := by
      simp [signSingle, hx, singleList, hashesOf, hN1]
      split_ifs <;> simp_all
    have hv := verify_signSingle C (hashesOf N nonceCoef T) hsig
    change Wins C nonceCoef N (x : ZMod n) T ⟨[(C.x (C.mulG (x : ZMod n)), msgs j)], (0, 1),
      (C.x (C.mulG 1), (if C.hasEvenY (C.mulG 1) then 1 else -1) +
        (T (⟨[(C.x (C.mulG (x : ZMod n)), msgs j)], hNL⟩, C.x (C.mulG 1),
          (C.x (C.mulG (x : ZMod n)), msgs j)) * C.ops.evenScalar (x : ZMod n) + 0))⟩ st
    unfold Wins
    dsimp only
    refine ⟨one_ne_zero, by simp [Tweak.sk, hx], hNL, ⟨msgs j, ?_, ?_⟩, ?_⟩
    · simp [Tweak.sk]
    · intro hmem
      have hT : Tweak.sk ((0, 1) : Tweak n) (x : ZMod n) = x := by simp [Tweak.sk]
      rw [hT] at hmem
      exact hj (hinv _ hmem)
    · simpa [singleList] using hv

variable (e₀ : Ex) (A : SkAdversary n N E X M Rnd Rp Ex W Coins)

/-- **A query to the nonce hash at a secret point makes the forger win**, in
the game with any nonce values. -/
theorem winE_keyForger (hunmask : ∀ x k a, unmask k (mask x k a) a = some x)
    (hmsgs : Injective msgs)
    (hN : 0 < N) (x : (ZMod n)ˣ) (c : Coins) (T : SigIn N X M → ZMod n)
    (G : Rnd × Ex × Bool → W) (Aux : Rp → Rnd) (nv : Fin qs → Ex → SecNonce n)
    (hbad : ∃ k, mask x k (Aux (ctr k)) ∈
      (gLog G (challengerE C nonceCoef N qs nv (x : ZMod n) T)
        (answerG Aux (A c (C.mulG (x : ZMod n)))) (⟨0, [], []⟩, fun _ => e₀)).map Prod.fst) :
    winE C nonceCoef N qs (fun c P => answerG Aux (keyForger C N qs unmask msgs ctr A c P)) e₀
      (x, c, T) G nv := by
  obtain ⟨k, hk⟩ := hbad
  obtain ⟨o', hrun, hlog, hcl, hinv⟩ := run_tally_obs C nonceCoef N qs (x : ZMod n) nv T G
    (answerG Aux (A c (C.mulG (x : ZMod n)))) ([], []) (⟨0, [], []⟩, fun _ => e₀)
    ⟨List.nodup_nil, by simp, Nat.zero_le _⟩ ⟨le_rfl, by simp⟩
  have hkey : findKey C qs unmask (C.mulG (x : ZMod n)) o'.1
      ((List.finRange qs).map fun k => (k, Aux (ctr k))) = some x := by
    refine findKey_eq C qs unmask mask hunmask x _ _ k (Aux (ctr k))
      (List.mem_map.mpr ⟨k, List.mem_finRange k, rfl⟩) ?_
    obtain ⟨z, hz, hz1⟩ := List.mem_map.mp hk
    exact List.mem_map.mpr ⟨z, hlog z (Or.inr hz), hz1⟩
  set res := (answerG G (answerG Aux (A c (C.mulG (x : ZMod n))))).run
    (challengerE C nonceCoef N qs nv (x : ZMod n) T) (⟨0, [], []⟩, fun _ => e₀) with hres
  have hwin := forgeTail_wins C nonceCoef N qs msgs hmsgs hN x T (fun k => nv k (res.2.2 k)) o'.2
    res.1 res.2.1 (hinv.1.trans hcl.length_le) hinv.2
  have hF : (answerG G (answerG Aux (keyForger C N qs unmask msgs ctr A c
      (C.mulG (x : ZMod n))))).run (challengerE C nonceCoef N qs nv (x : ZMod n) T)
        (⟨0, [], []⟩, fun _ => e₀) =
      (liftQ (forgeTail C N qs msgs (x : ZMod n) o'.2 res.1) :
        Alg (AdvQ n N E X M ⊕ Ex) (SumR AdvR Unit) (Forgery n X M)).run
          (challengerE C nonceCoef N qs nv (x : ZMod n) T) res.2 := by
    unfold keyForger
    rw [answerG_bind, answerG_tally, answerG_bind, Alg.run_bind, hrun]
    dsimp only
    rw [answerG_bind, answerG_askList, Alg.done_bind, hkey]
    dsimp only
    rw [answerG_liftQ, answerG_liftQ]
  unfold winE
  dsimp only
  rw [hF, run_liftQ_challengerE]
  dsimp only
  rw [hwin.1]
  exact hwin.2

/-! ## The game with a counter -/

variable (ρ : W → ZMod n)

/-- **The unforgeability game with `NonceGen`, its `sk` argument and a counter
in place of `rand'`** on one sample: the `rand` of slot `k` is
`mask x k (Aux (ctr k))`. The counter values `ctr k` are public. The game is the
one of `Dahlias.NonceGenSk` with them in place of the uniform values
`rand'`. -/
def nonceGenCtrExperiment
    (ω : (Rest n N X M Coins × (Rnd × Ex × Bool → W)) × (Rp → Rnd)) : Prop :=
  winSk C nonceCoef N qs A ρ e₀ mask ω.1 ω.2 fun k => ω.2 (ctr k)

/-- Samples with the last two parts exchanged. -/
def swapLast {U V Z : Type} : (U × V) × Z ≃ (U × Z) × V where
  toFun p := ((p.1.1, p.2), p.1.2)
  invFun p := ((p.1.1, p.2), p.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Samples of the game with independent nonce values, with the table of the
aux hash in the coins. -/
def auxInCoins {U K T Z G V : Type} :
    ((U × K × T) × Z) × (G × V) ≃ ((U × (K × Z) × T) × G) × V where
  toFun p := (((p.1.1.1, (p.1.1.2.1, p.1.2), p.1.1.2.2), p.2.1), p.2.2)
  invFun p := (((p.1.1.1, p.1.1.2.1.1, p.1.1.2.2), p.1.1.2.1.2), (p.1.2, p.2))
  left_inv _ := rfl
  right_inv _ := rfl

variable [Fintype Coins] [Fintype (SigIn N X M)] [Fintype Rnd] [Nonempty Rnd] [Fintype Rp]
  [DecidableEq Rp] [Fintype Ex] [DecidableEq Ex] [Fintype W] [Nonempty W]

/-- The adversary's advantage in the game with a counter. -/
noncomputable def nonceGenCtrAdvantage : ℝ :=
  prob (nonceGenCtrExperiment C nonceCoef N qs ctr mask e₀ A ρ)

set_option synthInstance.maxSize 4000 in
/-- **`NonceGen` with a counter in place of `rand'`.** The counter values are
distinct, the secret key can be read off a `rand` and the value of the aux
hash (`unmask`), and there are `qs + 1` messages. Then an adversary wins the
game at most as often as it and the forger `keyForger A` together win the game
with uniform nonces, plus the terms for two equal values of the aux hash and
for the reduction modulo the group order.

The nonces are fresh values of the nonce hash unless the adversary queries it
at a `rand`, and a `rand` gives the secret key. -/
theorem nonceGenCtr_advantage (hctr : Injective ctr)
    (hunmask : ∀ x k a, unmask k (mask x k a) a = some x) (hmsgs : Injective msgs) (hN : 0 < N)
    (g : (ZMod n)ˣ → W) (hg : Injective g) (hρ : ∀ u, ρ (g u) = u) :
    nonceGenCtrAdvantage C nonceCoef N qs ctr mask e₀ A ρ ≤
      forgeAdvantage C nonceCoef N qs (withTable N (withAux N A)) +
        forgeAdvantage C nonceCoef N qs
          (withTable N (withAux N (keyForger C N qs unmask msgs ctr A))) +
        (qs : ℝ) ^ 2 / Fintype.card Rnd +
        2 * ((2 * qs : ℕ) * ((Fintype.card W - Fintype.card (ZMod n)ˣ : ℝ) / Fintype.card W)) := by
  classical
  have hRnd : (0 : ℝ) < Fintype.card Rnd := Nat.cast_pos.mpr Fintype.card_pos
  -- the game, with the table of the nonce hash last
  have h0 : nonceGenCtrAdvantage C nonceCoef N qs ctr mask e₀ A ρ =
      prob (fun s : (Rest n N X M Coins × (Rp → Rnd)) × (Rnd × Ex × Bool → W) =>
        winE C nonceCoef N qs (fun c P => answerG s.1.2 (A c P)) e₀ s.1.1 s.2
          (nvOf qs ρ fun i => s.2 (noncePt qs (fun k => mask s.1.1.1 k (s.1.2 (ctr k))) i))) := by
    unfold nonceGenCtrAdvantage
    rw [← prob_equiv swapLast (nonceGenCtrExperiment C nonceCoef N qs ctr mask e₀ A ρ)]
    rfl
  -- two slots have the same `rand`, or not
  have h1 := prob_le_add
    (p := fun s : (Rest n N X M Coins × (Rp → Rnd)) × (Rnd × Ex × Bool → W) =>
      winE C nonceCoef N qs (fun c P => answerG s.1.2 (A c P)) e₀ s.1.1 s.2
        (nvOf qs ρ fun i => s.2 (noncePt qs (fun k => mask s.1.1.1 k (s.1.2 (ctr k))) i)))
    (q := fun s => ¬Injective fun k => mask s.1.1.1 k (s.1.2 (ctr k)))
    (r := fun s => (Injective fun k => mask s.1.1.1 k (s.1.2 (ctr k))) ∧
      winE C nonceCoef N qs (fun c P => answerG s.1.2 (A c P)) e₀ s.1.1 s.2
        (nvOf qs ρ fun i => s.2 (noncePt qs (fun k => mask s.1.1.1 k (s.1.2 (ctr k))) i)))
    fun s hs => by
      by_cases h : Injective fun k => mask s.1.1.1 k (s.1.2 (ctr k))
      · exact Or.inr ⟨h, hs⟩
      · exact Or.inl h
  have h2 : prob (fun s : (Rest n N X M Coins × (Rp → Rnd)) × (Rnd × Ex × Bool → W) =>
      ¬Injective fun k => mask s.1.1.1 k (s.1.2 (ctr k))) ≤ (qs : ℝ) ^ 2 / Fintype.card Rnd := by
    rw [prob_fst (fun a : Rest n N X M Coins × (Rp → Rnd) =>
      ¬Injective fun k => mask a.1.1 k (a.2 (ctr k)))]
    refine prob_prod_le' _ _ (by positivity) fun θ => ?_
    -- the values of the aux hash at the counters are independent and uniform, and so are
    -- their images under the bijections of the slots
    have hm := prob_equiv (Equiv.piCongrRight fun k : Fin qs => mask θ.1 k)
      (fun u : Fin qs → Rnd => ¬Injective u)
    refine le_trans (le_of_eq ?_) (prob_not_injective (qs := qs) (R := Rnd))
    rw [← hm]
    exact prob_comp_injective ctr hctr (fun v : Fin qs → Rnd =>
      ¬Injective fun k => mask θ.1 k (v k))
  -- the nonces are fresh values of the nonce hash, unless it is queried at a `rand`
  have h3 : prob (fun s : (Rest n N X M Coins × (Rp → Rnd)) × (Rnd × Ex × Bool → W) =>
      (Injective fun k => mask s.1.1.1 k (s.1.2 (ctr k))) ∧
        winE C nonceCoef N qs (fun c P => answerG s.1.2 (A c P)) e₀ s.1.1 s.2
          (nvOf qs ρ fun i => s.2 (noncePt qs (fun k => mask s.1.1.1 k (s.1.2 (ctr k))) i))) ≤
      prob (fun s : (Rest n N X M Coins × (Rp → Rnd)) ×
          ((Rnd × Ex × Bool → W) × (Fin qs × Ex × Bool → W)) =>
        winE C nonceCoef N qs (fun c P => answerG s.1.2 (A c P)) e₀ s.1.1 s.2.1
            (nvOf qs ρ s.2.2) ∨
          ∃ k, mask s.1.1.1 k (s.1.2 (ctr k)) ∈
            (gLog s.2.1 (challengerE C nonceCoef N qs (nvOf qs ρ s.2.2) (s.1.1.1 : ZMod n)
              s.1.1.2.2) (answerG s.1.2 (A s.1.1.2.1 (C.mulG (s.1.1.1 : ZMod n))))
              (⟨0, [], []⟩, fun _ => e₀)).map Prod.fst) + 0 := by
    refine prob_prod_mono _ _ 0 le_rfl fun a => ?_
    rw [add_zero]
    by_cases hinj : Injective fun k => mask a.1.1 k (a.2 (ctr k))
    · refine le_trans (prob_mono fun G h => h.2) ?_
      refine (fresh_values_or_hit (noncePt qs fun k => mask a.1.1 k (a.2 (ctr k)))
        (noncePt_injective qs hinj) (fun z => ∃ k, z.1 = mask a.1.1 k (a.2 (ctr k)))
        (fun i => ⟨i.1, rfl⟩)
        (fun G v => winE C nonceCoef N qs (fun c P => answerG a.2 (A c P)) e₀ a.1 G (nvOf qs ρ v))
        (fun G v => gLog G (challengerE C nonceCoef N qs (nvOf qs ρ v) (a.1.1 : ZMod n) a.1.2.2)
          (answerG a.2 (A a.1.2.1 (C.mulG (a.1.1 : ZMod n)))) (⟨0, [], []⟩, fun _ => e₀))
        (fun G G' v h => by
          unfold winE
          dsimp only
          rw [answerG_congr G G' _ _ _ h])).trans (prob_mono ?_)
      rintro y (h | ⟨z, hz, k, hk⟩)
      · exact Or.inl h
      · exact Or.inr ⟨k, List.mem_map.mpr ⟨z, hz, hk⟩⟩
    · have h0 : prob (fun _ : Rnd × Ex × Bool → W => False) = 0 := by
        unfold prob
        simp
      refine le_trans (prob_mono (q := fun _ => False) ?_) (h0.le.trans (prob_nonneg _))
      intro G h
      exact hinj h.1
  rw [add_zero] at h3
  -- a query at a `rand` makes the forger win
  have h4 := prob_le_add
    (p := fun s : (Rest n N X M Coins × (Rp → Rnd)) ×
        ((Rnd × Ex × Bool → W) × (Fin qs × Ex × Bool → W)) =>
      winE C nonceCoef N qs (fun c P => answerG s.1.2 (A c P)) e₀ s.1.1 s.2.1 (nvOf qs ρ s.2.2) ∨
        ∃ k, mask s.1.1.1 k (s.1.2 (ctr k)) ∈
          (gLog s.2.1 (challengerE C nonceCoef N qs (nvOf qs ρ s.2.2) (s.1.1.1 : ZMod n)
            s.1.1.2.2) (answerG s.1.2 (A s.1.1.2.1 (C.mulG (s.1.1.1 : ZMod n))))
            (⟨0, [], []⟩, fun _ => e₀)).map Prod.fst)
    (q := fun s => winE C nonceCoef N qs (fun c P => answerG s.1.2 (A c P)) e₀ s.1.1 s.2.1
      (nvOf qs ρ s.2.2))
    (r := fun s => winE C nonceCoef N qs
      (fun c P => answerG s.1.2 (keyForger C N qs unmask msgs ctr A c P)) e₀ s.1.1 s.2.1
      (nvOf qs ρ s.2.2))
    fun s h => h.imp id fun hb =>
      winE_keyForger C nonceCoef N qs unmask msgs ctr mask e₀ A hunmask hmsgs hN s.1.1.1
        s.1.1.2.1 s.1.1.2.2 s.2.1 s.1.2 (nvOf qs ρ s.2.2) hb
  -- independent nonce values are as good as uniform nonzero nonces
  have h5 : ∀ B : SkAdversary n N E X M Rnd Rp Ex W Coins,
      prob (fun s : (Rest n N X M Coins × (Rp → Rnd)) ×
          ((Rnd × Ex × Bool → W) × (Fin qs × Ex × Bool → W)) =>
        winE C nonceCoef N qs (fun c P => answerG s.1.2 (B c P)) e₀ s.1.1 s.2.1
          (nvOf qs ρ s.2.2)) ≤
      forgeAdvantage C nonceCoef N qs (withTable N (withAux N B)) +
        (2 * qs : ℕ) * ((Fintype.card W - Fintype.card (ZMod n)ˣ : ℝ) / Fintype.card W) := by
    intro B
    have h := prob_winE_le C nonceCoef N qs (withAux N B) ρ e₀ g hg hρ
    rw [← prob_equiv auxInCoins (fun s : (Rest n N X M (Coins × (Rp → Rnd)) ×
      (Rnd × Ex × Bool → W)) × (Fin qs × Ex × Bool → W) =>
        winE C nonceCoef N qs (withAux N B) e₀ s.1.1 s.1.2 (nvOf qs ρ s.2))] at h
    exact h
  have h5A := h5 A
  have h5F := h5 (keyForger C N qs unmask msgs ctr A)
  rw [h0]
  linarith

/-! ## The queries of the forger -/

omit [Fintype (SigIn N X M)] in
theorem hashBound_forgeTail (x' : ZMod n) (tr : List (SignedQ n X M)) (fb : Forgery n X M) :
    HashBound (forgeTail C N qs msgs x' tr fb) 1 := by
  unfold forgeTail
  cases (List.finRange (qs + 1)).find? fun j =>
      decide ([(C.x (C.mulG x'), msgs j)] ∉ tr.map (signedList C x')) with
  | none => trivial
  | some j =>
    dsimp only
    split_ifs <;> first | exact ⟨Nat.one_pos, fun r => trivial⟩ | trivial

omit [Fintype Coins] [Fintype (SigIn N X M)] [Fintype Rnd] [Nonempty Rnd] [Fintype Rp]
  [DecidableEq Rp] [Fintype Ex] [DecidableEq Ex] [Fintype W] [Nonempty W] in
/-- The forger queries the aux hash `qs` times more than the adversary. -/
theorem nbound_keyForger (qa : ℕ) (hA : ∀ c P, NBound (A c P) qa) (c : Coins) (P : E) :
    NBound (keyForger C N qs unmask msgs ctr A c P) (qa + qs) := by
  unfold keyForger
  refine NBound.bind (nbound_tally _ _ _ _ (hA c P)) fun out => ?_
  refine (NBound.bind (b := 0) (nbound_askList _ _) fun as => ?_).mono (by simp)
  cases findKey C qs unmask P out.2.1 as with
  | none => trivial
  | some x' => exact nbound_liftQ _ _

omit [Fintype Coins] [Fintype (SigIn N X M)] [Fintype Rnd] [Nonempty Rnd] [Fintype Rp]
  [DecidableEq Rp] [Fintype Ex] [DecidableEq Ex] [Fintype W] [Nonempty W] in
/-- The forger queries the nonce hash as often as the adversary. -/
theorem nbound_answerG_keyForger (qn : ℕ)
    (hG : ∀ c P (Aux : Rp → Rnd), NBound (answerG Aux (A c P)) qn) (c : Coins) (P : E)
    (Aux : Rp → Rnd) : NBound (answerG Aux (keyForger C N qs unmask msgs ctr A c P)) qn := by
  unfold keyForger
  rw [answerG_bind, answerG_tally]
  refine (NBound.bind (b := 0) (nbound_tally _ _ _ _ (hG c P Aux)) fun out => ?_).mono (by simp)
  rw [answerG_bind, answerG_askList, Alg.done_bind]
  cases findKey C qs unmask P out.2.1 ((List.finRange qs).map fun k => (k, Aux (ctr k))) with
  | none => trivial
  | some x' =>
    dsimp only
    rw [answerG_liftQ]
    exact nbound_liftQ _ _

omit [Fintype Coins] [Fintype (SigIn N X M)] [Fintype Rnd] [Nonempty Rnd] [Fintype Rp]
  [DecidableEq Rp] [Fintype Ex] [DecidableEq Ex] [Fintype W] [Nonempty W] in
/-- The forger makes one hash query more than the adversary. -/
theorem hashBound_keyForger (qh : ℕ)
    (hH : ∀ c P G (Aux : Rp → Rnd),
      HashBound (answerG (fun _ : Ex => ()) (answerG G (answerG Aux (A c P)))) qh)
    (c : Coins) (P : E) (G : Rnd × Ex × Bool → W) (Aux : Rp → Rnd) :
    HashBound (answerG (fun _ : Ex => ()) (answerG G
      (answerG Aux (keyForger C N qs unmask msgs ctr A c P)))) (qh + 1) := by
  unfold keyForger
  rw [answerG_bind, answerG_tally, answerG_bind, answerG_bind]
  refine hashBound_bind _ _ qh 1 ?_ fun out => ?_
  · refine hashBound_of_map Prod.fst _ qh ?_
    have h := hH c P G Aux
    rw [← tally_fst (obsUpd N) (answerG Aux (A c P)) ([], []), answerG_bind, answerG_bind] at h
    exact h
  · rw [answerG_bind, answerG_askList, Alg.done_bind]
    cases findKey C qs unmask P out.2.1 ((List.finRange qs).map fun k => (k, Aux (ctr k))) with
    | none => trivial
    | some x' =>
      dsimp only
      rw [answerG_liftQ, answerG_liftQ, answerG_liftQ]
      exact hashBound_forgeTail C N qs msgs _ _ _

/-! ## The security theorems -/

/-- The bound of `unforgeable_sqrt_lazy_both` on the advantage of a forger
that makes at most `qh` hash queries: the term with `reductionLazy` and
`colliderLazy` and the two additive terms. -/
noncomputable def lazyBound {Coins' : Type} [Fintype Coins'] (qh : ℕ)
    (F : Adversary n N E X M Coins') : ℝ :=
  Real.sqrt ((qh + qs + 1 : ℕ) *
      (omdlAdvantage C (2 * qs + 1) (reductionLazy C nonceCoef N qs F (2 * (qh + qs) + 1)) +
        collisionAdvantageLazy C nonceCoef N qs F (2 * (qh + qs)))) +
    (qh + qs + 1 : ℕ) / n + qs / (n - 1 : ℝ)

omit [Nonempty Rnd] [Nonempty W] in
set_option synthInstance.maxSize 4000 in
/-- The forger with tables of the nonce hash and the aux hash in its coins
wins at most with the bound for the forger that samples them lazily. -/
theorem forgeAdvantage_sk_le_lazyBound [Inhabited W] [DecidableEq W] [Inhabited Rnd]
    (hN : N < n) (qh qn qa : ℕ) (hA : ∀ c P, NBound (A c P) qa)
    (hG : ∀ c P (Aux : Rp → Rnd), NBound (answerG Aux (A c P)) qn)
    (hH : ∀ c P G (Aux : Rp → Rnd),
      HashBound (answerG (fun _ : Ex => ()) (answerG G (answerG Aux (A c P)))) qh) :
    forgeAdvantage C nonceCoef N qs (withTable N (withAux N A)) ≤
      lazyBound C nonceCoef N qs qh (withStream N qn (withAuxStream N qa A)) := by
  have hS : ∀ c P, NBound (withAuxStream N qa A c P) qn :=
    fun c P => nbound_answerLazy _ _ qn fun Aux => hG c.1 P Aux
  rw [forgeAdvantage_withAux_eq_lazy C nonceCoef N qs A qa hA,
    forgeAdvantage_withTable_eq_lazy C nonceCoef N qs (withAuxStream N qa A) qn hS]
  exact unforgeable_sqrt_lazy_both C nonceCoef N qs
    (withStream N qn (withAuxStream N qa A)) hN qh
    fun c P => hashBound_answerLazy _ _ qh fun G =>
      hashBound_answerG_answerLazy G _ _ qh fun Aux => hH c.1.1 P G Aux

omit [Nonempty Rnd] [Nonempty W] in
set_option synthInstance.maxSize 4000 in
/-- **Unforgeability with `NonceGen`, its `sk` argument and a counter in place
of `rand'`**, in the game with scalar answers of the challenge hash. The bound
has the terms of `unforgeable_sqrt_lazy_both` twice: for the adversary and for
the forger that recovers the key when the adversary queries the nonce hash at
a `rand`. -/
theorem nonceGenCtr_unforgeable [Inhabited W] [DecidableEq W] [Inhabited Rnd]
    (hctr : Injective ctr) (hunmask : ∀ x k a, unmask k (mask x k a) a = some x)
    (hmsgs : Injective msgs) (hN0 : 0 < N) (g : (ZMod n)ˣ → W) (hg : Injective g)
    (hρ : ∀ u, ρ (g u) = u) (hN : N < n) (qh qn qa : ℕ) (hA : ∀ c P, NBound (A c P) qa)
    (hG : ∀ c P (Aux : Rp → Rnd), NBound (answerG Aux (A c P)) qn)
    (hH : ∀ c P G (Aux : Rp → Rnd),
      HashBound (answerG (fun _ : Ex => ()) (answerG G (answerG Aux (A c P)))) qh) :
    nonceGenCtrAdvantage C nonceCoef N qs ctr mask e₀ A ρ ≤
      lazyBound C nonceCoef N qs qh (withStream N qn (withAuxStream N qa A)) +
        lazyBound C nonceCoef N qs (qh + 1)
          (withStream N qn (withAuxStream N (qa + qs) (keyForger C N qs unmask msgs ctr A))) +
        (qs : ℝ) ^ 2 / Fintype.card Rnd +
        2 * ((2 * qs : ℕ) * ((Fintype.card W - Fintype.card (ZMod n)ˣ : ℝ) / Fintype.card W)) := by
  have h1 := nonceGenCtr_advantage C nonceCoef N qs unmask msgs ctr mask e₀ A ρ hctr hunmask hmsgs
    hN0 g hg hρ
  have h2 := forgeAdvantage_sk_le_lazyBound C nonceCoef N qs A hN qh qn qa hA hG hH
  have h3 := forgeAdvantage_sk_le_lazyBound C nonceCoef N qs
    (keyForger C N qs unmask msgs ctr A) hN (qh + 1) qn (qa + qs)
    (nbound_keyForger C N qs unmask msgs ctr A qa hA)
    (nbound_answerG_keyForger C N qs unmask msgs ctr A qn hG)
    (hashBound_keyForger C N qs unmask msgs ctr A qh hH)
  linarith

/-! ## With a challenge hash that returns hash outputs -/

variable {H : Type} (red : H → ZMod n) (AH : SkAdversaryH n N E X M Rnd Rp Ex W H Coins)

/-- **The unforgeability game with `NonceGen`, its `sk` argument, a counter in
place of `rand'` and hash outputs in `H`** on one sample. -/
def nonceGenCtrExperimentH
    (ω : (RestH n N X M H Coins × (Rnd × Ex × Bool → W)) × (Rp → Rnd)) : Prop :=
  nonceGenExperimentH C nonceCoef N qs red (fun c P => answerG ω.2 (AH c P)) ρ e₀
    ((ω.1.1, fun k => mask ω.1.1.1 k (ω.2 (ctr k))), ω.1.2)

variable [Fintype H] [DecidableEq H]

/-- The adversary's advantage in the game with a counter and hash outputs in
`H`. -/
noncomputable def nonceGenCtrAdvantageH : ℝ :=
  prob (nonceGenCtrExperimentH C nonceCoef N qs ctr mask e₀ ρ red AH)

omit [Nonempty Rnd] [Nonempty W] in
set_option synthInstance.maxSize 4000 in
/-- **A hash output reduced to a scalar costs `(|H| - n) / |H|` for every
value of the oracle that the game reads**, in the game with a counter. -/
theorem nonceGenCtrAdvantageH_le (g : ZMod n → H) (hg : ∀ c, red (g c) = c) (qh : ℕ)
    (hH : ∀ c P G (Aux : Rp → Rnd),
      HashBound (answerG (fun _ : Ex => ()) (answerG G (answerG Aux (AH c P)))) qh) :
    nonceGenCtrAdvantageH C nonceCoef N qs ctr mask e₀ ρ red AH ≤
      nonceGenCtrAdvantage C nonceCoef N qs ctr mask e₀ (liftHashSk N g AH) ρ +
        (qh + qs + N : ℕ) * ((Fintype.card H - n : ℝ) / Fintype.card H) := by
  unfold nonceGenCtrAdvantageH nonceGenCtrAdvantage
  rw [← prob_equiv (tabLastN (Tb := SigIn N X M → H))
      (nonceGenCtrExperimentH C nonceCoef N qs ctr mask e₀ ρ red AH),
    ← prob_equiv (tabLastN (Tb := SigIn N X M → ZMod n))
      (nonceGenCtrExperiment C nonceCoef N qs ctr mask e₀ (liftHashSk N g AH) ρ)]
  refine prob_prod_mono _ _ _ (hashGap_nonneg red g hg _) fun a => ?_
  have h := nonceGenExperimentH_le C nonceCoef N qs red e₀ g hg (fun c P => answerG a.2 (AH c P))
    ρ qh a.1.1.1 a.1.1.2 (fun k => mask a.1.1.1 k (a.2 (ctr k))) a.1.2 (hH _ _ _ _)
  have hl : liftHashN N g (fun c P => answerG a.2 (AH c P)) =
      fun c P => answerG a.2 (liftHashSk N g AH c P) := by
    funext c P
    exact (answerG_mapAns a.2 _ _).symm
  rw [hl] at h
  exact h

omit [Nonempty Rnd] [Nonempty W] in
set_option synthInstance.maxSize 4000 in
/-- **Unforgeability with `NonceGen`, its `sk` argument, a counter in place of
`rand'` and the challenge hash reduced to a scalar**, under AOMDL with
`hash_BIP0459/sig`, `hash_BIP0459/nonce` and `hash_BIP0459/aux` as random
oracles, all sampled lazily by the forgers, the reduction and the collision
finder. -/
theorem nonceGenCtr_unforgeable_hashed [Inhabited W] [DecidableEq W] [Inhabited Rnd]
    (hctr : Injective ctr) (hunmask : ∀ x k a, unmask k (mask x k a) a = some x)
    (hmsgs : Injective msgs) (hN0 : 0 < N) (g : ZMod n → H) (hg : ∀ c, red (g c) = c)
    (gW : (ZMod n)ˣ → W) (hgW : Injective gW) (hρ : ∀ u, ρ (gW u) = u) (hN : N < n)
    (qh qn qa : ℕ) (hA : ∀ c P, NBound (AH c P) qa)
    (hG : ∀ c P (Aux : Rp → Rnd), NBound (answerG Aux (AH c P)) qn)
    (hH : ∀ c P G (Aux : Rp → Rnd),
      HashBound (answerG (fun _ : Ex => ()) (answerG G (answerG Aux (AH c P)))) qh) :
    nonceGenCtrAdvantageH C nonceCoef N qs ctr mask e₀ ρ red AH ≤
      lazyBound C nonceCoef N qs qh (withStream N qn (withAuxStream N qa (liftHashSk N g AH))) +
        lazyBound C nonceCoef N qs (qh + 1)
          (withStream N qn (withAuxStream N (qa + qs)
            (keyForger C N qs unmask msgs ctr (liftHashSk N g AH)))) +
        (qh + qs + N : ℕ) * ((Fintype.card H - n : ℝ) / Fintype.card H) +
        (qs : ℝ) ^ 2 / Fintype.card Rnd +
        2 * ((2 * qs : ℕ) * ((Fintype.card W - Fintype.card (ZMod n)ˣ : ℝ) / Fintype.card W)) := by
  have hLA : ∀ c P, NBound (liftHashSk N g AH c P) qa := fun c P => nbound_mapAns _ _ _ (hA c P)
  have hLG : ∀ c P (Aux : Rp → Rnd), NBound (answerG Aux (liftHashSk N g AH c P)) qn := by
    intro c P Aux
    change NBound (answerG Aux (mapAns (sumAns (sumAns (sumAns (hashAns N g)))) (AH c P))) qn
    rw [answerG_mapAns]
    exact nbound_mapAns _ _ _ (hG c P Aux)
  have hLH : ∀ c P G (Aux : Rp → Rnd), HashBound (answerG (fun _ : Ex => ())
      (answerG G (answerG Aux (liftHashSk N g AH c P)))) qh := by
    intro c P G Aux
    change HashBound (answerG (fun _ : Ex => ()) (answerG G (answerG Aux
      (mapAns (sumAns (sumAns (sumAns (hashAns N g)))) (AH c P))))) qh
    rw [answerG_mapAns, answerG_mapAns, answerG_mapAns]
    exact hashBound_mapAns N g _ qh (hH _ _ _ _)
  have h1 := nonceGenCtrAdvantageH_le C nonceCoef N qs ctr mask e₀ ρ red AH g hg qh hH
  have h2 := nonceGenCtr_unforgeable C nonceCoef N qs unmask msgs ctr mask e₀
    (liftHashSk N g AH) ρ hctr hunmask hmsgs hN0 gW hgW hρ hN qh qn qa hLA hLG hLH
  linarith

omit [Fintype H] [DecidableEq H] [Nonempty Rnd] [Nonempty W] [Fintype W] in
set_option synthInstance.maxSize 4000 in
/-- **BIP 459's `NonceGen` with its `sk` argument, a counter in place of
`rand'`, and the challenge hash**: `m`-valued random oracles reduced modulo
`n`, for `m = 2²⁵⁶`. -/
theorem nonceGenCtr_unforgeable_fin [Inhabited Rnd] {m : ℕ} [NeZero m] (hm : n ≤ m)
    (AH : SkAdversaryH n N E X M Rnd Rp Ex (Fin m) (Fin m) Coins) (hctr : Injective ctr)
    (hunmask : ∀ x k a, unmask k (mask x k a) a = some x) (hmsgs : Injective msgs) (hN0 : 0 < N)
    (hN : N < n) (qh qn qa : ℕ) (hA : ∀ c P, NBound (AH c P) qa)
    (hG : ∀ c P (Aux : Rp → Rnd), NBound (answerG Aux (AH c P)) qn)
    (hH : ∀ c P G (Aux : Rp → Rnd),
      HashBound (answerG (fun _ : Ex => ()) (answerG G (answerG Aux (AH c P)))) qh) :
    nonceGenCtrAdvantageH C nonceCoef N qs ctr mask e₀ (redFin m) (redFin m) AH ≤
      lazyBound C nonceCoef N qs qh
          (withStream N qn (withAuxStream N qa (liftHashSk N (liftFin hm) AH))) +
        lazyBound C nonceCoef N qs (qh + 1)
          (withStream N qn (withAuxStream N (qa + qs)
            (keyForger C N qs unmask msgs ctr (liftHashSk N (liftFin hm) AH)))) +
        (qh + qs + N : ℕ) * ((m - n : ℝ) / m) +
        (qs : ℝ) ^ 2 / Fintype.card Rnd +
        2 * ((2 * qs : ℕ) * ((m - (n - 1) : ℝ) / m)) := by
  have hn : 0 < n := (Fact.out : n.Prime).pos
  have h := nonceGenCtr_unforgeable_hashed C nonceCoef N qs unmask msgs ctr mask e₀ (redFin m)
    (redFin m) AH hctr hunmask hmsgs hN0 (liftFin hm) (fun c => ZMod.natCast_zmod_val c)
    (fun u => ⟨(u : ZMod n).val, lt_of_lt_of_le (ZMod.val_lt _) hm⟩)
    (fun u u' h => Units.ext (ZMod.val_injective n (Fin.mk.inj h)))
    (fun u => ZMod.natCast_zmod_val _) hN qh qn qa hA hG hH
  rw [ZMod.card_units_eq_totient, Nat.totient_prime Fact.out, Fintype.card_fin,
    Nat.cast_sub hn, Nat.cast_one] at h
  exact h

end Dahlias.Security
