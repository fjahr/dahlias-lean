import Dahlias.Encoding

/-!
# The games with the byte arrays of BIP 459 as the adversary's interface

In the games of `Dahlias.BytesSecurity` the adversary sends parsed values: a
signing query has the nonces as points, and a forgery has the signature as a
32-byte array and a scalar. Here the adversary sends and gets byte arrays.

* `AdvQB`: a signing query has the message, the aggregate nonce, the public
  keys, the messages and the public nonces as byte arrays of any length. The
  answers are the 66-byte public nonce and the 32-byte partial signature.
* `challengerB`: the signer closes a session with `Sign` on bytes
  (`Bytes.signWith`), with the challenge hash answered from the table.
* `WinsB`: a forgery has the public keys, the messages and the signature in
  bytes, and it wins if `Verify` on bytes (`Bytes.verifyWith`) accepts it.
* `run_trB`: a query in bytes is answered as its parsed query is answered in
  the game on parsed values. `wins_of_winsB`: a forgery that wins in bytes
  wins on parsed values.
* `bytesGame_unforgeable_256`, `bytesGame_nonceGen_unforgeable_256`,
  `bytesGame_nonceGenSk_unforgeable_256` and
  `bytesGame_nonceGenCtr_unforgeable_256` are the security theorems of
  `Dahlias.BytesSecurity` for these games. The bound is the one for the
  adversary that parses (`toStruct`, `toStructN`, `toStructSk`).

Three things are not byte arrays. The tweak of the signer's key in a signing
query and in a forgery is a pair of scalars: `Sign` gets the tweaked key from
its caller and has no tweak argument. A hash query is a tuple of 32-byte
arrays, which `sigInput_injective` ties to the bytes that BIP 459 hashes. And
a single-party signature has no algorithm on bytes in BIP 459, so that query
has 32-byte messages and returns the game's signature, serialized.
-/

set_option linter.unusedSectionVars false

namespace Dahlias.Security

open Taproot Taproot.Secp256k1 Taproot.BIP340Vectors Dahlias.Bytes Function QTree

/-! ## Translating the queries of an algorithm -/

section Transl

variable {Q Q' : Type} {R : Q → Type} {R' : Q' → Type} {D W α σ : Type}

/-- The algorithm that runs `f q` in place of every query `q`. -/
def transl (f : (q : Q) → Alg Q' R' (R q)) : Alg Q R α → Alg Q' R' α
  | .done a => .done a
  | .ask q k => f q >>= fun r => transl f (k r)

/-- If running `f q` with the handler `h` is answering `q` with `h'`, the
translated algorithm runs with `h` as the algorithm runs with `h'`. -/
theorem run_transl (f : (q : Q) → Alg Q' R' (R q)) (h : (q : Q') → σ → R' q × σ)
    (h' : (q : Q) → σ → R q × σ) (hh : ∀ q s, (f q).run h s = h' q s) (t : Alg Q R α) (s : σ) :
    (transl f t).run h s = t.run h' s := by
  induction t generalizing s with
  | done a => rfl
  | ask q k ih =>
    change (f q >>= fun r => transl f (k r)).run h s = _
    rw [Alg.run_bind, hh, Alg.run_ask]
    exact ih _ _

/-- The translation of the game's queries, with the queries of the table
passed on. -/
def sumTr (f : (q : Q) → Alg Q' R' (R q)) :
    (q : Q ⊕ D) → Alg (Q' ⊕ D) (SumR R' W) (SumR R W q)
  | .inl q => liftQ (f q)
  | .inr d => .ask (.inr d) .done

theorem answerG_transl (G : D → W) (f : (q : Q) → Alg Q' R' (R q))
    (t : Alg (Q ⊕ D) (SumR R W) α) :
    answerG G (transl (sumTr f) t) = transl f (answerG G t) := by
  induction t with
  | done a => rfl
  | ask x k ih =>
    cases x with
    | inl q =>
      change answerG G (liftQ (f q) >>= fun r => transl (sumTr f) (k r)) =
        (f q >>= fun r => transl f (answerG G (k r)))
      rw [answerG_bind, answerG_liftQ]
      congr 1
      funext r
      exact ih r
    | inr d => exact ih _

theorem nbound_transl (f : (q : Q) → Alg Q' R' (R q)) (t : Alg (Q ⊕ D) (SumR R W) α) (q : ℕ)
    (h : NBound t q) : NBound (transl (sumTr f) t) q := by
  induction t generalizing q with
  | done a => trivial
  | ask x k ih =>
    cases x with
    | inl y =>
      change NBound (liftQ (f y) >>= fun r => transl (sumTr f) (k r)) q
      exact (NBound.bind (nbound_liftQ (f y) 0) fun r => ih r _ (h r)).mono (by omega)
    | inr d => exact ⟨h.1, fun r => ih r _ (h.2 r)⟩

end Transl

/-! ## Byte arrays as 32-byte arrays -/

/-- A byte array as a 32-byte array: itself if it has 32 bytes. -/
def to32 (b : Bytes) : B32 := if h : b.length = 32 then ⟨b, h⟩ else default

theorem to32_of_length {b : Bytes} (h : b.length = 32) : to32 b = ⟨b, h⟩ := by
  simp only [to32, h, ↓reduceDIte]

@[simp] theorem to32_val (b : B32) : to32 b.1 = b := to32_of_length b.2

/-- Lists of public keys and messages as a list of pairs of 32-byte arrays. -/
def pairs32 (pks msgs : List Bytes) : List (B32 × B32) :=
  (pks.zip msgs).map fun e => (to32 e.1, to32 e.2)

theorem length_pairs32 {pks msgs : List Bytes} (h : pks.length = msgs.length) :
    (pairs32 pks msgs).length = pks.length := by
  simp [pairs32, h]

theorem map_fst_pairs32 : ∀ {pks msgs : List Bytes}, pks.length = msgs.length →
    pks.all is32 = true → (pairs32 pks msgs).map (fun e => e.1.1) = pks
  | [], [], _, _ => rfl
  | a :: pks, b :: msgs, hl, hp => by
    rw [List.all_cons, Bool.and_eq_true] at hp
    have ha : a.length = 32 := by simpa [is32] using hp.1
    have := map_fst_pairs32 (pks := pks) (msgs := msgs) (by simpa using hl) hp.2
    simp only [pairs32, List.zip_cons_cons, List.map_cons, to32_of_length ha] at this ⊢
    rw [this]
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

theorem map_snd_pairs32 : ∀ {pks msgs : List Bytes}, pks.length = msgs.length →
    msgs.all is32 = true → (pairs32 pks msgs).map (fun e => e.2.1) = msgs
  | [], [], _, _ => rfl
  | a :: pks, b :: msgs, hl, hm => by
    rw [List.all_cons, Bool.and_eq_true] at hm
    have hb : b.length = 32 := by simpa [is32] using hm.1
    have := map_snd_pairs32 (pks := pks) (msgs := msgs) (by simpa using hl) hm.2
    simp only [pairs32, List.zip_cons_cons, List.map_cons, to32_of_length hb] at this ⊢
    rw [this]
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

theorem map_to32_vals (L : List (B32 × B32)) :
    (vals L).map (fun e => (to32 e.1, to32 e.2)) = L := by
  unfold vals
  rw [List.map_map]
  conv_rhs => rw [← List.map_id L]
  exact List.map_congr_left fun e _ => by simp

/-- A scalar that parses from a byte array serializes to it. -/
theorem serScalar_of_scalar {b : Bytes} {s : ZMod n} (h : scalar b = some s) :
    serScalar s = b := by
  unfold scalar at h
  split_ifs at h with hb
  cases Option.some.inj h
  unfold serScalar
  rw [ZMod.val_natCast_of_lt hb.2]
  exact bytes32_toNatBE hb.1

/-! ## The hash functions on bytes for a table of hash outputs -/

variable {H : Type} (N qs : ℕ) (red : H → ZMod n)

/-- The hash functions on byte arrays for the table `Tab` of hash outputs: the
nonce coefficient hash of BIP 459, and for 32-byte public keys, messages and
`r` the reduced table value as the challenge hash. `Sign` and `Verify` hash
no other arrays. -/
def hashesB (Tab : SigIn N B32 B32 → H) : Hashes n Point Bytes Bytes where
  nonceCoef := Bytes.hashes.nonceCoef
  sig pm r pkm := (hashesOf N nonceCoef32 fun z => red (Tab z)).sig
    (pm.map fun e => (to32 e.1, to32 e.2)) (to32 r) (to32 pkm.1, to32 pkm.2)

theorem agree_hashesB (Tab : SigIn N B32 B32 → H) :
    Agree (hashesOf N nonceCoef32 fun z => red (Tab z)) (hashesB N red Tab) := by
  refine ⟨fun R₁ R₂ items => rfl, fun L r e => ?_⟩
  simp only [hashesB, map_to32_vals, to32_val]

/-! ## The queries and answers in bytes -/

/-- **The adversary's queries with byte arrays.** A signing query has the
arguments of `Sign` that the other parties choose: the message, the aggregate
nonce, the public keys, the messages and the public nonces, as byte arrays of
any length. The tweak of the signer's key stays a pair of scalars, and a hash
query has 32-byte arrays. -/
inductive AdvQB (N : ℕ) where
  /-- A random oracle query. -/
  | hash (z : SigIn N B32 B32)
  /-- Open a signing session. -/
  | openSession
  /-- Close session `k`: the honest signer's `Sign` with the tweak `τ`. -/
  | close (k : ℕ) (τ : Tweak n) (m aggnonce : Bytes) (pks msgs pubnonces : List Bytes)
  /-- Sign alone for a list of the honest signer's own tweaked keys and
  messages, with one nonce. -/
  | single (items : List (Tweak n × Bytes))

/-- The answers in bytes: a hash output, the 66-byte public nonce, the 32-byte
partial signature, the 64-byte signature. -/
def AdvRB (H : Type) {N : ℕ} : AdvQB N → Type
  | .hash _ => H
  | .openSession => Option Bytes
  | .close .. => Option Bytes
  | .single _ => Option Bytes

/-- A forgery in bytes: the public keys, the messages, the tweak of the honest
signer's key and the 64-byte signature. -/
structure ForgeryB where
  pks : List Bytes
  msgs : List Bytes
  τ : Tweak n
  sig : Bytes

/-- The forgery on parsed values. -/
def toForgery (f : ForgeryB) : Forgery n B32 B32 :=
  ⟨pairs32 f.pks f.msgs, f.τ, (to32 (f.sig.take 32), (scalar (f.sig.drop 32)).getD 0)⟩

/-- A byte query as a query of the game on parsed values. A signing query
whose public keys and messages are not 32-byte arrays of the same number is
answered with a failure, as `Sign` answers it. -/
def trB {N : ℕ} : (q : AdvQB N) → Alg (AdvQ n N Point B32 B32) (AdvRH H) (AdvRB H q)
  | .hash z => .ask (.hash z) fun c => .done c
  | .openSession => .ask .openSession fun r => .done (r.map serNonce)
  | .close k τ m aggnonce pks msgs pubnonces =>
    if pks.length = msgs.length ∧ pks.all is32 = true ∧ msgs.all is32 = true ∧ is32 m = true then
      .ask (.close k τ (to32 m) (parseNonce specOps aggnonce) (pairs32 pks msgs)
        (pubnonces.map (parseNonce specOps))) fun r => .done (r.map serScalar)
    else .done none
  | .single items =>
    if items.all (fun i => is32 i.2) = true then
      .ask (.single (items.map fun i => (i.1, to32 i.2))) fun r =>
        .done (r.map fun s => s.1.1 ++ serScalar s.2)
    else .done none

/-- **The game's answers to the queries in bytes**, for the table `Tab` of
hash outputs. A session is closed with `Sign` on bytes (`Bytes.signWith`),
with the challenge hash answered from the table. The public nonce of a new
session and a single-party signature are the game's, serialized. -/
def challengerB (x : ZMod n) (nonces : Fin qs → SecNonce n) (Tab : SigIn N B32 B32 → H) :
    (q : AdvQB N) → SignerState B32 B32 → AdvRB H q × SignerState B32 B32
  | .hash z, st => (Tab z, st)
  | .openSession, st =>
    (((challenger secp256k1X nonceCoef32 N qs x nonces (fun z => red (Tab z))
        .openSession st).1).map serNonce,
      (challenger secp256k1X nonceCoef32 N qs x nonces (fun z => red (Tab z)) .openSession st).2)
  | .close k τ m aggnonce pks msgs pubnonces, st =>
    if h : k < qs ∧ k < st.opened ∧ k ∉ st.closed ∧ τ.2 ≠ 0 ∧ pks.length ≤ N then
      match Bytes.signWith specOps (hashesB N red Tab)
          (serScalar (nonces ⟨k, h.1⟩).1 ++ serScalar (nonces ⟨k, h.1⟩).2) (serScalar (τ.sk x))
          m aggnonce pks msgs pubnonces with
      | some psig =>
        (some psig, { st with closed := k :: st.closed
                              signed := (pairs32 pks msgs,
                                secp256k1X.x (secp256k1X.mulG (τ.sk x)), to32 m) :: st.signed })
      | none => (none, st)
    else (none, st)
  | .single items, st =>
    if items.all (fun i => is32 i.2) = true then
      (((challenger secp256k1X nonceCoef32 N qs x nonces (fun z => red (Tab z))
          (.single (items.map fun i => (i.1, to32 i.2))) st).1).map fun s =>
            s.1.1 ++ serScalar s.2,
        (challenger secp256k1X nonceCoef32 N qs x nonces (fun z => red (Tab z))
          (.single (items.map fun i => (i.1, to32 i.2))) st).2)
    else (none, st)

/-- `Sign` on bytes fails unless the public keys and messages are 32-byte
arrays of the same number and the message has 32 bytes. -/
theorem signWith_eq_none (Hb : Hashes n Point Bytes Bytes) (secnonce sk m aggnonce : Bytes)
    (pks msgs pubnonces : List Bytes)
    (h : ¬(pks.length = msgs.length ∧ pks.all is32 = true ∧ msgs.all is32 = true ∧
      is32 m = true)) :
    Bytes.signWith specOps Hb secnonce sk m aggnonce pks msgs pubnonces = none := by
  unfold Bytes.signWith
  have hw : (wellFormed pks msgs pubnonces.length && is32 m && secnonce.length == 64) = false := by
    by_contra hc
    rw [Bool.not_eq_false, Bool.and_eq_true, Bool.and_eq_true] at hc
    obtain ⟨⟨hwf, hm⟩, -⟩ := hc
    simp only [wellFormed, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hwf
    exact h ⟨hwf.1.1.1.2.trans hwf.1.1.2.symm, hwf.1.2, hwf.2, hm⟩
  simp only [hw, Bool.false_eq_true, ↓reduceIte]

/-- **A query in bytes is answered as its parsed query is answered** by the
game on parsed values. -/
theorem run_trB (x : ZMod n) (nonces : Fin qs → SecNonce n) (Tab : SigIn N B32 B32 → H)
    (q : AdvQB N) (st : SignerState B32 B32) :
    (trB q).run (challengerH secp256k1X nonceCoef32 N qs red x nonces Tab) st =
      challengerB N qs red x nonces Tab q st := by
  cases q with
  | hash z => rfl
  | openSession => rfl
  | single items =>
    dsimp only [trB, challengerB]
    split_ifs <;> rfl
  | close k τ m aggnonce pks msgs pubnonces =>
    by_cases hwf : pks.length = msgs.length ∧ pks.all is32 = true ∧ msgs.all is32 = true ∧
        is32 m = true
    · have hm : (to32 m).1 = m := by
        rw [to32_of_length (by simpa [is32] using hwf.2.2.2)]
      have hsign : ∀ r₁ r₂ : ZMod n,
          Bytes.signWith specOps (hashesB N red Tab) (serScalar r₁ ++ serScalar r₂)
              (serScalar (τ.sk x)) m aggnonce pks msgs pubnonces =
            (sign secp256k1X.ops (hashesOf N nonceCoef32 fun z => red (Tab z)) (r₁, r₂) (τ.sk x)
              (to32 m) (parseNonce specOps aggnonce) (pairs32 pks msgs)
              (pubnonces.map (parseNonce specOps))).map serScalar := by
        intro r₁ r₂
        have := signWith_bytes (agree_hashesB N red Tab) r₁ r₂ (τ.sk x) (to32 m) aggnonce
          (pairs32 pks msgs) pubnonces
        rwa [hm, map_fst_pairs32 hwf.1 hwf.2.1, map_snd_pairs32 hwf.1 hwf.2.2.1] at this
      have hlen := length_pairs32 hwf.1
      unfold trB challengerB
      simp only [hwf, and_self, ↓reduceIte, Alg.run_ask, challengerH, challenger, challengerG,
        hlen, hsign]
      split_ifs with h
      · cases sign secp256k1X.ops (hashesOf N nonceCoef32 fun z => red (Tab z))
          (nonces ⟨k, h.1⟩) (τ.sk x) (to32 m) (parseNonce specOps aggnonce) (pairs32 pks msgs)
          (pubnonces.map (parseNonce specOps)) <;> rfl
      · rfl
    · unfold trB challengerB
      simp only [hwf, ↓reduceIte, signWith_eq_none _ _ _ _ _ _ _ _ hwf]
      split_ifs <;> rfl

/-! ## The winning condition in bytes -/

/-- **The winning condition on a forgery in bytes**: `Verify` on bytes
(`Bytes.verifyWith`) accepts, with the challenge hash answered from the
table, and the list has the honest signer's tweaked key with a message that
the signer did not sign in that list. -/
def WinsB (x : ZMod n) (Tab : SigIn N B32 B32 → H) (f : ForgeryB) (st : SignerState B32 B32) :
    Prop :=
  f.τ.2 ≠ 0 ∧ f.τ.sk x ≠ 0 ∧ f.pks.length ≤ N ∧
    (∃ m, (secp256k1X.x (secp256k1X.mulG (f.τ.sk x)), m) ∈ pairs32 f.pks f.msgs ∧
      (pairs32 f.pks f.msgs, secp256k1X.x (secp256k1X.mulG (f.τ.sk x)), m) ∉ st.signed) ∧
    Bytes.verifyWith specOps (hashesB N red Tab) f.pks f.msgs f.sig = true

/-- **A forgery that wins in bytes wins on parsed values.** -/
theorem wins_of_winsB (x : ZMod n) (Tab : SigIn N B32 B32 → H) (f : ForgeryB)
    (st : SignerState B32 B32) (h : WinsB N red x Tab f st) :
    Wins secp256k1X nonceCoef32 N x (fun z => red (Tab z)) (toForgery f) st := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  unfold Bytes.verifyWith at h5
  rw [Bool.and_eq_true, Bool.and_eq_true] at h5
  obtain ⟨⟨hwf, hlen⟩, hv⟩ := h5
  simp only [wellFormed, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hwf
  have hl : f.pks.length = f.msgs.length := hwf.1.1.2.symm
  have hlen : f.sig.length = 64 := by simpa using hlen
  cases hs : scalar (f.sig.drop 32) with
  | none => simp [hs] at hv
  | some s =>
    rw [hs] at hv
    have htake : (f.sig.take 32).length = 32 := by simp [hlen]
    have hsig : (to32 (f.sig.take 32)).1 ++ serScalar s = f.sig := by
      rw [to32_of_length htake, serScalar_of_scalar hs]
      exact List.take_append_drop 32 f.sig
    have hver := verifyWith_bytes (agree_hashesB N red Tab) (pairs32 f.pks f.msgs)
      (to32 (f.sig.take 32)) s
    rw [map_fst_pairs32 hl hwf.1.2, map_snd_pairs32 hl hwf.2, hsig] at hver
    refine ⟨h1, h2, ?_, h4, ?_⟩
    · change (pairs32 f.pks f.msgs).length ≤ N
      rw [length_pairs32 hl]
      exact h3
    · change verify secp256k1X.ops (hashesOf N nonceCoef32 fun z => red (Tab z))
        (pairs32 f.pks f.msgs) (to32 (f.sig.take 32), (scalar (f.sig.drop 32)).getD 0) = true
      rw [hs, Option.getD_some, ← hver]
      unfold Bytes.verifyWith
      simp only [wellFormed, hwf, hlen, hs, hv, Bool.and_self, decide_true, beq_self_eq_true]

/-! ## Bounds on the hash queries -/

/-- The cost of a query in bytes in random oracle queries. -/
def hashCostB {N : ℕ} : AdvQB N → ℕ
  | .hash _ => 1
  | .single items => items.length
  | _ => 0

/-- At most `qh` random oracle queries, whatever the answers: `HashBound` for
the queries in bytes. -/
def HashBoundB {N : ℕ} {α : Type} : Alg (AdvQB N) (AdvRB H) α → ℕ → Prop
  | .done _, _ => True
  | .ask q f, qh => hashCostB q ≤ qh ∧ ∀ r, HashBoundB (f r) (qh - hashCostB q)

theorem hashBound_trB (q : AdvQB N) : HashBound (trB (H := H) q) (hashCostB q) := by
  cases q with
  | hash z => exact ⟨Nat.one_pos, fun r => trivial⟩
  | openSession => exact fun r => trivial
  | close k τ m aggnonce pks msgs pubnonces =>
    dsimp only [trB]
    split_ifs
    · exact fun r => trivial
    · trivial
  | single items =>
    dsimp only [trB]
    split_ifs
    · exact ⟨by simp [hashCostB], fun r => trivial⟩
    · trivial

theorem hashBound_transl {α : Type} (t : Alg (AdvQB N) (AdvRB H) α) (qh : ℕ)
    (h : HashBoundB t qh) : HashBound (transl trB t) qh := by
  induction t generalizing qh with
  | done a => trivial
  | ask q k ih =>
    obtain ⟨hc, hk⟩ := h
    change HashBound (trB q >>= fun r => transl trB (k r)) qh
    exact hashBound_mono _ _ _
      (hashBound_bind _ _ _ _ (hashBound_trB N q) fun r => ih r _ (hk r)) (by omega)

/-! ## The game with uniform nonces -/

variable {Coins : Type}

/-- An adversary with the byte interface. -/
abbrev AdversaryB (N : ℕ) (H Coins : Type) := Coins → Point → Alg (AdvQB N) (AdvRB H) ForgeryB

/-- **The unforgeability game with the byte interface** on one sample, with
hash outputs in `H`. -/
def forgeExperimentB (A : AdversaryB N H Coins) (ω : ForgeSampleH n N qs B32 B32 H Coins) :
    Prop :=
  let x : ZMod n := ω.1
  let nonces : Fin qs → SecNonce n := fun k => ((ω.2.1 k).1, (ω.2.1 k).2)
  let Tab := ω.2.2.2
  let out := (A ω.2.2.1 (secp256k1X.mulG x)).run (challengerB N qs red x nonces Tab) ⟨0, [], []⟩
  WinsB N red x Tab out.1 out.2

/-- The adversary on parsed values: it parses the queries of `A` and its
forgery. -/
def toStruct (A : AdversaryB N H Coins) : AdversaryH n N Point B32 B32 H Coins :=
  fun c P => transl trB (A c P) >>= fun f => .done (toForgery f)

/-- When `A` wins with the byte interface, `toStruct N A` wins on parsed values,
on the same sample. -/
theorem forgeExperimentB_imp (A : AdversaryB N H Coins) (ω : ForgeSampleH n N qs B32 B32 H Coins)
    (h : forgeExperimentB N qs red A ω) :
    forgeExperimentH secp256k1X nonceCoef32 N qs red (toStruct N A) ω := by
  unfold forgeExperimentH toStruct
  dsimp only
  rw [Alg.run_bind, run_transl trB _ _ (run_trB N qs red _ _ _)]
  exact wins_of_winsB N red _ _ _ _ h

theorem hashBound_toStruct (A : AdversaryB N H Coins) (qh : ℕ)
    (hA : ∀ c P, HashBoundB (A c P) qh) (c : Coins) (P : Point) :
    HashBound (toStruct N A c P) qh := by
  have := hashBound_bind _ (fun f => (.done (toForgery f) :
    Alg (AdvQ n N Point B32 B32) (AdvRH H) (Forgery n B32 B32))) qh 0
    (hashBound_transl N _ qh (hA c P)) fun r => trivial
  exact this

/-! ## The games with `NonceGen` -/

variable {Rnd Rp Ex W : Type}

/-- The game's answers in bytes when the nonces of a slot depend on its
`extra_in`: `challengerEH` with the byte interface. -/
def challengerEB (nv : Fin qs → Ex → SecNonce n) (x : ZMod n) (Tab : SigIn N B32 B32 → H) :
    (q : AdvQB N ⊕ Ex) → SignerState B32 B32 × (ℕ → Ex) →
      SumR (AdvRB H) Unit q × (SignerState B32 B32 × (ℕ → Ex))
  | .inl q, s =>
    ((challengerB N qs red x (fun k => nv k (s.2 k)) Tab q s.1).1,
      ((challengerB N qs red x (fun k => nv k (s.2 k)) Tab q s.1).2, s.2))
  | .inr e, s => ((), (s.1, update s.2 s.1.opened e))

/-- An adversary of the game with `NonceGen`, with the byte interface. -/
abbrev NAdversaryB (N : ℕ) (Rnd Ex W H Coins : Type) :=
  Coins → Point → Alg ((AdvQB N ⊕ Ex) ⊕ (Rnd × Ex × Bool)) (SumR (SumR (AdvRB H) Unit) W) ForgeryB

/-- An adversary of the game with `NonceGen` and its `sk` argument, with the
byte interface. -/
abbrev SkAdversaryB (N : ℕ) (Rnd Rp Ex W H Coins : Type) :=
  Coins → Point → Alg (((AdvQB N ⊕ Ex) ⊕ (Rnd × Ex × Bool)) ⊕ Rp)
    (SumR (SumR (SumR (AdvRB H) Unit) W) Rnd) ForgeryB

/-- **The unforgeability game with `NonceGen`, hash outputs in `H` and the
byte interface** on one sample: `nonceGenExperimentH` with `Sign` and `Verify`
on bytes. -/
def nonceGenExperimentB (A : NAdversaryB N Rnd Ex W H Coins) (ρ : W → ZMod n) (e₀ : Ex)
    (ω : (RestH n N B32 B32 H Coins × (Fin qs → Rnd)) × (Rnd × Ex × Bool → W)) : Prop :=
  let x : ZMod n := ω.1.1.1
  let Tab := ω.1.1.2.2
  let out := (answerG ω.2 (A ω.1.1.2.1 (secp256k1X.mulG x))).run
    (challengerEB N qs red (nvOf qs ρ fun i => ω.2 (noncePt qs ω.1.2 i)) x Tab)
    (⟨0, [], []⟩, fun _ => e₀)
  WinsB N red x Tab out.1 out.2.1

/-- **The game with `NonceGen`, its `sk` argument and the byte interface** on
one sample: the `rand` of slot `k` is `mask x k (Aux (rand' k))`. -/
def nonceGenSkExperimentB (A : SkAdversaryB N Rnd Rp Ex W H Coins) (ρ : W → ZMod n) (e₀ : Ex)
    (mask : (ZMod n)ˣ → Fin qs → Rnd ≃ Rnd)
    (ω : ((RestH n N B32 B32 H Coins × (Rnd × Ex × Bool → W)) × (Fin qs → Rp)) × (Rp → Rnd)) :
    Prop :=
  nonceGenExperimentB N qs red (fun c P => answerG ω.2 (A c P)) ρ e₀
    ((ω.1.1.1, fun k => mask ω.1.1.1.1 k (ω.2 (ω.1.2 k))), ω.1.1.2)

/-- **The game with `NonceGen`, its `sk` argument, a counter in place of
`rand'` and the byte interface** on one sample: the `rand` of slot `k` is
`mask x k (Aux (ctr k))`. -/
def nonceGenCtrExperimentB (A : SkAdversaryB N Rnd Rp Ex W H Coins) (ρ : W → ZMod n) (e₀ : Ex)
    (mask : (ZMod n)ˣ → Fin qs → Rnd ≃ Rnd) (ctr : Fin qs → Rp)
    (ω : (RestH n N B32 B32 H Coins × (Rnd × Ex × Bool → W)) × (Rp → Rnd)) : Prop :=
  nonceGenExperimentB N qs red (fun c P => answerG ω.2 (A c P)) ρ e₀
    ((ω.1.1, fun k => mask ω.1.1.1 k (ω.2 (ctr k))), ω.1.2)

/-- The adversary of the game with `NonceGen` on parsed values. -/
def toStructN (A : NAdversaryB N Rnd Ex W H Coins) :
    NAdversaryH n N Point B32 B32 Rnd Ex W H Coins :=
  fun c P => transl (sumTr (sumTr trB)) (A c P) >>= fun f => .done (toForgery f)

/-- The adversary of the game with `NonceGen` and its `sk` argument on parsed
values. -/
def toStructSk (A : SkAdversaryB N Rnd Rp Ex W H Coins) :
    SkAdversaryH n N Point B32 B32 Rnd Rp Ex W H Coins :=
  fun c P => transl (sumTr (sumTr (sumTr trB))) (A c P) >>= fun f => .done (toForgery f)

theorem run_liftQ_challengerEH {α : Type} (nv : Fin qs → Ex → SecNonce n) (x : ZMod n)
    (Tab : SigIn N B32 B32 → H) (t : Alg (AdvQ n N Point B32 B32) (AdvRH H) α)
    (s : SignerState B32 B32 × (ℕ → Ex)) :
    (liftQ t : Alg (AdvQ n N Point B32 B32 ⊕ Ex) (SumR (AdvRH H) Unit) α).run
        (challengerEH secp256k1X nonceCoef32 N qs red nv x Tab) s =
      ((t.run (challengerH secp256k1X nonceCoef32 N qs red x (fun k => nv k (s.2 k)) Tab)
          s.1).1,
        ((t.run (challengerH secp256k1X nonceCoef32 N qs red x (fun k => nv k (s.2 k)) Tab)
          s.1).2, s.2)) := by
  induction t generalizing s with
  | done a => rfl
  | ask q f ih => exact ih _ _

theorem run_sumTr_challengerEH (nv : Fin qs → Ex → SecNonce n) (x : ZMod n)
    (Tab : SigIn N B32 B32 → H) (q : AdvQB N ⊕ Ex) (s : SignerState B32 B32 × (ℕ → Ex)) :
    (sumTr trB q : Alg (AdvQ n N Point B32 B32 ⊕ Ex) (SumR (AdvRH H) Unit) _).run
        (challengerEH secp256k1X nonceCoef32 N qs red nv x Tab) s =
      challengerEB N qs red nv x Tab q s := by
  cases q with
  | inl q =>
    change (liftQ (trB q) : Alg (AdvQ n N Point B32 B32 ⊕ Ex) (SumR (AdvRH H) Unit) _).run _ s = _
    rw [run_liftQ_challengerEH, run_trB]
    rfl
  | inr e => rfl

/-- When `A` wins the game with `NonceGen` and the byte interface, `toStructN N A`
wins on parsed values, on the same sample. -/
theorem nonceGenExperimentB_imp (A : NAdversaryB N Rnd Ex W H Coins) (ρ : W → ZMod n) (e₀ : Ex)
    (ω : (RestH n N B32 B32 H Coins × (Fin qs → Rnd)) × (Rnd × Ex × Bool → W))
    (h : nonceGenExperimentB N qs red A ρ e₀ ω) :
    nonceGenExperimentH secp256k1X nonceCoef32 N qs red (toStructN N A) ρ e₀ ω := by
  unfold nonceGenExperimentH toStructN
  dsimp only
  rw [answerG_bind, answerG_transl, Alg.run_bind,
    run_transl (sumTr trB) _ _ (run_sumTr_challengerEH N qs red _ _ _)]
  exact wins_of_winsB N red _ _ _ _ h

theorem toStructN_answerG (A : SkAdversaryB N Rnd Rp Ex W H Coins) (Aux : Rp → Rnd) :
    toStructN N (fun c P => answerG Aux (A c P)) = fun c P => answerG Aux (toStructSk N A c P) := by
  funext c P
  unfold toStructN toStructSk
  rw [answerG_bind, answerG_transl]
  rfl

theorem nonceGenSkExperimentB_imp (A : SkAdversaryB N Rnd Rp Ex W H Coins) (ρ : W → ZMod n)
    (e₀ : Ex) (mask : (ZMod n)ˣ → Fin qs → Rnd ≃ Rnd)
    (ω : ((RestH n N B32 B32 H Coins × (Rnd × Ex × Bool → W)) × (Fin qs → Rp)) × (Rp → Rnd))
    (h : nonceGenSkExperimentB N qs red A ρ e₀ mask ω) :
    nonceGenSkExperimentH secp256k1X nonceCoef32 N qs red (toStructSk N A) ρ e₀ mask ω := by
  have := nonceGenExperimentB_imp N qs red _ ρ e₀ _ h
  rw [toStructN_answerG] at this
  exact this

theorem nonceGenCtrExperimentB_imp (A : SkAdversaryB N Rnd Rp Ex W H Coins) (ρ : W → ZMod n)
    (e₀ : Ex) (mask : (ZMod n)ˣ → Fin qs → Rnd ≃ Rnd) (ctr : Fin qs → Rp)
    (ω : (RestH n N B32 B32 H Coins × (Rnd × Ex × Bool → W)) × (Rp → Rnd))
    (h : nonceGenCtrExperimentB N qs red A ρ e₀ mask ctr ω) :
    nonceGenCtrExperimentH secp256k1X nonceCoef32 N qs ctr mask e₀ ρ red (toStructSk N A) ω := by
  have := nonceGenExperimentB_imp N qs red _ ρ e₀ _ h
  rw [toStructN_answerG] at this
  exact this

/-! ### The queries of the adversaries on parsed values -/

theorem nbound_toStructN (A : NAdversaryB N Rnd Ex W H Coins) (qn : ℕ)
    (hA : ∀ c P, NBound (A c P) qn) (c : Coins) (P : Point) : NBound (toStructN N A c P) qn := by
  have := NBound.bind (b := 0) (nbound_transl (sumTr trB) _ qn (hA c P))
    (g := fun f => (.done (toForgery f) : Alg ((AdvQ n N Point B32 B32 ⊕ Ex) ⊕ (Rnd × Ex × Bool))
      (SumR (SumR (AdvRH H) Unit) W) (Forgery n B32 B32))) fun f => trivial
  exact this

theorem hashBound_toStructN (A : NAdversaryB N Rnd Ex W H Coins) (qh : ℕ)
    (hH : ∀ c P G, HashBoundB (answerG (fun _ : Ex => ()) (answerG G (A c P))) qh) (c : Coins)
    (P : Point) (G : Rnd × Ex × Bool → W) :
    HashBound (answerG (fun _ : Ex => ()) (answerG G (toStructN N A c P))) qh := by
  unfold toStructN
  rw [answerG_bind, answerG_transl, answerG_bind, answerG_transl]
  have := hashBound_bind _ (fun f => (.done (toForgery f) :
    Alg (AdvQ n N Point B32 B32) (AdvRH H) (Forgery n B32 B32))) qh 0
    (hashBound_transl N _ qh (hH c P G)) fun r => trivial
  exact this

theorem nbound_toStructSk (A : SkAdversaryB N Rnd Rp Ex W H Coins) (qa : ℕ)
    (hA : ∀ c P, NBound (A c P) qa) (c : Coins) (P : Point) : NBound (toStructSk N A c P) qa := by
  have := NBound.bind (b := 0) (nbound_transl (sumTr (sumTr trB)) _ qa (hA c P))
    (g := fun f => (.done (toForgery f) :
      Alg (((AdvQ n N Point B32 B32 ⊕ Ex) ⊕ (Rnd × Ex × Bool)) ⊕ Rp)
        (SumR (SumR (SumR (AdvRH H) Unit) W) Rnd) (Forgery n B32 B32))) fun f => trivial
  exact this

theorem nbound_answerG_toStructSk (A : SkAdversaryB N Rnd Rp Ex W H Coins) (qn : ℕ)
    (hG : ∀ c P (Aux : Rp → Rnd), NBound (answerG Aux (A c P)) qn) (c : Coins) (P : Point)
    (Aux : Rp → Rnd) : NBound (answerG Aux (toStructSk N A c P)) qn := by
  unfold toStructSk
  rw [answerG_bind, answerG_transl]
  have := NBound.bind (b := 0) (nbound_transl (sumTr trB) _ qn (hG c P Aux))
    (g := fun f => (.done (toForgery f) : Alg ((AdvQ n N Point B32 B32 ⊕ Ex) ⊕ (Rnd × Ex × Bool))
      (SumR (SumR (AdvRH H) Unit) W) (Forgery n B32 B32))) fun f => trivial
  exact this

theorem hashBound_toStructSk (A : SkAdversaryB N Rnd Rp Ex W H Coins) (qh : ℕ)
    (hH : ∀ c P G (Aux : Rp → Rnd),
      HashBoundB (answerG (fun _ : Ex => ()) (answerG G (answerG Aux (A c P)))) qh)
    (c : Coins) (P : Point) (G : Rnd × Ex × Bool → W) (Aux : Rp → Rnd) :
    HashBound (answerG (fun _ : Ex => ()) (answerG G (answerG Aux (toStructSk N A c P)))) qh := by
  unfold toStructSk
  rw [answerG_bind, answerG_transl, answerG_bind, answerG_transl, answerG_bind, answerG_transl]
  have := hashBound_bind _ (fun f => (.done (toForgery f) :
    Alg (AdvQ n N Point B32 B32) (AdvRH H) (Forgery n B32 B32))) qh 0
    (hashBound_transl N _ qh (hH c P G Aux)) fun r => trivial
  exact this

/-! ## The security theorems with the byte interface -/

set_option synthInstance.maxSize 2000 in
/-- **BIP 459 is unforgeable under AOMDL with the byte interface.** The
adversary sends the message, the aggregate nonce, the public keys, the
messages and the public nonces of a signing query as byte arrays of any
length, and its forgery as byte arrays. The signer runs `Sign` on bytes and
the game runs `Verify` on bytes, with the challenge hash as a 256-bit random
oracle reduced modulo `n` and the BIP's nonce coefficient hash. The bound is
the one of `bytes_unforgeable_256` for the adversary `toStruct A`, which
parses. -/
theorem bytesGame_unforgeable_256 {Coins : Type} [Fintype Coins] (N qs : ℕ)
    (A : AdversaryB N (Fin (2 ^ 256)) Coins) (hN : N < n) (qh : ℕ)
    (hA : ∀ c P, HashBoundB (A c P) qh) :
    prob (forgeExperimentB N qs (redFin (2 ^ 256)) A) ≤
      Real.sqrt ((qh + qs + 1 : ℕ) *
        (omdlAdvantage secp256k1X (2 * qs + 1)
            (reduction secp256k1X nonceCoef32 N qs
              fun coins P => liftHash N (liftFin n_lt.le) (toStruct N A coins P)) +
          collisionAdvantage secp256k1X nonceCoef32 N qs
            fun coins P => liftHash N (liftFin n_lt.le) (toStruct N A coins P))) +
        (qh + qs + 1 : ℕ) / n + qs / (n - 1 : ℝ) +
        (qh + qs + N : ℕ) * ((((2 ^ 256 : ℕ) : ℝ) - n) / ((2 ^ 256 : ℕ) : ℝ)) :=
  (prob_mono fun ω h => forgeExperimentB_imp N qs _ A ω h).trans
    (bytes_unforgeable_256 N qs (toStruct N A) hN qh (hashBound_toStruct N A qh hA))

set_option synthInstance.maxSize 4000 in
/-- **BIP 459 with `NonceGen` and 256-bit hashes is unforgeable under AOMDL
with the byte interface**, for `NonceGen` without its `sk` argument. The game
is the one of `bytes_nonceGen_unforgeable_256` with `Sign` and `Verify` on
bytes, and the bound is the one for the adversary `toStructN A`, which
parses. -/
theorem bytesGame_nonceGen_unforgeable_256 {Coins Ex : Type} [Fintype Coins] [Fintype Ex]
    [DecidableEq Ex] (N qs : ℕ)
    (A : NAdversaryB N B32 Ex (Fin (2 ^ 256)) (Fin (2 ^ 256)) Coins) (e₀ : Ex) (hN : N < n)
    (qh qn : ℕ) (hA : ∀ c P, NBound (A c P) qn)
    (hH : ∀ c P G, HashBoundB (answerG (fun _ : Ex => ()) (answerG G (A c P))) qh) :
    prob (nonceGenExperimentB N qs (redFin (2 ^ 256)) A (redFin (2 ^ 256)) e₀) ≤
      lazyBound secp256k1X nonceCoef32 N qs qh
          (withStream N qn (liftHashN N (liftFin n_lt.le) (toStructN N A))) +
        (qh + qs + N : ℕ) * ((((2 ^ 256 : ℕ) : ℝ) - n) / ((2 ^ 256 : ℕ) : ℝ)) +
        (qs : ℝ) ^ 2 / ((2 ^ 256 : ℕ) : ℝ) + qs * (qn / ((2 ^ 256 : ℕ) : ℝ)) +
        (2 * qs : ℕ) * ((((2 ^ 256 : ℕ) : ℝ) - (n - 1)) / ((2 ^ 256 : ℕ) : ℝ)) := by
  refine (prob_mono fun ω h => nonceGenExperimentB_imp N qs _ A _ e₀ ω h).trans ?_
  have := bytes_nonceGen_unforgeable_256 N qs (toStructN N A) e₀ hN qh qn
    (nbound_toStructN N A qn hA) (hashBound_toStructN N A qh hH)
  unfold lazyBound
  exact this

set_option synthInstance.maxSize 4000 in
/-- **BIP 459 with `NonceGen`, its `sk` argument and 256-bit hashes is
unforgeable under AOMDL with the byte interface.** The game is the one of
`bytes_nonceGenSk_unforgeable_256` with `Sign` and `Verify` on bytes: the
adversary sends byte arrays of any length, gets the public nonces and the
partial signatures as byte arrays, and sees the 256-bit outputs of the
challenge hash. The bound is the one for the adversary `toStructSk A`, which
parses. -/
theorem bytesGame_nonceGenSk_unforgeable_256 {Coins Ex : Type} [Fintype Coins] [Fintype Ex]
    [DecidableEq Ex] (N qs : ℕ)
    (A : SkAdversaryB N B32 B32 Ex (Fin (2 ^ 256)) (Fin (2 ^ 256)) Coins) (e₀ : Ex)
    (mask : (ZMod n)ˣ → Fin qs → B32 ≃ B32) (hN : N < n) (qh qn qa : ℕ)
    (hA : ∀ c P, NBound (A c P) qa)
    (hG : ∀ c P (Aux : B32 → B32), NBound (answerG Aux (A c P)) qn)
    (hH : ∀ c P G (Aux : B32 → B32),
      HashBoundB (answerG (fun _ : Ex => ()) (answerG G (answerG Aux (A c P)))) qh) :
    prob (nonceGenSkExperimentB N qs (redFin (2 ^ 256)) A (redFin (2 ^ 256)) e₀ mask) ≤
      lazyBound secp256k1X nonceCoef32 N qs qh
          (withStream N qn (withAuxStream N qa
            (liftHashSk N (liftFin n_lt.le) (toStructSk N A)))) +
        (qh + qs + N : ℕ) * ((((2 ^ 256 : ℕ) : ℝ) - n) / ((2 ^ 256 : ℕ) : ℝ)) +
        (qs : ℝ) ^ 2 / ((2 ^ 256 : ℕ) : ℝ) + qs * (qn / ((2 ^ 256 : ℕ) : ℝ)) +
        (2 * qs : ℕ) * ((((2 ^ 256 : ℕ) : ℝ) - (n - 1)) / ((2 ^ 256 : ℕ) : ℝ)) +
        (qs : ℝ) ^ 2 / ((2 ^ 256 : ℕ) : ℝ) + qs * (qa / ((2 ^ 256 : ℕ) : ℝ)) := by
  refine (prob_mono fun ω h => nonceGenSkExperimentB_imp N qs _ A _ e₀ mask ω h).trans ?_
  have := bytes_nonceGenSk_unforgeable_256 N qs (toStructSk N A) e₀ mask hN qh qn qa
    (nbound_toStructSk N A qa hA) (nbound_answerG_toStructSk N A qn hG)
    (hashBound_toStructSk N A qh hH)
  unfold lazyBound
  exact this

set_option synthInstance.maxSize 4000 in
/-- **BIP 459 with `NonceGen` with a counter in place of `rand'` and 256-bit
hashes is unforgeable under AOMDL with the byte interface.** The game is the
one of `bytes_nonceGenCtr_unforgeable_256` with `Sign` and `Verify` on bytes,
and the bound is the one for the adversary `toStructSk A`, which parses. -/
theorem bytesGame_nonceGenCtr_unforgeable_256 {Coins Ex : Type} [Fintype Coins] [Fintype Ex]
    [DecidableEq Ex] (N qs : ℕ)
    (A : SkAdversaryB N B32 B32 Ex (Fin (2 ^ 256)) (Fin (2 ^ 256)) Coins) (e₀ : Ex)
    (ctr : Fin qs → B32) (hctr : Injective ctr) (τ : Fin qs → Tweak n) (hτ : ∀ k, (τ k).2 ≠ 0)
    (msgs : Fin (qs + 1) → B32) (hmsgs : Injective msgs) (hN0 : 0 < N) (hN : N < n)
    (qh qn qa : ℕ) (hA : ∀ c P, NBound (A c P) qa)
    (hG : ∀ c P (Aux : B32 → B32), NBound (answerG Aux (A c P)) qn)
    (hH : ∀ c P G (Aux : B32 → B32),
      HashBoundB (answerG (fun _ : Ex => ()) (answerG G (answerG Aux (A c P)))) qh) :
    prob (nonceGenCtrExperimentB N qs (redFin (2 ^ 256)) A (redFin (2 ^ 256)) e₀
        (fun x k => maskXor ((τ k).sk x)) ctr) ≤
      lazyBound secp256k1X nonceCoef32 N qs qh
          (withStream N qn (withAuxStream N qa
            (liftHashSk N (liftFin n_lt.le) (toStructSk N A)))) +
        lazyBound secp256k1X nonceCoef32 N qs (qh + 1)
          (withStream N qn (withAuxStream N (qa + qs)
            (keyForger secp256k1X N qs (fun k => unmaskXor (τ k)) msgs ctr
              (liftHashSk N (liftFin n_lt.le) (toStructSk N A))))) +
        (qh + qs + N : ℕ) * ((((2 ^ 256 : ℕ) : ℝ) - n) / ((2 ^ 256 : ℕ) : ℝ)) +
        (qs : ℝ) ^ 2 / ((2 ^ 256 : ℕ) : ℝ) +
        2 * ((2 * qs : ℕ) * ((((2 ^ 256 : ℕ) : ℝ) - (n - 1)) / ((2 ^ 256 : ℕ) : ℝ))) := by
  refine (prob_mono fun ω h =>
    nonceGenCtrExperimentB_imp N qs _ A _ e₀ (fun x k => maskXor ((τ k).sk x)) ctr ω h).trans ?_
  exact bytes_nonceGenCtr_unforgeable_256 N qs (toStructSk N A) e₀ ctr hctr τ hτ msgs hmsgs hN0 hN
    qh qn qa (nbound_toStructSk N A qa hA) (nbound_answerG_toStructSk N A qn hG)
    (hashBound_toStructSk N A qh hH)

end Dahlias.Security
