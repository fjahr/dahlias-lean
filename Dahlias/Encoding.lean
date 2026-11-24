import Dahlias.BytesSecurity

/-!
# The byte encodings lose nothing

The model takes the hash functions as functions of structured inputs, compares
nonces as points, and the security theorems are about an instance with points
and scalars. This file connects those choices to BIP 459's bytes.

* `sigInput_injective`, `nonceCoefInput_injective`: the byte strings that
  `hash_BIP0459/sig` and `hash_BIP0459/noncecoef` hash determine the
  structured input, because every field has a fixed length. So a hash of the
  bytes is a function of the structured input and the other way round.
* `collision_bytes`: a collision of the nonce coefficient hash that the
  security theorems are stated for is a pair of different byte strings whose
  tagged SHA-256 hashes are congruent modulo `n`. This includes the inputs
  with the point at infinity, which the game uses for single-party signatures:
  `cbytes` maps it to `02 ‖ 0^32`, and no curve point has the x-coordinate `0`
  (`sq_ne_seven`, `cbytes_injective`).
* `cpoint_eq_some_iff`: `cpoint` accepts exactly the encodings `cbytes(P)` of
  the points `P` other than the point at infinity, so no point has two
  encodings.
* `matchIdxs_bytes`: comparing the second halves of the public nonces with
  `cbytes(R₂)` as bytes, as `Sign` in BIP 459 does, is comparing the parsed
  points, as the model does.
* `sign_bytes`, `verify_bytes`: `Sign` and `Verify` on bytes
  (`Dahlias.Bytes`), given the encodings of the signer's secrets and any byte
  arrays for the nonces, are `Sign` and `Verify` of the instance that
  `bytes_unforgeable` is about, on the parsed nonces. A nonce that does not
  parse becomes the point `0`, which the adversary of the game may also send.
* `length_sha256`: SHA-256 has 32 bytes of output. So `hash_BIP0459/sig` is a
  256-bit value reduced modulo `n` (`hashes_sig_eq_redFin`), the form that the
  games with hash outputs have.
* `nonceGen_eq`, `nonceGen_sk_eq`: `NonceGen` on bytes (`Dahlias.Bytes`)
  derives the secret nonces as the games of `Dahlias.NonceGen` and
  `Dahlias.NonceGenSk` do, with the tagged hashes `nonceHash256` and `auxHash`
  as the oracles and `maskXor` as the mask. `nonceInput_injective`: the bytes
  that `hash_BIP0459/nonce` hashes determine `(rand, extra_in, i)`.
-/

set_option linter.unusedSectionVars false

namespace Dahlias.Bytes

open Taproot Taproot.Secp256k1 Taproot.BIP340Vectors

/-! ## Points -/

/-- **`cpoint` accepts only `cbytes` of a point other than infinity.** -/
theorem cpoint_eq_some {b : Bytes} {P : Point} (h : cpoint specOps b = some P) :
    P ≠ 0 ∧ b = cbytes P := by
  unfold cpoint at h
  split at h
  · rename_i x
    obtain ⟨h0, he, hx⟩ := secp256k1B.liftX_spec x P h
    refine ⟨h0, ?_⟩
    have hx' : xbytes P = x := hx
    have he' : hasEvenY P = true := he
    simp [cbytes, he', hx']
  · rename_i x
    obtain ⟨Q, hQ, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨h0, he, hx⟩ := secp256k1B.liftX_spec x Q hQ
    refine ⟨neg_ne_zero.mpr h0, ?_⟩
    have hx' : xbytes (-Q) = x := (secp256k1B.x_neg Q).trans hx
    have he' : hasEvenY Q = true := he
    have hodd : hasEvenY (-Q) = false := by rw [hasEvenY_neg Q h0, he']; rfl
    simp [cbytes, hodd, hx']
  · exact absurd h (by simp)

theorem cpoint_eq_some_iff {b : Bytes} {P : Point} :
    cpoint specOps b = some P ↔ P ≠ 0 ∧ b = cbytes P :=
  ⟨cpoint_eq_some, fun ⟨h0, hb⟩ => hb ▸ cpoint_cbytes h0⟩

/-- Points other than infinity have different encodings. -/
theorem cbytes_injective_of_ne {P P' : Point} (h : P ≠ 0) (h' : P' ≠ 0)
    (heq : cbytes P = cbytes P') : P = P' :=
  Option.some.inj (by rw [← cpoint_cbytes h, ← cpoint_cbytes h', heq])

/-- **`7` is not a square modulo `p`**, by Euler's criterion: `7^((p-1)/2)` is
not `1`, which the kernel computes. -/
theorem sq_ne_seven (y : F) : y ^ 2 ≠ 7 := by
  intro h
  have hy : y ≠ 0 := by
    rintro rfl
    exact seven_ne_zero (by simpa using h.symm)
  have h1 : (7 : F) ^ ((p - 1) / 2) = 1 := by
    rw [← h, ← pow_mul, show 2 * ((p - 1) / 2) = p - 1 by decide +kernel]
    exact ZMod.pow_card_sub_one_eq_one hy
  have h7 : (7 : F) = ((7 : ℕ) : F) := by norm_num
  rw [h7, Pratt.natCast_pow_eq_powMod _ _ _ (by decide +kernel)] at h1
  revert h1
  decide +kernel

/-- No point of secp256k1 has the x-coordinate `0`. -/
theorem xCoord_ne_zero {P : Point} (hP : P ≠ 0) : xCoord P ≠ 0 := by
  cases P with
  | zero => exact absurd rfl hP
  | some x y h =>
    intro hx
    have hx' : x = 0 := hx
    have hc := (nonsingular_iff x y).mp h
    rw [hx'] at hc
    exact sq_ne_seven y (by simpa using hc)

/-- The encoding of the point at infinity, `02 ‖ 0^32`, is the encoding of no
other point. -/
theorem cbytes_ne_zero {P : Point} (hP : P ≠ 0) : cbytes P ≠ cbytes 0 := by
  intro h
  unfold cbytes at h
  have hx : xbytes P = xbytes 0 := (List.cons.inj h).2
  have hv := congrArg toNatBE hx
  rw [xbytes, xbytes, toNatBE_bytes32 ((ZMod.val_lt _).trans p_lt),
    toNatBE_bytes32 ((ZMod.val_lt _).trans p_lt)] at hv
  have h0 : xCoord (0 : Point) = 0 := rfl
  rw [h0, ZMod.val_zero] at hv
  exact xCoord_ne_zero hP ((ZMod.val_eq_zero _).mp hv)

/-- **No two points have the same encoding**, the point at infinity
included. -/
theorem cbytes_injective {P P' : Point} (heq : cbytes P = cbytes P') : P = P' := by
  by_cases h : P = 0
  · by_cases h' : P' = 0
    · rw [h, h']
    · rw [h] at heq
      exact absurd heq.symm (cbytes_ne_zero h')
  · by_cases h' : P' = 0
    · rw [h'] at heq
      exact absurd heq (cbytes_ne_zero h)
    · exact cbytes_injective_of_ne h h' heq

/-- The second half of a 66-byte nonce parses to `R` exactly if it is
`cbytes(R)`. -/
theorem parseNonce_snd_eq_iff {b : Bytes} (hb : b.length = 66) {R : Point} (hR : R ≠ 0) :
    (parseNonce specOps b).2 = R ↔ b.drop 33 = cbytes R := by
  simp only [parseNonce, hb, ↓reduceIte]
  constructor
  · intro h
    cases hc : cpoint specOps (b.drop 33) with
    | none =>
      rw [hc] at h
      exact absurd h.symm hR
    | some Q =>
      rw [hc] at h
      have hQ : Q = R := h
      subst hQ
      exact (cpoint_eq_some hc).2
  · intro h
    rw [h, cpoint_cbytes hR]
    rfl

/-- **The index lookup of `Sign` on bytes is the model's.** For 66-byte public
nonces, the indices `j` with `pubnonce_j[33:66] = cbytes(R₂)` are the indices
whose parsed second half is `R₂`. -/
theorem matchIdxs_bytes (pubnonces : List Bytes) (hlen : ∀ b ∈ pubnonces, b.length = 66)
    {R : Point} (hR : R ≠ 0) :
    matchIdxs (pubnonces.map (parseNonce specOps)) R =
      (List.range pubnonces.length).filter fun j =>
        (pubnonces[j]?).map (·.drop 33) = some (cbytes R) := by
  unfold matchIdxs
  rw [List.length_map]
  refine List.filter_congr fun j _ => ?_
  rw [List.getElem?_map]
  cases hj : pubnonces[j]? with
  | none => simp
  | some b =>
    have hb := hlen b (List.mem_of_getElem? hj)
    simp only [Option.map_some, Option.some.injEq, decide_eq_decide]
    exact parseNonce_snd_eq_iff hb hR

/-! ## Hash inputs -/

/-- The bytes that `hash_BIP0459/sig` hashes. -/
def sigInput (pm : List (Bytes × Bytes)) (r : Bytes) (pkm : Bytes × Bytes) : Bytes :=
  pm.flatMap (fun x => x.1 ++ x.2) ++ r ++ pkm.1 ++ pkm.2

/-- The bytes that `hash_BIP0459/noncecoef` hashes. -/
def nonceCoefInput (R₁ R₂ : Point) (items : List (Bytes × Bytes × Point)) : Bytes :=
  cbytes R₁ ++ cbytes R₂ ++ items.flatMap fun it => it.1 ++ it.2.1 ++ cbytes it.2.2

theorem hashes_sig (pm : List (Bytes × Bytes)) (r : Bytes) (pkm : Bytes × Bytes) :
    hashes.sig pm r pkm = scalarWrap (taggedHash "BIP0459/sig" (sigInput pm r pkm)) := rfl

theorem hashes_nonceCoef (R₁ R₂ : Point) (items : List (Bytes × Bytes × Point)) :
    hashes.nonceCoef R₁ R₂ items =
      scalarWrap (taggedHash "BIP0459/noncecoef" (nonceCoefInput R₁ R₂ items)) := rfl

/-- All public keys and messages of a list are 32 bytes. -/
def Pairs32 (pm : List (Bytes × Bytes)) : Prop := ∀ e ∈ pm, e.1.length = 32 ∧ e.2.length = 32

theorem length_flatMap_pairs {pm : List (Bytes × Bytes)} (h : Pairs32 pm) :
    (pm.flatMap fun x => x.1 ++ x.2).length = 64 * pm.length := by
  induction pm with
  | nil => rfl
  | cons a l ih =>
    have ha := h a List.mem_cons_self
    have := ih fun e he => h e (List.mem_cons_of_mem _ he)
    simp only [List.flatMap_cons, List.length_append, List.length_cons, this, ha.1, ha.2]
    omega

theorem flatMap_pairs_append_inj {pm pm' : List (Bytes × Bytes)} (h : Pairs32 pm)
    (h' : Pairs32 pm') (hlen : pm.length = pm'.length) {t t' : Bytes}
    (heq : pm.flatMap (fun x => x.1 ++ x.2) ++ t = pm'.flatMap (fun x => x.1 ++ x.2) ++ t') :
    pm = pm' ∧ t = t' := by
  induction pm generalizing pm' with
  | nil =>
    cases pm' with
    | nil => exact ⟨rfl, heq⟩
    | cons b l' => simp at hlen
  | cons a l ih =>
    cases pm' with
    | nil => simp at hlen
    | cons b l' =>
      have ha := h a List.mem_cons_self
      have hb := h' b List.mem_cons_self
      simp only [List.flatMap_cons, List.append_assoc] at heq
      obtain ⟨h1, heq⟩ := List.append_inj heq (by rw [ha.1, hb.1])
      obtain ⟨h2, heq⟩ := List.append_inj heq (by rw [ha.2, hb.2])
      obtain ⟨h3, h4⟩ := ih (fun e he => h e (List.mem_cons_of_mem _ he))
        (fun e he => h' e (List.mem_cons_of_mem _ he)) (by simpa using hlen) heq
      exact ⟨by rw [Prod.ext h1 h2, h3], h4⟩

/-- **The input of `hash_BIP0459/sig` determines `(L, r, pk, m)`**, for
32-byte public keys, messages and `r`. -/
theorem sigInput_injective {pm pm' : List (Bytes × Bytes)} {r r' : Bytes}
    {pkm pkm' : Bytes × Bytes} (h : Pairs32 pm) (h' : Pairs32 pm') (hr : r.length = 32)
    (hr' : r'.length = 32) (hk : pkm.1.length = 32) (hk' : pkm'.1.length = 32)
    (hm : pkm.2.length = 32) (hm' : pkm'.2.length = 32)
    (heq : sigInput pm r pkm = sigInput pm' r' pkm') : pm = pm' ∧ r = r' ∧ pkm = pkm' := by
  unfold sigInput at heq
  have hlen : pm.length = pm'.length := by
    have := congrArg List.length heq
    simp only [List.length_append, length_flatMap_pairs h, length_flatMap_pairs h', hr, hr', hk,
      hk', hm, hm'] at this
    omega
  simp only [List.append_assoc] at heq
  obtain ⟨h1, heq⟩ := flatMap_pairs_append_inj h h' hlen heq
  obtain ⟨h2, heq⟩ := List.append_inj heq (by rw [hr, hr'])
  obtain ⟨h3, h4⟩ := List.append_inj heq (by rw [hk, hk'])
  exact ⟨h1, h2, Prod.ext h3 h4⟩

/-- The items of a nonce coefficient input have 32-byte public keys and
messages. -/
def Items32 (items : List (Bytes × Bytes × Point)) : Prop :=
  ∀ it ∈ items, it.1.length = 32 ∧ it.2.1.length = 32

theorem flatMap_items_inj {items items' : List (Bytes × Bytes × Point)} (h : Items32 items)
    (h' : Items32 items')
    (heq : items.flatMap (fun it => it.1 ++ it.2.1 ++ cbytes it.2.2) =
      items'.flatMap fun it => it.1 ++ it.2.1 ++ cbytes it.2.2) : items = items' := by
  induction items generalizing items' with
  | nil =>
    cases items' with
    | nil => rfl
    | cons b l' =>
      have := congrArg List.length heq
      simp at this
      omega
  | cons a l ih =>
    cases items' with
    | nil =>
      have := congrArg List.length heq
      simp at this
    | cons b l' =>
      have ha := h a List.mem_cons_self
      have hb := h' b List.mem_cons_self
      rw [List.flatMap_cons, List.flatMap_cons] at heq
      obtain ⟨hchunk, heq⟩ := List.append_inj heq (by
        simp only [List.length_append, length_cbytes, ha.1, ha.2, hb.1, hb.2])
      obtain ⟨h12, h3⟩ := List.append_inj hchunk (by
        simp only [List.length_append, ha.1, ha.2, hb.1, hb.2])
      obtain ⟨h1, h2⟩ := List.append_inj h12 (by rw [ha.1, hb.1])
      have h3' := cbytes_injective h3
      rw [ih (fun e he => h e (List.mem_cons_of_mem _ he))
        (fun e he => h' e (List.mem_cons_of_mem _ he)) heq]
      exact congrArg (· :: l') (Prod.ext h1 (Prod.ext h2 h3'))

/-- **The input of `hash_BIP0459/noncecoef` determines `(R₁, R₂)` and the
`(pkᵢ, mᵢ, R₂,ᵢ)`**, for 32-byte public keys and messages. The points may be
the point at infinity: `GetSessionValues` hashes no such input, but the game
does for the nonce of a single-party signature. -/
theorem nonceCoefInput_injective {R₁ R₂ R₁' R₂' : Point}
    {items items' : List (Bytes × Bytes × Point)} (h : Items32 items) (h' : Items32 items')
    (heq : nonceCoefInput R₁ R₂ items = nonceCoefInput R₁' R₂' items') :
    R₁ = R₁' ∧ R₂ = R₂' ∧ items = items' := by
  unfold nonceCoefInput at heq
  obtain ⟨hpre, heq⟩ := List.append_inj heq (by simp only [List.length_append, length_cbytes])
  obtain ⟨e1, e2⟩ := List.append_inj hpre (by rw [length_cbytes, length_cbytes])
  exact ⟨cbytes_injective e1, cbytes_injective e2, flatMap_items_inj h h' heq⟩

end Dahlias.Bytes

namespace Dahlias.Security

open Taproot Taproot.Secp256k1 Taproot.BIP340Vectors Dahlias.Bytes

/-! ## `Sign` and `Verify` on bytes are those of the security instance -/

/-! ## A collision of the nonce coefficient hash, in bytes -/

/-- The bytes that `hash_BIP0459/noncecoef` hashes for an input of
`nonceCoef32`. -/
def nonceCoefBytes (z : Point × Point × List (B32 × B32 × Point)) : Bytes :=
  nonceCoefInput z.1 z.2.1 (z.2.2.map fun t => (t.1.1, t.2.1.1, t.2.2))

theorem nonceCoefBytes_injective : Function.Injective nonceCoefBytes := by
  rintro ⟨R₁, R₂, items⟩ ⟨R₁', R₂', items'⟩ h
  have h32 : ∀ l : List (B32 × B32 × Point),
      Items32 (l.map fun t => (t.1.1, t.2.1.1, t.2.2)) := by
    intro l it hit
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp hit
    exact ⟨t.1.2, t.2.1.2⟩
  obtain ⟨rfl, rfl, hi⟩ := nonceCoefInput_injective (h32 items) (h32 items') h
  have hinj : Function.Injective fun t : B32 × B32 × Point => (t.1.1, t.2.1.1, t.2.2) := by
    rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (Subtype.ext h.1) (Prod.ext (Subtype.ext h.2.1) h.2.2)
  rw [List.map_injective_iff.mpr hinj hi]

/-- **A collision of the nonce coefficient hash is a collision of SHA-256
modulo `n`.** The two inputs are hashed as two different byte strings, and
the tagged hashes of the two strings, read as numbers, are congruent modulo
`n`. So `collisionAdvantage` for `nonceCoef32` is the probability that
`collider` finds such a pair of strings. -/
theorem collision_bytes
    {p : (Point × Point × List (B32 × B32 × Point)) × (Point × Point × List (B32 × B32 × Point))}
    (h : IsCollision nonceCoef32 p) :
    nonceCoefBytes p.1 ≠ nonceCoefBytes p.2 ∧
      toNatBE (taggedHash "BIP0459/noncecoef" (nonceCoefBytes p.1)) % n =
        toNatBE (taggedHash "BIP0459/noncecoef" (nonceCoefBytes p.2)) % n := by
  obtain ⟨hne, heq⟩ := h
  refine ⟨fun hb => hne (nonceCoefBytes_injective hb), ?_⟩
  have heq' : (toNatBE (taggedHash "BIP0459/noncecoef" (nonceCoefBytes p.1)) : ZMod n) =
      (toNatBE (taggedHash "BIP0459/noncecoef" (nonceCoefBytes p.2)) : ZMod n) := heq
  exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp heq'

theorem signPre_eq_none {E X M : Type} [AddCommGroup E] [DecidableEq E] [DecidableEq X]
    [DecidableEq M] (O : Ops n E X) (H : Hashes n E X M) (secnonce : SecNonce n) (sk : ZMod n)
    (m : M) (agg : PubNonce E) (pm : List (X × M)) (pubs : List (PubNonce E))
    (h : pm = [] ∨ pm.length ≠ pubs.length) : signPre O H secnonce sk m agg pm pubs = none := by
  have hg : getSessionValues O H agg pm pubs = none := by
    have hc : pm = [] ∨ pm.length ≠ pubs.length ∨ agg.1 = 0 ∨ agg.2 = 0 ∨
        ∃ N ∈ pubs, N.2 = 0 := by
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    unfold getSessionValues
    simp only [hc, ↓reduceIte]
  unfold signPre
  split_ifs
  · rfl
  · split
    · split_ifs
      · exact hg
      · rfl
    · rfl

theorem zip_vals (pm : List (B32 × B32)) :
    (pm.map fun e => e.1.1).zip (pm.map fun e => e.2.1) = vals pm := by
  unfold vals
  induction pm with
  | nil => rfl
  | cons e l ih => simp only [List.map_cons, List.zip_cons_cons, ih]

theorem all_is32 (pm : List (B32 × B32)) :
    (pm.map fun e => e.1.1).all is32 = true ∧ (pm.map fun e => e.2.1).all is32 = true := by
  constructor <;>
  · rw [List.all_map, List.all_eq_true]
    intro e _
    simp [is32, e.1.2, e.2.2]

/-- **`Verify` on bytes is `Verify` of the instance**: for 32-byte public
keys, messages and `r`, and the encoding of the scalar `s`. -/
theorem verify_bytes {H : Hashes n Point B32 B32} (hH : Agree H hashes) (pm : List (B32 × B32))
    (r : B32) (s : ZMod n) :
    Bytes.verify specOps (pm.map fun e => e.1.1) (pm.map fun e => e.2.1) (r.1 ++ serScalar s) =
      verify secp256k1X.ops H pm (r, s) := by
  rw [verify_val hH]
  unfold Bytes.verify
  have hlen : (r.1 ++ serScalar s).length = 64 := by
    rw [List.length_append, r.2]
    simp [serScalar]
  have hdrop : (r.1 ++ serScalar s).drop 32 = serScalar s := List.drop_left' r.2
  have htake : (r.1 ++ serScalar s).take 32 = r.1 := List.take_left' r.2
  rw [hdrop, htake, scalar_serScalar, zip_vals]
  cases pm with
  | nil =>
    simp only [wellFormed, List.map_nil, List.length_nil, lt_self_iff_false, decide_false,
      Bool.false_and]
    unfold verify
    cases specOps.liftX r.1 <;> rfl
  | cons e l =>
    have hw : wellFormed ((e :: l).map fun e => e.1.1) ((e :: l).map fun e => e.2.1)
        ((e :: l).map fun e => e.1.1).length = true := by
      have ha := all_is32 (e :: l)
      simp only [wellFormed, ha.1, ha.2, List.length_map, List.length_cons, beq_self_eq_true,
        Bool.and_true, decide_eq_true_eq]
      omega
    simp only [hw, hlen, beq_self_eq_true, Bool.true_and]

/-- **`Sign` on bytes is `Sign` of the instance**: for the encodings of the
secret nonce and the secret key, a 32-byte message, 32-byte public keys and
messages, and any byte arrays for the aggregate nonce and the public nonces,
which are parsed. -/
theorem sign_bytes {H : Hashes n Point B32 B32} (hH : Agree H hashes) (r₁ r₂ d : ZMod n)
    (m : B32) (aggnonce : Bytes) (pm : List (B32 × B32)) (pubnonces : List Bytes) :
    Bytes.sign specOps (serScalar r₁ ++ serScalar r₂) (serScalar d) m.1 aggnonce
        (pm.map fun e => e.1.1) (pm.map fun e => e.2.1) pubnonces =
      (sign secp256k1X.ops H (r₁, r₂) d m (parseNonce specOps aggnonce) pm
        (pubnonces.map (parseNonce specOps))).map serScalar := by
  rw [sign_val hH]
  unfold Bytes.sign
  have h32 : (serScalar r₁).length = 32 := by simp [serScalar]
  have hlen : (serScalar r₁ ++ serScalar r₂).length = 64 := by
    rw [List.length_append]
    simp [serScalar]
  have hdrop : (serScalar r₁ ++ serScalar r₂).drop 32 = serScalar r₂ := List.drop_left' h32
  have htake : (serScalar r₁ ++ serScalar r₂).take 32 = serScalar r₁ := List.take_left' h32
  have hm : is32 m.1 = true := by simp [is32, m.2]
  have ha := all_is32 pm
  rw [hdrop, htake, scalar_serScalar, scalar_serScalar, scalar_serScalar, zip_vals]
  by_cases hw : 0 < pubnonces.length ∧ pm.length = pubnonces.length
  · have : wellFormed (pm.map fun e => e.1.1) (pm.map fun e => e.2.1) pubnonces.length = true := by
      simp only [wellFormed, ha.1, ha.2, List.length_map, hw.2, beq_self_eq_true, Bool.and_true,
        decide_eq_true_eq]
      exact hw.1
    simp only [this, hm, hlen, beq_self_eq_true, Bool.and_self, ↓reduceIte]
  · have hwf : wellFormed (pm.map fun e => e.1.1) (pm.map fun e => e.2.1) pubnonces.length =
        false := by
      simp only [wellFormed, List.length_map, Bool.and_eq_false_iff, decide_eq_false_iff_not,
        beq_eq_false_iff_ne]
      by_cases h0 : 0 < pubnonces.length
      · exact Or.inl (Or.inl (Or.inl (Or.inr fun h => hw ⟨h0, h⟩)))
      · exact Or.inl (Or.inl (Or.inl (Or.inl h0)))
    have hnone : sign specOps hashes (r₁, r₂) d m.1 (parseNonce specOps aggnonce) (vals pm)
        (pubnonces.map (parseNonce specOps)) = none := by
      rw [sign_eq, signPre_eq_none]
      · rfl
      · simp only [vals, List.length_map, List.map_eq_nil_iff]
        by_cases h0 : 0 < pubnonces.length
        · exact Or.inr fun h => hw ⟨h0, h⟩
        · have hp : pubnonces = [] := List.length_eq_zero_iff.mp (by omega)
          by_cases hpm : pm = []
          · exact Or.inl hpm
          · refine Or.inr fun h => hpm (List.length_eq_zero_iff.mp ?_)
            rw [h, hp]
            rfl
    simp only [hwf, Bool.false_and, Bool.false_eq_true, ↓reduceIte, hnone, Option.map_none]

/-! ## The hash functions as functions to 256-bit values, and `NonceGen` -/

theorem size_sha256Block (h : Array UInt32) (blk : Array UInt8) (off : ℕ) :
    (sha256Block h blk off).size = 8 := by
  unfold sha256Block
  simp

theorem foldl_invariant {α β : Type} (P : β → Prop) (f : β → α → β)
    (hf : ∀ b a, P b → P (f b a)) : ∀ (l : List α) (b : β), P b → P (l.foldl f b)
  | [], _, hb => hb
  | a :: l, b, hb => foldl_invariant P f hf l (f b a) (hf b a hb)

/-- **SHA-256 has 32 bytes of output.** -/
theorem length_sha256 (msg : Bytes) : (sha256 msg).length = 32 := by
  unfold sha256
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', List.forIn_pure_yield_eq_foldl]
  simp only [Id.run, bind, pure]
  have hsize : ∀ l : List ℕ, (List.foldl
      (fun b a => sha256Block b (List.toArray (sha256Pad msg)) (64 * a)) sha256H0 l).size = 8 :=
    fun l => foldl_invariant (fun h : Array UInt32 => h.size = 8) _
      (fun b a _ => size_sha256Block _ _ _) l _ rfl
  rw [List.length_flatMap]
  simp [hsize]

theorem length_taggedHash (tag : String) (msg : Bytes) : (taggedHash tag msg).length = 32 :=
  length_sha256 _

/-- A 32-byte array as a 256-bit value. -/
def int256 (b : Bytes) (h : b.length = 32) : Fin (2 ^ 256) :=
  ⟨toNatBE b, by
    have := toNatBE_lt b
    rw [h] at this
    exact lt_of_lt_of_eq this (by norm_num)⟩

/-- `hash_BIP0459/sig` with its 256-bit output. -/
def sigHash256 (pm : List (Bytes × Bytes)) (r : Bytes) (pkm : Bytes × Bytes) : Fin (2 ^ 256) :=
  int256 (taggedHash "BIP0459/sig" (sigInput pm r pkm)) (length_taggedHash _ _)

/-- **The challenge hash of BIP 459 is a 256-bit hash output reduced modulo
`n`**: the form `red ∘ Tab` that the games with hash outputs have, with
`red = redFin (2^256)`. -/
theorem hashes_sig_eq_redFin (pm : List (Bytes × Bytes)) (r : Bytes) (pkm : Bytes × Bytes) :
    Bytes.hashes.sig pm r pkm = redFin (2 ^ 256) (sigHash256 pm r pkm) :=
  rfl

/-- `hash_BIP0459/aux` on 32-byte arrays. -/
def auxHash (r : B32) : B32 := ⟨taggedHash "BIP0459/aux" r.1, length_taggedHash _ _⟩

/-- The bytes that `hash_BIP0459/nonce` hashes: `rand ‖ extra_in ‖ i`. -/
def nonceInput (rand : B32) (extraIn : Bytes) (i : Bool) : Bytes :=
  rand.1 ++ extraIn ++ [if i then 1 else 0]

/-- `hash_BIP0459/nonce` with its 256-bit output, as a function of
`(rand, extra_in, i)`. -/
def nonceHash256 (z : B32 × Bytes × Bool) : Fin (2 ^ 256) :=
  int256 (taggedHash "BIP0459/nonce" (nonceInput z.1 z.2.1 z.2.2)) (length_taggedHash _ _)

/-- **The input of `hash_BIP0459/nonce` determines `(rand, extra_in, i)`**,
for a 32-byte `rand` and an `extra_in` of any length. So a hash of the bytes
is a function of the triple, which is what the games query. -/
theorem nonceInput_injective {rand rand' : B32} {e e' : Bytes} {i i' : Bool}
    (h : nonceInput rand e i = nonceInput rand' e' i') : rand = rand' ∧ e = e' ∧ i = i' := by
  unfold nonceInput at h
  rw [List.append_assoc, List.append_assoc] at h
  obtain ⟨h1, h2⟩ := List.append_inj h (rand.2.trans rand'.2.symm)
  obtain ⟨h3, h4⟩ := List.append_inj' h2 rfl
  refine ⟨Subtype.ext h1, h3, ?_⟩
  cases i <;> cases i' <;> simp_all

/-- **`NonceGen` without the `sk` argument, on bytes, derives the nonces as the
games do**: the secret nonces are `ρ (G (rand, extra_in, i))` for
`G = nonceHash256` and `ρ = redFin (2^256)`. It fails if one of them is
zero. -/
theorem nonceGen_eq (O : Ops n Point Bytes) (rand : B32) (extraIn : Bytes) :
    Bytes.nonceGen O rand.1 none extraIn =
      (Dahlias.nonceGen O (redFin (2 ^ 256) (nonceHash256 (rand, extraIn, false)))
        (redFin (2 ^ 256) (nonceHash256 (rand, extraIn, true)))).map
          fun (sec, pub) => (serScalar sec.1 ++ serScalar sec.2, serNonce pub) := by
  have h32 : is32 rand.1 = true := by simp [is32, rand.2]
  unfold Bytes.nonceGen
  simp only [h32, Option.all_none, Bool.and_true, ↓reduceIte]
  rfl

/-- **`NonceGen` with the `sk` argument, on bytes, derives the nonces as the
games do**, for the secret key `d` as the argument: the secret nonces are
`ρ (G (rand, extra_in, i))` with `rand = maskXor d (Aux rand')`, for
`G = nonceHash256`, `Aux = auxHash` and `ρ = redFin (2^256)`. So `maskXor` is
the xor of BIP 459's `NonceGen`. -/
theorem nonceGen_sk_eq (O : Ops n Point Bytes) (d : ZMod n) (rand' : B32) (extraIn : Bytes) :
    Bytes.nonceGen O rand'.1 (some (serScalar d)) extraIn =
      (Dahlias.nonceGen O
        (redFin (2 ^ 256) (nonceHash256 (maskXor d (auxHash rand'), extraIn, false)))
        (redFin (2 ^ 256) (nonceHash256 (maskXor d (auxHash rand'), extraIn, true)))).map
          fun (sec, pub) => (serScalar sec.1 ++ serScalar sec.2, serNonce pub) := by
  have h32 : is32 rand'.1 = true := by simp [is32, rand'.2]
  have hsk : is32 (serScalar d) = true := by simp [is32, serScalar]
  unfold Bytes.nonceGen
  simp only [h32, Option.all_some, hsk, Bool.and_true, ↓reduceIte]
  rfl

end Dahlias.Security
