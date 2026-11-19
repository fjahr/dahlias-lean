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
theorem cbytes_injective {P P' : Point} (h : P ≠ 0) (h' : P' ≠ 0) (heq : cbytes P = cbytes P') :
    P = P' :=
  Option.some.inj (by rw [← cpoint_cbytes h, ← cpoint_cbytes h', heq])

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
messages and nonces other than the point at infinity. -/
def Items32 (items : List (Bytes × Bytes × Point)) : Prop :=
  ∀ it ∈ items, it.1.length = 32 ∧ it.2.1.length = 32 ∧ it.2.2 ≠ 0

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
        simp only [List.length_append, length_cbytes, ha.1, ha.2.1, hb.1, hb.2.1])
      obtain ⟨h12, h3⟩ := List.append_inj hchunk (by
        simp only [List.length_append, ha.1, ha.2.1, hb.1, hb.2.1])
      obtain ⟨h1, h2⟩ := List.append_inj h12 (by rw [ha.1, hb.1])
      have h3' := cbytes_injective ha.2.2 hb.2.2 h3
      rw [ih (fun e he => h e (List.mem_cons_of_mem _ he))
        (fun e he => h' e (List.mem_cons_of_mem _ he)) heq]
      exact congrArg (· :: l') (Prod.ext h1 (Prod.ext h2 h3'))

/-- **The input of `hash_BIP0459/noncecoef` determines `(R₁, R₂)` and the
`(pkᵢ, mᵢ, R₂,ᵢ)`**, for 32-byte public keys and messages and points other
than the point at infinity. `GetSessionValues` hashes only such inputs. -/
theorem nonceCoefInput_injective {R₁ R₂ R₁' R₂' : Point}
    {items items' : List (Bytes × Bytes × Point)} (h1 : R₁ ≠ 0) (h2 : R₂ ≠ 0) (h1' : R₁' ≠ 0)
    (h2' : R₂' ≠ 0) (h : Items32 items) (h' : Items32 items')
    (heq : nonceCoefInput R₁ R₂ items = nonceCoefInput R₁' R₂' items') :
    R₁ = R₁' ∧ R₂ = R₂' ∧ items = items' := by
  unfold nonceCoefInput at heq
  obtain ⟨hpre, heq⟩ := List.append_inj heq (by simp only [List.length_append, length_cbytes])
  obtain ⟨e1, e2⟩ := List.append_inj hpre (by rw [length_cbytes, length_cbytes])
  exact ⟨cbytes_injective h1 h1' e1, cbytes_injective h2 h2' e2, flatMap_items_inj h h' heq⟩

end Dahlias.Bytes

namespace Dahlias.Security

open Taproot Taproot.Secp256k1 Taproot.BIP340Vectors Dahlias.Bytes

/-! ## `Sign` and `Verify` on bytes are those of the security instance -/

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

end Dahlias.Security
