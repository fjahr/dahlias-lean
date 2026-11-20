import Dahlias.BytesCurve

/-!
# Correctness of BIP 459 on bytes

`verify_honest`: for an honest session run on byte arrays with `NonceAgg`,
`Sign` and `SigAgg`, the 64-byte output passes `Verify`. The statement is
about `specOps`, SHA-256 tagged hashes and the encodings of `Dahlias.Bytes`,
with no abstraction left.
-/

namespace Dahlias.Bytes

open Taproot Taproot.Secp256k1 Taproot.BIP340Vectors

/-! ## Encodings round-trip -/

@[simp] theorem length_xbytes (P : Point) : (xbytes P).length = 32 := length_bytes32 _

@[simp] theorem length_cbytes (P : Point) : (cbytes P).length = 33 := by simp [cbytes]

theorem cpoint_cbytes {P : Point} (hP : P ≠ 0) : cpoint specOps (cbytes P) = some P := by
  unfold cbytes
  by_cases h : hasEvenY P = true
  · simp only [h, ↓reduceIte, cpoint]
    exact secp256k1B.liftX_x P hP h
  · have h' : hasEvenY (-P) = true := by rw [hasEvenY_neg P hP]; simpa using h
    have := secp256k1B.liftX_x (-P) (neg_ne_zero.mpr hP) h'
    rw [secp256k1B.x_neg] at this
    simp only [h, Bool.false_eq_true, ↓reduceIte, cpoint]
    change (secp256k1B.liftX (secp256k1B.x P)).map (- ·) = some P
    rw [this]
    simp

theorem parseNonce_serNonce {N : PubNonce Point} (h1 : N.1 ≠ 0) (h2 : N.2 ≠ 0) :
    parseNonce specOps (serNonce N) = N := by
  simp [parseNonce, serNonce, List.take_left' (length_cbytes N.1),
    List.drop_left' (length_cbytes N.1), cpoint_cbytes h1, cpoint_cbytes h2]

theorem n_lt : n < 2 ^ 256 := by decide

theorem scalar_serScalar (s : ZMod n) : scalar (serScalar s) = some s := by
  have hv : s.val < n := ZMod.val_lt s
  simp [scalar, serScalar, toNatBE_bytes32 (hv.trans n_lt), hv]

/-! ## An honest session -/

/-- The byte arrays an honest signer holds or sends. -/
def pkOf (σ : Signer n Bytes) : Bytes := xbytes (secp256k1F.mulG σ.sk)
def skOf (σ : Signer n Bytes) : Bytes := serScalar σ.sk
def secnonceOf (σ : Signer n Bytes) : Bytes := serScalar σ.r₁ ++ serScalar σ.r₂
def pubnonceOf (σ : Signer n Bytes) : Bytes := serNonce (σ.pubnonce secp256k1B)

/-- **An honest session on bytes produces a valid signature.** Every signer
runs `Sign` on its 32-byte secret key and message, its 64-byte secret nonce,
the 66-byte aggregate nonce from `NonceAgg`, and the arrays of public keys,
messages and public nonces. If all of them succeed, the 64-byte output of
`SigAgg` passes `Verify`. -/
theorem verify_honest {signers : List (Signer n Bytes)} {aggnonce : Bytes} {psigs : List Bytes}
    {sig : Bytes}
    (hagg : nonceAgg specOps (signers.map pubnonceOf) = some aggnonce)
    (hlen : psigs.length = signers.length)
    (hsign : ∀ (i : ℕ) (hi : i < signers.length),
      sign specOps (secnonceOf signers[i]) (skOf signers[i]) signers[i].m aggnonce
        (signers.map pkOf) (signers.map (·.m)) (signers.map pubnonceOf) =
          some (psigs[i]'(by omega)))
    (hsig : sigAgg specOps aggnonce (signers.map pkOf) (signers.map (·.m))
      (signers.map pubnonceOf) psigs = some sig) :
    verify specOps (signers.map pkOf) (signers.map (·.m)) sig = true := by
  -- The scalars of `Sign` parse back.
  have hsc : ∀ σ : Signer n Bytes, scalar ((secnonceOf σ).take 32) = some σ.r₁ ∧
      scalar ((secnonceOf σ).drop 32) = some σ.r₂ ∧ scalar (skOf σ) = some σ.sk := fun σ => by
    have hl : (serScalar σ.r₁).length = 32 := length_bytes32 _
    simp [secnonceOf, skOf, List.take_left' hl, List.drop_left' hl, scalar_serScalar]
  have hzip : (signers.map pkOf).zip (signers.map (·.m)) =
      signers.map (Signer.pkm secp256k1B) := by
    rw [List.zip_map']; rfl
  -- Every `Sign` call is a call of the model.
  have hsign' : ∀ (i : ℕ) (hi : i < signers.length), ∃ s,
      Dahlias.sign specOps hashes (signers[i].r₁, signers[i].r₂) signers[i].sk signers[i].m
        (parseNonce specOps aggnonce) (signers.map (Signer.pkm secp256k1B))
        ((signers.map pubnonceOf).map (parseNonce specOps)) = some s ∧
      psigs[i]'(by omega) = serScalar s := by
    intro i hi
    have h := hsign i hi
    unfold sign at h
    obtain ⟨h1, h2, h3⟩ := hsc signers[i]
    simp only [h1, h2, h3, hzip] at h
    split_ifs at h
    obtain ⟨s, hs, hs'⟩ := Option.map_eq_some_iff.mp h
    exact ⟨s, hs, hs'.symm⟩
  -- So all nonces are nonzero and the public nonces parse back.
  have hpub : (signers.map pubnonceOf).map (parseNonce specOps) =
      signers.map (Signer.pubnonce secp256k1B) := by
    rw [List.map_map]
    refine List.map_congr_left fun σ hσ => ?_
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hσ
    obtain ⟨s, hs, -⟩ := hsign' i hi
    obtain ⟨hr₁, hr₂, -⟩ := sign_ne_zero hashes hs
    exact parseNonce_serNonce (secp256k1B.mulG_ne_zero hr₁) (secp256k1B.mulG_ne_zero hr₂)
  -- The aggregate nonce parses back.
  unfold nonceAgg at hagg
  rw [hpub] at hagg
  obtain ⟨agg, hagg', rfl⟩ := Option.map_eq_some_iff.mp hagg
  have hagg0 : agg.1 ≠ 0 ∧ agg.2 ≠ 0 := by
    have h := hagg'
    unfold Dahlias.nonceAgg at h
    dsimp only at h
    split_ifs at h with h0
    cases Option.some.inj h
    exact ⟨fun h' => h0 (.inr (.inr (.inl h'))), fun h' => h0 (.inr (.inr (.inr h')))⟩
  have hparse : parseNonce specOps (serNonce agg) = agg := parseNonce_serNonce hagg0.1 hagg0.2
  rw [hparse, hpub] at hsign'
  -- `SigAgg` is `sigAgg` of the model on the parsed partial signatures.
  unfold sigAgg at hsig
  rw [hzip, hpub, hparse] at hsig
  split_ifs at hsig with hwf
  obtain ⟨⟨r, s⟩, hsig', rfl⟩ := Option.map_eq_some_iff.mp hsig
  have hv := Dahlias.verify_honest secp256k1B hashes (signers := signers)
    (psigs := psigs.map fun b => (scalar b).getD 0) hagg' (by simpa using hlen)
    (fun i hi => by
      obtain ⟨s, hs, hs'⟩ := hsign' i hi
      simp only [List.getElem_map, hs', scalar_serScalar, Option.getD_some]
      exact hs) hsig'
  have hr : r.length = 32 := by
    unfold Dahlias.sigAgg at hsig'
    split_ifs at hsig'
    obtain ⟨⟨R, b⟩, -, h⟩ := Option.map_eq_some_iff.mp hsig'
    cases h
    exact length_xbytes R
  have hwf' : wellFormed (signers.map pkOf) (signers.map (·.m)) (signers.map pkOf).length =
      true := by
    simp only [Bool.and_eq_true] at hwf
    simpa using hwf.1
  have hs : (serScalar s).length = 32 := length_bytes32 _
  unfold verify
  dsimp only
  simp only [hwf', hzip, List.length_append, hr, hs, List.drop_left' hr, List.take_left' hr,
    scalar_serScalar, Bool.true_and, beq_self_eq_true]
  exact hv

end Dahlias.Bytes
