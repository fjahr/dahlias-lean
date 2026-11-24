import Dahlias.Secp256k1
import Dahlias.BytesCorrectness
import Dahlias.Proofs.Game
import Dahlias.Hashed
import Dahlias.BindingHashed
import Dahlias.NonceGenCounter

/-!
# The security theorems for 32-byte keys and messages

`bytes_unforgeable` and `bytes_strongly_binding` are the security theorems for
secp256k1 with public keys, messages and the `R` of a signature as 32-byte
arrays (`B32`), and with the nonce coefficient hash of BIP 459:
`hash_BIP0459/noncecoef` (SHA-256) on the BIP's byte encoding.

`verify_val` and `sign_val` say that the algorithms of this instance are the
algorithms of `Dahlias.Bytes` on the underlying byte arrays, so the theorems
are about what `Dahlias.Bytes` and the test vectors run, with the challenge
hash replaced by the random oracle.

In `bytes_unforgeable` the random oracle answers with a uniform scalar. In
`bytes_unforgeable_256` it answers with a uniform 256-bit value that `Sign`
and `Verify` reduce modulo `n`, as BIP 459 does with SHA-256. The difference
is at most `2^-127` for every oracle value the game reads (`hash_gap`).

`bytes_nonceGenSk_unforgeable_256` and `bytes_nonceGen_unforgeable_256` have
all of it at once: the 32-byte instance, the 256-bit challenge hash and the
nonces of `NonceGen`, with and without its `sk` argument. The forger, the
reduction and the collision finder in them sample all random oracles lazily.
`bytes_nonceGenCtr_unforgeable_256` is the statement for `NonceGen` with the
secret key and a counter in place of `rand'`.
-/

set_option linter.unusedSectionVars false

namespace Dahlias.Security

open Taproot Taproot.Secp256k1 Taproot.BIP340Vectors Dahlias.Bytes

/-- 32-byte arrays. -/
abbrev B32 := {b : Bytes // b.length = 32}

instance : DecidableEq B32 := inferInstance

noncomputable instance : Fintype B32 :=
  haveI : Finite B32 := (List.finite_length_eq UInt8 32).to_subtype
  Fintype.ofFinite _

/-- **secp256k1 with x-coordinates as 32-byte arrays.** -/
def secp256k1X : Curve n Point B32 where
  G := secp256k1B.G
  G_ne_zero := secp256k1B.G_ne_zero
  order_G := secp256k1B.order_G
  x P := ⟨xbytes P, length_xbytes P⟩
  hasEvenY := hasEvenY
  liftX b := secp256k1B.liftX b.1
  x_neg P := Subtype.ext (secp256k1B.x_neg P)
  hasEvenY_neg := secp256k1B.hasEvenY_neg
  liftX_x P hP he := secp256k1B.liftX_x P hP he
  liftX_spec r P h :=
    ⟨(secp256k1B.liftX_spec r.1 P h).1, (secp256k1B.liftX_spec r.1 P h).2.1,
      Subtype.ext (secp256k1B.liftX_spec r.1 P h).2.2⟩

/-- `hash_BIP0459/noncecoef` on 32-byte public keys and messages. -/
def nonceCoef32 (R₁ R₂ : Point) (items : List (B32 × B32 × Point)) : ZMod n :=
  Bytes.hashes.nonceCoef R₁ R₂ (items.map fun t => (t.1.1, t.2.1.1, t.2.2))

set_option synthInstance.maxSize 2000 in
/-- **BIP 459 with 32-byte keys and messages is unforgeable under AOMDL**, with
the challenge hash as a random oracle and the BIP's nonce coefficient hash. -/
theorem bytes_unforgeable {Coins : Type} [Fintype Coins] (N qs : ℕ)
    (A : Adversary n N Point B32 B32 Coins) (hN : N < n) (qh : ℕ)
    (hA : ∀ coins P, HashBound (A coins P) qh) :
    forgeAdvantage secp256k1X nonceCoef32 N qs A ≤
      Real.sqrt ((qh + qs + 1 : ℕ) *
        (omdlAdvantage secp256k1X (2 * qs + 1) (reduction secp256k1X nonceCoef32 N qs A) +
          collisionAdvantage secp256k1X nonceCoef32 N qs A)) + (qh + qs + 1 : ℕ) / n +
        qs / (n - 1 : ℝ) :=
  unforgeable_sqrt secp256k1X nonceCoef32 N qs A hN qh hA

set_option synthInstance.maxSize 2000 in
/-- **BIP 459 with 32-byte keys and messages is unforgeable under AOMDL**, with
the challenge hash as a 256-bit random oracle reduced modulo `n` and the BIP's
nonce coefficient hash. -/
theorem bytes_unforgeable_256 {Coins : Type} [Fintype Coins] (N qs : ℕ)
    (A : AdversaryH n N Point B32 B32 (Fin (2 ^ 256)) Coins) (hN : N < n) (qh : ℕ)
    (hA : ∀ coins P, HashBound (A coins P) qh) :
    forgeAdvantageH secp256k1X nonceCoef32 N qs (redFin (2 ^ 256)) A ≤
      Real.sqrt ((qh + qs + 1 : ℕ) *
        (omdlAdvantage secp256k1X (2 * qs + 1)
            (reduction secp256k1X nonceCoef32 N qs
              fun coins P => liftHash N (liftFin n_lt.le) (A coins P)) +
          collisionAdvantage secp256k1X nonceCoef32 N qs
            fun coins P => liftHash N (liftFin n_lt.le) (A coins P))) +
        (qh + qs + 1 : ℕ) / n + qs / (n - 1 : ℝ) +
        (qh + qs + N : ℕ) * ((((2 ^ 256 : ℕ) : ℝ) - n) / ((2 ^ 256 : ℕ) : ℝ)) :=
  unforgeable_sqrt_fin secp256k1X nonceCoef32 N qs n_lt.le A hN qh hA

/-- The cost of reducing a 256-bit hash output modulo `n`, for every oracle
value the game reads, is at most `2^-127`. -/
theorem hash_gap : (((2 ^ 256 : ℕ) : ℝ) - n) / ((2 ^ 256 : ℕ) : ℝ) ≤ 1 / 2 ^ 127 := by
  have h : 2 ^ 256 ≤ n + 2 ^ 129 := by decide
  have h' : ((2 ^ 256 : ℕ) : ℝ) ≤ (n : ℝ) + ((2 ^ 129 : ℕ) : ℝ) := by exact_mod_cast h
  have hpos : (0 : ℝ) < ((2 ^ 256 : ℕ) : ℝ) := by positivity
  rw [div_le_div_iff₀ hpos (by positivity)]
  have e : ((2 ^ 256 : ℕ) : ℝ) = ((2 ^ 129 : ℕ) : ℝ) * 2 ^ 127 := by norm_num
  nlinarith [h', e]

set_option synthInstance.maxSize 2000 in
/-- **BIP 459 with 32-byte keys and messages is strongly binding.** -/
theorem bytes_strongly_binding {Coins : Type} [Fintype Coins] (N : ℕ)
    (A : BindAdversary n N B32 B32 Coins) (hN : N < n) (qh : ℕ)
    (hA : ∀ coins T, (QTree.fresh T (A coins)).length ≤ qh) :
    prob (bindExperiment secp256k1X nonceCoef32 N A) ≤ ((qh + 2 * N : ℕ) : ℝ) ^ 2 / n :=
  strongly_binding secp256k1X nonceCoef32 N A secp256k1_primeOrder hN qh hA

set_option synthInstance.maxSize 2000 in
/-- **BIP 459 with 32-byte keys and messages is strongly binding**, with the
challenge hash as a 256-bit random oracle reduced modulo `n`. -/
theorem bytes_strongly_binding_256 {Coins : Type} [Fintype Coins] (N : ℕ)
    (A : BindAdversaryH n N B32 B32 (Fin (2 ^ 256)) Coins) (hN : N < n) (qh : ℕ)
    (hA : ∀ coins Tab, (QTree.fresh Tab (A coins)).length ≤ qh) :
    prob (bindExperimentH secp256k1X nonceCoef32 N (redFin (2 ^ 256)) A) ≤
      ((qh + 2 * N : ℕ) : ℝ) ^ 2 / n +
        (qh + 2 * N : ℕ) * ((((2 ^ 256 : ℕ) : ℝ) - n) / ((2 ^ 256 : ℕ) : ℝ)) :=
  strongly_binding_fin secp256k1X nonceCoef32 N n_lt.le A secp256k1_primeOrder hN qh hA

/-! ## `NonceGen`, 256-bit hashes and 32-byte values together -/

instance : Inhabited B32 := ⟨⟨List.replicate 32 0, List.length_replicate⟩⟩

/-- There are `2²⁵⁶` 32-byte arrays. -/
theorem card_B32 : Fintype.card B32 = 2 ^ 256 := by
  have h : Fintype.card B32 = Fintype.card (List.Vector UInt8 32) :=
    Fintype.card_congr (Equiv.refl _)
  rw [h, card_vector,
    Fintype.card_congr (⟨UInt8.toFin, UInt8.ofFin, UInt8.ofFin_toFin, UInt8.toFin_ofFin⟩ :
      UInt8 ≃ Fin 256), Fintype.card_fin]
  norm_num

set_option synthInstance.maxSize 4000 in
/-- **BIP 459 with 32-byte keys and messages, `NonceGen` and 256-bit hashes is
unforgeable under AOMDL.** The nonces come from `NonceGen` with its `sk`
argument, for 32-byte values `rand'` and `rand` and any family of bijections
`mask`, such as `maskXor d` for the secret key `d` that `NonceGen` gets in the
slot: the signer's key or a key tweaked from it by a tweak that is fixed
before the game. `hash_BIP0459/sig`, `hash_BIP0459/nonce` and
`hash_BIP0459/aux` are random oracles. The first two have 256-bit outputs
that are reduced modulo `n`. The nonce coefficient hash is the BIP's.

The adversary makes at most `qh`, `qn` and `qa` queries to the three oracles
and opens at most `qs` sessions. `extra_in` is a value of any finite type
`Ex`. The forger `withStream (withAuxStream …)`, the reduction and the
collision finder sample all random oracles lazily. -/
theorem bytes_nonceGenSk_unforgeable_256 {Coins Ex : Type} [Fintype Coins] [Fintype Ex]
    [DecidableEq Ex] (N qs : ℕ)
    (A : SkAdversaryH n N Point B32 B32 B32 B32 Ex (Fin (2 ^ 256)) (Fin (2 ^ 256)) Coins)
    (e₀ : Ex) (mask : (ZMod n)ˣ → Fin qs → B32 ≃ B32) (hN : N < n) (qh qn qa : ℕ)
    (hA : ∀ c P, NBound (A c P) qa)
    (hG : ∀ c P (Aux : B32 → B32), NBound (answerG Aux (A c P)) qn)
    (hH : ∀ c P G (Aux : B32 → B32),
      HashBound (answerG (fun _ : Ex => ()) (answerG G (answerG Aux (A c P)))) qh) :
    nonceGenSkAdvantageH secp256k1X nonceCoef32 N qs (redFin (2 ^ 256)) A (redFin (2 ^ 256)) e₀
        mask ≤
      Real.sqrt ((qh + qs + 1 : ℕ) *
        (omdlAdvantage secp256k1X (2 * qs + 1)
            (reductionLazy secp256k1X nonceCoef32 N qs
              (withStream N qn (withAuxStream N qa (liftHashSk N (liftFin n_lt.le) A)))
              (2 * (qh + qs) + 1)) +
          collisionAdvantageLazy secp256k1X nonceCoef32 N qs
            (withStream N qn (withAuxStream N qa (liftHashSk N (liftFin n_lt.le) A)))
            (2 * (qh + qs)))) +
        (qh + qs + 1 : ℕ) / n + qs / (n - 1 : ℝ) +
        (qh + qs + N : ℕ) * ((((2 ^ 256 : ℕ) : ℝ) - n) / ((2 ^ 256 : ℕ) : ℝ)) +
        (qs : ℝ) ^ 2 / ((2 ^ 256 : ℕ) : ℝ) + qs * (qn / ((2 ^ 256 : ℕ) : ℝ)) +
        (2 * qs : ℕ) * ((((2 ^ 256 : ℕ) : ℝ) - (n - 1)) / ((2 ^ 256 : ℕ) : ℝ)) +
        (qs : ℝ) ^ 2 / ((2 ^ 256 : ℕ) : ℝ) + qs * (qa / ((2 ^ 256 : ℕ) : ℝ)) := by
  have h := nonceGenSk_unforgeable_fin secp256k1X nonceCoef32 N qs e₀ mask n_lt.le A hN qh qn qa
    hA hG hH
  rw [card_B32] at h
  exact h

set_option synthInstance.maxSize 4000 in
/-- **BIP 459 with 32-byte keys and messages, `NonceGen` without its `sk`
argument and 256-bit hashes is unforgeable under AOMDL.** The `rand` of
`NonceGen` is a uniform 32-byte value. `hash_BIP0459/sig` and
`hash_BIP0459/nonce` are random oracles with 256-bit outputs that are reduced
modulo `n`. The nonce coefficient hash is the BIP's. The forger `withStream`,
the reduction and the collision finder sample the random oracles lazily. -/
theorem bytes_nonceGen_unforgeable_256 {Coins Ex : Type} [Fintype Coins] [Fintype Ex]
    [DecidableEq Ex] (N qs : ℕ)
    (A : NAdversaryH n N Point B32 B32 B32 Ex (Fin (2 ^ 256)) (Fin (2 ^ 256)) Coins) (e₀ : Ex)
    (hN : N < n) (qh qn : ℕ) (hA : ∀ c P, NBound (A c P) qn)
    (hH : ∀ c P G, HashBound (answerG (fun _ : Ex => ()) (answerG G (A c P))) qh) :
    nonceGenAdvantageH secp256k1X nonceCoef32 N qs (redFin (2 ^ 256)) A (redFin (2 ^ 256)) e₀ ≤
      Real.sqrt ((qh + qs + 1 : ℕ) *
        (omdlAdvantage secp256k1X (2 * qs + 1)
            (reductionLazy secp256k1X nonceCoef32 N qs
              (withStream N qn (liftHashN N (liftFin n_lt.le) A)) (2 * (qh + qs) + 1)) +
          collisionAdvantageLazy secp256k1X nonceCoef32 N qs
            (withStream N qn (liftHashN N (liftFin n_lt.le) A)) (2 * (qh + qs)))) +
        (qh + qs + 1 : ℕ) / n + qs / (n - 1 : ℝ) +
        (qh + qs + N : ℕ) * ((((2 ^ 256 : ℕ) : ℝ) - n) / ((2 ^ 256 : ℕ) : ℝ)) +
        (qs : ℝ) ^ 2 / ((2 ^ 256 : ℕ) : ℝ) + qs * (qn / ((2 ^ 256 : ℕ) : ℝ)) +
        (2 * qs : ℕ) * ((((2 ^ 256 : ℕ) : ℝ) - (n - 1)) / ((2 ^ 256 : ℕ) : ℝ)) := by
  have h := nonceGen_unforgeable_fin secp256k1X nonceCoef32 N qs e₀ n_lt.le A hN qh qn hA hH
  rw [card_B32] at h
  exact h

/-! ## A counter in place of `rand'` -/

theorem zipXor_cancel_right : ∀ l₁ l₂ : List UInt8, l₁.length = l₂.length →
    List.zipWith (· ^^^ ·) (List.zipWith (· ^^^ ·) l₁ l₂) l₂ = l₁
  | [], [], _ => rfl
  | a :: l₁, b :: l₂, h => by
    simp only [List.zipWith_cons_cons, List.cons.injEq]
    exact ⟨by rw [UInt8.xor_assoc, UInt8.xor_self, UInt8.xor_zero],
      zipXor_cancel_right l₁ l₂ (by simpa using h)⟩
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem zipXor_cancel_left : ∀ l₁ l₂ : List UInt8, l₁.length = l₂.length →
    List.zipWith (· ^^^ ·) l₁ (List.zipWith (· ^^^ ·) l₁ l₂) = l₂
  | [], [], _ => rfl
  | a :: l₁, b :: l₂, h => by
    simp only [List.zipWith_cons_cons, List.cons.injEq]
    exact ⟨by rw [← UInt8.xor_assoc, UInt8.xor_self, UInt8.zero_xor],
      zipXor_cancel_left l₁ l₂ (by simpa using h)⟩
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- The byte-wise xor of two 32-byte arrays. -/
def xor32 (a b : B32) : B32 :=
  ⟨List.zipWith (· ^^^ ·) a.1 b.1, by rw [List.length_zipWith, a.2, b.2, min_self]⟩

/-- `bytes(x)` as a 32-byte array. -/
def ser32 (x : ZMod n) : B32 := ⟨serScalar x, length_bytes32 _⟩

/-- **The `rand` of `NonceGen` with the secret key `d` as its `sk` argument**:
`bytes(d) xor hash_BIP0459/aux(rand')`, as a bijection on the values of the
aux hash. -/
def maskXor (d : ZMod n) : B32 ≃ B32 where
  toFun a := xor32 (ser32 d) a
  invFun a := xor32 (ser32 d) a
  left_inv a := Subtype.ext (zipXor_cancel_left _ _ ((ser32 d).2.trans a.2.symm))
  right_inv a := Subtype.ext (zipXor_cancel_left _ _ ((ser32 d).2.trans a.2.symm))

/-- The signer's secret key from a `rand` and the value of the aux hash, when
`NonceGen` got the key with the tweak `τ`. -/
def unmaskXor (τ : Tweak n) (r a : B32) : Option (ZMod n)ˣ :=
  (scalar (xor32 r a).1).bind fun d =>
    if h : (d - τ.1) / τ.2 = 0 then none else some (Units.mk0 ((d - τ.1) / τ.2) h)

/-- A `rand` and the value of the aux hash give the secret key. -/
theorem unmaskXor_maskXor (τ : Tweak n) (hτ : τ.2 ≠ 0) (x : (ZMod n)ˣ) (a : B32) :
    unmaskXor τ (maskXor (τ.sk x) a) a = some x := by
  have hc : (xor32 (maskXor (τ.sk x) a) a).1 = serScalar (τ.sk x) :=
    zipXor_cancel_right _ _ ((ser32 (τ.sk x)).2.trans a.2.symm)
  have hx : (τ.sk x - τ.1) / τ.2 = x := by
    unfold Tweak.sk
    rw [add_sub_cancel_left, mul_div_cancel_left₀ _ hτ]
  have h0 : (τ.sk x - τ.1) / τ.2 ≠ 0 := by
    rw [hx]
    exact x.ne_zero
  unfold unmaskXor
  rw [hc, scalar_serScalar]
  change (if h : (τ.sk x - τ.1) / τ.2 = 0 then none else some (Units.mk0 _ h)) = some x
  simp only [h0, ↓reduceDIte]
  exact congrArg some (Units.ext hx)

set_option synthInstance.maxSize 4000 in
/-- **BIP 459 with 32-byte keys and messages, 256-bit hashes and `NonceGen`
with a counter in place of `rand'` is unforgeable under AOMDL.** For slot `k`
the signer runs `NonceGen` with the secret key `d = (τ k).sk x` and the public
32-byte value `ctr k` in place of a random value, as
`secp256k1_fullagg_nonce_gen_counter` does. The values `ctr k` are distinct.
The tweaks `τ k` are fixed before the game and have a nonzero factor, as the
tweaks of BIP 459 have. With `τ k = (0, 1)` the key is the signer's key `x`.
`rand` is `bytes(d) xor hash_BIP0459/aux(ctr k)`. `hash_BIP0459/sig`,
`hash_BIP0459/nonce` and `hash_BIP0459/aux` are random oracles, the first two
with 256-bit outputs that are reduced modulo `n`. The nonce coefficient hash
is the BIP's.

The bound has the terms of `unforgeable_sqrt_lazy_both` twice: for the
adversary, and for the forger `keyForger`, which finds the secret key when the
adversary queries the nonce hash at a `rand`. `msgs` are any `qs + 1` distinct
messages. -/
theorem bytes_nonceGenCtr_unforgeable_256 {Coins Ex : Type} [Fintype Coins] [Fintype Ex]
    [DecidableEq Ex] (N qs : ℕ)
    (A : SkAdversaryH n N Point B32 B32 B32 B32 Ex (Fin (2 ^ 256)) (Fin (2 ^ 256)) Coins)
    (e₀ : Ex) (ctr : Fin qs → B32) (hctr : Function.Injective ctr) (τ : Fin qs → Tweak n)
    (hτ : ∀ k, (τ k).2 ≠ 0) (msgs : Fin (qs + 1) → B32) (hmsgs : Function.Injective msgs)
    (hN0 : 0 < N) (hN : N < n) (qh qn qa : ℕ)
    (hA : ∀ c P, NBound (A c P) qa)
    (hG : ∀ c P (Aux : B32 → B32), NBound (answerG Aux (A c P)) qn)
    (hH : ∀ c P G (Aux : B32 → B32),
      HashBound (answerG (fun _ : Ex => ()) (answerG G (answerG Aux (A c P)))) qh) :
    nonceGenCtrAdvantageH secp256k1X nonceCoef32 N qs ctr (fun x k => maskXor ((τ k).sk x)) e₀
        (redFin (2 ^ 256)) (redFin (2 ^ 256)) A ≤
      lazyBound secp256k1X nonceCoef32 N qs qh
          (withStream N qn (withAuxStream N qa (liftHashSk N (liftFin n_lt.le) A))) +
        lazyBound secp256k1X nonceCoef32 N qs (qh + 1)
          (withStream N qn (withAuxStream N (qa + qs)
            (keyForger secp256k1X N qs (fun k => unmaskXor (τ k)) msgs ctr
              (liftHashSk N (liftFin n_lt.le) A)))) +
        (qh + qs + N : ℕ) * ((((2 ^ 256 : ℕ) : ℝ) - n) / ((2 ^ 256 : ℕ) : ℝ)) +
        (qs : ℝ) ^ 2 / ((2 ^ 256 : ℕ) : ℝ) +
        2 * ((2 * qs : ℕ) * ((((2 ^ 256 : ℕ) : ℝ) - (n - 1)) / ((2 ^ 256 : ℕ) : ℝ))) := by
  have h := nonceGenCtr_unforgeable_fin secp256k1X nonceCoef32 N qs (fun k => unmaskXor (τ k))
    msgs ctr (fun x k => maskXor ((τ k).sk x)) e₀ n_lt.le A hctr
    (fun x k a => unmaskXor_maskXor (τ k) (hτ k) x a) hmsgs hN0 hN qh qn qa hA hG hH
  rw [card_B32] at h
  exact h

/-! ## The instance runs the byte-level algorithms -/

/-- A list of 32-byte pairs as a list of byte array pairs. -/
def vals (L : List (B32 × B32)) : List (Bytes × Bytes) := L.map fun e => (e.1.1, e.2.1)

/-- Hash functions on 32-byte arrays that agree with hash functions on byte
arrays. -/
def Agree (H : Hashes n Point B32 B32) (Hb : Hashes n Point Bytes Bytes) : Prop :=
  (∀ R₁ R₂ items, H.nonceCoef R₁ R₂ items =
      Hb.nonceCoef R₁ R₂ (items.map fun t => (t.1.1, t.2.1.1, t.2.2))) ∧
    ∀ L r e, H.sig L r e = Hb.sig (vals L) r.1 (e.1.1, e.2.1)

theorem keySum_val {H : Hashes n Point B32 B32} {Hb : Hashes n Point Bytes Bytes}
    (h : Agree H Hb) (L : List (B32 × B32)) (r : B32) :
    keySum secp256k1X.ops H L r = keySum specOps Hb (vals L) r.1 := by
  unfold keySum vals
  rw [List.map_map]
  congr 1
  refine List.map_congr_left fun e _ => ?_
  simp only [Function.comp_apply, h.2]
  rfl

/-- **`Verify` of the instance is `Verify` on the byte arrays.** -/
theorem verify_val {H : Hashes n Point B32 B32} {Hb : Hashes n Point Bytes Bytes}
    (h : Agree H Hb) (L : List (B32 × B32)) (sig : B32 × ZMod n) :
    verify secp256k1X.ops H L sig = verify specOps Hb (vals L) (sig.1.1, sig.2) := by
  unfold verify
  simp only [keySum_val h]
  have hl : secp256k1X.ops.liftX sig.1 = specOps.liftX sig.1.1 := rfl
  rw [hl]
  cases specOps.liftX sig.1.1 with
  | none => rfl
  | some R =>
    simp only [vals, List.isEmpty_map, List.all_map]
    rfl

theorem coefItems_vals (pm : List (B32 × B32)) (pubs : List (PubNonce Point)) :
    coefItems (vals pm) pubs = (coefItems pm pubs).map fun t => (t.1.1, t.2.1.1, t.2.2) := by
  induction pm generalizing pubs with
  | nil => simp [coefItems, vals]
  | cons e pm ih =>
    cases pubs with
    | nil => simp [coefItems, vals]
    | cons N pubs =>
      have := ih pubs
      simp only [coefItems, vals, List.map_cons, List.zipWith_cons_cons, List.cons.injEq,
        true_and] at this ⊢
      exact this

theorem getSessionValues_val {H : Hashes n Point B32 B32} {Hb : Hashes n Point Bytes Bytes}
    (h : Agree H Hb) (agg : PubNonce Point) (pm : List (B32 × B32))
    (pubs : List (PubNonce Point)) :
    getSessionValues secp256k1X.ops H agg pm pubs =
      getSessionValues specOps Hb agg (vals pm) pubs := by
  unfold getSessionValues
  simp only [h.1, ← coefItems_vals]
  simp only [vals, List.map_eq_nil_iff, List.length_map]
  rfl

/-- **`Sign` of the instance is `Sign` on the byte arrays.** -/
theorem sign_val {H : Hashes n Point B32 B32} {Hb : Hashes n Point Bytes Bytes}
    (h : Agree H Hb) (secnonce : SecNonce n) (sk : ZMod n) (m : B32) (agg : PubNonce Point)
    (pm : List (B32 × B32)) (pubs : List (PubNonce Point)) :
    sign secp256k1X.ops H secnonce sk m agg pm pubs =
      sign specOps Hb secnonce sk m.1 agg (vals pm) pubs := by
  rw [sign_eq, sign_eq]
  have hpre : signPre secp256k1X.ops H secnonce sk m agg pm pubs =
      signPre specOps Hb secnonce sk m.1 agg (vals pm) pubs := by
    unfold signPre
    simp only [getSessionValues_val h]
    have hm : ∀ j : ℕ, (pm[j]? = some (secp256k1X.ops.x (secp256k1X.ops.mulG sk), m)) ↔
        ((vals pm)[j]? = some (specOps.x (specOps.mulG sk), m.1)) := by
      intro j
      simp only [vals, List.getElem?_map]
      cases pm[j]? with
      | none => simp
      | some e =>
        simp only [Option.map_some, Option.some.injEq, Prod.ext_iff]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨congrArg Subtype.val h1, congrArg Subtype.val h2⟩
        · rintro ⟨h1, h2⟩
          exact ⟨Subtype.ext h1, Subtype.ext h2⟩
    have hG : secp256k1X.ops.mulG = specOps.mulG := rfl
    simp only [hG] at hm ⊢
    split_ifs with h0
    · rfl
    · rcases matchIdxs pubs (specOps.mulG secnonce.2) with _ | ⟨j, _ | ⟨j', l⟩⟩
      · rfl
      · simp only [hm j]
      · rfl
  rw [hpre]
  cases signPre specOps Hb secnonce sk m.1 agg (vals pm) pubs with
  | none => rfl
  | some Rb =>
    simp only [Option.map_some, h.2]
    rfl

end Dahlias.Security
