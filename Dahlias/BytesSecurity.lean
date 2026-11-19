import Dahlias.Secp256k1
import Dahlias.BytesCorrectness
import Dahlias.Proofs.Game
import Dahlias.Hashed

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
