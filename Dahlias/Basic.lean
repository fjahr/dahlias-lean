import Taproot.Curve

/-!
# BIP 459: DahLIAS fully aggregated signatures

The algorithms `NonceGen`, `NonceAgg`, `GetSessionValues`, `Sign`, `SigAgg`,
`PartialSigVerify`, `Verify` and the two key tweaks of BIP 459.

Modelling choices:
* The algorithms are written against `Ops`, the handful of curve operations
  BIP 459 uses. `Curve.ops` gives the operations of a `Taproot.Curve`, which
  is what the theorems are about. `Dahlias.Bytes` supplies a second, fast
  implementation for secp256k1 and proves it equal, so that the test vectors
  run through the same definitions.
* Public keys and the `R` of a signature are x-coordinates (`X`). Nonces are
  points (`E`). A point given as `0` stands for an encoding that `cpoint`
  rejects: `cpoint` never returns the point at infinity, so the algorithms
  fail on `0` where the BIP parses the corresponding bytes.
* Scalars are elements of `ZMod n`. Byte encodings, length checks and range
  checks are in `Dahlias.Bytes`.
* The tagged hashes are arbitrary functions, bundled in `Hashes`.
  `nonceCoef R₁ R₂ [(pk₀, m₀, R₂,₀), …]` is
  `int(hash_BIP0459/noncecoef(cbytes(R₁) ‖ cbytes(R₂) ‖ pk₀ ‖ m₀ ‖ cbytes(R₂,₀) ‖ …)) mod n`
  and `sig [(pk₀, m₀), …] r (pk, m)` is
  `int(hash_BIP0459/sig(pk₀ ‖ m₀ ‖ … ‖ r ‖ pk ‖ m)) mod n`.
  All fields have fixed lengths, so these encodings are injective
  (`Dahlias.Bytes`).
-/

namespace Dahlias

open Taproot

/-- The curve operations BIP 459 uses. -/
structure Ops (n : ℕ) (E X : Type*) where
  /-- `k ↦ k⋅G`. -/
  mulG : ZMod n → E
  /-- `(k, P) ↦ k⋅P`. -/
  smul : ZMod n → E → E
  /-- `x(P)`. -/
  x : E → X
  /-- `has_even_y(P)`. -/
  hasEvenY : E → Bool
  /-- `lift_x`. -/
  liftX : X → Option E

/-- The operations of a `Taproot.Curve`. -/
def _root_.Taproot.Curve.ops {n : ℕ} [Fact n.Prime] {E X : Type*} [AddCommGroup E]
    (C : Curve n E X) : Ops n E X where
  mulG := C.mulG
  smul k P := k.val • P
  x := C.x
  hasEvenY := C.hasEvenY
  liftX := C.liftX

/-- The two hash functions of the signing protocol. -/
structure Hashes (n : ℕ) (E X M : Type*) where
  /-- `hash_BIP0459/noncecoef`, on `R₁`, `R₂` and the `(pkᵢ, mᵢ, R₂,ᵢ)`. -/
  nonceCoef : E → E → List (X × M × E) → ZMod n
  /-- `hash_BIP0459/sig`, on the list `L`, `xbytes(R)` and the signer's `(pk, m)`. -/
  sig : List (X × M) → X → X × M → ZMod n

variable {n : ℕ} {E X M : Type*} [AddCommGroup E] [DecidableEq E] [DecidableEq X] [DecidableEq M]

/-- A public nonce `(R₁, R₂)`; also the type of aggregate nonces. -/
abbrev PubNonce (E : Type*) := E × E

/-- A secret nonce `(r₁, r₂)`. -/
abbrev SecNonce (n : ℕ) := ZMod n × ZMod n

namespace Ops

variable (O : Ops n E X)

/-- `d` if `d⋅G` has an even y, otherwise `n - d`. -/
def evenScalar (d : ZMod n) : ZMod n := if O.hasEvenY (O.mulG d) then d else -d

/-- `P` if `has_even_y(R)`, otherwise `-P`: multiplication by the `e` of
`Sign` and `PartialSigVerify`. -/
def signOf (R P : E) : E := if O.hasEvenY R then P else -P

end Ops

/-! ## Key tweaking -/

/-- `TweakSK`: plain (`sk + t`) or x-only (`d + t`, with `d` the even-y
normalization of `sk`). Fails if the result is zero. -/
def tweakSK (O : Ops n E X) (sk t : ZMod n) (xonly : Bool) : Option (ZMod n) :=
  let d := if xonly then O.evenScalar sk else sk
  if d + t = 0 then none else some (d + t)

/-- `TweakPK`: plain (`P + t⋅G`) or x-only (`lift_x(x(P)) + t⋅G`). Fails if
the result is the point at infinity. -/
def tweakPK (O : Ops n E X) (P : E) (t : ZMod n) (xonly : Bool) : Option E :=
  let P' := if xonly && !O.hasEvenY P then -P else P
  if P' + O.mulG t = 0 then none else some (P' + O.mulG t)

/-! ## Nonces -/

/-- `NonceGen`, from the two derived scalars
`rᵢ = int(hash_BIP0459/nonce(rand ‖ extra_in ‖ i)) mod n`. -/
def nonceGen (O : Ops n E X) (r₁ r₂ : ZMod n) : Option (SecNonce n × PubNonce E) :=
  if r₁ = 0 ∨ r₂ = 0 then none else some ((r₁, r₂), (O.mulG r₁, O.mulG r₂))

/-- `NonceAgg`. -/
def nonceAgg (pubnonces : List (PubNonce E)) : Option (PubNonce E) :=
  let R₁ := (pubnonces.map Prod.fst).sum
  let R₂ := (pubnonces.map Prod.snd).sum
  if pubnonces = [] ∨ (∃ N ∈ pubnonces, N.1 = 0 ∨ N.2 = 0) ∨ R₁ = 0 ∨ R₂ = 0 then none
  else some (R₁, R₂)

/-- The `(pkᵢ, mᵢ, R₂,ᵢ)` that enter the nonce coefficient. -/
def coefItems (pm : List (X × M)) (pubnonces : List (PubNonce E)) : List (X × M × E) :=
  List.zipWith (fun pkm N => (pkm.1, pkm.2, N.2)) pm pubnonces

/-- `GetSessionValues`, returning `(R, b)`. Only the second halves of the
public nonces are parsed. -/
def getSessionValues (O : Ops n E X) (H : Hashes n E X M) (agg : PubNonce E)
    (pm : List (X × M)) (pubnonces : List (PubNonce E)) : Option (E × ZMod n) :=
  if pm = [] ∨ pm.length ≠ pubnonces.length ∨ agg.1 = 0 ∨ agg.2 = 0 ∨
      (∃ N ∈ pubnonces, N.2 = 0) then none
  else
    let b := H.nonceCoef agg.1 agg.2 (coefItems pm pubnonces)
    let R := agg.1 + O.smul b agg.2
    if R = 0 then none else some (R, b)

/-! ## Signing -/

/-- The indices `j` with `R₂,ⱼ = R₂`. -/
def matchIdxs (pubnonces : List (PubNonce E)) (R₂ : E) : List ℕ :=
  (List.range pubnonces.length).filter fun j => (pubnonces[j]?).map Prod.snd = some R₂

/-- `Sign`. -/
def sign (O : Ops n E X) (H : Hashes n E X M) (secnonce : SecNonce n) (sk : ZMod n) (m : M)
    (agg : PubNonce E) (pm : List (X × M)) (pubnonces : List (PubNonce E)) : Option (ZMod n) :=
  let (r₁, r₂) := secnonce
  if r₁ = 0 ∨ r₂ = 0 ∨ sk = 0 then none else
  let P := O.mulG sk
  match matchIdxs pubnonces (O.mulG r₂) with
  | [j] =>
    if pm[j]? = some (O.x P, m) then
      (getSessionValues O H agg pm pubnonces).map fun (R, b) =>
        let k := r₁ + b * r₂
        let c := H.sig pm (O.x R) (O.x P, m)
        (if O.hasEvenY R then k else -k) + c * O.evenScalar sk
    else none
  | _ => none

/-- `SigAgg`, returning `(xbytes(R), s)`. -/
def sigAgg (O : Ops n E X) (H : Hashes n E X M) (agg : PubNonce E) (pm : List (X × M))
    (pubnonces : List (PubNonce E)) (psigs : List (ZMod n)) : Option (X × ZMod n) :=
  if psigs.length ≠ pm.length then none else
  (getSessionValues O H agg pm pubnonces).map fun (R, _) => (O.x R, psigs.sum)

/-- `PartialSigVerify`. -/
def partialSigVerify (O : Ops n E X) (H : Hashes n E X M) (psig : ZMod n) (pm : List (X × M))
    (pubnonces : List (PubNonce E)) (i : ℕ) : Bool :=
  match pm[i]?, pubnonces[i]? with
  | some pkm, some N =>
    if N.1 = 0 ∨ N.2 = 0 then false else
    match O.liftX pkm.1, (nonceAgg pubnonces).bind (getSessionValues O H · pm pubnonces) with
    | some P, some (R, b) =>
      let c := H.sig pm (O.x R) pkm
      decide (O.mulG psig = O.signOf R (N.1 + O.smul b N.2) + O.smul c P)
    | _, _ => false
  | _, _ => false

/-! ## Verification -/

/-- `c₀⋅P₀ + … + c_{u-1}⋅P_{u-1}`, with a failed `lift_x` read as `0` (the
verifier checks the lifts separately). -/
def keySum (O : Ops n E X) (H : Hashes n E X M) (pm : List (X × M)) (r : X) : E :=
  (pm.map fun pkm => O.smul (H.sig pm r pkm) ((O.liftX pkm.1).getD 0)).sum

/-- `Verify`, for the signature `(r, s)`. -/
def verify (O : Ops n E X) (H : Hashes n E X M) (pm : List (X × M)) (sig : X × ZMod n) : Bool :=
  match O.liftX sig.1 with
  | none => false
  | some R =>
    !pm.isEmpty && pm.all (fun pkm => (O.liftX pkm.1).isSome) &&
      decide (O.mulG sig.2 = R + keySum O H pm sig.1)

end Dahlias
