import Dahlias.Basic
import Dahlias.OrderG
import Taproot.BIP340Vectors

/-!
# BIP 459 on bytes

The algorithms of `Dahlias.Basic` on secp256k1 with BIP 459's byte encodings,
length checks, range checks and SHA-256 tagged hashes. As in the reference
implementation, every failure is `none` or `false`.

Public keys, messages and the `R` of a signature stay byte arrays here: the
model is instantiated with `X = M = Bytes`, and `lift_x` rejects arrays that
are not 32 bytes or encode a value `≥ p`. This matters because `Sign` hashes
the other signers' public keys without ever decoding them.

`specOps` are the curve operations as specified. `fastOps` computes the same
operations by double-and-add and fast square roots and is proven equal, so
that the algorithms can be evaluated.
-/

namespace Dahlias.Bytes

open Taproot Taproot.Secp256k1 Taproot.BIP340Vectors

/-- `xbytes(P)`. -/
def xbytes (P : Point) : Bytes := bytes32 (xCoord P).val

/-- The secp256k1 operations of BIP 459, on 32-byte x-coordinates. -/
def specOps : Ops n Point Bytes where
  mulG := secp256k1F.mulG
  smul k P := k.val • P
  x := xbytes
  hasEvenY := hasEvenY
  liftX b := if b.length = 32 ∧ toNatBE b < p then liftX (toNatBE b : F) else none

/-- `specOps`, computed by double-and-add and fast square roots. -/
def fastOps : Ops n Point Bytes where
  mulG := mulGFast
  smul k P := smulDA k.val P
  x := xbytes
  hasEvenY := hasEvenY
  liftX b := if b.length = 32 ∧ toNatBE b < p then liftXFast (toNatBE b : F) else none

theorem mulGFast_eq_mulG (k : ZMod n) : mulGFast k = secp256k1F.mulG k := by
  rw [mulGFast, smulDA_eq, Curve.mulG_eq_val_smul]
  rfl

theorem fastOps_eq : fastOps = specOps := by
  simp only [fastOps, specOps, liftXFast_eq, smulDA_eq]
  congr 1
  funext k
  exact mulGFast_eq_mulG k

/-! ## Encodings -/

/-- `cbytes(P)`. -/
def cbytes (P : Point) : Bytes := (if hasEvenY P then 2 else 3) :: xbytes P

/-- `cpoint(b)`. -/
def cpoint (O : Ops n Point Bytes) (b : Bytes) : Option Point :=
  match b with
  | 2 :: x => O.liftX x
  | 3 :: x => (O.liftX x).map (- ·)
  | _ => none

/-- A 66-byte public or aggregate nonce as two points, with `0` for a half
that `cpoint` rejects (see `Dahlias.Basic`). -/
def parseNonce (O : Ops n Point Bytes) (b : Bytes) : PubNonce Point :=
  if b.length = 66 then ((cpoint O (b.take 33)).getD 0, (cpoint O (b.drop 33)).getD 0) else (0, 0)

def serNonce (N : PubNonce Point) : Bytes := cbytes N.1 ++ cbytes N.2

/-- `int(b)` for a 32-byte array, failing if the value is `≥ n`. -/
def scalar (b : Bytes) : Option (ZMod n) :=
  if b.length = 32 ∧ toNatBE b < n then some (toNatBE b : ZMod n) else none

/-- `int(b) mod n`. -/
def scalarWrap (b : Bytes) : ZMod n := (toNatBE b : ZMod n)

def serScalar (s : ZMod n) : Bytes := bytes32 s.val

def is32 (b : Bytes) : Bool := b.length == 32

/-- The tagged hashes of the signing protocol. -/
def hashes : Hashes n Point Bytes Bytes where
  nonceCoef R₁ R₂ items := scalarWrap (taggedHash "BIP0459/noncecoef"
    (cbytes R₁ ++ cbytes R₂ ++ items.flatMap fun it => it.1 ++ it.2.1 ++ cbytes it.2.2))
  sig pm r pkm := scalarWrap (taggedHash "BIP0459/sig"
    (pm.flatMap (fun x => x.1 ++ x.2) ++ r ++ pkm.1 ++ pkm.2))

/-- The common input conditions: the arrays have the same nonzero length,
public keys and messages are 32 bytes. -/
def wellFormed (pks msgs : List Bytes) (u : ℕ) : Bool :=
  decide (0 < u) && pks.length == u && msgs.length == u && pks.all is32 && msgs.all is32

/-! ## The algorithms -/

variable (O : Ops n Point Bytes)

/-- `NonceGen` with the random value `rand'` as an argument, returning
`(secnonce, pubnonce)`. -/
def nonceGen (rand' : Bytes) (sk : Option Bytes) (extraIn : Bytes) : Option (Bytes × Bytes) :=
  let rand := match sk with
    | some sk => List.zipWith (· ^^^ ·) sk (taggedHash "BIP0459/aux" rand')
    | none => rand'
  let r (i : UInt8) := scalarWrap (taggedHash "BIP0459/nonce" (rand ++ extraIn ++ [i]))
  (Dahlias.nonceGen O (r 0) (r 1)).map fun (sec, pub) =>
    (serScalar sec.1 ++ serScalar sec.2, serNonce pub)

/-- `NonceAgg`. -/
def nonceAgg (pubnonces : List Bytes) : Option Bytes :=
  (Dahlias.nonceAgg (pubnonces.map (parseNonce O))).map serNonce

/-- `Sign`. -/
def sign (secnonce sk m aggnonce : Bytes) (pks msgs pubnonces : List Bytes) : Option Bytes :=
  if wellFormed pks msgs pubnonces.length && is32 m && secnonce.length == 64 then
    match scalar (secnonce.take 32), scalar (secnonce.drop 32), scalar sk with
    | some r₁, some r₂, some d =>
      (Dahlias.sign O hashes (r₁, r₂) d m (parseNonce O aggnonce) (pks.zip msgs)
        (pubnonces.map (parseNonce O))).map serScalar
    | _, _, _ => none
  else none

/-- `SigAgg`. -/
def sigAgg (aggnonce : Bytes) (pks msgs pubnonces psigs : List Bytes) : Option Bytes :=
  if wellFormed pks msgs pubnonces.length && psigs.all (fun b => (scalar b).isSome) then
    (Dahlias.sigAgg O hashes (parseNonce O aggnonce) (pks.zip msgs)
      (pubnonces.map (parseNonce O)) (psigs.map fun b => (scalar b).getD 0)).map
        fun (r, s) => r ++ serScalar s
  else none

/-- `PartialSigVerify`. -/
def partialSigVerify (psig : Bytes) (pks msgs pubnonces : List Bytes) (i : ℕ) : Bool :=
  wellFormed pks msgs pubnonces.length &&
    match scalar psig with
    | some s => Dahlias.partialSigVerify O hashes s (pks.zip msgs) (pubnonces.map (parseNonce O)) i
    | none => false

/-- `Verify`. -/
def verify (pks msgs : List Bytes) (sig : Bytes) : Bool :=
  wellFormed pks msgs pks.length && sig.length == 64 &&
    match scalar (sig.drop 32) with
    | some s => Dahlias.verify O hashes (pks.zip msgs) (sig.take 32, s)
    | none => false

/-- `TweakSK` on a 32-byte secret key and tweak. -/
def tweakSK (sk t : Bytes) (xonly : Bool) : Option Bytes :=
  match scalar sk, scalar t with
  | some d, some t => if d = 0 then none else (Dahlias.tweakSK O d t xonly).map serScalar
  | _, _ => none

/-- `TweakPK` on the public key point of the 32-byte secret key `sk`,
returning `cbytes` of the tweaked point. -/
def tweakPKOfSK (sk t : Bytes) (xonly : Bool) : Option Bytes :=
  match scalar sk, scalar t with
  | some d, some t => if d = 0 then none else (Dahlias.tweakPK O (O.mulG d) t xonly).map cbytes
  | _, _ => none

end Dahlias.Bytes
