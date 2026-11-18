import Dahlias.Bytes
import Dahlias.VectorData

/-!
# The BIP 459 test vectors

Every row of the seven vector files of `bip-0459/vectors`, checked the way
`bip-0459/run_test_vectors.py` checks them. The rows are evaluated by compiled
code (`native_decide`) through `fastOps`, which is proven equal to `specOps`.
No theorem outside this file depends on them.
-/

namespace Dahlias.Vectors

open Taproot Taproot.Secp256k1 Taproot.BIP340Vectors Dahlias.Bytes

set_option linter.style.native false

/-- A `;`-separated list of hex strings. -/
def hexList (s : String) : List Bytes :=
  if s.isEmpty then [] else (s.splitOn ";").map hex

def optHex (s : String) : Option Bytes := if s.isEmpty then none else some (hex s)

variable (O : Ops n Point Bytes)

def checkNonceGen : List String → Bool
  | [_, rand, sk, extraIn, secnonce, pubnonce, _] =>
    Bytes.nonceGen O (hex rand) (optHex sk) (hex extraIn) == some (hex secnonce, hex pubnonce)
  | _ => false

def checkNonceAgg : List String → Bool
  | [_, pubnonces, result, aggnonce, _] =>
    Bytes.nonceAgg O (hexList pubnonces) == if result == "TRUE" then some (hex aggnonce) else none
  | _ => false

/-- A whole honest session: public keys and nonces are derived from the secret
ones, then `NonceAgg`, `Sign` for every signer, `PartialSigVerify` for every
signer, `SigAgg` and `Verify`. -/
def checkSign : List String → Bool
  | [_, sks, msgs, secnonces, aggnonce, psigs, sig, _] =>
    let sks := hexList sks
    let msgs := hexList msgs
    let secnonces := hexList secnonces
    let pks := sks.map fun sk => ((scalar sk).map fun d => O.x (O.mulG d)).getD []
    let pubnonces := secnonces.map fun sn =>
      match scalar (sn.take 32), scalar (sn.drop 32) with
      | some r₁, some r₂ => serNonce (O.mulG r₁, O.mulG r₂)
      | _, _ => []
    let psigs' := (List.range sks.length).map fun i =>
      Bytes.sign O (secnonces.getD i []) (sks.getD i []) (msgs.getD i []) (hex aggnonce)
        pks msgs pubnonces
    Bytes.nonceAgg O pubnonces == some (hex aggnonce) &&
      psigs' == (hexList psigs).map some &&
      (List.range sks.length).all (fun i =>
        Bytes.partialSigVerify O ((hexList psigs).getD i []) pks msgs pubnonces i) &&
      Bytes.sigAgg O (hex aggnonce) pks msgs pubnonces (hexList psigs) == some (hex sig) &&
      Bytes.verify O pks msgs (hex sig)
  | _ => false

def checkSignError : List String → Bool
  | [_, sk, m, secnonce, aggnonce, pks, msgs, pubnonces, _] =>
    Bytes.sign O (hex secnonce) (hex sk) (hex m) (hex aggnonce) (hexList pks) (hexList msgs)
      (hexList pubnonces) == none
  | _ => false

def checkPartialSigVerify : List String → Bool
  | [_, i, psig, pks, msgs, pubnonces, result, _] =>
    Bytes.partialSigVerify O (hex psig) (hexList pks) (hexList msgs) (hexList pubnonces)
      i.toNat! == (result == "TRUE")
  | _ => false

def checkVerify : List String → Bool
  | [_, pks, msgs, sig, result, _] =>
    Bytes.verify O (hexList pks) (hexList msgs) (hex sig) == (result == "TRUE")
  | _ => false

def checkTweak : List String → Bool
  | [_, sk, t, xonly, result, sk', pk', _] =>
    let xonly := xonly == "TRUE"
    if result == "TRUE" then
      Bytes.tweakSK O (hex sk) (hex t) xonly == some (hex sk') &&
        Bytes.tweakPKOfSK O (hex sk) (hex t) xonly == some (hex pk')
    else
      Bytes.tweakSK O (hex sk) (hex t) xonly == none &&
        Bytes.tweakPKOfSK O (hex sk) (hex t) xonly == none
  | _ => false

theorem nonceGen_vectors : nonceGenRows.all (checkNonceGen specOps) = true := by
  rw [← fastOps_eq]; native_decide

theorem nonceAgg_vectors : nonceAggRows.all (checkNonceAgg specOps) = true := by
  rw [← fastOps_eq]; native_decide

theorem sign_vectors : signRows.all (checkSign specOps) = true := by
  rw [← fastOps_eq]; native_decide

theorem signError_vectors : signErrorRows.all (checkSignError specOps) = true := by
  rw [← fastOps_eq]; native_decide

theorem partialSigVerify_vectors :
    partialSigVerifyRows.all (checkPartialSigVerify specOps) = true := by
  rw [← fastOps_eq]; native_decide

theorem verify_vectors : verifyRows.all (checkVerify specOps) = true := by
  rw [← fastOps_eq]; native_decide

theorem tweak_vectors : tweakRows.all (checkTweak specOps) = true := by
  rw [← fastOps_eq]; native_decide

end Dahlias.Vectors
