import Dahlias.Unforgeability
import Taproot.Secp256k1

/-!
# Unforgeability of BIP 459 on secp256k1

`secp256k1_unforgeable` is `unforgeable` for the curve secp256k1, with public
keys and the `R` of a signature as x-coordinates in the field (their 32-byte
encoding is injective) and messages from any finite type, such as the
32-byte arrays of BIP 459.

With finite types of public keys and messages, the inputs of the challenge
hash for lists of at most `N` entries form a finite type, which is what the
random oracle of `Dahlias.Security` needs.
-/

namespace Dahlias.Security

open Taproot Taproot.Secp256k1

/-- Lists of bounded length over finite types form a finite type. -/
noncomputable instance instFintypeBList (N : ℕ) (X M : Type) [Finite X] [Finite M] :
    Fintype (BList N X M) :=
  haveI : Finite (BList N X M) := (List.finite_length_le (X × M) N).to_subtype
  Fintype.ofFinite _

/-- The challenge hash has finitely many inputs. -/
noncomputable instance instFintypeSigIn (N : ℕ) (X M : Type) [Fintype X] [Fintype M] :
    Fintype (SigIn N X M) :=
  instFintypeProd _ _

/-- **BIP 459 on secp256k1 is unforgeable under AOMDL**, with the challenge hash
as a random oracle and a collision resistant nonce coefficient hash. -/
theorem secp256k1_unforgeable {M Coins : Type} [Fintype M] [DecidableEq M] [Fintype Coins]
    (nonceCoef : Point → Point → List (F × M × Point) → ZMod n) (N qs : ℕ)
    (A : Adversary n N Point F M Coins) (hN : N < n) (qh : ℕ)
    (hA : ∀ coins P, HashBound (A coins P) qh) :
    forgeAdvantage secp256k1 nonceCoef N qs A *
        (forgeAdvantage secp256k1 nonceCoef N qs A / (qh + qs + 1 : ℕ) - 1 / n) ≤
      omdlAdvantage secp256k1 (2 * qs + 1) (reduction secp256k1 nonceCoef N qs A) +
        collisionAdvantage secp256k1 nonceCoef N qs A :=
  unforgeable secp256k1 nonceCoef N qs A hN qh hA

end Dahlias.Security
