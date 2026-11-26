import Dahlias.Security
import Dahlias.Correctness

/-!
# BIP 459's tweaks are tweaks of the security game

The game of `Dahlias.Security` lets the adversary choose a tweak `(α, β)` with
`β ≠ 0`, the affine map `x ↦ α + β⋅x` on secret keys. `tweakSK_affine`: a
plain or x-only tweak of BIP 459 by `t` is the affine map `(t, β)` with
`β = 1` or `β = -1`, and `β` can be read off the public key point.
`Tweak.comp`: affine maps compose, so sequences of BIP 459 tweaks, such as a
BIP 32 derivation followed by a Taproot tweak, are covered as well.

The last section is about the tweaks `(α, β)` and `(-α, -β)`. They give the
same x-only public key and the same partial signatures, which is why the game
records tweaked keys and not tweaks, as the paper's game does.
-/

set_option linter.unusedSectionVars false

namespace Dahlias.Security

open Taproot

variable {n : ℕ} [Fact n.Prime] {E X : Type} [AddCommGroup E] (C : Curve n E X)

/-- The `β` of a BIP 459 tweak of the key with public key point `P`. -/
def bipTweakSign (P : E) (xonly : Bool) : ZMod n := if xonly && !C.hasEvenY P then -1 else 1

theorem bipTweakSign_ne_zero (P : E) (xonly : Bool) : bipTweakSign C P xonly ≠ 0 := by
  unfold bipTweakSign
  split_ifs <;> simp

/-- **A BIP 459 tweak is an affine tweak** with `β = ±1`. -/
theorem tweakSK_affine (sk t : ZMod n) (xonly : Bool) {sk' : ZMod n}
    (h : tweakSK C.ops sk t xonly = some sk') :
    sk' = Tweak.sk (t, bipTweakSign C (C.mulG sk) xonly) sk := by
  cases xonly
  · simp only [tweakSK, Bool.false_eq_true, ↓reduceIte] at h
    split_ifs at h
    cases Option.some.inj h
    simp [Tweak.sk, bipTweakSign, add_comm]
  · simp only [tweakSK, ↓reduceIte] at h
    split_ifs at h
    cases Option.some.inj h
    simp only [Tweak.sk, bipTweakSign, Ops.evenScalar, ops_hasEvenY, ops_mulG]
    by_cases he : C.hasEvenY (C.mulG sk) = true <;> simp [he, add_comm]

/-- The composition of two tweaks: first `τ`, then `τ'`. -/
def Tweak.comp (τ' τ : Tweak n) : Tweak n := (τ'.1 + τ'.2 * τ.1, τ'.2 * τ.2)

theorem Tweak.sk_comp (τ' τ : Tweak n) (x : ZMod n) :
    (Tweak.comp τ' τ).sk x = τ'.sk (τ.sk x) := by
  simp only [Tweak.comp, Tweak.sk]
  ring

theorem Tweak.comp_snd_ne_zero {τ' τ : Tweak n} (h' : τ'.2 ≠ 0) (h : τ.2 ≠ 0) :
    (Tweak.comp τ' τ).2 ≠ 0 :=
  mul_ne_zero h' h

/-! ## Two tweaks with one x-only key

The tweaks `(α, β)` and `(-α, -β)` give the secret keys `d` and `-d`. These
have the same x-only public key, and `Sign` returns the same partial signature
for both, because it signs with the key of the point with the even
y-coordinate. So the signer of the game cannot tell the two tweaks apart
(`challengerG_close_neg`).

The paper's game records the tweak of every signing query and accepts a forgery
under any tweak that is not recorded. Its proof needs a property of the
tweaking scheme that it calls collision-extractability: two different tweaks
with the same tweaked public key reveal the secret key. With x-only public
keys there is no such extraction (`not_collisionExtractable`), and the answer
to a signing query with the tweak `τ` would count as a forgery under `τ.neg`.
The game of `Dahlias.Security` records the tweaked x-only key instead. -/

/-- The tweak with the negated secret key, `x ↦ -(α + β⋅x)`. -/
def Tweak.neg (τ : Tweak n) : Tweak n := (-τ.1, -τ.2)

theorem Tweak.sk_neg (τ : Tweak n) (x : ZMod n) : τ.neg.sk x = -τ.sk x := by
  simp only [Tweak.neg, Tweak.sk]
  ring

theorem Tweak.neg_snd_ne_zero {τ : Tweak n} : τ.neg.2 ≠ 0 ↔ τ.2 ≠ 0 := by
  simp [Tweak.neg]

/-- The two tweaks are different, unless `n = 2`. -/
theorem Tweak.neg_ne (h2 : (2 : ZMod n) ≠ 0) {τ : Tweak n} (hτ : τ.2 ≠ 0) : τ.neg ≠ τ := by
  intro h
  have h1 : -τ.2 = τ.2 := congrArg Prod.snd h
  have h3 : (2 : ZMod n) * τ.2 = 0 := by linear_combination (-1 : ZMod n) * h1
  exact (mul_eq_zero.mp h3).elim h2 hτ

/-- **Both tweaks give the same x-only public key.** -/
theorem Tweak.xonly_neg (τ : Tweak n) (x : ZMod n) :
    C.x (C.mulG (τ.neg.sk x)) = C.x (C.mulG (τ.sk x)) := by
  rw [Tweak.sk_neg, map_neg, C.x_neg]

/-- The even-y normalization of `-d` is the one of `d`. -/
theorem evenScalar_neg {d : ZMod n} (hd : d ≠ 0) : C.evenScalar (-d) = C.evenScalar d := by
  unfold Curve.evenScalar
  rw [map_neg, C.hasEvenY_neg _ (C.mulG_ne_zero hd)]
  cases C.hasEvenY (C.mulG d) <;> simp

variable {M : Type} [DecidableEq E] [DecidableEq X] [DecidableEq M]

/-- **`Sign` returns the same partial signature for the secret keys `d` and
`-d`.** -/
theorem sign_neg (H : Hashes n E X M) (secnonce : SecNonce n) (d : ZMod n) (m : M)
    (agg : PubNonce E) (pm : List (X × M)) (pubnonces : List (PubNonce E)) :
    sign C.ops H secnonce (-d) m agg pm pubnonces = sign C.ops H secnonce d m agg pm pubnonces := by
  by_cases hd : d = 0
  · simp [hd]
  · simp only [sign, neg_eq_zero, ops_mulG, map_neg, ops_x, C.x_neg, ops_evenScalar,
      evenScalar_neg C hd]
    rfl

/-- **The signer of the game cannot tell the two tweaks apart.** A signing
query with the tweak `τ.neg` gets the answer of the query with `τ` and leaves
the signer in the same state. -/
theorem challengerG_close_neg (der : Bool) (nonceCoef : E → E → List (X × M × E) → ZMod n)
    (N qs : ℕ) (x : ZMod n) (nonces : Fin qs → SecNonce n) (T : SigIn N X M → ZMod n) (k : ℕ)
    (τ : Tweak n) (m : M) (agg : PubNonce E) (pm : List (X × M)) (pubnonces : List (PubNonce E))
    (st : SignerState X M) :
    challengerG der C nonceCoef N qs x nonces T (.close k τ.neg m agg pm pubnonces) st =
      challengerG der C nonceCoef N qs x nonces T (.close k τ m agg pm pubnonces) st := by
  simp only [challengerG, Tweak.neg_snd_ne_zero, Tweak.sk_neg, sign_neg, map_neg, C.x_neg]
  rfl

/-- **Collision-extractability fails for x-only public keys.** No function
computes a nonzero secret key from two different tweaks with the same tweaked
x-only public key: `τ` and `τ.neg` have the same key whatever the secret key
is. The paper's Definition 5 asks for such a function (property P-3), and
its tweaking scheme, with group elements as public keys, has one. -/
theorem not_collisionExtractable (h2 : (2 : ZMod n) ≠ 0) :
    ¬ ∃ extract : Tweak n → Tweak n → ZMod n, ∀ (x : ZMod n) (τ τ' : Tweak n),
      x ≠ 0 → τ.2 ≠ 0 → τ'.2 ≠ 0 → τ ≠ τ' →
        C.x (C.mulG (τ.sk x)) = C.x (C.mulG (τ'.sk x)) → extract τ τ' = x := by
  rintro ⟨extract, h⟩
  have hτ : ((0, 1) : Tweak n).2 ≠ 0 := one_ne_zero
  have hne := (Tweak.neg_ne h2 hτ).symm
  have h1 := h 1 (0, 1) (Tweak.neg (0, 1)) one_ne_zero hτ (Tweak.neg_snd_ne_zero.mpr hτ) hne
    (Tweak.xonly_neg C _ 1).symm
  have h3 := h 2 (0, 1) (Tweak.neg (0, 1)) h2 hτ (Tweak.neg_snd_ne_zero.mpr hτ) hne
    (Tweak.xonly_neg C _ 2).symm
  have : (1 : ZMod n) = 2 := h1.symm.trans h3
  exact one_ne_zero (by linear_combination (-1 : ZMod n) * this)

end Dahlias.Security
