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

end Dahlias.Security
