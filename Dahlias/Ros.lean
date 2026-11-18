import Dahlias.Attacks

/-!
# The ROS attack on a weaker uniqueness check

BIP 459's `Sign` fails unless the signer's `R₂` appears exactly once among the
public nonces. Its footnote warns that it is not enough to check that the
combination of public key, message and `R₂` appears exactly once. This file
proves that warning: with the weaker check (`signTupleCheck`), an adversary
that runs `ℓ ≥ log₂ n` signing sessions concurrently forges a signature. This
is the attack of Appendix C of the DahLIAS paper, built on the solution of
the ROS problem by Benhamouda, Lepoint, Loss, Orrù and Raykova
(ePrint 2020/945).

In every session the adversary uses a list in which the signer's public key
and public nonce appear twice, with two different messages. The weaker check
lets the signer close such a session with either message. Both ways use the
same secret nonce `r₁ + b⋅r₂` but different challenges `c0ₖ` and `c1ₖ`
(`signTupleCheck_two`).

* `ros_bits`: for any target `t` there is a choice of one challenge per
  session, `cₖ = c0ₖ` or `c1ₖ`, with `Σ αₖ⋅cₖ = t`, for coefficients `αₖ` that
  do not depend on the choice. The choice is the binary expansion of a value
  the adversary knows.
* `ros_forgery`: the adversary computes the nonce `R'` of its forgery from the
  `αₖ`, then the challenge `c'` of the forgery, then the choice for the target
  `±c'`, and only then closes the sessions. The combination of the partial
  signatures is a valid signature on a message the signer never saw.
-/

set_option linter.unusedSectionVars false
set_option linter.deprecated false

namespace Dahlias.Security

open Taproot Finset

variable {n : ℕ} [Fact n.Prime] {E X M : Type} [AddCommGroup E] [DecidableEq E] [DecidableEq X]
  [DecidableEq M]

/-! ## The weaker check -/

/-- `Sign` with the weaker check: the combination of the signer's public key,
message and `R₂` appears exactly once. -/
def signTupleCheck (O : Ops n E X) (H : Hashes n E X M) (secnonce : SecNonce n) (sk : ZMod n)
    (m : M) (agg : PubNonce E) (pm : List (X × M)) (pubnonces : List (PubNonce E)) :
    Option (ZMod n) :=
  if secnonce.1 = 0 ∨ secnonce.2 = 0 ∨ sk = 0 then none else
  match (List.range pubnonces.length).filter fun j =>
      decide (pm[j]? = some (O.x (O.mulG sk), m) ∧
        (pubnonces[j]?).map Prod.snd = some (O.mulG secnonce.2)) with
  | [_] =>
    (getSessionValues O H agg pm pubnonces).map fun Rb =>
      signPost O secnonce sk Rb (H.sig pm (O.x Rb.1) (O.x (O.mulG sk), m))
  | _ => none

/-- **With the weaker check a session can be closed with either of two
messages**, with the same session values and so the same secret nonce. -/
theorem signTupleCheck_two (O : Ops n E X) (H : Hashes n E X M) {r₁ r₂ sk : ZMod n}
    (h₁ : r₁ ≠ 0) (h₂ : r₂ ≠ 0) (hsk : sk ≠ 0) {m0 m1 : M} (hm : m0 ≠ m1) (agg : PubNonce E)
    (R₁ : E) {Rb : E × ZMod n}
    (hsv : getSessionValues O H agg [(O.x (O.mulG sk), m0), (O.x (O.mulG sk), m1)]
      [(R₁, O.mulG r₂), (R₁, O.mulG r₂)] = some Rb) (β : Bool) :
    signTupleCheck O H (r₁, r₂) sk (if β then m1 else m0) agg
        [(O.x (O.mulG sk), m0), (O.x (O.mulG sk), m1)] [(R₁, O.mulG r₂), (R₁, O.mulG r₂)] =
      some (signPost O (r₁, r₂) sk Rb
        (H.sig [(O.x (O.mulG sk), m0), (O.x (O.mulG sk), m1)] (O.x Rb.1)
          (O.x (O.mulG sk), if β then m1 else m0))) := by
  unfold signTupleCheck
  have h0 : ¬((r₁, r₂).1 = 0 ∨ (r₁, r₂).2 = 0 ∨ sk = 0) := by simp [h₁, h₂, hsk]
  rw [if_neg h0, hsv]
  have hm' : m1 ≠ m0 := Ne.symm hm
  cases β <;> simp [List.range_succ, hm, hm']

/-! ## Choosing the challenges -/

/-- The binary digits of `v` below position `ℓ` sum to `v mod 2^ℓ`. -/
theorem sum_bits (v ℓ : ℕ) : ∑ k ∈ range ℓ, 2 ^ k * (v / 2 ^ k % 2) = v % 2 ^ ℓ := by
  induction ℓ with
  | zero => simp [Nat.mod_one]
  | succ ℓ ih => rw [sum_range_succ, ih, Nat.mod_pow_succ]

/-- The coefficient of session `k`. -/
def rosCoef (c0 c1 : ℕ → ZMod n) (k : ℕ) : ZMod n := 2 ^ k / (c1 k - c0 k)

/-- The constant of the attack. -/
def rosConst (c0 c1 : ℕ → ZMod n) (ℓ : ℕ) : ZMod n :=
  ∑ k ∈ range ℓ, 2 ^ k * c0 k / (c1 k - c0 k)

/-- The adversary's choice in session `k` for the target `t`. -/
def rosBit (c0 c1 : ℕ → ZMod n) (ℓ : ℕ) (t : ZMod n) (k : ℕ) : Bool :=
  decide ((t - rosConst c0 c1 ℓ).val / 2 ^ k % 2 = 1)

/-- **The ROS problem is easy for `ℓ ≥ log₂ n`**: the chosen challenges combine
to the target. -/
theorem ros_bits (c0 c1 : ℕ → ZMod n) (ℓ : ℕ) (hℓ : n ≤ 2 ^ ℓ)
    (hc : ∀ k < ℓ, c0 k ≠ c1 k) (t : ZMod n) :
    ∑ k ∈ range ℓ, rosCoef c0 c1 k * (if rosBit c0 c1 ℓ t k then c1 k else c0 k) = t := by
  set v := (t - rosConst c0 c1 ℓ).val with hv
  have hterm : ∀ k ∈ range ℓ,
      rosCoef c0 c1 k * (if rosBit c0 c1 ℓ t k then c1 k else c0 k) =
        ((2 ^ k * (v / 2 ^ k % 2) : ℕ) : ZMod n) + 2 ^ k * c0 k / (c1 k - c0 k) := by
    intro k hk
    have hd : c1 k - c0 k ≠ 0 := sub_ne_zero.mpr (Ne.symm (hc k (mem_range.mp hk)))
    unfold rosCoef rosBit
    rcases Nat.mod_two_eq_zero_or_one (v / 2 ^ k) with h | h
    · simp only [← hv, h, mul_zero, Nat.cast_zero, zero_add, Nat.zero_ne_one, decide_false,
        Bool.false_eq_true, ↓reduceIte]
      ring
    · simp only [← hv, h, decide_true, ↓reduceIte, mul_one, Nat.cast_pow, Nat.cast_ofNat]
      field_simp
      ring
  rw [sum_congr rfl hterm, sum_add_distrib, ← Nat.cast_sum, sum_bits,
    Nat.mod_eq_of_lt (lt_of_lt_of_le (ZMod.val_lt _) hℓ), ZMod.natCast_zmod_val]
  unfold rosConst
  ring

/-! ## The forgery -/

variable (C : Curve n E X) (H : Hashes n E X M)

theorem sgn_mul_self (O : Ops n E X) (R : E) : sgn O R * sgn O R = 1 := by
  unfold sgn; split_ifs <;> ring

theorem mulG_sgn_mul (R : E) (a : ZMod n) :
    C.mulG (sgn C.ops R * a) = C.ops.signOf R (C.mulG a) := by
  unfold sgn Ops.signOf
  split_ifs <;> simp

/-- The secret nonce the signer uses in a session with session values `Rb`. -/
def effNonce (O : Ops n E X) (secnonce : SecNonce n) (Rb : E × ZMod n) : ZMod n :=
  if O.hasEvenY Rb.1 then secnonce.1 + Rb.2 * secnonce.2 else -(secnonce.1 + Rb.2 * secnonce.2)

theorem signPost_eq (O : Ops n E X) (secnonce : SecNonce n) (sk : ZMod n) (Rb : E × ZMod n)
    (c : ZMod n) : signPost O secnonce sk Rb c = effNonce O secnonce Rb + c * O.evenScalar sk :=
  rfl

/-- The adversary knows the point of the signer's secret nonce: it is a
combination of the signer's public nonce. So it can compute `R'` in
`ros_forgery`, a combination of these points, before the sessions are closed. -/
theorem mulG_effNonce (r₁ r₂ : ZMod n) (Rb : E × ZMod n) :
    C.mulG (effNonce C.ops (r₁, r₂) Rb) =
      C.ops.signOf Rb.1 (C.mulG r₁ + Rb.2.val • C.mulG r₂) := by
  unfold effNonce Ops.signOf
  simp only [ops_hasEvenY, C.val_smul_mulG]
  by_cases h : C.hasEvenY Rb.1 = true <;> simp [h, add_comm]

/-- **The ROS attack forges a signature.** The honest signer with secret key
`sk` takes part in `ℓ ≥ log₂ n` sessions. In session `k` its public key and
public nonce appear twice in the lists, with the messages `m0 k ≠ m1 k`, and
the two possible challenges `c0 k` and `c1 k` differ. The adversary computes
`R'` and the challenge `c'` of a signature on any message `m'` under the
signer's key alone, and from them the message `m0 k` or `m1 k` it asks the
signer to sign in session `k`. The signer, using the weaker check, answers
with `s k`. Then `(x(R'), ±Σ αₖ⋅sₖ)` is a valid signature for the list
`[(pk, m')]`, although the signer never signed `m'`. -/
theorem ros_forgery {sk : ZMod n} (hsk : sk ≠ 0) (ℓ : ℕ) (hℓ : n ≤ 2 ^ ℓ)
    (r₁ r₂ : ℕ → ZMod n) (m0 m1 : ℕ → M) (agg : ℕ → PubNonce E) (R₁ : ℕ → E)
    (Rb : ℕ → E × ZMod n) (m' : M) (s : ℕ → ZMod n)
    (hr₁ : ∀ k < ℓ, r₁ k ≠ 0) (hr₂ : ∀ k < ℓ, r₂ k ≠ 0) (hm : ∀ k < ℓ, m0 k ≠ m1 k)
    (hsv : ∀ k < ℓ, getSessionValues C.ops H (agg k)
      [(C.x (C.mulG sk), m0 k), (C.x (C.mulG sk), m1 k)]
      [(R₁ k, C.mulG (r₂ k)), (R₁ k, C.mulG (r₂ k))] = some (Rb k)) :
    -- the two challenges of every session
    let pm : ℕ → List (X × M) := fun k => [(C.x (C.mulG sk), m0 k), (C.x (C.mulG sk), m1 k)]
    let c0 : ℕ → ZMod n := fun k => H.sig (pm k) (C.x (Rb k).1) (C.x (C.mulG sk), m0 k)
    let c1 : ℕ → ZMod n := fun k => H.sig (pm k) (C.x (Rb k).1) (C.x (C.mulG sk), m1 k)
    -- the nonce and the challenge of the forgery
    let R' : E := C.mulG (∑ k ∈ range ℓ, rosCoef c0 c1 k * effNonce C.ops (r₁ k, r₂ k) (Rb k))
    let c' : ZMod n := H.sig [(C.x (C.mulG sk), m')] (C.x R') (C.x (C.mulG sk), m')
    -- the adversary's choices
    let β : ℕ → Bool := rosBit c0 c1 ℓ (sgn C.ops R' * c')
    (∀ k < ℓ, c0 k ≠ c1 k) → R' ≠ 0 →
    -- the signer's answers
    (∀ k < ℓ, signTupleCheck C.ops H (r₁ k, r₂ k) sk (if β k then m1 k else m0 k) (agg k) (pm k)
      [(R₁ k, C.mulG (r₂ k)), (R₁ k, C.mulG (r₂ k))] = some (s k)) →
    verify C.ops H [(C.x (C.mulG sk), m')]
      (C.x R', sgn C.ops R' * ∑ k ∈ range ℓ, rosCoef c0 c1 k * s k) = true := by
  intro pm c0 c1 R' c' β hc hR' hs
  -- what the signer answered
  have hsk' : ∀ k ∈ range ℓ, s k = effNonce C.ops (r₁ k, r₂ k) (Rb k) +
      (if β k then c1 k else c0 k) * C.evenScalar sk := by
    intro k hk
    have hk' := mem_range.mp hk
    have h := signTupleCheck_two C.ops H (hr₁ k hk') (hr₂ k hk') hsk (hm k hk') (agg k) (R₁ k)
      (hsv k hk') (β k)
    have h2 := hs k hk'
    simp only [ops_x, ops_mulG] at h
    rw [h] at h2
    rw [← Option.some.inj h2, signPost_eq]
    cases β k <;> rfl
  -- the combination of the answers
  have hsum : ∑ k ∈ range ℓ, rosCoef c0 c1 k * s k =
      (∑ k ∈ range ℓ, rosCoef c0 c1 k * effNonce C.ops (r₁ k, r₂ k) (Rb k)) +
        sgn C.ops R' * c' * C.evenScalar sk := by
    rw [← ros_bits c0 c1 ℓ hℓ hc (sgn C.ops R' * c'), sum_mul, ← sum_add_distrib]
    refine sum_congr rfl fun k hk => ?_
    rw [hsk' k hk]
    ring
  have hfinal : sgn C.ops R' * ∑ k ∈ range ℓ, rosCoef c0 c1 k * s k =
      sgn C.ops R' * (∑ k ∈ range ℓ, rosCoef c0 c1 k * effNonce C.ops (r₁ k, r₂ k) (Rb k)) +
        c' * C.evenScalar sk := by
    rw [hsum, mul_add, ← mul_assoc, ← mul_assoc, sgn_mul_self, one_mul]
  unfold verify
  simp only [ops_liftX, liftX_x_signOf C hR', C.liftX_x_mulG hsk, List.isEmpty_cons,
    Bool.not_false, List.all_cons, Option.isSome_some, List.all_nil, Bool.and_true,
    Bool.true_and, decide_eq_true_eq, keySum, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero, Option.getD_some, ops_smul, C.val_smul_mulG, ops_mulG]
  rw [hfinal, map_add, mulG_sgn_mul]

end Dahlias.Security
