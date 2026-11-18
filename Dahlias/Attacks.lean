import Dahlias.Proofs.Game
import Dahlias.Correctness

/-!
# Why the warnings of BIP 459 are there

Three statements that turn warnings of BIP 459 into theorems.

* `evenScalar_of_nonce_reuse`: two partial signatures made with the same
  secret nonce in the same session values, for different challenges, reveal
  the secret key. ("A secnonce must never be used in more than one `Sign`
  invocation.")
* `evenScalar_of_three_sessions`: three partial signatures made with the same
  secret nonce in three sessions reveal the secret key, if a determinant of
  public values is nonzero. This is the attack on deterministic nonces in the
  footnote of the BIP's section on nonce generation.
* `msgSwap_wins`: if `Sign` did not compare the message at the signer's index
  with the message the signer intends to sign, a coordinator could make the
  signer sign any message. `signNoMsgCheck` is `Sign` without that check, and
  `msgSwap` wins the unforgeability game against it with one session.
-/

set_option linter.unusedSectionVars false
set_option linter.deprecated false

namespace Dahlias.Security

open Taproot

variable {n : ℕ} [Fact n.Prime] {E X M : Type} [AddCommGroup E] [DecidableEq E] [DecidableEq X]
  [DecidableEq M]

/-! ## Nonce reuse -/

/-- **Nonce reuse with two challenges reveals the secret key.** -/
theorem evenScalar_of_nonce_reuse (O : Ops n E X) (secnonce : SecNonce n) (d : ZMod n)
    (Rb : E × ZMod n) {c₁ c₂ : ZMod n} (h : c₁ ≠ c₂) :
    (signPost O secnonce d Rb c₁ - signPost O secnonce d Rb c₂) / (c₁ - c₂) = O.evenScalar d := by
  have h' : c₁ - c₂ ≠ 0 := sub_ne_zero.mpr h
  simp only [signPost]
  field_simp
  ring

/-- `1` if `R` has an even y, otherwise `-1`: the `e` of `Sign`. -/
def sgn (O : Ops n E X) (R : E) : ZMod n := if O.hasEvenY R then 1 else -1

theorem sgn_mul_signPost (O : Ops n E X) (secnonce : SecNonce n) (d : ZMod n) (Rb : E × ZMod n)
    (c : ZMod n) :
    sgn O Rb.1 * signPost O secnonce d Rb c =
      secnonce.1 + Rb.2 * secnonce.2 + sgn O Rb.1 * c * O.evenScalar d := by
  unfold sgn signPost
  split_ifs <;> ring

/-- **Three sessions with the same secret nonce reveal the secret key.** The
three partial signatures `sᵢ`, the session values `(Rᵢ, bᵢ)` and the
challenges `cᵢ` are public. With `wᵢ = eᵢ⋅sᵢ` and `gᵢ = eᵢ⋅cᵢ`, the secret key
is a quotient of two expressions in these, if the denominator is nonzero. -/
theorem evenScalar_of_three_sessions (O : Ops n E X) (secnonce : SecNonce n) (d : ZMod n)
    (Rb₁ Rb₂ Rb₃ : E × ZMod n) (c₁ c₂ c₃ : ZMod n)
    (hD : (sgn O Rb₁.1 * c₁ - sgn O Rb₂.1 * c₂) * (Rb₁.2 - Rb₃.2) -
      (sgn O Rb₁.1 * c₁ - sgn O Rb₃.1 * c₃) * (Rb₁.2 - Rb₂.2) ≠ 0) :
    ((sgn O Rb₁.1 * signPost O secnonce d Rb₁ c₁ - sgn O Rb₂.1 * signPost O secnonce d Rb₂ c₂) *
        (Rb₁.2 - Rb₃.2) -
      (sgn O Rb₁.1 * signPost O secnonce d Rb₁ c₁ - sgn O Rb₃.1 * signPost O secnonce d Rb₃ c₃) *
        (Rb₁.2 - Rb₂.2)) /
      ((sgn O Rb₁.1 * c₁ - sgn O Rb₂.1 * c₂) * (Rb₁.2 - Rb₃.2) -
        (sgn O Rb₁.1 * c₁ - sgn O Rb₃.1 * c₃) * (Rb₁.2 - Rb₂.2)) = O.evenScalar d := by
  rw [div_eq_iff hD]
  simp only [sgn_mul_signPost]
  ring

/-- The values in `evenScalar_of_three_sessions` are what `Sign` returns. -/
theorem sign_eq_signPost (O : Ops n E X) (H : Hashes n E X M) (secnonce : SecNonce n)
    (sk : ZMod n) (m : M) (agg : PubNonce E) (pm : List (X × M)) (pubnonces : List (PubNonce E))
    {s : ZMod n} (h : sign O H secnonce sk m agg pm pubnonces = some s) :
    ∃ Rb, getSessionValues O H agg pm pubnonces = some Rb ∧
      s = signPost O secnonce sk Rb (H.sig pm (O.x Rb.1) (O.x (O.mulG sk), m)) := by
  rw [sign_eq] at h
  obtain ⟨Rb, hpre, rfl⟩ := Option.map_eq_some_iff.mp h
  refine ⟨Rb, ?_, rfl⟩
  unfold signPre at hpre
  split_ifs at hpre
  split at hpre
  · split_ifs at hpre
    exact hpre
  · exact absurd hpre (by simp)

/-! ## The message check -/

/-- `Sign` without the comparison of the message at the signer's index with
the message the signer intends to sign. The challenge is for the entry of the
list, as in BIP 459. -/
def signNoMsgCheck (O : Ops n E X) (H : Hashes n E X M) (secnonce : SecNonce n) (sk : ZMod n)
    (_m : M) (agg : PubNonce E) (pm : List (X × M)) (pubnonces : List (PubNonce E)) :
    Option (ZMod n) :=
  if secnonce.1 = 0 ∨ secnonce.2 = 0 ∨ sk = 0 then none else
  match matchIdxs pubnonces (O.mulG secnonce.2) with
  | [j] =>
    match pm[j]? with
    | some e =>
      if e.1 = O.x (O.mulG sk) then
        (getSessionValues O H agg pm pubnonces).map fun Rb =>
          signPost O secnonce sk Rb (H.sig pm (O.x Rb.1) e)
      else none
    | none => none
  | _ => none

variable (C : Curve n E X) (nonceCoef : E → E → List (X × M × E) → ZMod n) (N qs : ℕ)

/-- `challenger` with the signer's `Sign` as a parameter. -/
def challengerWith
    (signFn : (SigIn N X M → ZMod n) → SecNonce n → ZMod n → M → PubNonce E → List (X × M) →
      List (PubNonce E) → Option (ZMod n))
    (x : ZMod n) (nonces : Fin qs → SecNonce n) (T : SigIn N X M → ZMod n) :
    (q : AdvQ n N E X M) → SignerState X M → AdvR q × SignerState X M
  | .hash z, st => (T z, st)
  | .openSession, st =>
    if h : st.opened < qs then
      (some (C.mulG (nonces ⟨st.opened, h⟩).1, C.mulG (nonces ⟨st.opened, h⟩).2),
        { st with opened := st.opened + 1 })
    else (none, st)
  | .close k τ m agg pm pubnonces, st =>
    if h : k < qs ∧ k < st.opened ∧ k ∉ st.closed ∧ τ.2 ≠ 0 ∧ pm.length ≤ N then
      match signFn T (nonces ⟨k, h.1⟩) (τ.sk x) m agg pm pubnonces with
      | some s => (some s, { st with closed := k :: st.closed
                                     signed := (pm, C.x (C.mulG (τ.sk x)), m) :: st.signed })
      | none => (none, st)
    else (none, st)

/-- With BIP 459's `Sign` this is the signer of the unforgeability game. -/
theorem challengerWith_sign (x : ZMod n) (nonces : Fin qs → SecNonce n)
    (T : SigIn N X M → ZMod n) :
    challengerWith C N qs (fun T => sign C.ops (hashesOf N nonceCoef T)) x nonces T =
      challenger C nonceCoef N qs x nonces T := by
  funext q st
  cases q <;> rfl

/-- A coordinator that opens one session, asks the signer to sign `m` and puts
`m'` at the signer's index. -/
def msgSwap (m m' : M) : Adversary n N E X M Unit := fun _ P =>
  .ask .openSession fun (o : Option (PubNonce E)) =>
    match o with
    | none => .done ⟨[], (0, 1), (C.x P, 0)⟩
    | some U =>
      .ask (.close 0 (0, 1) m U [(C.x P, m')] [U]) fun (r : Option (ZMod n)) =>
        match r with
        | none => .done ⟨[], (0, 1), (C.x P, 0)⟩
        | some s =>
          .done ⟨[(C.x P, m')], (0, 1),
            (C.x (U.1 + (nonceCoef U.1 U.2 [(C.x P, m', U.2)]).val • U.2), s)⟩

/-- **Without the message check the signer can be made to sign any message.**
On every sample on which the session's nonce is not the point at infinity,
`msgSwap` wins the unforgeability game against `signNoMsgCheck`: the signer
intended to sign `m`, and the output is a valid signature for `m'`. -/
theorem msgSwap_wins (hN : 1 ≤ N) (hqs : 0 < qs) {m m' : M} (hm : m ≠ m') (x : (ZMod n)ˣ)
    (ν : Fin qs → (ZMod n)ˣ × (ZMod n)ˣ) (T : SigIn N X M → ZMod n)
    (hR : ((ν ⟨0, hqs⟩).1 : ZMod n) +
      nonceCoef (C.mulG ((ν ⟨0, hqs⟩).1 : ZMod n)) (C.mulG ((ν ⟨0, hqs⟩).2 : ZMod n))
        [(C.x (C.mulG (x : ZMod n)), m', C.mulG ((ν ⟨0, hqs⟩).2 : ZMod n))] *
          ((ν ⟨0, hqs⟩).2 : ZMod n) ≠ 0) :
    Wins C nonceCoef N (x : ZMod n) T
      ((msgSwap C nonceCoef N m m' () (C.mulG (x : ZMod n))).run
        (challengerWith C N qs (fun T => signNoMsgCheck C.ops (hashesOf N nonceCoef T))
          (x : ZMod n) (fun k => ((ν k).1, (ν k).2)) T) ⟨0, [], []⟩).1
      ((msgSwap C nonceCoef N m m' () (C.mulG (x : ZMod n))).run
        (challengerWith C N qs (fun T => signNoMsgCheck C.ops (hashesOf N nonceCoef T))
          (x : ZMod n) (fun k => ((ν k).1, (ν k).2)) T) ⟨0, [], []⟩).2 := by
  set r₁ : ZMod n := ((ν ⟨0, hqs⟩).1 : ZMod n) with hr₁
  set r₂ : ZMod n := ((ν ⟨0, hqs⟩).2 : ZMod n) with hr₂
  have h1 : r₁ ≠ 0 := Units.ne_zero _
  have h2 : r₂ ≠ 0 := Units.ne_zero _
  have hx : (x : ZMod n) ≠ 0 := Units.ne_zero x
  have hsk : Tweak.sk ((0, 1) : Tweak n) (x : ZMod n) = x := by simp [Tweak.sk]
  set P := C.mulG (x : ZMod n) with hP
  set b := nonceCoef (C.mulG r₁) (C.mulG r₂) [(C.x P, m', C.mulG r₂)] with hb
  set R := C.mulG r₁ + b.val • C.mulG r₂ with hRdef
  have hRne : R ≠ 0 := by
    rw [hRdef, C.val_smul_mulG, ← map_add]
    exact C.mulG_ne_zero hR
  have hL : ([(C.x P, m')] : List (X × M)).length ≤ N := by simpa using hN
  -- the session values
  have hsv : getSessionValues C.ops (hashesOf N nonceCoef T) (C.mulG r₁, C.mulG r₂)
      [(C.x P, m')] [(C.mulG r₁, C.mulG r₂)] = some (R, b) := by
    unfold getSessionValues
    have hc1 : ¬(([(C.x P, m')] : List (X × M)) = [] ∨
        ([(C.x P, m')] : List (X × M)).length ≠ [(C.mulG r₁, C.mulG r₂)].length ∨
        (C.mulG r₁, C.mulG r₂).1 = 0 ∨ (C.mulG r₁, C.mulG r₂).2 = 0 ∨
        ∃ Nn ∈ [(C.mulG r₁, C.mulG r₂)], Nn.2 = 0) := by
      simp [C.mulG_eq_zero, h1, h2]
    rw [if_neg hc1]
    change (if R = 0 then none else some (R, b)) = some (R, b)
    rw [if_neg hRne]
  -- the signer's answer
  have hmi : matchIdxs [(C.mulG r₁, C.mulG r₂)] (C.mulG r₂) = [0] := by simp [matchIdxs]
  have hsign : signNoMsgCheck C.ops (hashesOf N nonceCoef T) (r₁, r₂)
      (Tweak.sk ((0, 1) : Tweak n) (x : ZMod n)) m (C.mulG r₁, C.mulG r₂) [(C.x P, m')]
      [(C.mulG r₁, C.mulG r₂)] =
      some (signPost C.ops (r₁, r₂) (x : ZMod n) (R, b)
        (T (⟨[(C.x P, m')], hL⟩, C.x R, (C.x P, m')))) := by
    unfold signNoMsgCheck
    have h0 : ¬((r₁, r₂).1 = 0 ∨ (r₁, r₂).2 = 0 ∨ Tweak.sk ((0, 1) : Tweak n) (x : ZMod n) = 0) := by
      simp [h1, h2, hsk, hx]
    rw [if_neg h0]
    simp only [ops_mulG, hmi, List.getElem?_cons_zero, ops_x, hsk, ← hP, ↓reduceIte, hsv,
      Option.map_some]
    simp only [hashesOf, hL, ↓reduceDIte]
  -- the run
  have hopen : challengerWith C N qs (fun T => signNoMsgCheck C.ops (hashesOf N nonceCoef T))
      (x : ZMod n) (fun k => ((ν k).1, (ν k).2)) T .openSession ⟨0, [], []⟩ =
      (some (C.mulG r₁, C.mulG r₂), ⟨1, [], []⟩) := by
    simp only [challengerWith, hqs, ↓reduceDIte]
    rfl
  have hcond : (0 : ℕ) < qs ∧ 0 < 1 ∧ 0 ∉ ([] : List ℕ) ∧ ((0, 1) : Tweak n).2 ≠ 0 ∧
      ([(C.x P, m')] : List (X × M)).length ≤ N := ⟨hqs, Nat.one_pos, by simp, one_ne_zero, hL⟩
  have hclose : challengerWith C N qs (fun T => signNoMsgCheck C.ops (hashesOf N nonceCoef T))
      (x : ZMod n) (fun k => ((ν k).1, (ν k).2)) T
      (.close 0 (0, 1) m (C.mulG r₁, C.mulG r₂) [(C.x P, m')] [(C.mulG r₁, C.mulG r₂)])
      ⟨1, [], []⟩ =
      (some (signPost C.ops (r₁, r₂) (x : ZMod n) (R, b)
        (T (⟨[(C.x P, m')], hL⟩, C.x R, (C.x P, m')))),
        ⟨1, [0], [([(C.x P, m')], C.x P, m)]⟩) := by
    rw [hsk] at hsign
    simp only [challengerWith]
    rw [dif_pos hcond]
    simp only [← hr₁, ← hr₂, hsk, ← hP, hsign]
    rfl
  have hrun : (msgSwap C nonceCoef N m m' () P).run
      (challengerWith C N qs (fun T => signNoMsgCheck C.ops (hashesOf N nonceCoef T))
        (x : ZMod n) (fun k => ((ν k).1, (ν k).2)) T) ⟨0, [], []⟩ =
      (⟨[(C.x P, m')], (0, 1), (C.x R, signPost C.ops (r₁, r₂) (x : ZMod n) (R, b)
        (T (⟨[(C.x P, m')], hL⟩, C.x R, (C.x P, m'))))⟩,
        ⟨1, [0], [([(C.x P, m')], C.x P, m)]⟩) := by
    unfold msgSwap
    refine (Alg.run_ask _ _ _ _).trans ?_
    rw [hopen]
    dsimp only
    refine (Alg.run_ask _ _ _ _).trans ?_
    rw [hclose]
    rfl
  rw [hrun]
  refine ⟨one_ne_zero, by rw [hsk]; exact hx, hL, ⟨m', by simp [hsk, hP], ?_⟩, ?_⟩
  · simp only [hsk, List.mem_singleton, Prod.mk.injEq, not_and]
    intro _ _ h
    exact hm h.symm
  · unfold verify
    simp only [ops_liftX, ops_mulG, liftX_x_signOf C hRne, hP, C.liftX_x_mulG hx,
      List.isEmpty_cons, Bool.not_false, List.all_cons, Option.isSome_some, List.all_nil,
      Bool.and_true, Bool.true_and, decide_eq_true_eq, keySum, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero, Option.getD_some, ops_smul, C.val_smul_mulG,
      map_add, signPost, Ops.signOf, ops_hasEvenY, ops_evenScalar, hashesOf]
    simp only [List.length_cons, List.length_nil, zero_add, hN, ↓reduceDIte]
    have hRm : R = C.mulG (r₁ + b * r₂) := by rw [hRdef, C.val_smul_mulG, map_add]
    by_cases he : C.hasEvenY R = true
    · simp only [he, ↓reduceIte]
      simp [hRm]
    · simp only [he, Bool.false_eq_true, ↓reduceIte]
      simp [hRm]

end Dahlias.Security
