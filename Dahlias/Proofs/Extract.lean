import Dahlias.Proofs.Simulate

/-!
# Extracting the discrete logarithms

* `evenScalar_of_fork`: two valid signatures for the same list and the same
  `r`, on tables that differ only at the fork point, give the discrete
  logarithm of the even-y version of the honest signer's tweaked key.
* `extractX_evenScalar`: the secret key from that discrete logarithm.
* `CloseRec.w_eq`: `r₁ + b⋅r₂` from a record and the secret key.
-/

set_option linter.unusedSectionVars false
set_option linter.deprecated false

namespace Dahlias.Security

open Taproot Function

variable {n : ℕ} [Fact n.Prime] {E X M : Type} [AddCommGroup E] [DecidableEq E] [DecidableEq X]
  [DecidableEq M] (C : Curve n E X) (nonceCoef : E → E → List (X × M × E) → ZMod n) (N qs : ℕ)

/-! ## The fork point -/

theorem forkPointPub_eq (x : ZMod n) (f : Forgery n X M) (st : SignerState X M) :
    forkPointPub C N (C.mulG x) f st = forkPoint C N x f st := by
  have hiff : (f.L.length ≤ N ∧ f.τ.2 ≠ 0 ∧ f.τ.pk C (C.mulG x) ≠ 0) ↔
      (f.L.length ≤ N ∧ f.τ.2 ≠ 0 ∧ f.τ.sk x ≠ 0) := by
    rw [tweak_pk]
    exact and_congr_right fun _ => and_congr_right fun _ => (C.mulG_eq_zero).not
  unfold forkPointPub forkPoint
  by_cases h : f.L.length ≤ N ∧ f.τ.2 ≠ 0 ∧ f.τ.sk x ≠ 0
  · rw [dif_pos h, dif_pos (hiff.mpr h)]
    simp only [tweak_pk]
  · rw [dif_neg h, dif_neg (mt hiff.mp h)]

/-- What a fork point says about the forgery. -/
theorem forkPoint_eq_some {x : ZMod n} {f : Forgery n X M} {st : SignerState X M}
    {z : SigIn N X M} (h : forkPoint C N x f st = some z) :
    ∃ (hL : f.L.length ≤ N) (e : X × M), z = (⟨f.L, hL⟩, f.sig.1, e) ∧ e ∈ f.L ∧
      e.1 = C.x (C.mulG (f.τ.sk x)) ∧ (f.L, e.1, e.2) ∉ st.signed ∧ f.τ.2 ≠ 0 ∧ f.τ.sk x ≠ 0 := by
  unfold forkPoint at h
  split_ifs at h with hc
  obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp h
  have hp := List.find?_some he
  simp only [decide_eq_true_eq] at hp
  exact ⟨hc.1, e, rfl, List.mem_of_find?_eq_some he, hp.1, hp.2, hc.2.1, hc.2.2⟩

/-! ## The secret key -/

/-- **The secret key from the even-y discrete logarithm of the tweaked key.** -/
theorem extractX_evenScalar (x : ZMod n) (τ : Tweak n) (hβ : τ.2 ≠ 0) :
    extractX C (C.mulG x) τ (C.evenScalar (τ.sk x)) = x := by
  have h1 : (τ.sk x - τ.1) / τ.2 = x := by
    unfold Tweak.sk; field_simp; ring
  unfold extractX Curve.evenScalar
  by_cases he : C.hasEvenY (C.mulG (τ.sk x)) = true
  · simp [he, h1]
  · simp only [he, Bool.false_eq_true, ↓reduceIte, neg_neg, h1]
    split_ifs with h2
    · exact C.mulG_injective h2
    · rfl

theorem sum_map_sub' {α : Type} (L : List α) (f g : α → E) :
    (L.map f).sum - (L.map g).sum = (L.map fun a => f a - g a).sum := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.map_cons, List.sum_cons, ← ih]; abel

/-- A sum over a list with one distinguished value. -/
theorem sum_map_ite_eq_count {α : Type} [DecidableEq α] (L : List α) (e : α) (A : E) :
    (L.map fun a => if a = e then A else 0).sum =
      (L.filter fun a => decide (a = e)).length • A := by
  induction L with
  | nil => simp
  | cons a L ih =>
    by_cases h : a = e
    · simp [h, ih, add_nsmul, add_comm]
    · simp [h, ih]

/-- **Two signatures at the fork point give the tweaked key's discrete
logarithm.** -/
theorem evenScalar_of_fork (hN : N < n) (T : SigIn N X M → ZMod n) {L : List (X × M)}
    (hL : L.length ≤ N) {r : X} {e : X × M} (he : e ∈ L) {d : ZMod n} (hd : d ≠ 0)
    (hed : e.1 = C.x (C.mulG d)) {s₁ s₂ sNew : ZMod n}
    (hne : sNew ≠ T (⟨L, hL⟩, r, e))
    (h₁ : verify C.ops (hashesOf N nonceCoef T) L (r, s₁) = true)
    (h₂ : verify C.ops (hashesOf N nonceCoef (update T (⟨L, hL⟩, r, e) sNew)) L (r, s₂) = true) :
    (s₁ - s₂) / ((((L.filter fun a => decide (a = e)).length : ℕ) : ZMod n) *
      (T (⟨L, hL⟩, r, e) - sNew)) = C.evenScalar d := by
  set z : SigIn N X M := (⟨L, hL⟩, r, e) with hz
  set cnt := (L.filter fun a => decide (a = e)).length with hcnt
  -- the two verification equations
  unfold verify at h₁ h₂
  cases hR : C.ops.liftX r with
  | none => simp [hR] at h₁
  | some R =>
    simp only [hR, Bool.and_eq_true, decide_eq_true_eq] at h₁ h₂
    have e₁ := h₁.2
    have e₂ := h₂.2
    -- the key sums differ only in the entries equal to `e`
    have hlift : (C.ops.liftX e.1).getD 0 = C.mulG (C.evenScalar d) := by
      rw [hed, ops_liftX, C.liftX_x_mulG hd]; rfl
    have hdiff : keySum C.ops (hashesOf N nonceCoef T) L r -
        keySum C.ops (hashesOf N nonceCoef (update T z sNew)) L r =
        cnt • C.mulG ((T z - sNew) * C.evenScalar d) := by
      unfold keySum
      rw [sum_map_sub', ← sum_map_ite_eq_count]
      congr 1
      refine List.map_congr_left fun a _ => ?_
      simp only [hashesOf, hL, ↓reduceDIte, ops_smul]
      by_cases ha : a = e
      · subst ha
        rw [if_pos rfl, update_self, hlift, C.val_smul_mulG, C.val_smul_mulG, ← map_sub, sub_mul]
      · have hza : ((⟨L, hL⟩, r, a) : SigIn N X M) ≠ z := by
          intro h
          exact ha (congrArg (fun t => t.2.2) h)
        rw [if_neg ha, update_of_ne hza, sub_self]
    have hsub : C.mulG (s₁ - s₂) = C.mulG ((cnt : ZMod n) * ((T z - sNew) * C.evenScalar d)) := by
      rw [map_sub, ops_mulG] at *
      rw [e₁, e₂, add_sub_add_left_eq_sub, hdiff, ← map_nsmul, nsmul_eq_mul]
    have hs := C.mulG_injective hsub
    have hcnt0 : (cnt : ZMod n) ≠ 0 := by
      have hpos : 0 < cnt := List.length_pos_of_mem (List.mem_filter.mpr ⟨he, by simp⟩)
      have hle : cnt ≤ L.length := List.length_filter_le _ _
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact Nat.not_dvd_of_pos_of_lt hpos (by omega)
    have hT : T z - sNew ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    rw [hs]
    field_simp

/-! ## The session nonces -/

variable (xu : (ZMod n)ˣ) (ν : Fin qs → (ZMod n)ˣ × (ZMod n)ˣ)

theorem keySk_eq_sign (x : ZMod n) (keys : List (KeyTerm n M)) :
    keySk C x keys =
      (keys.map fun κ => κ.2.2 * (keySign C (C.mulG x) κ.1 * κ.1.sk x)).sum := by
  unfold keySk
  refine congrArg List.sum (List.map_congr_left fun κ _ => ?_)
  rw [evenScalar_sk]
  simp only [Tweak.sk]
  ring

/-- **`r₁ + b⋅r₂` from a record and the secret key.** -/
theorem CloseRec.w_eq {r : CloseRec n E X M} (h : RecSig C qs xu ν r) :
    ∃ hk : r.k < qs, r.w C (C.mulG (xu : ZMod n)) xu =
      (noncesOf qs ν ⟨r.k, hk⟩).1 + r.Rb.2 * (noncesOf qs ν ⟨r.k, hk⟩).2 := by
  obtain ⟨hk, hs⟩ := h
  refine ⟨hk, ?_⟩
  simp only [CloseRec.w, hs, sigOf, ← keySk_eq_sign]
  by_cases h1 : C.hasEvenY r.Rb.1 = true <;>
    simp only [h1, ite_true, ite_false, Bool.false_eq_true] <;> ring

end Dahlias.Security
