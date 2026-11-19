import Dahlias.Correctness

/-!
# Finding a disruptive signer

BIP 459 uses `PartialSigVerify` to find the signer whose partial signature
makes the aggregate signature invalid. `Dahlias.Correctness` proves two parts
of that: an honest signer's partial signature passes
(`partialSigVerify_sign`), and if all partial signatures pass, the aggregate
signature is valid (`verify_sigAgg_of_partialSigVerify`). This file adds the
rest.

* `partialSigVerify_iff`: in a session for which `NonceAgg` and
  `GetSessionValues` succeed, `PartialSigVerify` accepts `s` at index `i` iff
  `pkᵢ` lifts to a point `Pᵢ` and `s⋅G = e⋅(R₁,ᵢ + b⋅R₂,ᵢ) + cᵢ⋅Pᵢ`.
* `partialSigVerify_unique`: at most one value passes at an index.
* `partialSigVerify_iff_eq_sign`: at an honest signer's index the value that
  `Sign` returns is the only one that passes. A signer cannot be blamed for a
  partial signature it made, and nobody else can make a different one that
  passes in its place.
* `exists_partialSigVerify_eq_false`: if the signature from `SigAgg` does not
  verify, `PartialSigVerify` fails for at least one signer.
* `partialSigVerify_of_verify`: if the signature from `SigAgg` verifies and
  the partial signatures of all signers but one pass, the remaining one passes
  as well. `verify_eq_false_of_one_bad` is the contrapositive: one bad partial
  signature among good ones always makes the aggregate signature invalid.

Two or more signers can send partial signatures that fail on their own and
cancel in the sum. The aggregate signature is then valid, and
`PartialSigVerify` still fails for each of them.

All statements hold for every choice of the hash functions.
-/

set_option linter.unusedSectionVars false

namespace Dahlias

open Taproot Taproot.Curve

variable {n : ℕ} [Fact n.Prime] {E X M : Type*} [AddCommGroup E] (C : Curve n E X)
  (H : Hashes n E X M) [DecidableEq E] [DecidableEq X] [DecidableEq M]

/-! ## What `PartialSigVerify` checks -/

/-- `NonceAgg` fails unless both halves of every public nonce are points. -/
theorem nonceAgg_ne_zero {pubnonces : List (PubNonce E)} {agg : PubNonce E}
    (h : nonceAgg pubnonces = some agg) {N : PubNonce E} (hN : N ∈ pubnonces) :
    N.1 ≠ 0 ∧ N.2 ≠ 0 := by
  unfold nonceAgg at h
  dsimp only at h
  split_ifs at h with h0
  push Not at h0
  exact h0.2.1 N hN

/-- **The equation of `PartialSigVerify`.** In a session for which `NonceAgg`
and `GetSessionValues` succeed, `PartialSigVerify` accepts `s` at index `i`
iff `pkᵢ` lifts to a point `Pᵢ` and `s⋅G = e⋅(R₁,ᵢ + b⋅R₂,ᵢ) + cᵢ⋅Pᵢ`. -/
theorem partialSigVerify_iff {pm : List (X × M)} {pubnonces : List (PubNonce E)}
    {agg : PubNonce E} {R : E} {b : ZMod n} (hagg : nonceAgg pubnonces = some agg)
    (hsv : getSessionValues C.ops H agg pm pubnonces = some (R, b)) (s : ZMod n) {i : ℕ}
    (hi : i < pm.length) (hi' : i < pubnonces.length) :
    partialSigVerify C.ops H s pm pubnonces i = true ↔
      ∃ P, C.liftX pm[i].1 = some P ∧
        C.mulG s = C.ops.signOf R (pubnonces[i].1 + b.val • pubnonces[i].2) +
          (H.sig pm (C.x R) pm[i]).val • P := by
  obtain ⟨hN₁, hN₂⟩ := nonceAgg_ne_zero hagg (List.getElem_mem hi')
  unfold partialSigVerify
  simp only [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi', hagg, Option.bind_some,
    hsv, hN₁, hN₂, or_self, ↓reduceIte, ops_liftX]
  constructor
  · intro h
    cases hP : C.liftX pm[i].1 with
    | none => simp [hP] at h
    | some P =>
      simp only [hP] at h
      exact ⟨P, rfl, of_decide_eq_true h⟩
  · rintro ⟨P, hP, h⟩
    simp only [hP]
    exact decide_eq_true h

/-- **At most one partial signature passes at an index.** -/
theorem partialSigVerify_unique {pm : List (X × M)} {pubnonces : List (PubNonce E)}
    {s s' : ZMod n} {i : ℕ} (h : partialSigVerify C.ops H s pm pubnonces i = true)
    (h' : partialSigVerify C.ops H s' pm pubnonces i = true) : s = s' := by
  unfold partialSigVerify at h h'
  cases hpm : pm[i]? with
  | none => simp [hpm] at h
  | some pkm =>
    cases hN : pubnonces[i]? with
    | none => simp [hpm, hN] at h
    | some N =>
      simp only [hpm, hN] at h h'
      by_cases h0 : N.1 = 0 ∨ N.2 = 0
      · simp [h0] at h
      · simp only [h0, ↓reduceIte] at h h'
        cases hP : C.ops.liftX pkm.1 with
        | none => simp [hP] at h
        | some P =>
          cases hS : (nonceAgg pubnonces).bind (getSessionValues C.ops H · pm pubnonces) with
          | none => simp [hP, hS] at h
          | some Rb =>
            simp only [hP, hS] at h h'
            exact C.mulG_injective ((of_decide_eq_true h).trans (of_decide_eq_true h').symm)

/-- **The honest partial signature is the only one that passes.** At the
index that holds an honest signer's public nonce, `PartialSigVerify` accepts
`s'` iff `s'` is the partial signature that `Sign` returns. -/
theorem partialSigVerify_iff_eq_sign {r₁ r₂ sk : ZMod n} {m : M} {agg : PubNonce E}
    {pm : List (X × M)} {pubnonces : List (PubNonce E)} {s : ZMod n} {j : ℕ}
    (hagg : nonceAgg pubnonces = some agg)
    (hj : pubnonces[j]? = some (C.mulG r₁, C.mulG r₂))
    (hs : sign C.ops H (r₁, r₂) sk m agg pm pubnonces = some s) (s' : ZMod n) :
    partialSigVerify C.ops H s' pm pubnonces j = true ↔ s' = s :=
  ⟨fun h => partialSigVerify_unique C H h (partialSigVerify_sign C H hagg hj hs),
    fun h => h ▸ partialSigVerify_sign C H hagg hj hs⟩

/-! ## If the aggregate signature is invalid, a partial signature fails -/

/-- **An invalid aggregate signature has a partial signature that fails.** If
the signature that `SigAgg` returns, called with the aggregate nonce from
`NonceAgg`, does not pass `Verify`, then `PartialSigVerify` rejects the
partial signature of at least one signer. -/
theorem exists_partialSigVerify_eq_false {pm : List (X × M)} {pubnonces : List (PubNonce E)}
    {psigs : List (ZMod n)} {agg : PubNonce E} {sig : X × ZMod n}
    (hagg : nonceAgg pubnonces = some agg)
    (hsig : sigAgg C.ops H agg pm pubnonces psigs = some sig)
    (hver : verify C.ops H pm sig = false) :
    ∃ (i : ℕ) (hi : i < psigs.length),
      partialSigVerify C.ops H psigs[i] pm pubnonces i = false := by
  by_contra hcon
  push Not at hcon
  have hv := verify_sigAgg_of_partialSigVerify C H hagg hsig fun i hi => by
    simpa using hcon i hi
  rw [hv] at hver
  exact absurd hver (by simp)

/-! ## One bad partial signature makes the aggregate signature invalid -/

/-- How far the entry `(pkᵢ, mᵢ)`, `(R₁,ᵢ, R₂,ᵢ)`, `sᵢ` is from the equation of
`PartialSigVerify`: `sᵢ⋅G - (e⋅(R₁,ᵢ + b⋅R₂,ᵢ) + cᵢ⋅Pᵢ)`. -/
def defect (f : X × M → ZMod n) (R : E) (b : ZMod n) (t : (X × M) × PubNonce E × ZMod n) : E :=
  C.mulG t.2.2 -
    (C.ops.signOf R (t.2.1.1 + b.val • t.2.1.2) + (f t.1).val • (C.liftX t.1.1).getD 0)

/-- The defects add up to the defect of the equation of `Verify`. -/
theorem sum_defect (f : X × M → ZMod n) (R : E) (b : ZMod n) :
    ∀ (pm : List (X × M)) (pubnonces : List (PubNonce E)) (psigs : List (ZMod n)),
      pm.length = pubnonces.length → psigs.length = pm.length →
      ((pm.zip (pubnonces.zip psigs)).map (defect C f R b)).sum =
        C.mulG psigs.sum - (C.ops.signOf R ((pubnonces.map Prod.fst).sum +
            b.val • (pubnonces.map Prod.snd).sum) +
          (pm.map fun pkm => (f pkm).val • (C.liftX pkm.1).getD 0).sum)
  | [], [], [], _, _ => by simp
  | pkm :: pm, N :: pubnonces, s :: psigs, h1, h2 => by
    have ih := sum_defect f R b pm pubnonces psigs (by simpa using h1) (by simpa using h2)
    simp only [List.zip_cons_cons, List.map_cons, List.sum_cons, ih, defect, map_add, smul_add,
      signOf_add]
    abel
  | [], _ :: _, _, h1, _ => by simp at h1
  | _ :: _, [], _, h1, _ => by simp at h1
  | [], [], _ :: _, _, h2 => by simp at h2
  | _ :: _, _ :: _, [], _, h2 => by simp at h2

/-- A list in which all entries but one are zero sums to that entry. -/
theorem sum_eq_getElem_of_ne {l : List E} {i : ℕ} (hi : i < l.length)
    (h : ∀ (k : ℕ) (hk : k < l.length), k ≠ i → l[k] = 0) : l.sum = l[i] := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a t ih =>
    cases i with
    | zero =>
      have ht : t.sum = 0 := List.sum_eq_zero fun x hx => by
        obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hx
        exact h (k + 1) (by simpa using hk) (by simp)
      exact (by rw [List.sum_cons, ht, add_zero] : (a :: t).sum = a)
    | succ i =>
      have ha : a = 0 := h 0 (by simp) (by simp)
      have ht := ih (i := i) (by simpa using hi) fun k hk hne =>
        h (k + 1) (by simpa using hk) (by simpa using hne)
      rw [List.sum_cons, ha, zero_add]
      exact ht

/-- **If the aggregate signature is valid and all partial signatures but one
pass, the remaining one passes as well.** -/
theorem partialSigVerify_of_verify {pm : List (X × M)} {pubnonces : List (PubNonce E)}
    {psigs : List (ZMod n)} {agg : PubNonce E} {sig : X × ZMod n} {i : ℕ}
    (hagg : nonceAgg pubnonces = some agg)
    (hsig : sigAgg C.ops H agg pm pubnonces psigs = some sig)
    (hver : verify C.ops H pm sig = true) (hi : i < psigs.length)
    (hothers : ∀ (k : ℕ) (hk : k < psigs.length), k ≠ i →
      partialSigVerify C.ops H psigs[k] pm pubnonces k = true) :
    partialSigVerify C.ops H psigs[i] pm pubnonces i = true := by
  unfold sigAgg at hsig
  split_ifs at hsig with hlen
  push Not at hlen
  obtain ⟨⟨R, b⟩, hsv, rfl⟩ := Option.map_eq_some_iff.mp hsig
  obtain ⟨hne, hlen', hR, hReq⟩ := getSessionValues_eq_some C H hsv
  have hagg' := nonceAgg_eq_some hagg
  have hReq' : R = (pubnonces.map Prod.fst).sum + b.val • (pubnonces.map Prod.snd).sum := by
    rw [hReq, hagg']
  -- what `Verify` checks
  unfold verify at hver
  simp only [ops_x, ops_liftX, liftX_x_signOf C hR, Bool.and_eq_true, Bool.not_eq_true',
    List.isEmpty_eq_false_iff, List.all_eq_true, ops_mulG] at hver
  obtain ⟨⟨-, hlift⟩, heq⟩ := hver
  have heq' : C.mulG psigs.sum = C.ops.signOf R R +
      (pm.map fun pkm => (H.sig pm (C.x R) pkm).val • (C.liftX pkm.1).getD 0).sum :=
    of_decide_eq_true heq
  -- the defects add up to zero, and all but the one at `i` are zero
  set l := (pm.zip (pubnonces.zip psigs)).map (defect C (H.sig pm (C.x R)) R b) with hl
  have hsum : l.sum = 0 := by
    rw [hl, sum_defect C _ R b pm pubnonces psigs hlen' hlen, ← hReq', heq', sub_self]
  have hll : l.length = psigs.length := by
    simp only [hl, List.length_map, List.length_zip]; omega
  have hi₁ : i < pm.length := by omega
  have hi₂ : i < pubnonces.length := by omega
  have hget : ∀ (k : ℕ) (hk : k < psigs.length),
      l[k]'(by omega) = defect C (H.sig pm (C.x R)) R b
        (pm[k]'(by omega), pubnonces[k]'(by omega), psigs[k]) := fun k hk => by
    simp [hl, List.getElem_zip]
  have hzero : ∀ (k : ℕ) (hk : k < l.length), k ≠ i → l[k] = 0 := fun k hk hne => by
    have hk' : k < psigs.length := by omega
    obtain ⟨P, hP, hs⟩ := (partialSigVerify_iff C H hagg hsv psigs[k] (by omega) (by omega)).mp
      (hothers k hk' hne)
    rw [hget k hk']
    simp [defect, hP, hs]
  have hdef := (sum_eq_getElem_of_ne (by omega) hzero).symm.trans hsum
  rw [hget i hi] at hdef
  obtain ⟨P, hP⟩ := Option.isSome_iff_exists.mp (hlift pm[i] (List.getElem_mem hi₁))
  refine (partialSigVerify_iff C H hagg hsv psigs[i] hi₁ hi₂).mpr ⟨P, hP, ?_⟩
  simpa [defect, hP, sub_eq_zero] using hdef

/-- **One bad partial signature among good ones makes the aggregate signature
invalid.** If `PartialSigVerify` rejects the partial signature of signer `i`
and accepts those of all other signers, the signature from `SigAgg` does not
pass `Verify`. -/
theorem verify_eq_false_of_one_bad {pm : List (X × M)} {pubnonces : List (PubNonce E)}
    {psigs : List (ZMod n)} {agg : PubNonce E} {sig : X × ZMod n} {i : ℕ}
    (hagg : nonceAgg pubnonces = some agg)
    (hsig : sigAgg C.ops H agg pm pubnonces psigs = some sig) (hi : i < psigs.length)
    (hbad : partialSigVerify C.ops H psigs[i] pm pubnonces i = false)
    (hothers : ∀ (k : ℕ) (hk : k < psigs.length), k ≠ i →
      partialSigVerify C.ops H psigs[k] pm pubnonces k = true) :
    verify C.ops H pm sig = false := by
  by_contra hv
  rw [Bool.not_eq_false] at hv
  rw [partialSigVerify_of_verify C H hagg hsig hv hi hothers] at hbad
  exact absurd hbad (by simp)

end Dahlias
