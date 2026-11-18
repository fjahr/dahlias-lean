import Dahlias.Basic

/-!
# Correctness of BIP 459

* `partialSigVerify_sign`: a partial signature made by `Sign` passes
  `PartialSigVerify` at the signer's index.
* `verify_sigAgg_of_partialSigVerify`: if `PartialSigVerify` accepts the
  partial signatures of all signers, `SigAgg` with the aggregate nonce from
  `NonceAgg` gives a signature that `Verify` accepts. This is the claim in the
  BIP's description of `PartialSigVerify`.
* `verify_honest`: an honest session produces a signature that verifies.
* `tweakPK_mulG`: tweaking the secret key and tweaking the public key agree.

All statements hold for every choice of the hash functions.
-/

namespace Dahlias

open Taproot Taproot.Curve

variable {n : ℕ} [Fact n.Prime] {E X M : Type*} [AddCommGroup E] (C : Curve n E X)
  (H : Hashes n E X M)

@[simp] theorem ops_mulG : C.ops.mulG = C.mulG := rfl
@[simp] theorem ops_smul (k : ZMod n) (P : E) : C.ops.smul k P = k.val • P := rfl
@[simp] theorem ops_x : C.ops.x = C.x := rfl
@[simp] theorem ops_hasEvenY : C.ops.hasEvenY = C.hasEvenY := rfl
@[simp] theorem ops_liftX : C.ops.liftX = C.liftX := rfl
@[simp] theorem ops_evenScalar : C.ops.evenScalar = C.evenScalar := rfl

omit [Fact n.Prime] in
theorem signOf_add (O : Ops n E X) (R P Q : E) :
    O.signOf R (P + Q) = O.signOf R P + O.signOf R Q := by
  unfold Ops.signOf; split_ifs <;> simp [add_comm]

omit [Fact n.Prime] in
@[simp] theorem signOf_zero (O : Ops n E X) (R : E) : O.signOf R 0 = 0 := by
  unfold Ops.signOf; split_ifs <;> simp

/-- `lift_x(x(R))` is `R` or `-R`, whichever has an even y. -/
theorem liftX_x_signOf {R : E} (hR : R ≠ 0) : C.liftX (C.x R) = some (C.ops.signOf R R) := by
  unfold Ops.signOf
  by_cases h : C.hasEvenY R = true
  · simp [h, C.liftX_x R hR h]
  · have h' : C.hasEvenY (-R) = true := by rw [C.hasEvenY_neg R hR]; simpa using h
    simp only [ops_hasEvenY, h, Bool.false_eq_true, ↓reduceIte]
    rw [← C.x_neg]
    exact C.liftX_x _ (neg_ne_zero.mpr hR) h'

/-! ## Unfolding the algorithms -/

variable [DecidableEq E] [DecidableEq X] [DecidableEq M]

omit [Fact n.Prime] [DecidableEq X] [DecidableEq M] in
theorem nonceAgg_eq_some {pubnonces : List (PubNonce E)} {agg : PubNonce E}
    (h : nonceAgg pubnonces = some agg) :
    agg = ((pubnonces.map Prod.fst).sum, (pubnonces.map Prod.snd).sum) := by
  unfold nonceAgg at h
  dsimp only at h
  split_ifs at h
  exact (Option.some.inj h).symm

omit [DecidableEq X] [DecidableEq M] in
theorem getSessionValues_eq_some {agg : PubNonce E} {pm : List (X × M)}
    {pubnonces : List (PubNonce E)} {R : E} {b : ZMod n}
    (h : getSessionValues C.ops H agg pm pubnonces = some (R, b)) :
    pm ≠ [] ∧ pm.length = pubnonces.length ∧ R ≠ 0 ∧ R = agg.1 + b.val • agg.2 := by
  unfold getSessionValues at h
  dsimp only at h
  split_ifs at h with h1 h2
  · push Not at h1
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨h1.1, h1.2.1, h2, rfl⟩

/-! ## From partial signatures to the aggregate signature -/

omit [DecidableEq E] [DecidableEq X] [DecidableEq M] in
/-- Summing the equations that `PartialSigVerify` checks. -/
theorem sum_partial (f : X × M → ZMod n) (R : E) (b : ZMod n) :
    ∀ (pm : List (X × M)) (pubnonces : List (PubNonce E)) (psigs : List (ZMod n)),
      pm.length = pubnonces.length → psigs.length = pm.length →
      (∀ t ∈ pm.zip (pubnonces.zip psigs), ∃ P, C.liftX t.1.1 = some P ∧
        C.mulG t.2.2 = C.ops.signOf R (t.2.1.1 + b.val • t.2.1.2) + (f t.1).val • P) →
      (∀ pkm ∈ pm, (C.liftX pkm.1).isSome) ∧
      C.mulG psigs.sum = C.ops.signOf R ((pubnonces.map Prod.fst).sum +
          b.val • (pubnonces.map Prod.snd).sum) +
        (pm.map fun pkm => (f pkm).val • (C.liftX pkm.1).getD 0).sum
  | [], [], [], _, _, _ => by simp
  | pkm :: pm, N :: pubnonces, s :: psigs, h1, h2, h => by
    obtain ⟨P, hP, hs⟩ := h (pkm, N, s) (by simp)
    obtain ⟨ih1, ih2⟩ := sum_partial f R b pm pubnonces psigs (by simpa using h1)
      (by simpa using h2) fun t ht => h t (by simp [ht])
    refine ⟨by simpa [hP] using ih1, ?_⟩
    simp only [List.sum_cons, List.map_cons, map_add, hs, ih2, hP, Option.getD_some, smul_add,
      signOf_add]
    abel
  | [], _ :: _, _, h1, _, _ => by simp at h1
  | _ :: _, [], _, h1, _, _ => by simp at h1
  | [], [], _ :: _, _, h2, _ => by simp at h2
  | _ :: _, _ :: _, [], _, h2, _ => by simp at h2

omit [DecidableEq X] [DecidableEq M] in
/-- **Partial signatures that verify aggregate to a valid signature.** If
`PartialSigVerify` accepts the partial signature of every signer, then
`SigAgg`, called with the aggregate nonce from `NonceAgg`, returns a signature
that `Verify` accepts. -/
theorem verify_sigAgg_of_partialSigVerify {pm : List (X × M)} {pubnonces : List (PubNonce E)}
    {psigs : List (ZMod n)} {agg : PubNonce E} {sig : X × ZMod n}
    (hagg : nonceAgg pubnonces = some agg)
    (hsig : sigAgg C.ops H agg pm pubnonces psigs = some sig)
    (hpart : ∀ (i : ℕ) (hi : i < psigs.length),
      partialSigVerify C.ops H psigs[i] pm pubnonces i = true) :
    verify C.ops H pm sig = true := by
  unfold sigAgg at hsig
  split_ifs at hsig with hlen
  push Not at hlen
  obtain ⟨⟨R, b⟩, hsv, rfl⟩ := Option.map_eq_some_iff.mp hsig
  obtain ⟨hne, hlen', hR, hReq⟩ := getSessionValues_eq_some C H hsv
  have hagg' := nonceAgg_eq_some hagg
  have key := sum_partial C (H.sig pm (C.x R)) R b pm pubnonces psigs hlen' hlen (by
    intro t ht
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ht
    simp only [List.length_zip] at hi
    have hi1 : i < pm.length := by omega
    have hi2 : i < pubnonces.length := by omega
    have hi3 : i < psigs.length := by omega
    have hp := hpart i hi3
    unfold partialSigVerify at hp
    simp only [List.getElem?_eq_getElem hi1, List.getElem?_eq_getElem hi2, hagg,
      Option.bind_some, hsv] at hp
    split_ifs at hp with h0
    · cases hP : C.ops.liftX pm[i].1 with
      | none => simp [hP] at hp
      | some P =>
        simp only [hP, decide_eq_true_eq] at hp
        exact ⟨P, by simpa [List.getElem_zip] using hP, by simpa [List.getElem_zip] using hp⟩)
  obtain ⟨hlift, hsum⟩ := key
  unfold verify
  simp only [ops_x, ops_liftX, liftX_x_signOf C hR, Bool.and_eq_true, Bool.not_eq_true',
    List.isEmpty_eq_false_iff, List.all_eq_true, ops_mulG]
  refine ⟨⟨hne, hlift⟩, ?_⟩
  have hReq' : R = (pubnonces.map Prod.fst).sum + b.val • (pubnonces.map Prod.snd).sum := by
    rw [hReq, hagg']
  refine decide_eq_true (hsum.trans ?_)
  rw [← hReq']
  all_goals rfl

/-! ## From `Sign` to `PartialSigVerify` -/

omit [Fact n.Prime] [AddCommGroup E] [DecidableEq X] [DecidableEq M] in
theorem mem_matchIdxs {pubnonces : List (PubNonce E)} {R₂ : E} {j : ℕ} :
    j ∈ matchIdxs pubnonces R₂ ↔ (pubnonces[j]?).map Prod.snd = some R₂ := by
  unfold matchIdxs
  simp only [List.mem_filter, List.mem_range, decide_eq_true_eq, and_iff_right_iff_imp]
  intro h
  by_contra hj
  simp [List.getElem?_eq_none (not_lt.mp hj)] at h

/-- `Sign` fails on a zero nonce or secret key. -/
theorem sign_ne_zero {O : Ops n E X} {r₁ r₂ sk : ZMod n} {m : M} {agg : PubNonce E}
    {pm : List (X × M)} {pubnonces : List (PubNonce E)} {s : ZMod n}
    (hs : sign O H (r₁, r₂) sk m agg pm pubnonces = some s) : r₁ ≠ 0 ∧ r₂ ≠ 0 ∧ sk ≠ 0 := by
  unfold sign at hs
  dsimp only at hs
  split_ifs at hs with h0
  push Not at h0
  exact h0

/-- **A partial signature made by `Sign` passes `PartialSigVerify`**, at the
index `j` that holds the signer's public nonce, when the aggregate nonce is
the one `NonceAgg` computes. -/
theorem partialSigVerify_sign {r₁ r₂ sk : ZMod n} {m : M} {agg : PubNonce E}
    {pm : List (X × M)} {pubnonces : List (PubNonce E)} {s : ZMod n} {j : ℕ}
    (hagg : nonceAgg pubnonces = some agg)
    (hj : pubnonces[j]? = some (C.mulG r₁, C.mulG r₂))
    (hs : sign C.ops H (r₁, r₂) sk m agg pm pubnonces = some s) :
    partialSigVerify C.ops H s pm pubnonces j = true := by
  unfold sign at hs
  dsimp only at hs
  split_ifs at hs with h0
  push Not at h0
  obtain ⟨hr₁, hr₂, hsk⟩ := h0
  have hjm : j ∈ matchIdxs pubnonces (C.ops.mulG r₂) := by
    rw [mem_matchIdxs]; simp [hj]
  split at hs
  · rename_i j' hm
    rw [hm, List.mem_singleton] at hjm
    subst hjm
    split_ifs at hs with hpm
    obtain ⟨⟨R, b⟩, hsv, rfl⟩ := Option.map_eq_some_iff.mp hs
    unfold partialSigVerify
    simp only [hpm, hj, hagg, Option.bind_some, hsv, ops_mulG, ops_x, ops_liftX,
      C.liftX_x_mulG hsk, C.mulG_eq_zero, hr₁, hr₂, or_self, ↓reduceIte, decide_eq_true_eq]
    simp only [ops_smul, ops_evenScalar, C.val_smul_mulG, map_add, Ops.signOf, ops_hasEvenY]
    by_cases he : C.hasEvenY R = true <;> simp [he, map_neg, add_comm]
  · exact absurd hs (by simp)

/-! ## An honest session -/

/-- One signer of an honest session: secret key, message and secret nonce. -/
structure Signer (n : ℕ) (M : Type*) where
  sk : ZMod n
  m : M
  r₁ : ZMod n
  r₂ : ZMod n

/-- The signer's entry `(pk, m)` of the list `L`. -/
def Signer.pkm (C : Curve n E X) (σ : Signer n M) : X × M := (C.x (C.mulG σ.sk), σ.m)

/-- The signer's public nonce. -/
def Signer.pubnonce (C : Curve n E X) (σ : Signer n M) : PubNonce E :=
  (C.mulG σ.r₁, C.mulG σ.r₂)

/-- **An honest session produces a valid signature.** If every signer's
`Sign` succeeds on the list, the public nonces and the aggregate nonce from
`NonceAgg`, then the output of `SigAgg` passes `Verify`.

`Sign` fails for some signer exactly when a scalar is zero, two signers have
the same `R₂`, or a nonce sum is the point at infinity; for nonces drawn at
random this has negligible probability. -/
theorem verify_honest {signers : List (Signer n M)} {agg : PubNonce E} {psigs : List (ZMod n)}
    {sig : X × ZMod n}
    (hagg : nonceAgg (signers.map (Signer.pubnonce C)) = some agg)
    (hlen : psigs.length = signers.length)
    (hsign : ∀ (i : ℕ) (hi : i < signers.length),
      sign C.ops H (signers[i].r₁, signers[i].r₂) signers[i].sk signers[i].m agg
        (signers.map (Signer.pkm C)) (signers.map (Signer.pubnonce C)) = some (psigs[i]'(by omega)))
    (hsig : sigAgg C.ops H agg (signers.map (Signer.pkm C)) (signers.map (Signer.pubnonce C))
      psigs = some sig) :
    verify C.ops H (signers.map (Signer.pkm C)) sig = true := by
  refine verify_sigAgg_of_partialSigVerify C H hagg hsig fun i hi => ?_
  have hi' : i < signers.length := by omega
  exact partialSigVerify_sign C H hagg (by simp [hi', Signer.pubnonce]) (hsign i hi')

/-! ## Key tweaking -/

omit [DecidableEq X] [DecidableEq M] in
/-- **The two tweaks agree**: `TweakPK` on the public key of `sk` gives the
public key of `TweakSK(sk)`, and one fails exactly when the other does. -/
theorem tweakPK_mulG (sk t : ZMod n) (xonly : Bool) :
    tweakPK C.ops (C.mulG sk) t xonly = (tweakSK C.ops sk t xonly).map C.mulG := by
  unfold tweakPK tweakSK
  simp only [ops_hasEvenY, ops_mulG, ops_evenScalar]
  cases xonly
  · simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, ← map_add, C.mulG_eq_zero]
    split_ifs <;> simp
  · unfold Curve.evenScalar
    by_cases h : C.hasEvenY (C.mulG sk) = true
    · simp only [h, Bool.true_and, Bool.not_true, Bool.false_eq_true, ↓reduceIte, ← map_add,
        C.mulG_eq_zero]
      split_ifs <;> simp
    · rw [Bool.not_eq_true] at h
      simp only [h, Bool.true_and, Bool.not_false, Bool.false_eq_true, ↓reduceIte, ← map_neg,
        ← map_add, C.mulG_eq_zero]
      split_ifs <;> simp

end Dahlias
