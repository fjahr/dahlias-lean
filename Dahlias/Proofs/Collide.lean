import Dahlias.Proofs.Solve

/-!
# Equal nonce coefficient inputs give equal queries

`point_eq_of_ncIn_eq`: two records of the same session, one from each run of
the fork, with the same input to the nonce coefficient hash have the same
discrete logarithm query point. So if the reduction asked two different
queries for a session and their nonce coefficients agree, the inputs differ
and the nonce coefficient hash has a collision, which `collider` finds
(`collider_isCollision`).
-/

set_option linter.unusedSectionVars false

namespace Dahlias.Security

open Taproot Function

variable {n : ℕ} [Fact n.Prime] {E X M : Type} [AddCommGroup E] [DecidableEq E] [DecidableEq X]
  [DecidableEq M] (C : Curve n E X) (nonceCoef : E → E → List (X × M × E) → ZMod n) (N qs : ℕ)

/-! ## What the checks of `Sign` determine -/

theorem getSessionValues_some {H : Hashes n E X M} {agg : PubNonce E} {pm : List (X × M)}
    {pubs : List (PubNonce E)} {Rb : E × ZMod n}
    (h : getSessionValues C.ops H agg pm pubs = some Rb) :
    pm.length = pubs.length ∧ Rb.2 = H.nonceCoef agg.1 agg.2 (coefItems pm pubs) ∧
      Rb.1 = agg.1 + Rb.2.val • agg.2 := by
  unfold getSessionValues at h
  dsimp only at h
  split_ifs at h with h1 h2
  push Not at h1
  cases Option.some.inj h
  exact ⟨h1.2.1, rfl, rfl⟩

theorem signPre_some {H : Hashes n E X M} {r₁ r₂ d : ZMod n} {m : M} {agg : PubNonce E}
    {pm : List (X × M)} {pubs : List (PubNonce E)} {Rb : E × ZMod n}
    (h : signPre C.ops H (r₁, r₂) d m agg pm pubs = some Rb) :
    d ≠ 0 ∧ ∃ j, matchIdxs pubs (C.mulG r₂) = [j] ∧ pm[j]? = some (C.x (C.mulG d), m) ∧
      getSessionValues C.ops H agg pm pubs = some Rb := by
  unfold signPre at h
  dsimp only at h
  split_ifs at h with h0
  push Not at h0
  refine ⟨h0.2.2, ?_⟩
  split at h
  · rename_i j hj
    split_ifs at h with hpm
    exact ⟨j, hj, hpm, h⟩
  · exact absurd h (by simp)

omit [Fact n.Prime] [AddCommGroup E] [DecidableEq E] [DecidableEq X] [DecidableEq M] in
theorem coefItems_fst : ∀ (pm : List (X × M)) (pubs : List (PubNonce E)),
    pm.length = pubs.length → (coefItems pm pubs).map (fun t => (t.1, t.2.1)) = pm
  | [], [], _ => rfl
  | a :: pm, b :: pubs, h => by
    simp only [coefItems, List.zipWith_cons_cons, List.map_cons, List.cons.injEq, true_and]
    exact coefItems_fst pm pubs (by simpa using h)
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

omit [Fact n.Prime] [AddCommGroup E] [DecidableEq E] [DecidableEq X] [DecidableEq M] in
theorem coefItems_snd : ∀ (pm : List (X × M)) (pubs : List (PubNonce E)),
    pm.length = pubs.length → (coefItems pm pubs).map (fun t => t.2.2) = pubs.map Prod.snd
  | [], [], _ => rfl
  | a :: pm, b :: pubs, h => by
    simp only [coefItems, List.zipWith_cons_cons, List.map_cons, List.cons.injEq, true_and]
    exact coefItems_snd pm pubs (by simpa using h)
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

omit [Fact n.Prime] [AddCommGroup E] [DecidableEq X] [DecidableEq M] in
theorem matchIdxs_congr {pubs pubs' : List (PubNonce E)}
    (h : pubs.map Prod.snd = pubs'.map Prod.snd) (R : E) :
    matchIdxs pubs R = matchIdxs pubs' R := by
  have hlen : pubs.length = pubs'.length := by simpa using congrArg List.length h
  unfold matchIdxs
  rw [hlen]
  refine List.filter_congr fun j _ => ?_
  rw [← List.getElem?_map, ← List.getElem?_map, h]

omit [DecidableEq X] [DecidableEq M] in
theorem evenLift_eq_of_x {P P' : E} (hP : P ≠ 0) (hP' : P' ≠ 0) (h : C.x P = C.x P') :
    evenLift C P = evenLift C P' := by
  have h1 := liftX_x_signOf C hP
  have h2 := liftX_x_signOf C hP'
  rw [h, h2] at h1
  exact (Option.some.inj h1).symm

/-! ## Equal inputs, equal queries -/

variable (x : ZMod n) (nonces : Fin qs → SecNonce n)

/-- **Records of one session with the same nonce coefficient input have the
same query point**, if the tables agree on the first record's oracle input. -/
theorem point_eq_of_ncIn_eq (T T' : SigIn N X M → ZMod n) (P : E) (U : ℕ → PubNonce E)
    {a a' : CloseRec n E X M}
    (ha : RecOk C nonceCoef N qs x nonces T a) (ha' : RecOk C nonceCoef N qs x nonces T' a')
    (hk : a.k = a'.k) (hnc : a.ncIn = a'.ncIn)
    (hT : ∀ hN : a.pm.length ≤ N,
      T' (⟨a.pm, hN⟩, C.x a.Rb.1, (C.x (C.mulG (a.τ.sk x)), a.m)) =
        T (⟨a.pm, hN⟩, C.x a.Rb.1, (C.x (C.mulG (a.τ.sk x)), a.m)))
    (hP : ∀ τ : Tweak n, τ.pk C P = C.mulG (τ.sk x)) :
    a.point C P U = a'.point C P U := by
  obtain ⟨hkq, hN, -, hpre, hc, -⟩ := ha
  obtain ⟨hkq', hN', -, hpre', hc', -⟩ := ha'
  obtain ⟨hd, j, hj, hpm, hsv⟩ := signPre_some C hpre
  obtain ⟨hd', j', hj', hpm', hsv'⟩ := signPre_some C hpre'
  obtain ⟨hlen, hb, hR⟩ := getSessionValues_some C hsv
  obtain ⟨hlen', hb', hR'⟩ := getSessionValues_some C hsv'
  simp only [CloseRec.ncIn, Prod.mk.injEq] at hnc
  obtain ⟨hagg1, hagg2, hitems⟩ := hnc
  -- the session values agree
  have hRb : a.Rb = a'.Rb := by
    have h2 : a.Rb.2 = a'.Rb.2 := by rw [hb, hb', hagg1, hagg2, hitems]
    exact Prod.ext (by rw [hR, hR', hagg1, hagg2, h2]) h2
  -- the lists agree
  have hpmeq : a.pm = a'.pm := by
    rw [← coefItems_fst a.pm a.pubs hlen, ← coefItems_fst a'.pm a'.pubs hlen', hitems]
  have hsnd : a.pubs.map Prod.snd = a'.pubs.map Prod.snd := by
    rw [← coefItems_snd a.pm a.pubs hlen, ← coefItems_snd a'.pm a'.pubs hlen', hitems]
  -- so does the signer's entry
  have hfin : (⟨a.k, hkq⟩ : Fin qs) = ⟨a'.k, hkq'⟩ := Fin.ext hk
  rw [matchIdxs_congr hsnd, hfin, hj'] at hj
  cases List.cons.inj hj |>.1
  rw [hpmeq, hpm'] at hpm
  simp only [Option.some.injEq, Prod.mk.injEq] at hpm
  obtain ⟨hx, hm⟩ := hpm
  -- and the challenge
  have hceq : a.c = a'.c := by
    rw [hc, hc', ← hT hN]
    congr 1
    simp only [Prod.mk.injEq, Subtype.mk.injEq]
    exact ⟨hpmeq, by rw [hRb], hx.symm, hm.symm⟩
  simp only [CloseRec.point, dlogPoint, hP, hk, hRb, hceq]
  congr 2
  exact (evenLift_eq_of_x C (C.mulG_ne_zero hd') (C.mulG_ne_zero hd) hx).symm

/-! ## The collision finder -/

variable {Coins : Type} (A : Adversary n N E X M Coins)

open Classical in
/-- **The collision finder finds a collision when there is one** between
records of the same session of the two runs. -/
theorem collider_isCollision (p : ForgeSample n N qs X M Coins × ZMod n) {z : SigIn N X M}
    (hz : forkPoint C N (p.1.1 : ZMod n) (gameRecs C nonceCoef N qs A p.1 p.1.2.2.2).1
      (gameRecs C nonceCoef N qs A p.1 p.1.2.2.2).2.1 = some z)
    {a a' : CloseRec n E X M} (ha : a ∈ (gameRecs C nonceCoef N qs A p.1 p.1.2.2.2).2.2)
    (ha' : a' ∈ (gameRecs C nonceCoef N qs A p.1 (update p.1.2.2.2 z p.2)).2.2)
    (hk : a.k = a'.k) (hcol : IsCollision nonceCoef (a.ncIn, a'.ncIn)) :
    IsCollision nonceCoef (collider C nonceCoef N qs A p) := by
  unfold collider
  simp only [hz]
  have hex : ((gameRecs C nonceCoef N qs A p.1 p.1.2.2.2).2.2.product
      (gameRecs C nonceCoef N qs A p.1 (update p.1.2.2.2 z p.2)).2.2).find? (fun ab =>
        decide (ab.1.k = ab.2.k ∧ IsCollision nonceCoef (ab.1.ncIn, ab.2.ncIn))) ≠ none := by
    rw [Ne, List.find?_eq_none]
    push Not
    exact ⟨(a, a'), List.pair_mem_product.mpr ⟨ha, ha'⟩, by simp [hk, hcol]⟩
  obtain ⟨ab, hab⟩ := Option.ne_none_iff_exists'.mp hex
  rw [hab]
  have := List.find?_some hab
  simp only [decide_eq_true_eq] at this
  exact this.2

end Dahlias.Security
