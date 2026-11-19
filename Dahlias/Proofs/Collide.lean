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

/-- The entry `(pk, m)` of a key term. -/
def KeyTerm.entry (κ : KeyTerm n M) : X × M := (C.x (C.mulG (κ.1.sk x)), κ.2.1)

/-- The key part of a query point, from the entries and the table. -/
theorem keyPoint_eq_entries (P : E) (hP : ∀ τ : Tweak n, τ.pk C P = C.mulG (τ.sk x))
    (T : SigIn N X M → ZMod n) {pm : List (X × M)} (hN : pm.length ≤ N) (r : X)
    (keys : List (KeyTerm n M))
    (hkeys : ∀ κ ∈ keys, κ.1.sk x ≠ 0 ∧ κ.2.2 = T (⟨pm, hN⟩, r, κ.entry C x)) :
    keyPoint C P keys = ((keys.map (KeyTerm.entry C x)).map fun e =>
      (T (⟨pm, hN⟩, r, e)).val • (C.liftX e.1).getD 0).sum := by
  unfold keyPoint
  rw [List.map_map]
  refine congrArg List.sum (List.map_congr_left fun κ hκ => ?_)
  obtain ⟨hd, hc⟩ := hkeys κ hκ
  have hl : C.liftX (C.x (C.mulG (κ.1.sk x))) = some (evenLift C (C.mulG (κ.1.sk x))) :=
    liftX_x_signOf C (C.mulG_ne_zero hd)
  simp only [Function.comp_apply, KeyTerm.entry, hl, Option.getD_some, hP]
  rw [hc]
  rfl

/-- **Records of one slot with the same nonce coefficient input have the same
query point**, if the tables agree on the first record's oracle inputs. -/
theorem point_eq_of_ncIn_eq (T T' : SigIn N X M → ZMod n) (P : E) (U : ℕ → PubNonce E)
    {a a' : CloseRec n E X M}
    (ha : RecOk C nonceCoef N qs x nonces T a) (ha' : RecOk C nonceCoef N qs x nonces T' a')
    (hk : a.k = a'.k) (hnc : a.ncIn = a'.ncIn)
    (hT : ∀ (hN : a.pm.length ≤ N), ∀ κ ∈ a.keys,
      T' (⟨a.pm, hN⟩, C.x a.Rb.1, κ.entry C x) = T (⟨a.pm, hN⟩, C.x a.Rb.1, κ.entry C x))
    (hP : ∀ τ : Tweak n, τ.pk C P = C.mulG (τ.sk x)) :
    a.point C P U = a'.point C P U := by
  obtain ⟨hkq, hN, hlen, hb, -, hkeys, hkind⟩ := ha
  obtain ⟨hkq', hN', hlen', hb', -, hkeys', hkind'⟩ := ha'
  have hnc' := hnc
  simp only [CloseRec.ncIn, Prod.mk.injEq] at hnc'
  obtain ⟨hagg1, hagg2, hitems⟩ := hnc'
  have hb2 : a.Rb.2 = a'.Rb.2 := by rw [hb, hb', hnc]
  have hpmeq : a.pm = a'.pm := by
    rw [← coefItems_fst a.pm a.pubs hlen, ← coefItems_fst a'.pm a'.pubs hlen', hitems]
  have hfin : (⟨a.k, hkq⟩ : Fin qs) = ⟨a'.k, hkq'⟩ := Fin.ext hk
  -- the nonce point and the entries agree
  have hmain : a.Rb.1 = a'.Rb.1 ∧
      a.keys.map (KeyTerm.entry C x) = a'.keys.map (KeyTerm.entry C x) := by
    rcases hkind with ⟨τ, m, c, hks, hpre⟩ | ⟨hagg, hent, hR⟩
    · obtain ⟨hd, j, hj, hpm, hsv⟩ := signPre_some C hpre
      obtain ⟨-, -, hR, hne⟩ := getSessionValues_some C hsv
      rcases hkind' with ⟨τ', m', c', hks', hpre'⟩ | ⟨hagg', -, -⟩
      · obtain ⟨hd', j', hj', hpm', hsv'⟩ := signPre_some C hpre'
        obtain ⟨-, -, hR', -⟩ := getSessionValues_some C hsv'
        have hsnd : a.pubs.map Prod.snd = a'.pubs.map Prod.snd := by
          rw [← coefItems_snd a.pm a.pubs hlen, ← coefItems_snd a'.pm a'.pubs hlen', hitems]
        rw [matchIdxs_congr hsnd, hfin, hj'] at hj
        cases List.cons.inj hj |>.1
        rw [hpmeq, hpm'] at hpm
        refine ⟨by rw [hR, hR', hagg1, hagg2, hb2], ?_⟩
        rw [hks, hks']
        simp only [List.map_cons, List.map_nil, KeyTerm.entry]
        exact congrArg (fun e => [e]) (Option.some.inj hpm).symm
      · exact absurd (hagg1.trans (congrArg Prod.fst hagg')) hne
    · rcases hkind' with ⟨τ', m', c', hks', hpre'⟩ | ⟨hagg', hent', hR'⟩
      · obtain ⟨-, j', -, -, hsv'⟩ := signPre_some C hpre'
        obtain ⟨-, -, -, hne'⟩ := getSessionValues_some C hsv'
        exact absurd (hagg1.symm.trans (congrArg Prod.fst hagg)) hne'
      · exact ⟨by rw [hR, hR', hfin, hb2], hent.trans (hpmeq.trans hent'.symm)⟩
  obtain ⟨hR1, hents⟩ := hmain
  have hRb : a.Rb = a'.Rb := Prod.ext hR1 hb2
  simp only [CloseRec.point, dlogPoint, hk, hRb]
  congr 1
  rw [keyPoint_eq_entries C N x P hP T hN (C.x a.Rb.1) a.keys hkeys,
    keyPoint_eq_entries C N x P hP T' hN' (C.x a'.Rb.1) a'.keys hkeys', ← hents, ← hR1]
  refine congrArg List.sum (List.map_congr_left fun e he => ?_)
  obtain ⟨κ, hκ, rfl⟩ := List.mem_map.mp he
  have hsub : (⟨a'.pm, hN'⟩ : BList N X M) = ⟨a.pm, hN⟩ := Subtype.ext hpmeq.symm
  rw [hsub, hT hN κ hκ]

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
