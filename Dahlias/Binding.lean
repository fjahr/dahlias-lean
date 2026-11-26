import Dahlias.Proofs.Extract

/-!
# BIP 459 is strongly binding

No adversary can find a signature that is valid for two different lists of
public key and message pairs, except with small probability. This is
Theorem 3 of the DahLIAS paper (ePrint 2025/692) for the verification
algorithm of BIP 459.

## The game

The adversary is a deterministic algorithm with coins that queries the
challenge hash, a random oracle on lists of at most `N` entries as in
`Dahlias.Security`. It outputs two lists and a signature and wins if the lists
differ, have at most `N` entries, and the signature verifies for both
(`bindExperiment`).

## The theorem

`strongly_binding`: an adversary with at most `qh` different oracle queries
wins with probability at most `(qh + 2⋅N)² / n`.

The theorem is for groups of prime order (`Curve.PrimeOrder`: every point `P`
has `n⋅P = 0`), which secp256k1 is. The proof needs it because the public keys
in the lists are arbitrary points of the curve. BIP 459's x-only public keys
are never the point at infinity, which the paper has to require separately.
-/

set_option linter.unusedSectionVars false
set_option linter.deprecated false

namespace Dahlias.Security

open Taproot QTree Function

variable {n : ℕ} [Fact n.Prime] {E X M : Type} [AddCommGroup E] [DecidableEq E] [DecidableEq X]
  [DecidableEq M] (C : Curve n E X) (nonceCoef : E → E → List (X × M × E) → ZMod n) (N : ℕ)

/-- A binding adversary with coins in `Coins`: it queries the challenge hash
and outputs two lists and a signature. -/
abbrev BindAdversary (n N : ℕ) (X M Coins : Type) :=
  Coins → QTree (SigIn N X M) (ZMod n) (List (X × M) × List (X × M) × (X × ZMod n))

/-- **The strong binding game** on one sample. -/
def bindExperiment {Coins : Type} (A : BindAdversary n N X M Coins)
    (ω : Coins × (SigIn N X M → ZMod n)) : Prop :=
  (eval ω.2 (A ω.1)).1 ≠ (eval ω.2 (A ω.1)).2.1 ∧
    (eval ω.2 (A ω.1)).1.length ≤ N ∧ (eval ω.2 (A ω.1)).2.1.length ≤ N ∧
    verify C.ops (hashesOf N nonceCoef ω.2) (eval ω.2 (A ω.1)).1 (eval ω.2 (A ω.1)).2.2 = true ∧
    verify C.ops (hashesOf N nonceCoef ω.2) (eval ω.2 (A ω.1)).2.1 (eval ω.2 (A ω.1)).2.2 = true

/-! ## The adversary followed by the verifier's queries -/

/-- The oracle inputs of the verifier for the list `L` and the nonce `r`. -/
def keysOf (L : List (X × M)) (hL : L.length ≤ N) (r : X) : List (SigIn N X M) :=
  L.map fun e => (⟨L, hL⟩, r, e)

/-- The oracle inputs of the verifier for the adversary's output. -/
def ptsOf (out : List (X × M) × List (X × M) × (X × ZMod n)) : List (SigIn N X M) :=
  if h : out.1.length ≤ N ∧ out.2.1.length ≤ N then
    keysOf N out.1 h.1 out.2.2.1 ++ keysOf N out.2.1 h.2 out.2.2.1
  else []

variable {Coins : Type} (A : BindAdversary n N X M Coins)

/-- The adversary, followed by the verifier's queries. -/
def withVerifier (coins : Coins) :
    QTree (SigIn N X M) (ZMod n) (List (X × M) × List (X × M) × (X × ZMod n)) :=
  A coins >>= fun out => (queryAll (ptsOf N out) : QTree _ _ Unit) >>= fun _ => .done out

theorem length_ptsOf (out : List (X × M) × List (X × M) × (X × ZMod n)) :
    (ptsOf N out).length ≤ 2 * N := by
  unfold ptsOf keysOf
  split_ifs with h
  · simp only [List.length_append, List.length_map]
    omega
  · simp

theorem length_fresh_withVerifier (T : SigIn N X M → ZMod n) (coins : Coins) (qh : ℕ)
    (hA : (fresh T (A coins)).length ≤ qh) :
    (fresh T (withVerifier N A coins)).length ≤ qh + 2 * N := by
  unfold withVerifier
  rw [fresh_bind, flog_bind]
  have h1 := length_flog_queryAll T (fresh T (A coins)) (ptsOf N (eval T (A coins)))
  have h2 := length_ptsOf (n := n) N (eval T (A coins))
  exact (le_of_eq rfl).trans (h1.trans (by omega))

theorem ptsOf_subset_fresh (T : SigIn N X M → ZMod n) (coins : Coins) :
    ptsOf N (eval T (A coins)) ⊆ fresh T (withVerifier N A coins) := by
  unfold withVerifier
  rw [fresh_bind, flog_bind]
  exact subset_flog_queryAll T _ _

/-! ## The bad event -/

/-- Every public key of the list lifts. -/
def Lifts (L : List (X × M)) : Prop := ∀ e ∈ L, (C.liftX e.1).isSome

/-- The bad event at a fresh query `z` with earlier fresh queries `pre`: the
key sum of the list of `z` equals the key sum of a different list, all of
whose oracle inputs were queried before. -/
def BadAt (T : SigIn N X M → ZMod n) (pre : List (SigIn N X M)) (z : SigIn N X M) : Prop :=
  z.2.2 ∈ z.1.1 ∧ Lifts C z.1.1 ∧ ∃ p ∈ pre, p.2.1 = z.2.1 ∧ p.1 ≠ z.1 ∧
    (∀ e' ∈ p.1.1, (p.1, z.2.1, e') ∈ pre) ∧
    keySum C.ops (hashesOf N nonceCoef T) z.1.1 z.2.1 =
      keySum C.ops (hashesOf N nonceCoef T) p.1.1 z.2.1

/-- The bad event at the `j`-th fresh query. -/
def Bad (coins : Coins) (j : ℕ) (T : SigIn N X M → ZMod n) : Prop :=
  ∃ z, (fresh T (withVerifier N A coins))[j]? = some z ∧
    BadAt C nonceCoef N T ((fresh T (withVerifier N A coins)).take j) z

theorem verify_true {H : Hashes n E X M} {L : List (X × M)} {sig : X × ZMod n}
    (h : verify C.ops H L sig = true) :
    L ≠ [] ∧ Lifts C L ∧
      ∃ R, C.liftX sig.1 = some R ∧ C.mulG sig.2 = R + keySum C.ops H L sig.1 := by
  unfold verify at h
  cases hR : C.ops.liftX sig.1 with
  | none => simp [hR] at h
  | some R =>
    simp only [hR, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
      List.all_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1.1, h.1.2, R, hR, h.2⟩

theorem mem_take_of_idxOf_lt {α : Type} [BEq α] [LawfulBEq α] {F : List α} {y : α} {j : ℕ}
    (hy : y ∈ F) (h : F.idxOf y < j) : y ∈ F.take j := by
  rw [List.mem_take_iff_getElem]
  exact ⟨F.idxOf y, by
    have := List.idxOf_lt_length_of_mem hy
    omega, List.getElem_idxOf _⟩

/-- **A win makes the bad event happen** at one of the fresh queries. -/
theorem bad_of_win (T : SigIn N X M → ZMod n) (coins : Coins) (qh : ℕ)
    (hA : (fresh T (A coins)).length ≤ qh) (hwin : bindExperiment C nonceCoef N A (coins, T)) :
    ∃ j, j < qh + 2 * N ∧ Bad C nonceCoef N A coins j T := by
  obtain ⟨hne, hL, hL', hv, hv'⟩ := hwin
  dsimp only at hne hL hL' hv hv'
  set out := eval T (A coins) with hout
  obtain ⟨hnil, hlift, R, hR, hs⟩ := verify_true C hv
  obtain ⟨hnil', hlift', R', hR', hs'⟩ := verify_true C hv'
  have hRR : R' = R := Option.some.inj (hR'.symm.trans hR)
  have hks : keySum C.ops (hashesOf N nonceCoef T) out.1 out.2.2.1 =
      keySum C.ops (hashesOf N nonceCoef T) out.2.1 out.2.2.1 := by
    rw [hRR] at hs'
    exact add_left_cancel (hs.symm.trans hs')
  set F := fresh T (withVerifier N A coins) with hF
  have hlenF : F.length ≤ qh + 2 * N := length_fresh_withVerifier N A T coins qh hA
  have hsub : keysOf N out.1 hL out.2.2.1 ++ keysOf N out.2.1 hL' out.2.2.1 ⊆ F := by
    have := ptsOf_subset_fresh N A T coins
    rw [← hout, ptsOf, dif_pos ⟨hL, hL'⟩] at this
    exact this
  set K := keysOf N out.1 hL out.2.2.1 ++ keysOf N out.2.1 hL' out.2.2.1 with hK
  have hKne : K.toFinset.Nonempty := by
    obtain ⟨e, he⟩ := List.exists_mem_of_ne_nil _ hnil
    exact ⟨(⟨out.1, hL⟩, out.2.2.1, e), by simp [hK, keysOf, he]⟩
  let idx : SigIn N X M → ℕ := fun y => F.idxOf y
  obtain ⟨z, hzK, hmax⟩ := Finset.exists_max_image K.toFinset idx hKne
  rw [List.mem_toFinset] at hzK
  have hzF : z ∈ F := hsub hzK
  have hjlt : idx z < F.length := List.idxOf_lt_length_of_mem hzF
  have hget : F[idx z]? = some z := List.getElem?_idxOf hzF
  have hpre : ∀ y ∈ K, y ≠ z → y ∈ F.take (idx z) := by
    intro y hy hyz
    have hle : idx y ≤ idx z := hmax y (List.mem_toFinset.mpr hy)
    have hneq : idx y ≠ idx z := fun h => hyz ((List.idxOf_inj (hsub hy)).mp h)
    exact mem_take_of_idxOf_lt (hsub hy) (lt_of_le_of_ne hle hneq)
  refine ⟨idx z, by omega, z, hget, ?_⟩
  rcases List.mem_append.mp hzK with hz | hz
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hz
    obtain ⟨e₀, he₀⟩ := List.exists_mem_of_ne_nil _ hnil'
    have hsne : (⟨out.2.1, hL'⟩ : BList N X M) ≠ ⟨out.1, hL⟩ := fun h =>
      hne (congrArg Subtype.val h).symm
    refine ⟨he, hlift, (⟨out.2.1, hL'⟩, out.2.2.1, e₀), ?_, rfl, hsne, ?_, hks⟩
    · exact hpre _ (by simp [hK, keysOf, he₀]) fun h => hsne (congrArg Prod.fst h)
    · intro e' he'
      exact hpre _ (by simp [hK, keysOf, he']) fun h => hsne (congrArg Prod.fst h)
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hz
    obtain ⟨e₀, he₀⟩ := List.exists_mem_of_ne_nil _ hnil
    have hsne : (⟨out.1, hL⟩ : BList N X M) ≠ ⟨out.2.1, hL'⟩ := fun h =>
      hne (congrArg Subtype.val h)
    refine ⟨he, hlift', (⟨out.1, hL⟩, out.2.2.1, e₀), ?_, rfl, hsne, ?_, hks.symm⟩
    · exact hpre _ (by simp [hK, keysOf, he₀]) fun h => hsne (congrArg Prod.fst h)
    · intro e' he'
      exact hpre _ (by simp [hK, keysOf, he']) fun h => hsne (congrArg Prod.fst h)

/-! ## The bad event is unlikely -/

/-- The key sum does not depend on a table entry it does not use. -/
theorem keySum_update_of_ne (T : SigIn N X M → ZMod n) (z : SigIn N X M) (s : ZMod n)
    (L : BList N X M) (r : X) (h : ∀ e ∈ L.1, (L, r, e) ≠ z) :
    keySum C.ops (hashesOf N nonceCoef (update T z s)) L.1 r =
      keySum C.ops (hashesOf N nonceCoef T) L.1 r := by
  unfold keySum
  congr 1
  refine List.map_congr_left fun e he => ?_
  simp only [hashesOf, L.2, ↓reduceDIte]
  rw [update_of_ne (h e he)]

/-- How the key sum of the list of `z` depends on the table entry at `z`. -/
theorem keySum_update_sub (hE : Curve.PrimeOrder n E) (T : SigIn N X M → ZMod n)
    (z : SigIn N X M) (s s' : ZMod n) :
    keySum C.ops (hashesOf N nonceCoef (update T z s)) z.1.1 z.2.1 -
        keySum C.ops (hashesOf N nonceCoef (update T z s')) z.1.1 z.2.1 =
      (z.1.1.filter fun a => decide (a = z.2.2)).length •
        ((s - s').val • (C.liftX z.2.2.1).getD 0) := by
  obtain ⟨⟨L, hL⟩, r, e⟩ := z
  unfold keySum
  rw [sum_map_sub', ← sum_map_ite_eq_count]
  congr 1
  refine List.map_congr_left fun a _ => ?_
  simp only [hashesOf, hL, ↓reduceDIte, ops_smul, ops_liftX]
  by_cases ha : a = e
  · subst ha
    rw [if_pos rfl, update_self, update_self]
    exact (Curve.val_sub_smul (hE _) s s').symm
  · have hza : ((⟨L, hL⟩, r, a) : SigIn N X M) ≠ (⟨L, hL⟩, r, e) := fun h =>
      ha (congrArg (fun t => t.2.2) h)
    rw [if_neg ha, update_of_ne hza, update_of_ne hza, sub_self]

open Classical in
/-- **At most one new value per earlier query makes the bad event happen.** -/
theorem card_badAt_le (hE : Curve.PrimeOrder n E) (hN : N < n) (T : SigIn N X M → ZMod n)
    (pre : List (SigIn N X M)) (z : SigIn N X M) (hz : z ∉ pre) :
    (Finset.univ.filter fun s => BadAt C nonceCoef N (update T z s) pre z).card ≤ pre.length := by
  set Q : SigIn N X M → ZMod n → Prop := fun p s =>
    z.2.2 ∈ z.1.1 ∧ Lifts C z.1.1 ∧ p.1 ≠ z.1 ∧ (∀ e' ∈ p.1.1, (p.1, z.2.1, e') ∈ pre) ∧
      keySum C.ops (hashesOf N nonceCoef (update T z s)) z.1.1 z.2.1 =
        keySum C.ops (hashesOf N nonceCoef (update T z s)) p.1.1 z.2.1 with hQ
  have hsub : (Finset.univ.filter fun s => BadAt C nonceCoef N (update T z s) pre z) ⊆
      pre.toFinset.biUnion fun p => Finset.univ.filter (Q p) := by
    intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
    obtain ⟨h1, h2, p, hp, -, h4, h5, h6⟩ := hs
    simp only [Finset.mem_biUnion, List.mem_toFinset, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact ⟨p, hp, h1, h2, h4, h5, h6⟩
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  refine (Finset.sum_le_sum (g := fun _ => 1) fun p _ => ?_).trans ?_
  · -- one value per `p`
    rw [Finset.card_le_one]
    intro s hs s' hs'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs hs'
    obtain ⟨hmem, hlift, hne, hall, hks⟩ := hs
    obtain ⟨-, -, -, -, hks'⟩ := hs'
    have hind : ∀ t : ZMod n, keySum C.ops (hashesOf N nonceCoef (update T z t)) p.1.1 z.2.1 =
        keySum C.ops (hashesOf N nonceCoef T) p.1.1 z.2.1 := fun t =>
      keySum_update_of_ne C nonceCoef N T z t p.1 z.2.1 fun e' he' h =>
        hz (h ▸ hall e' he')
    have hdiff := keySum_update_sub C nonceCoef N hE T z s s'
    rw [hks, hks', hind, hind, sub_self] at hdiff
    -- the public key of `z` is a nonzero point
    obtain ⟨P, hP⟩ := Option.isSome_iff_exists.mp (hlift z.2.2 hmem)
    have hP0 : P ≠ 0 := (C.liftX_spec _ _ hP).1
    rw [hP, Option.getD_some] at hdiff
    set cnt := (z.1.1.filter fun a => decide (a = z.2.2)).length with hcnt
    have hpos : 0 < cnt := List.length_pos_of_mem (List.mem_filter.mpr ⟨hmem, by simp⟩)
    have hle : cnt ≤ z.1.1.length := List.length_filter_le _ _
    have hlt : cnt < n := lt_of_le_of_lt (hle.trans z.1.2) hN
    have hval : ((cnt : ZMod n)).val = cnt := ZMod.val_natCast_of_lt hlt
    have hzero : ((cnt : ZMod n) * (s - s')).val • P = 0 := by
      rw [Curve.val_mul_smul (hE P), hval]
      exact hdiff.symm
    by_contra hss
    have hc0 : (cnt : ZMod n) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact Nat.not_dvd_of_pos_of_lt hpos hlt
    exact hP0 (Curve.eq_zero_of_val_smul (hE P) (mul_ne_zero hc0 (sub_ne_zero.mpr hss)) hzero)
  · simp only [Finset.sum_const, smul_eq_mul, mul_one]
    exact List.toFinset_card_le pre

variable [Fintype Coins] [Fintype (SigIn N X M)]

open Classical in
/-- **The bad event at the `j`-th fresh query has probability at most `j / n`.** -/
theorem prob_bad_le (hE : Curve.PrimeOrder n E) (hN : N < n) (j : ℕ) :
    prob (fun ω : Coins × (SigIn N X M → ZMod n) => Bad C nonceCoef N A ω.1 j ω.2) ≤ j / n := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Fact.out : n.Prime).pos
  rw [prob_eq_sum, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul]
  rcases isEmpty_or_nonempty Coins with hC | hC
  · simp only [Finset.univ_eq_empty, Finset.sum_empty, zero_div]
    positivity
  have hK : (0 : ℝ) < Fintype.card Coins := Nat.cast_pos.mpr Fintype.card_pos
  have hM : (0 : ℝ) < Fintype.card (SigIn N X M → ZMod n) := Nat.cast_pos.mpr Fintype.card_pos
  -- for all coins
  have hone : ∀ coins : Coins,
      (∑ T, if Bad C nonceCoef N A coins j T then (1 : ℝ) else 0) ≤
        Fintype.card (SigIn N X M → ZMod n) * (j / n) := by
    intro coins
    set x : (SigIn N X M → ZMod n) → Option (SigIn N X M) :=
      fun T => (fresh T (withVerifier N A coins))[j]? with hx
    have hxinv : ∀ T d s, x T = some d → x (update T d s) = some d := fun T d s hd =>
      fresh_update T d s _ hd
    have hres := LocalFork.sum_resample hxinv
      fun T => if Bad C nonceCoef N A coins j T then (1 : ℝ) else 0
    have hbound : ∀ T, (∑ s, if Bad C nonceCoef N A coins j (LocalFork.upd x T s)
        then (1 : ℝ) else 0) ≤ j := by
      intro T
      cases hxT : x T with
      | none =>
        have : ∀ s, ¬Bad C nonceCoef N A coins j (LocalFork.upd x T s) := by
          rintro s ⟨z, hz, -⟩
          simp only [LocalFork.upd, hxT] at hz
          rw [show (fresh T (withVerifier N A coins))[j]? = x T from rfl, hxT] at hz
          exact absurd hz (by simp)
        simp [this]
      | some z =>
        set F := fresh T (withVerifier N A coins) with hF
        have hzj : F[j]? = some z := hxT
        have hznot : z ∉ F.take j := by
          intro hmem
          obtain ⟨i, hi, hiz⟩ := List.mem_take_iff_getElem.mp hmem
          obtain ⟨hjlt, hjz⟩ := List.getElem?_eq_some_iff.mp hzj
          have := (List.Nodup.getElem_inj_iff (nodup_fresh T (withVerifier N A coins))).mp
            (hiz.trans hjz.symm)
          omega
        have himp : ∀ s, Bad C nonceCoef N A coins j (update T z s) →
            BadAt C nonceCoef N (update T z s) (F.take j) z := by
          rintro s ⟨z', hz', hbad⟩
          have htake := fresh_update_take T z s (withVerifier N A coins) hzj
          have hz'' := fresh_update T z s (withVerifier N A coins) hzj
          have hzz : z' = z := Option.some.inj (hz'.symm.trans hz'')
          have hpre : (fresh (update T z s) (withVerifier N A coins)).take j = F.take j := by
            have := congrArg (List.take j) htake
            simpa [List.take_take] using this
          rw [hzz, hpre] at hbad
          exact hbad
        calc (∑ s, if Bad C nonceCoef N A coins j (LocalFork.upd x T s) then (1 : ℝ) else 0)
            ≤ ∑ s, if BadAt C nonceCoef N (update T z s) (F.take j) z then (1 : ℝ) else 0 := by
              refine Finset.sum_le_sum fun s _ => ?_
              simp only [LocalFork.upd, hxT]
              by_cases hb : Bad C nonceCoef N A coins j (update T z s)
              · simp [hb, himp s hb]
              · simp only [hb, ↓reduceIte]
                split_ifs <;> norm_num
          _ = ((Finset.univ.filter fun s =>
                BadAt C nonceCoef N (update T z s) (F.take j) z).card : ℝ) := by
              rw [Finset.card_filter]
              push_cast
              rfl
          _ ≤ (F.take j).length := by
              exact_mod_cast card_badAt_le C nonceCoef N hE hN T (F.take j) z hznot
          _ ≤ j := by
              exact_mod_cast (List.length_take_le j F)
    have hsum : (Fintype.card (ZMod n) : ℝ) *
        ∑ T, (if Bad C nonceCoef N A coins j T then (1 : ℝ) else 0) ≤
        Fintype.card (SigIn N X M → ZMod n) * j := by
      rw [← hres]
      calc _ ≤ ∑ _T : SigIn N X M → ZMod n, (j : ℝ) := Finset.sum_le_sum fun T _ => hbound T
        _ = Fintype.card (SigIn N X M → ZMod n) * j := by simp [Finset.card_univ]
    rw [ZMod.card] at hsum
    rw [mul_div_assoc']
    rw [le_div_iff₀ hn]
    linarith [hsum]
  calc (∑ coins, ∑ T, if Bad C nonceCoef N A coins j T then (1 : ℝ) else 0) /
        (Fintype.card Coins * Fintype.card (SigIn N X M → ZMod n))
      ≤ (∑ _coins : Coins, (Fintype.card (SigIn N X M → ZMod n) : ℝ) * (j / n)) /
        (Fintype.card Coins * Fintype.card (SigIn N X M → ZMod n)) := by
        gcongr with coins
        exact hone coins
    _ = j / n := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp

/-- **BIP 459 is strongly binding**: an adversary with at most `qh` different
random oracle queries finds a signature that is valid for two different lists
with probability at most `(qh + 2⋅N)² / n`. -/
theorem strongly_binding (hE : Curve.PrimeOrder n E) (hN : N < n) (qh : ℕ)
    (hA : ∀ coins T, (fresh T (A coins)).length ≤ qh) :
    prob (bindExperiment C nonceCoef N A) ≤ ((qh + 2 * N : ℕ) : ℝ) ^ 2 / n := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Fact.out : n.Prime).pos
  have h1 : prob (bindExperiment C nonceCoef N A) ≤
      prob (fun ω : Coins × (SigIn N X M → ZMod n) =>
        ∃ j, j < qh + 2 * N ∧ Bad C nonceCoef N A ω.1 j ω.2) :=
    prob_mono fun ω hω => bad_of_win C nonceCoef N A ω.2 ω.1 qh (hA _ _) hω
  have h2 : prob (fun ω : Coins × (SigIn N X M → ZMod n) =>
        ∃ j, j < qh + 2 * N ∧ Bad C nonceCoef N A ω.1 j ω.2) ≤
      ∑ j ∈ Finset.range (qh + 2 * N),
        prob (fun ω : Coins × (SigIn N X M → ZMod n) => Bad C nonceCoef N A ω.1 j ω.2) :=
    prob_exists_le (qh + 2 * N)
      fun j (ω : Coins × (SigIn N X M → ZMod n)) => Bad C nonceCoef N A ω.1 j ω.2
  have h3 : ∑ j ∈ Finset.range (qh + 2 * N),
        prob (fun ω : Coins × (SigIn N X M → ZMod n) => Bad C nonceCoef N A ω.1 j ω.2) ≤
      ∑ _j ∈ Finset.range (qh + 2 * N), ((qh + 2 * N : ℕ) : ℝ) / n := by
    refine Finset.sum_le_sum fun j hj => ?_
    refine (prob_bad_le C nonceCoef N A hE hN j).trans ?_
    have hjq : (j : ℝ) ≤ ((qh + 2 * N : ℕ) : ℝ) := by
      exact_mod_cast (Finset.mem_range.mp hj).le
    exact div_le_div_of_nonneg_right hjq hn.le
  have h4 : ∑ _j ∈ Finset.range (qh + 2 * N), ((qh + 2 * N : ℕ) : ℝ) / n =
      ((qh + 2 * N : ℕ) : ℝ) ^ 2 / n := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, sq, mul_div_assoc]
  exact h1.trans (h2.trans (h3.trans h4.le))

end Dahlias.Security
