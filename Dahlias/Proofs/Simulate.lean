import Dahlias.Proofs.Omdl
import Dahlias.Correctness

/-!
# The reduction simulates the honest signer

`sim_run`: when the challenges are the secret key and the session nonces of a
sample, the forger run by the reduction sees the honest signer of that sample.
The reduction ends with the same output, signer state and records
(`SimRel`), and its discrete logarithm queries are the new entries of its
cache: at most one for every session closed in this run, each with a query
point that no earlier entry of the session has.
-/

set_option linter.unusedSectionVars false
set_option linter.deprecated false

namespace Dahlias.Security

open Taproot Function

variable {n : ℕ} [Fact n.Prime] {E X M : Type} [AddCommGroup E] [DecidableEq E] [DecidableEq X]
  [DecidableEq M] (C : Curve n E X) (nonceCoef : E → E → List (X × M × E) → ZMod n) (N qs : ℕ)

/-! ## Public and secret computations agree -/

theorem tweak_pk (τ : Tweak n) (x : ZMod n) : τ.pk C (C.mulG x) = C.mulG (τ.sk x) := by
  simp [Tweak.pk, Tweak.sk, C.val_smul_mulG]

theorem evenLift_mulG (d : ZMod n) : evenLift C (C.mulG d) = C.mulG (C.evenScalar d) := by
  unfold evenLift Curve.evenScalar
  split_ifs <;> simp

theorem mulG_sigOf (r₁ r₂ : ZMod n) (Rb : E × ZMod n) (ks : ZMod n) :
    C.mulG (sigOf C (r₁, r₂) Rb ks) =
      dlogPoint C (C.mulG r₁, C.mulG r₂) Rb (C.mulG ks) := by
  simp only [sigOf, dlogPoint, Ops.signOf, ops_hasEvenY, C.val_smul_mulG, map_add]
  by_cases h : C.hasEvenY Rb.1 = true <;> simp [h]

theorem mulG_keySk (x : ZMod n) (keys : List (KeyTerm n M)) :
    C.mulG (keySk C x keys) = keyPoint C (C.mulG x) keys := by
  unfold keySk keyPoint
  induction keys with
  | nil => simp
  | cons κ l ih =>
    simp only [List.map_cons, List.sum_cons, map_add, ih, tweak_pk, evenLift_mulG,
      C.val_smul_mulG]

theorem evenScalar_sk (x : ZMod n) (τ : Tweak n) :
    C.evenScalar (τ.sk x) =
      keySign C (C.mulG x) τ * τ.1 + keySign C (C.mulG x) τ * τ.2 * x := by
  unfold keySign Curve.evenScalar
  rw [tweak_pk]
  simp only [Tweak.sk]
  by_cases h : C.hasEvenY (C.mulG (τ.1 + τ.2 * x)) = true <;>
    simp only [h, ite_true, ite_false, Bool.false_eq_true] <;> ring

/-- The key part of a signature in terms of the secret key. -/
theorem keySk_eq (x : ZMod n) (keys : List (KeyTerm n M)) :
    keySk C x keys = (keys.map fun κ => κ.2.2 * keySign C (C.mulG x) κ.1 * κ.1.1).sum +
      (keys.map fun κ => κ.2.2 * keySign C (C.mulG x) κ.1 * κ.1.2).sum * x := by
  unfold keySk
  induction keys with
  | nil => simp
  | cons κ l ih =>
    rw [List.map_cons, List.sum_cons, ih, evenScalar_sk, List.map_cons, List.sum_cons,
      List.map_cons, List.sum_cons]
    ring

theorem signPre_eq_pub (H : Hashes n E X M) {r₁ r₂ : ZMod n} (h₁ : r₁ ≠ 0) (h₂ : r₂ ≠ 0)
    (d : ZMod n) (m : M) (agg : PubNonce E) (pm : List (X × M)) (pubnonces : List (PubNonce E)) :
    signPre C.ops H (r₁, r₂) d m agg pm pubnonces =
      signPrePub C H (C.mulG r₂) (C.mulG d) m agg pm pubnonces := by
  simp only [signPre, signPrePub, h₁, h₂, false_or, ops_mulG, ops_x, C.mulG_eq_zero]
  rfl

/-! ## The challenges of a sample -/

variable (xu : (ZMod n)ˣ) (ν : Fin qs → (ZMod n)ˣ × (ZMod n)ˣ)

/-- The public nonces of the sessions, as the reduction reads them off its
challenges. -/
def Uof (k : ℕ) : PubNonce E :=
  (C.mulG (logAt (merge xu ν) (2 * k + 1)), C.mulG (logAt (merge xu ν) (2 * k + 2)))

theorem Uof_eq {k : ℕ} (hk : k < qs) :
    Uof C qs xu ν k = (C.mulG (noncesOf qs ν ⟨k, hk⟩).1, C.mulG (noncesOf qs ν ⟨k, hk⟩).2) := by
  simp [Uof, noncesOf, logAt_merge_odd xu ν hk, logAt_merge_even xu ν hk]

theorem nonces_ne_zero (k : Fin qs) : (noncesOf qs ν k).1 ≠ 0 ∧ (noncesOf qs ν k).2 ≠ 0 :=
  ⟨Units.ne_zero _, Units.ne_zero _⟩

/-- The discrete logarithm oracle returns the signature scalar. -/
theorem dlogRep_eval {k : ℕ} (hk : k < qs) (Rb : E × ZMod n) (keys : List (KeyTerm n M)) :
    (dlogRep C qs (C.mulG (xu : ZMod n)) k Rb keys).1 +
        (List.zipWith (· * ·) (dlogRep C qs (C.mulG (xu : ZMod n)) k Rb keys).2
          (chalLogs (merge xu ν) (2 * qs + 1))).sum =
      sigOf C (noncesOf qs ν ⟨k, hk⟩) Rb (keySk C xu keys) := by
  rw [chalLogs_eq]
  simp only [dlogRep]
  rw [coefVec_eval _ _ _ (by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp <;> omega)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    logAt_merge_zero, logAt_merge_odd xu ν hk, logAt_merge_even xu ν hk, sigOf, noncesOf,
    keySk_eq]
  by_cases h2 : C.hasEvenY Rb.1 = true <;>
    simp only [h2, ite_true, ite_false, Bool.false_eq_true] <;> ring

/-! ## The simulation relation -/

variable (T : SigIn N X M → ZMod n)

/-- A record's scalar is the signer's, for its stored key terms. -/
def RecSig (r : CloseRec n E X M) : Prop :=
  ∃ hk : r.k < qs, r.s = sigOf C (noncesOf qs ν ⟨r.k, hk⟩) r.Rb (keySk C xu r.keys)

theorem RecOk.recSig {r : CloseRec n E X M}
    (h : RecOk C nonceCoef N qs (xu : ZMod n) (noncesOf qs ν) T r) : RecSig C qs xu ν r := by
  obtain ⟨hk, -, -, -, hs, -⟩ := h
  exact ⟨hk, hs⟩

/-- The scalar of a record is the discrete logarithm of its point. -/
theorem RecSig.mulG_s {r : CloseRec n E X M} (h : RecSig C qs xu ν r) :
    C.mulG r.s = r.point C (C.mulG (xu : ZMod n)) (Uof C qs xu ν) := by
  obtain ⟨hk, hs⟩ := h
  rw [hs, CloseRec.point, Uof_eq C qs xu ν hk, ← mulG_keySk]
  exact mulG_sigOf C _ _ _ _

/-- The reduction's state and the AOMDL game's state against the state of the
signer with records. `c₀` and `d₀` are the cache and the number of discrete
logarithm queries at the start of the run. -/
structure SimRel (c₀ : List (CloseRec n E X M)) (d₀ : ℕ)
    (su : SimState n E X M × (ℕ × ℕ))
    (ls : SignerState X M × List (CloseRec n E X M)) : Prop where
  chals : su.2.1 = 2 * qs + 1
  signer : su.1.signer = ls.1
  recs : su.1.recs = ls.2
  inv : LogInv C nonceCoef N qs (xu : ZMod n) (noncesOf qs ν) T ls
  cache : ∃ new, su.1.cache = new ++ c₀ ∧ su.2.2 = d₀ + new.length ∧ (∀ r ∈ new, r ∈ ls.2) ∧
    (∀ k, (new.filter fun r => decide (r.k = k)).length ≤ if k ∈ ls.1.closed then 1 else 0) ∧
    ∀ a ∈ new, ∀ a' ∈ c₀, a.k = a'.k →
      a.point C (C.mulG (xu : ZMod n)) (Uof C qs xu ν) ≠
        a'.point C (C.mulG (xu : ZMod n)) (Uof C qs xu ν)

/-- One query of the forger, answered by the reduction inside the AOMDL game. -/
def simStep (q : AdvQ n N E X M) (su : SimState n E X M × (ℕ × ℕ)) :
    AdvR q × (SimState n E X M × (ℕ × ℕ)) :=
  let a := (simChallenger C nonceCoef N qs (C.mulG (xu : ZMod n)) (Uof C qs xu ν) T q su.1).run
    (omdlChallenger C (merge xu ν)) su.2
  (a.1.1, (a.1.2, a.2))

/-- **A signing query, answered from the cache or by the oracle**: the
reduction returns the signer's scalar and stays in the simulation relation. -/
theorem simSign_rel (c₀ : List (CloseRec n E X M)) (d₀ : ℕ)
    (hc₀ : ∀ r ∈ c₀, RecSig C qs xu ν r) {st : SimState n E X M} {d : ℕ}
    {sg : SignerState X M} {log : List (CloseRec n E X M)}
    (h : SimRel C nonceCoef N qs xu ν T c₀ d₀ (st, (2 * qs + 1, d)) (sg, log))
    (rec0 : CloseRec n E X M) (hk : rec0.k < qs) (hkc : rec0.k ∉ sg.closed)
    (sg' : SignerState X M) (hsg' : sg'.closed = rec0.k :: sg.closed)
    (hinv' : LogInv C nonceCoef N qs (xu : ZMod n) (noncesOf qs ν) T
      (sg', { rec0 with
        s := sigOf C (noncesOf qs ν ⟨rec0.k, hk⟩) rec0.Rb (keySk C xu rec0.keys) } :: log)) :
    let s := sigOf C (noncesOf qs ν ⟨rec0.k, hk⟩) rec0.Rb (keySk C xu rec0.keys)
    let res := (simSign C qs (C.mulG (xu : ZMod n)) (Uof C qs xu ν) rec0 sg' st).run
      (omdlChallenger C (merge xu ν)) (2 * qs + 1, d)
    res.1.1 = s ∧ SimRel C nonceCoef N qs xu ν T c₀ d₀ (res.1.2, res.2)
      (sg', { rec0 with s := s } :: log) := by
  intro s res
  obtain ⟨-, hsg, hrecs, hinv, new, hcache, hd, hnew, hcnt, hpts⟩ := h
  dsimp only at hsg hrecs hcache hd
  have hQ : C.mulG s = rec0.point C (C.mulG (xu : ZMod n)) (Uof C qs xu ν) :=
    RecSig.mulG_s C qs xu ν (r := { rec0 with s := s }) ⟨hk, rfl⟩
  have hcnt' : ∀ k', (new.filter fun r => decide (r.k = k')).length ≤
      if k' ∈ sg'.closed then 1 else 0 := by
    intro k'
    refine (hcnt k').trans ?_
    rw [hsg']
    by_cases hk' : k' ∈ sg.closed <;> simp [hk']
  simp only [res, simSign]
  split
  · -- a cached query
    rename_i r hf
    have hrmem : r ∈ st.cache := List.mem_of_find?_eq_some hf
    have hrp := List.find?_some hf
    simp only [decide_eq_true_eq] at hrp
    have hrsig : RecSig C qs xu ν r := by
      rw [hcache] at hrmem
      rcases List.mem_append.mp hrmem with hr | hr
      · exact ((hinv.2 r (hnew r hr)).1).recSig
      · exact hc₀ r hr
    have hrs : r.s = s :=
      C.mulG_injective ((hrsig.mulG_s C qs xu ν).trans (hrp.2.trans hQ.symm))
    refine ⟨hrs, { chals := rfl, signer := rfl
                   recs := by
                     change _ :: st.recs = _ :: log
                     rw [hrecs, hrs]
                   inv := hinv'
                   cache := ⟨new, hcache, hd, ?_, hcnt', hpts⟩ }⟩
    exact fun r hr => List.mem_cons_of_mem _ (hnew r hr)
  · -- a new query
    rename_i hf
    rw [run_dlog C (merge xu ν), dlogRep_eval C qs xu ν hk rec0.Rb rec0.keys]
    refine ⟨rfl, { chals := rfl, signer := rfl
                   recs := by
                     change _ :: st.recs = _ :: log
                     rw [hrecs]
                   inv := hinv'
                   cache := ⟨{ rec0 with s := s } :: new, by
                       change _ :: st.cache = _ :: (new ++ c₀)
                       rw [hcache], by
                       change d + 1 = d₀ + (new.length + 1)
                       omega, ?_, ?_, ?_⟩ }⟩
    · intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · simp
      · exact List.mem_cons_of_mem _ (hnew r hr)
    · intro k'
      by_cases hk' : rec0.k = k'
      · subst hk'
        have := hcnt rec0.k
        simp only [hkc, ↓reduceIte, Nat.le_zero] at this
        simp [this, hsg']
      · have := hcnt' k'
        simp only [List.filter_cons, hk', decide_false, Bool.false_eq_true, ↓reduceIte]
        exact this
    · intro a ha a' ha' hk'
      rcases List.mem_cons.mp ha with rfl | ha
      · have hnone := List.find?_eq_none.mp hf a' (by rw [hcache]; simp [ha'])
        simp only [decide_eq_true_eq, not_and] at hnone
        intro heq
        exact hnone hk'.symm heq.symm
      · exact hpts a ha a' ha' hk'

theorem singleKeysPub_eq (x : ZMod n) (items : List (Tweak n × M)) :
    singleKeysPub C (C.mulG x) items = singleKeys C x items := by
  simp only [singleKeysPub, singleKeys, tweak_pk]

theorem simStep_rel (c₀ : List (CloseRec n E X M)) (d₀ : ℕ)
    (hc₀ : ∀ r ∈ c₀, RecSig C qs xu ν r) (q : AdvQ n N E X M)
    (su : SimState n E X M × (ℕ × ℕ)) (ls : SignerState X M × List (CloseRec n E X M))
    (h : SimRel C nonceCoef N qs xu ν T c₀ d₀ su ls) :
    (simStep C nonceCoef N qs xu ν T q su).1 =
        (logChallenger C nonceCoef N qs (xu : ZMod n) (noncesOf qs ν) T q ls).1 ∧
      SimRel C nonceCoef N qs xu ν T c₀ d₀ (simStep C nonceCoef N qs xu ν T q su).2
        (logChallenger C nonceCoef N qs (xu : ZMod n) (noncesOf qs ν) T q ls).2 := by
  obtain ⟨st, ℓ, d⟩ := su
  obtain ⟨sg, log⟩ := ls
  have h0 := h
  obtain ⟨hch, hsg, hrecs, hinv, new, hcache, hd, hnew, hcnt, hpts⟩ := h
  dsimp only at hch hsg hrecs hcache hd
  subst hch
  have hinv' := logInv_step C nonceCoef N qs (xu : ZMod n) (noncesOf qs ν) T q (sg, log) hinv
  cases q with
  | hash z => exact ⟨rfl, ⟨rfl, hsg, hrecs, hinv, new, hcache, hd, hnew, hcnt, hpts⟩⟩
  | openSession =>
    simp only [simStep, simChallenger, logChallenger, challengerG, Alg.run_done, hsg]
    by_cases ho : sg.opened < qs
    · simp only [ho, ↓reduceIte, ↓reduceDIte, Uof_eq C qs xu ν ho]
      try (refine ⟨rfl, ?_⟩)
      exact { chals := rfl, signer := rfl, recs := hrecs
              inv := by simpa [logChallenger, challengerG, ho] using hinv'
              cache := ⟨new, hcache, hd, hnew, hcnt, hpts⟩ }
    · simp only [ho, ↓reduceIte, ↓reduceDIte]
      try (refine ⟨rfl, ?_⟩)
      exact { chals := rfl, signer := hsg, recs := hrecs, inv := hinv
              cache := ⟨new, hcache, hd, hnew, hcnt, hpts⟩ }
  | close k τ m agg pm pubnonces =>
    simp only [simStep, simChallenger, logChallenger, hsg] at hinv' ⊢
    by_cases hcond : k < qs ∧ k < sg.opened ∧ k ∉ sg.closed ∧ τ.2 ≠ 0 ∧ pm.length ≤ N
    · rw [dif_pos hcond, dif_pos hcond]
      rw [dif_pos hcond] at hinv'
      have hU := Uof_eq C qs xu ν hcond.1
      have hne := nonces_ne_zero qs ν ⟨k, hcond.1⟩
      have hpre : signPrePub C (H₀ nonceCoef N) (Uof C qs xu ν k).2
          (τ.pk C (C.mulG (xu : ZMod n))) m agg pm pubnonces =
          signPre C.ops (H₀ nonceCoef N) (noncesOf qs ν ⟨k, hcond.1⟩) (τ.sk xu) m agg pm
            pubnonces := by
        rw [hU, tweak_pk]
        exact (signPre_eq_pub C (H₀ nonceCoef N) hne.1 hne.2 _ m agg pm pubnonces).symm
      rw [hpre]
      rcases hp : signPre C.ops (H₀ nonceCoef N) (noncesOf qs ν ⟨k, hcond.1⟩) (τ.sk xu) m agg pm
          pubnonces with _ | Rb
      · simp only [Alg.run_done]
        try (refine ⟨rfl, ?_⟩)
        exact { chals := rfl, signer := hsg, recs := hrecs, inv := hinv
                cache := ⟨new, hcache, hd, hnew, hcnt, hpts⟩ }
      · simp only [hp] at hinv'
        simp only [tweak_pk, Alg.run_bind, Alg.run_done]
        have key := simSign_rel C nonceCoef N qs xu ν T c₀ d₀ hc₀ h0
          ⟨k, [(τ, m, T (⟨pm, hcond.2.2.2.2⟩, C.x Rb.1, (C.x (C.mulG (τ.sk xu)), m)))], agg, pm,
            pubnonces, Rb, 0⟩ hcond.1 hcond.2.2.1
          { sg with closed := k :: sg.closed
                    signed := (pm, C.x (C.mulG (τ.sk xu)), m) :: sg.signed } rfl (by
            convert hinv' using 3
            simp only [signPost, sigOf, keySk, List.map_cons, List.map_nil, List.sum_cons,
              List.sum_nil, add_zero]
            rfl)
        dsimp only at key
        refine ⟨?_, ?_⟩
        · rw [key.1]
          simp only [signPost, sigOf, keySk, List.map_cons, List.map_nil, List.sum_cons,
            List.sum_nil, add_zero]
          rfl
        · convert key.2 using 3
          simp only [signPost, sigOf, keySk, List.map_cons, List.map_nil, List.sum_cons,
            List.sum_nil, add_zero]
          rfl
    · rw [dif_neg hcond, dif_neg hcond]
      simp only [Alg.run_done]
      try (refine ⟨rfl, ?_⟩)
      exact { chals := rfl, signer := hsg, recs := hrecs, inv := hinv
              cache := ⟨new, hcache, hd, hnew, hcnt, hpts⟩ }
  | single items =>
    simp only [simStep, simChallenger, logChallenger, hsg, singleKeysPub_eq] at hinv' ⊢
    by_cases ho : sg.opened < qs
    · rw [dif_pos ho, dif_pos ho]
      rw [dif_pos ho] at hinv'
      have hU := Uof_eq C qs xu ν ho
      have hR : (Uof C qs xu ν sg.opened).1 +
          (ncHash nonceCoef (singleNcIn (singleKeys C (xu : ZMod n) items))).val •
            (Uof C qs xu ν sg.opened).2 =
          C.mulG (singleNonce true nonceCoef (singleKeys C (xu : ZMod n) items)
            (noncesOf qs ν ⟨sg.opened, ho⟩)) := by
        rw [hU]
        simp only [singleNonce, ↓reduceIte, map_add, C.val_smul_mulG]
        rfl
      simp only [hR, tweak_pk] at hinv' ⊢
      have hnot : sg.opened ∉ sg.closed := fun hm => lt_irrefl _ (hinv.1 _ hm)
      have hcntS : ∀ k', (new.filter fun r => decide (r.k = k')).length ≤
          if k' ∈ sg.opened :: sg.closed then 1 else 0 := by
        intro k'
        refine (hcnt k').trans ?_
        by_cases hk' : k' ∈ sg.closed <;> simp [hk']
      by_cases hc : items ≠ [] ∧ (singleKeys C (xu : ZMod n) items).length ≤ N ∧
          singleNonce true nonceCoef (singleKeys C (xu : ZMod n) items)
            (noncesOf qs ν ⟨sg.opened, ho⟩) ≠ 0 ∧
          ∀ i ∈ items, i.1.2 ≠ 0 ∧ i.1.sk (xu : ZMod n) ≠ 0
      · have hpub : items ≠ [] ∧ (singleKeys C (xu : ZMod n) items).length ≤ N ∧
            C.mulG (singleNonce true nonceCoef (singleKeys C (xu : ZMod n) items)
              (noncesOf qs ν ⟨sg.opened, ho⟩)) ≠ 0 ∧
            ∀ i ∈ items, i.1.2 ≠ 0 ∧ C.mulG (i.1.sk (xu : ZMod n)) ≠ 0 :=
          ⟨hc.1, hc.2.1, C.mulG_ne_zero hc.2.2.1, fun i hi =>
            ⟨(hc.2.2.2 i hi).1, C.mulG_ne_zero (hc.2.2.2 i hi).2⟩⟩
        rw [dif_pos hpub, dif_pos hc]
        rw [dif_pos hc] at hinv'
        have hS0 : singleS C (xu : ZMod n) items
            (singleNonce true nonceCoef (singleKeys C (xu : ZMod n) items)
              (noncesOf qs ν ⟨sg.opened, ho⟩))
            ((singleKeys C (xu : ZMod n) items).map fun e =>
              T (⟨singleKeys C (xu : ZMod n) items, hc.2.1⟩,
                C.x (C.mulG (singleNonce true nonceCoef (singleKeys C (xu : ZMod n) items)
                  (noncesOf qs ν ⟨sg.opened, ho⟩))), e)) =
            sigOf C (noncesOf qs ν ⟨sg.opened, ho⟩)
              (C.mulG (singleNonce true nonceCoef (singleKeys C (xu : ZMod n) items)
                (noncesOf qs ν ⟨sg.opened, ho⟩)),
                ncHash nonceCoef (singleNcIn (singleKeys C (xu : ZMod n) items)))
              (keySk C xu (singleTerms items ((singleKeys C (xu : ZMod n) items).map fun e =>
                T (⟨singleKeys C (xu : ZMod n) items, hc.2.1⟩,
                  C.x (C.mulG (singleNonce true nonceCoef (singleKeys C (xu : ZMod n) items)
                    (noncesOf qs ν ⟨sg.opened, ho⟩))), e)))) := by
          have hcs : ((singleKeys C (xu : ZMod n) items).map fun e =>
              T (⟨singleKeys C (xu : ZMod n) items, hc.2.1⟩,
                C.x (C.mulG (singleNonce true nonceCoef (singleKeys C (xu : ZMod n) items)
                  (noncesOf qs ν ⟨sg.opened, ho⟩))), e)) =
              items.map fun i => T (⟨singleKeys C (xu : ZMod n) items, hc.2.1⟩,
                C.x (C.mulG (singleNonce true nonceCoef (singleKeys C (xu : ZMod n) items)
                  (noncesOf qs ν ⟨sg.opened, ho⟩))),
                (C.x (C.mulG (i.1.sk (xu : ZMod n))), i.2)) := by
            simp only [singleKeys, List.map_map]
            rfl
          rw [hcs, singleS_eq]
          rfl
        have hS := hS0
        rw [hS] at hinv'
        have key := simSign_rel C nonceCoef N qs xu ν T c₀ d₀ hc₀ h0
          ⟨sg.opened, singleTerms items ((singleKeys C (xu : ZMod n) items).map fun e =>
              T (⟨singleKeys C (xu : ZMod n) items, hc.2.1⟩,
                C.x (C.mulG (singleNonce true nonceCoef (singleKeys C (xu : ZMod n) items)
                  (noncesOf qs ν ⟨sg.opened, ho⟩))), e)), (0, 0),
            singleKeys C (xu : ZMod n) items,
            (singleKeys C (xu : ZMod n) items).map fun _ => (0, 0),
            (C.mulG (singleNonce true nonceCoef (singleKeys C (xu : ZMod n) items)
              (noncesOf qs ν ⟨sg.opened, ho⟩)),
              ncHash nonceCoef (singleNcIn (singleKeys C (xu : ZMod n) items))), 0⟩ ho hnot
          { opened := sg.opened + 1
            closed := sg.opened :: sg.closed
            signed := (singleKeys C (xu : ZMod n) items).map
              (fun e => (singleKeys C (xu : ZMod n) items, e.1, e.2)) ++ sg.signed } rfl
          hinv'
        dsimp only at key
        simp only [Alg.run_bind, Alg.run_done]
        rw [hS]
        refine ⟨?_, key.2⟩
        rw [key.1]
      · have hpub : ¬(items ≠ [] ∧ (singleKeys C (xu : ZMod n) items).length ≤ N ∧
            C.mulG (singleNonce true nonceCoef (singleKeys C (xu : ZMod n) items)
              (noncesOf qs ν ⟨sg.opened, ho⟩)) ≠ 0 ∧
            ∀ i ∈ items, i.1.2 ≠ 0 ∧ C.mulG (i.1.sk (xu : ZMod n)) ≠ 0) := fun hp =>
          hc ⟨hp.1, hp.2.1, fun h0 => hp.2.2.1 (by rw [h0, map_zero]), fun i hi =>
            ⟨(hp.2.2.2 i hi).1, fun h0 => (hp.2.2.2 i hi).2 (by rw [h0, map_zero])⟩⟩
        rw [dif_neg hpub, dif_neg hc]
        rw [dif_neg hc] at hinv'
        simp only [Alg.run_done]
        try (refine ⟨rfl, ?_⟩)
        exact { chals := rfl, signer := rfl, recs := hrecs, inv := hinv'
                cache := ⟨new, hcache, hd, hnew, hcntS, hpts⟩ }
    · rw [dif_neg ho, dif_neg ho]
      simp only [Alg.run_done]
      try (refine ⟨rfl, ?_⟩)
      exact { chals := rfl, signer := hsg, recs := hrecs, inv := hinv
              cache := ⟨new, hcache, hd, hnew, hcnt, hpts⟩ }

/-- **The reduction simulates the honest signer.** -/
theorem sim_run (c₀ : List (CloseRec n E X M)) (d₀ : ℕ) (hc₀ : ∀ r ∈ c₀, RecSig C qs xu ν r)
    {α : Type} (t : Alg (AdvQ n N E X M) AdvR α) (su : SimState n E X M × (ℕ × ℕ))
    (ls : SignerState X M × List (CloseRec n E X M))
    (h : SimRel C nonceCoef N qs xu ν T c₀ d₀ su ls) :
    let r := (Alg.interp (simChallenger C nonceCoef N qs (C.mulG (xu : ZMod n))
      (Uof C qs xu ν) T) t su.1).run (omdlChallenger C (merge xu ν)) su.2
    let r' := t.run (logChallenger C nonceCoef N qs (xu : ZMod n) (noncesOf qs ν) T) ls
    r.1.1 = r'.1 ∧ SimRel C nonceCoef N qs xu ν T c₀ d₀ (r.1.2, r.2) r'.2 := by
  intro r r'
  have hrun := Alg.run_interp (simChallenger C nonceCoef N qs (C.mulG (xu : ZMod n))
    (Uof C qs xu ν) T) (omdlChallenger C (merge xu ν)) t su.1 su.2
  have hrel := Alg.run_rel (simStep C nonceCoef N qs xu ν T)
    (logChallenger C nonceCoef N qs (xu : ZMod n) (noncesOf qs ν) T)
    (SimRel C nonceCoef N qs xu ν T c₀ d₀)
    (fun q s s' hs => simStep_rel C nonceCoef N qs xu ν T c₀ d₀ hc₀ q s s' hs) t su ls h
  simp only [r, hrun]
  exact hrel

end Dahlias.Security
