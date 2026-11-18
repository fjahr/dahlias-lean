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

theorem mulG_signPost (r₁ r₂ d : ZMod n) (Rb : E × ZMod n) (c : ZMod n) :
    C.mulG (signPost C.ops (r₁, r₂) d Rb c) =
      dlogPoint C (C.mulG r₁, C.mulG r₂) (C.mulG d) Rb c := by
  simp only [signPost, dlogPoint, Ops.signOf, ops_hasEvenY, ops_evenScalar, evenLift_mulG,
    C.val_smul_mulG, map_add]
  by_cases h : C.hasEvenY Rb.1 = true <;> simp [h, add_comm]

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

/-- The discrete logarithm oracle returns the partial signature. -/
theorem dlogRep_eval {k : ℕ} (hk : k < qs) (τ : Tweak n) (Rb : E × ZMod n) (c : ZMod n) :
    (dlogRep C qs (C.mulG (xu : ZMod n)) k τ Rb c).1 +
        (List.zipWith (· * ·) (dlogRep C qs (C.mulG (xu : ZMod n)) k τ Rb c).2
          (chalLogs (merge xu ν) (2 * qs + 1))).sum =
      signPost C.ops (noncesOf qs ν ⟨k, hk⟩) (τ.sk xu) Rb c := by
  rw [chalLogs_eq]
  simp only [dlogRep]
  rw [coefVec_eval _ _ _ (by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> simp <;> omega)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    logAt_merge_zero, logAt_merge_odd xu ν hk, logAt_merge_even xu ν hk, tweak_pk, signPost,
    ops_hasEvenY, ops_evenScalar, Curve.evenScalar, noncesOf, Tweak.sk]
  by_cases h2 : C.hasEvenY Rb.1 = true <;>
    by_cases h1 : C.hasEvenY (C.mulG (τ.1 + τ.2 * (xu : ZMod n))) = true <;>
    simp only [h1, h2, ite_true, ite_false, Bool.false_eq_true] <;> ring

/-! ## The simulation relation -/

variable (T : SigIn N X M → ZMod n)

/-- A record's partial signature is the signer's, for its stored challenge. -/
def RecSig (r : CloseRec n E X M) : Prop :=
  ∃ hk : r.k < qs, r.s = signPost C.ops (noncesOf qs ν ⟨r.k, hk⟩) (r.τ.sk xu) r.Rb r.c

theorem RecOk.recSig {r : CloseRec n E X M}
    (h : RecOk C nonceCoef N qs (xu : ZMod n) (noncesOf qs ν) T r) : RecSig C qs xu ν r := by
  obtain ⟨hk, -, -, -, -, hs⟩ := h
  exact ⟨hk, hs⟩

/-- The partial signature of a record is the discrete logarithm of its point. -/
theorem RecSig.mulG_s {r : CloseRec n E X M} (h : RecSig C qs xu ν r) :
    C.mulG r.s = r.point C (C.mulG (xu : ZMod n)) (Uof C qs xu ν) := by
  obtain ⟨hk, hs⟩ := h
  rw [hs, mulG_signPost, CloseRec.point, Uof_eq C qs xu ν hk, tweak_pk]

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
  obtain ⟨hch, hsg, hrecs, hinv, new, hcache, hd, hnew, hcnt, hpts⟩ := h
  dsimp only at hch hsg hrecs hcache hd
  subst hch
  have hinv' := logInv_step C nonceCoef N qs (xu : ZMod n) (noncesOf qs ν) T q (sg, log) hinv
  cases q with
  | hash z => exact ⟨rfl, ⟨rfl, hsg, hrecs, hinv, new, hcache, hd, hnew, hcnt, hpts⟩⟩
  | openSession =>
    simp only [simStep, simChallenger, logChallenger, challenger, Alg.run_done, hsg]
    by_cases ho : sg.opened < qs
    · simp only [ho, ↓reduceIte, ↓reduceDIte, Uof_eq C qs xu ν ho]
      try (refine ⟨rfl, ?_⟩)
      exact { chals := rfl, signer := rfl, recs := hrecs
              inv := by simpa [logChallenger, challenger, ho] using hinv'
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
        simp only [tweak_pk]
        set c := T (⟨pm, hcond.2.2.2.2⟩, C.x Rb.1, (C.x (C.mulG (τ.sk xu)), m)) with hc
        set s := signPost C.ops (noncesOf qs ν ⟨k, hcond.1⟩) (τ.sk xu) Rb c with hs
        have hQ : C.mulG s = dlogPoint C (Uof C qs xu ν k) (C.mulG (τ.sk xu)) Rb c := by
          rw [hs, mulG_signPost, hU]
        split
        · -- a cached query
          rename_i r hf
          have hrmem : r ∈ st.cache := List.mem_of_find?_eq_some hf
          have hrp := List.find?_some hf
          simp only [decide_eq_true_eq] at hrp
          have hrsig : RecSig C qs xu ν r := by
            rw [hcache] at hrmem
            rcases List.mem_append.mp hrmem with hr | hr
            · exact ((hinv r (hnew r hr)).1).recSig
            · exact hc₀ r hr
          have hrs : r.s = s :=
            C.mulG_injective ((hrsig.mulG_s C qs xu ν).trans (hrp.2.trans hQ.symm))
          rw [hrs]
          try (refine ⟨rfl, ?_⟩)
          refine { chals := rfl, signer := rfl, recs := by simp [hrecs], inv := hinv'
                   cache := ⟨new, hcache, hd, ?_, ?_, hpts⟩ }
          · exact fun r hr => List.mem_cons_of_mem _ (hnew r hr)
          · intro k'
            refine (hcnt k').trans ?_
            by_cases hk' : k' ∈ sg.closed <;> simp [hk']
        · -- a new query
          rename_i hf
          rw [run_dlog C (merge xu ν), tweak_pk, dlogRep_eval C qs xu ν hcond.1 τ Rb c, ← hs]
          try (refine ⟨rfl, ?_⟩)
          refine { chals := rfl, signer := rfl, recs := by simp [hrecs], inv := hinv'
                   cache := ⟨⟨k, τ, m, agg, pm, pubnonces, Rb, c, s⟩ :: new, by simp [hcache],
                     by simp [hd]; omega, ?_, ?_, ?_⟩ }
          · intro r hr
            rcases List.mem_cons.mp hr with rfl | hr
            · simp
            · exact List.mem_cons_of_mem _ (hnew r hr)
          · intro k'
            by_cases hk' : k = k'
            · subst hk'
              have := hcnt k
              simp only [hcond.2.2.1, ↓reduceIte, Nat.le_zero] at this
              simp [this]
            · have := hcnt k'
              simp only [List.filter_cons, hk', decide_false, Bool.false_eq_true, ↓reduceIte,
                List.mem_cons, Ne.symm hk', false_or]
              exact this
          · intro a ha a' ha' hk'
            rcases List.mem_cons.mp ha with rfl | ha
            · have hnone := List.find?_eq_none.mp hf a' (by rw [hcache]; simp [ha'])
              simp only [decide_eq_true_eq, not_and] at hnone
              intro heq
              exact hnone hk'.symm (by rw [← heq, CloseRec.point, tweak_pk])
            · exact hpts a ha a' ha' hk'
    · rw [dif_neg hcond, dif_neg hcond]
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
