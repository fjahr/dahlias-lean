import Dahlias.Proofs.Collide

/-!
# From a fork to a solution of AOMDL

`fork_to_omdl`: on every sample on which the fork event happens, the reduction
wins the AOMDL game whose challenges are the secret key and the session nonces
of the sample, or the collision finder outputs a collision of the nonce
coefficient hash.
-/

set_option linter.unusedSectionVars false

namespace Dahlias.Security

open Taproot Function

variable {n : ℕ} [Fact n.Prime] {E X M : Type} [AddCommGroup E] [DecidableEq E] [DecidableEq X]
  [DecidableEq M] (C : Curve n E X) (nonceCoef : E → E → List (X × M × E) → ZMod n) (N qs : ℕ)
  {Coins : Type} (A : Adversary n N E X M Coins)

theorem getD_chals (xs : Fin (2 * qs + 1) → (ZMod n)ˣ) (i : ℕ) :
    ((List.range (2 * qs + 1)).map fun j => C.mulG (logAt xs j)).getD i 0 =
      C.mulG (logAt xs i) := by
  by_cases h : i < 2 * qs + 1
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h, logAt]

variable (xu : (ZMod n)ˣ) (ν : Fin qs → (ZMod n)ˣ × (ZMod n)ˣ)

/-- After the challenge phase the reduction knows `P` and the `U`. -/
theorem run_reduction (ρ : Coins × (SigIn N X M → ZMod n) × ZMod n) :
    (reduction C nonceCoef N qs A ρ).run (omdlChallenger C (merge xu ν)) (0, 0) =
      (reductionBody C nonceCoef N qs (C.mulG (xu : ZMod n)) (Uof C qs xu ν) A ρ).run
        (omdlChallenger C (merge xu ν)) (2 * qs + 1, 0) := by
  unfold reduction
  rw [Alg.run_bind, run_getChals C (merge xu ν) (2 * qs + 1) 0 0 (by omega)]
  simp only [zero_add, getD_chals, logAt_merge_zero]
  rfl

theorem simRel_init (T : SigIn N X M → ZMod n) (c₀ : List (CloseRec n E X M)) (u : ℕ × ℕ)
    (hu : u.1 = 2 * qs + 1) :
    SimRel C nonceCoef N qs xu ν T c₀ u.2 (⟨⟨0, [], []⟩, [], c₀⟩, u) (⟨0, [], []⟩, []) where
  chals := hu
  signer := rfl
  recs := rfl
  inv := fun r hr => by simp at hr
  cache := ⟨[], rfl, rfl, by simp, by simp, by simp⟩

/-- **A fork solves AOMDL or gives a collision.** -/
theorem fork_to_omdl (hN : N < n) (p : ForgeSample n N qs X M Coins × ZMod n)
    (hfork : ForkEvent C nonceCoef N qs A p) :
    omdlExperiment C (2 * qs + 1) (reduction C nonceCoef N qs A)
        (merge p.1.1 p.1.2.1, (p.1.2.2.1, p.1.2.2.2, p.2)) ∨
      IsCollision nonceCoef (collider C nonceCoef N qs A p) := by
  obtain ⟨⟨xu, ν, coins, T⟩, s⟩ := p
  unfold ForkEvent QTree.Forks at hfork
  dsimp only at hfork ⊢
  obtain ⟨z, hsel₁, -, hsel₂, hsz⟩ := hfork
  -- the two runs of the game, with records
  have he : ∀ T' : SigIn N X M → ZMod n,
      QTree.eval T' (sampleTree C nonceCoef N qs A (xu, ν, coins)) =
        ((gameRecs C nonceCoef N qs A (xu, ν, coins, T) T').1,
          (gameRecs C nonceCoef N qs A (xu, ν, coins, T) T').2.1) := by
    intro T'
    have h := run_logChallenger C nonceCoef N qs (xu : ZMod n) (noncesOf qs ν) T'
      (A coins (C.mulG (xu : ZMod n))) (⟨0, [], []⟩, [])
    rw [sampleTree, eval_gameTree]
    exact Prod.ext h.1.symm h.2.symm
  have hinv : ∀ T' : SigIn N X M → ZMod n,
      LogInv C nonceCoef N qs (xu : ZMod n) (noncesOf qs ν) T'
        (gameRecs C nonceCoef N qs A (xu, ν, coins, T) T').2 := fun T' =>
    run_logInv C nonceCoef N qs (xu : ZMod n) (noncesOf qs ν) T' _ _ (fun r hr => by simp at hr)
  rw [he] at hsel₁ hsel₂
  set G₁ := gameRecs C nonceCoef N qs A (xu, ν, coins, T) T with hG₁
  set G₂ := gameRecs C nonceCoef N qs A (xu, ν, coins, T) (update T z s) with hG₂
  have hinv₁ := hinv T
  have hinv₂ := hinv (update T z s)
  rw [← hG₁] at hinv₁
  rw [← hG₂] at hinv₂
  unfold gameSel at hsel₁ hsel₂
  dsimp only at hsel₁ hsel₂
  split_ifs at hsel₁ with hv₁
  split_ifs at hsel₂ with hv₂
  by_cases hcol : ∃ a ∈ G₁.2.2, ∃ a' ∈ G₂.2.2, a.k = a'.k ∧
      IsCollision nonceCoef (a.ncIn, a'.ncIn)
  · right
    obtain ⟨a, ha, a', ha', hk, hc⟩ := hcol
    exact collider_isCollision C nonceCoef N qs A ((xu, ν, coins, T), s) hsel₁ ha ha' hk hc
  left
  push Not at hcol
  -- what the fork point says
  obtain ⟨hL, e, hze, heL, he1, hens, hβ, hd⟩ := forkPoint_eq_some C N hsel₁
  obtain ⟨hL2, e2, hze2, -, -, -, -, -⟩ := forkPoint_eq_some C N hsel₂
  have hLL : G₂.1.L = G₁.1.L := by
    have := congrArg (fun t : SigIn N X M => t.1.1) (hze.symm.trans hze2)
    exact this.symm
  have hrr : G₂.1.sig.1 = G₁.1.sig.1 := by
    have := congrArg (fun t : SigIn N X M => t.2.1) (hze.symm.trans hze2)
    exact this.symm
  -- the reduction
  unfold omdlExperiment
  dsimp only
  rw [run_reduction]
  unfold reductionBody
  dsimp only
  rw [Alg.run_bind]
  have S1 := sim_run C nonceCoef N qs xu ν T [] 0 (by simp) (A coins (C.mulG (xu : ZMod n)))
    (⟨⟨0, [], []⟩, [], []⟩, (2 * qs + 1, 0)) (⟨0, [], []⟩, [])
    (simRel_init C nonceCoef N qs xu ν T [] (2 * qs + 1, 0) rfl)
  dsimp only at S1
  set r₁ := (Alg.interp (simChallenger C nonceCoef N qs (C.mulG (xu : ZMod n))
    (Uof C qs xu ν) T) (A coins (C.mulG (xu : ZMod n))) ⟨⟨0, [], []⟩, [], []⟩).run
      (omdlChallenger C (merge xu ν)) (2 * qs + 1, 0) with hr₁
  replace S1 : r₁.1.1 = G₁.1 ∧ SimRel C nonceCoef N qs xu ν T [] 0 (r₁.1.2, r₁.2) G₁.2 := S1
  obtain ⟨h11, hch1, hsg1, hrec1, -, new₁, hcache1, hd1, hnew1, hcnt1, -⟩ := S1
  dsimp only at hch1 hsg1 hrec1 hcache1 hd1 hnew1 hcnt1
  rw [List.append_nil] at hcache1
  have hfp : forkPointPub C N (C.mulG (xu : ZMod n)) r₁.1.1 r₁.1.2.signer = some z := by
    rw [h11, hsg1, forkPointPub_eq]; exact hsel₁
  rw [hfp]
  dsimp only
  rw [Alg.run_bind]
  have hc₀ : ∀ r ∈ r₁.1.2.cache, RecSig C qs xu ν r := by
    rw [hcache1]
    exact fun r hr => ((hinv₁ r (hnew1 r hr)).1).recSig
  have S2 := sim_run C nonceCoef N qs xu ν (update T z s) r₁.1.2.cache r₁.2.2 hc₀
    (A coins (C.mulG (xu : ZMod n))) (⟨⟨0, [], []⟩, [], r₁.1.2.cache⟩, r₁.2) (⟨0, [], []⟩, [])
    (simRel_init C nonceCoef N qs xu ν (update T z s) r₁.1.2.cache r₁.2 hch1)
  dsimp only at S2
  set r₂ := (Alg.interp (simChallenger C nonceCoef N qs (C.mulG (xu : ZMod n))
    (Uof C qs xu ν) (update T z s)) (A coins (C.mulG (xu : ZMod n)))
      ⟨⟨0, [], []⟩, [], r₁.1.2.cache⟩).run (omdlChallenger C (merge xu ν)) r₁.2 with hr₂
  replace S2 : r₂.1.1 = G₂.1 ∧ SimRel C nonceCoef N qs xu ν (update T z s) r₁.1.2.cache r₁.2.2
      (r₂.1.2, r₂.2) G₂.2 := S2
  obtain ⟨h21, hch2, hsg2, hrec2, -, new₂, hcache2, hd2, hnew2, hcnt2, hpts2⟩ := S2
  dsimp only at hch2 hsg2 hrec2 hcache2 hd2 hnew2 hcnt2 hpts2
  rw [Alg.run_bind]
  have hst2 : r₂.2 = (2 * qs + 1, r₂.2.2) := Prod.ext hch2 rfl
  rw [hst2]
  -- the cache after both runs
  have hsigc : ∀ r ∈ r₂.1.2.cache, RecSig C qs xu ν r := by
    rw [hcache2]
    intro r hr
    rcases List.mem_append.mp hr with h | h
    · exact ((hinv₂ r (hnew2 r h)).1).recSig
    · exact hc₀ r h
  have hlenc : ∀ k, (entries k r₂.1.2.cache).length ≤ 2 := by
    intro k
    rw [hcache2, hcache1]
    simp only [entries, List.filter_append, List.length_append]
    have a := hcnt2 k
    have b := hcnt1 k
    split_ifs at a b <;> omega
  have hbc : ∀ k a a' rest, entries k r₂.1.2.cache = a :: a' :: rest → a.Rb.2 ≠ a'.Rb.2 := by
    intro k a a' rest hent
    rw [hcache2, hcache1] at hent
    simp only [entries, List.filter_append] at hent
    have l2 : (new₂.filter fun r => decide (r.k = k)).length ≤ 1 := by
      have := hcnt2 k; split_ifs at this <;> omega
    have l1 : (new₁.filter fun r => decide (r.k = k)).length ≤ 1 := by
      have := hcnt1 k; split_ifs at this <;> omega
    have hsplit : (new₂.filter fun r => decide (r.k = k)) = [a] ∧
        (new₁.filter fun r => decide (r.k = k)) = a' :: rest := by
      rcases h2 : new₂.filter (fun r => decide (r.k = k)) with _ | ⟨b, _ | ⟨b', t⟩⟩
      · rw [h2, List.nil_append] at hent
        rw [hent] at l1
        simp at l1
      · rw [h2] at hent
        simp only [List.cons_append, List.nil_append, List.cons.injEq] at hent
        exact ⟨by rw [h2, hent.1], hent.2⟩
      · rw [h2] at l2
        simp at l2
    obtain ⟨hA, hA'⟩ := hsplit
    have ha2 : a ∈ new₂ ∧ a.k = k := by
      have : a ∈ new₂.filter fun r => decide (r.k = k) := by rw [hA]; simp
      simpa using List.mem_filter.mp this
    have ha1 : a' ∈ new₁ ∧ a'.k = k := by
      have : a' ∈ new₁.filter fun r => decide (r.k = k) := by rw [hA']; simp
      simpa using List.mem_filter.mp this
    have hk : a.k = a'.k := ha2.2.trans ha1.2.symm
    have hpt := hpts2 a ha2.1 a' (by rw [hcache1]; exact ha1.1) hk
    intro hbeq
    apply hpt
    obtain ⟨okA', -, hsgnA'⟩ := hinv₁ a' (hnew1 a' ha1.1)
    obtain ⟨okA, -, -⟩ := hinv₂ a (hnew2 a ha2.1)
    have hbA : a.Rb.2 = ncHash nonceCoef a.ncIn := by
      obtain ⟨hkq, -, -, hpre, -, -⟩ := okA
      obtain ⟨-, j, -, -, hsv⟩ := signPre_some C hpre
      exact (getSessionValues_some C hsv).2.1
    have hbA' : a'.Rb.2 = ncHash nonceCoef a'.ncIn := by
      obtain ⟨hkq, -, -, hpre, -, -⟩ := okA'
      obtain ⟨-, j, -, -, hsv⟩ := signPre_some C hpre
      exact (getSessionValues_some C hsv).2.1
    have hnceq : a'.ncIn = a.ncIn := by
      by_contra hne
      exact hcol a' (hnew1 a' ha1.1) a (hnew2 a ha2.1) hk.symm
        ⟨hne, by rw [← hbA', ← hbA, hbeq]⟩
    refine (point_eq_of_ncIn_eq C nonceCoef N qs (xu : ZMod n) (noncesOf qs ν) T (update T z s)
      (C.mulG (xu : ZMod n)) (Uof C qs xu ν) okA' okA hk.symm hnceq ?_
      (fun τ => tweak_pk C τ (xu : ZMod n))).symm
    intro hNa
    refine update_of_ne ?_ _ _
    intro hkey
    rw [hze] at hkey
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at hkey
    apply hens
    rw [← hkey.1, ← hkey.2.2]
    exact hsgnA'
  obtain ⟨-, g2, g3, g4⟩ := run_solveSessions C qs xu ν r₂.1.2.cache hsigc hlenc hbc qs le_rfl
    r₂.2.2
  set sols := (solveSessions C qs (C.mulG (xu : ZMod n)) r₂.1.2.cache qs).run
    (omdlChallenger C (merge xu ν)) (2 * qs + 1, r₂.2.2) with hsols
  simp only [Alg.run_done]
  -- the secret key
  have hx : extractX C (C.mulG (xu : ZMod n)) r₁.1.1.τ
      ((r₁.1.1.sig.2 - r₂.1.1.sig.2) /
        ((((r₁.1.1.L.filter fun a => decide (a = z.2.2)).length : ℕ) : ZMod n) * (T z - s))) =
      (xu : ZMod n) := by
    rw [h11, h21]
    have hv₂' : verify C.ops (hashesOf N nonceCoef (update T (⟨G₁.1.L, hL⟩, G₁.1.sig.1, e) s))
        G₁.1.L (G₁.1.sig.1, G₂.1.sig.2) = true := by
      rw [← hze, ← hLL, ← hrr]
      exact hv₂
    have key := evenScalar_of_fork C nonceCoef N hN T hL heL hd he1 (sNew := s)
      (s₁ := G₁.1.sig.2) (s₂ := G₂.1.sig.2) (by rw [← hze]; exact hsz) hv₁ hv₂'
    rw [hze]
    dsimp only
    rw [key]
    exact extractX_evenScalar C (xu : ZMod n) _ hβ
  refine ⟨?_, ?_⟩
  · rw [g3, chalLogs_eq, hx]
    refine List.map_congr_left fun i hi => ?_
    have hi' : i < 2 * qs + 1 := List.mem_range.mp hi
    by_cases h0 : i = 0
    · simp [h0, logAt_merge_zero]
    · have hk : (i - 1) / 2 < qs := by omega
      have hsol := g2 ((i - 1) / 2) hk
      simp only [h0, ↓reduceIte, hsol, noncesOf]
      by_cases hpar : (i - 1) % 2 = 0
      · have hi2 : i = 2 * ((i - 1) / 2) + 1 := by omega
        simp only [hpar, ↓reduceIte]
        conv_rhs => rw [hi2, logAt_merge_odd xu ν hk]
      · have hi2 : i = 2 * ((i - 1) / 2) + 2 := by omega
        simp only [hpar, ↓reduceIte]
        conv_rhs => rw [hi2, logAt_merge_even xu ν hk]
  · rw [g3]
    have hall : (r₂.1.2.cache.filter fun r => decide (r.k < qs)) = r₂.1.2.cache := by
      refine List.filter_eq_self.mpr fun r hr => ?_
      obtain ⟨hk, -⟩ := hsigc r hr
      simpa using hk
    rw [hall, hcache2, hcache1] at g4
    simp only [List.length_append] at g4
    omega

end Dahlias.Security
