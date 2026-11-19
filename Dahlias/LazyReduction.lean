import Dahlias.Second
import Dahlias.Unforgeability

/-!
# A reduction that samples the random oracle lazily

`reduction A` takes a whole table of the random oracle as part of its coins.
`reductionLazy A` takes `2⋅(qh + qs) + 1` scalars instead and answers every new
query of the forger with the next of them.

* `reductionM` is the reduction written as an algorithm that queries the
  table. `answerG_reductionM`: with the queries answered from a table it is
  `reduction`.
* `nbound_reductionM`: it makes at most `2⋅(qh + qs) + 1` table queries.
* `omdlAdvantage_reduction_eq_lazy`: `reductionLazy A` wins the AOMDL game
  with the same probability as `reduction A`.
* `unforgeable_sqrt_lazy`: the security theorem with `reductionLazy`.

The coins of `reductionLazy` are the forger's coins and `2⋅(qh + qs) + 2`
scalars. The framework has no cost model, so there is still no statement
about running time; what is proven is that the reduction needs no object of
exponential size.
-/

set_option linter.unusedSectionVars false

namespace Dahlias.Security

open Taproot QTree Function

variable {n : ℕ} [Fact n.Prime] {E X M : Type} [AddCommGroup E] [DecidableEq E] [DecidableEq X]
  [DecidableEq M] (C : Curve n E X) (nonceCoef : E → E → List (X × M × E) → ZMod n) (N qs : ℕ)

/-- Algorithms for the AOMDL game that also query the table of the random
oracle. -/
abbrev RM (n N : ℕ) (E X M : Type) :=
  Alg (OmdlQ n ⊕ SigIn N X M) (SumR (OmdlR (n := n) E) (ZMod n))

/-- Read the table. -/
def rdTable (z : SigIn N X M) : RM n N E X M (ZMod n) := .ask (.inr z) .done

/-- Read the table that has the value `s` at `z₀`. -/
def rdFork (z₀ : SigIn N X M) (s : ZMod n) (z : SigIn N X M) : RM n N E X M (ZMod n) :=
  if z = z₀ then .done s else .ask (.inr z) .done

/-- Read a list of points. -/
def readAll (rd : SigIn N X M → RM n N E X M (ZMod n)) :
    List (SigIn N X M) → RM n N E X M (List (ZMod n))
  | [] => .done []
  | d :: l => rd d >>= fun c => readAll rd l >>= fun cs => .done (c :: cs)

omit [Fact n.Prime] [AddCommGroup E] [DecidableEq E] [DecidableEq X] [DecidableEq M] in
theorem answerG_readAll (T T' : SigIn N X M → ZMod n) (rd : SigIn N X M → RM n N E X M (ZMod n))
    (hrd : ∀ z, answerG T (rd z) = .done (T' z)) (l : List (SigIn N X M)) :
    answerG T (readAll N rd l) = .done (l.map T') := by
  induction l with
  | nil => rfl
  | cons d l ih =>
    simp only [readAll, answerG_bind, hrd, ih]
    rfl

variable (P : E) (U : ℕ → PubNonce E)

/-- `simChallenger`, reading the table through `rd`. -/
def simChallengerM (rd : SigIn N X M → RM n N E X M (ZMod n)) :
    (q : AdvQ n N E X M) → SimState n E X M → RM n N E X M (AdvR q × SimState n E X M)
  | .hash z, st => rd z >>= fun c => .done (c, st)
  | .openSession, st =>
    .done (if st.signer.opened < qs then
        (some (U st.signer.opened), { st with signer.opened := st.signer.opened + 1 })
      else (none, st))
  | .close k τ m agg pm pubnonces, st =>
    if h : k < qs ∧ k < st.signer.opened ∧ k ∉ st.signer.closed ∧ τ.2 ≠ 0 ∧ pm.length ≤ N then
      match signPrePub C (H₀ nonceCoef N) (U k).2 (τ.pk C P) m agg pm pubnonces with
      | some Rb =>
        rd (⟨pm, h.2.2.2.2⟩, C.x Rb.1, (C.x (τ.pk C P), m)) >>= fun c =>
          liftQ (simSign C qs P U ⟨k, [(τ, m, c)], agg, pm, pubnonces, Rb, 0⟩
            { st.signer with closed := k :: st.signer.closed
                             signed := (pm, C.x (τ.pk C P), m) :: st.signer.signed } st) >>=
            fun p => .done (some p.1, p.2)
      | none => .done (none, st)
    else .done (none, st)
  | .single items, st =>
    if _ : st.signer.opened < qs then
      let L := singleKeysPub C P items
      let b := ncHash nonceCoef (singleNcIn L)
      let R := (U st.signer.opened).1 + b.val • (U st.signer.opened).2
      if hc : items ≠ [] ∧ L.length ≤ N ∧ R ≠ 0 ∧ ∀ i ∈ items, i.1.2 ≠ 0 ∧ i.1.pk C P ≠ 0 then
        readAll N rd (L.map fun e => ((⟨L, hc.2.1⟩ : BList N X M), C.x R, e)) >>= fun cs =>
          liftQ (simSign C qs P U
            ⟨st.signer.opened, singleTerms items cs, (0, 0), L, L.map fun _ => (0, 0), (R, b), 0⟩
            { opened := st.signer.opened + 1
              closed := st.signer.opened :: st.signer.closed
              signed := L.map (fun e => (L, e.1, e.2)) ++ st.signer.signed } st) >>=
            fun p => .done (some (C.x R, p.1), p.2)
      else .done (none, { st with signer := { st.signer with
        opened := st.signer.opened + 1, closed := st.signer.opened :: st.signer.closed } })
    else .done (none, st)

/-- With the table queries answered, `simChallengerM` is `simChallenger`. -/
theorem answerG_simChallengerM (T T' : SigIn N X M → ZMod n)
    (rd : SigIn N X M → RM n N E X M (ZMod n)) (hrd : ∀ z, answerG T (rd z) = .done (T' z))
    (q : AdvQ n N E X M) (st : SimState n E X M) :
    answerG T (simChallengerM C nonceCoef N qs P U rd q st) =
      simChallenger C nonceCoef N qs P U T' q st := by
  cases q with
  | hash z =>
    simp only [simChallengerM, simChallenger, answerG_bind, hrd]
    rfl
  | openSession => rfl
  | close k τ m agg pm pubnonces =>
    unfold simChallengerM simChallenger
    dsimp only
    split_ifs with h
    · cases signPrePub C (H₀ nonceCoef N) (U k).2 (τ.pk C P) m agg pm pubnonces with
      | none => rfl
      | some Rb =>
        simp only [answerG_bind, hrd, answerG_liftQ]
        rfl
    · rfl
  | single items =>
    unfold simChallengerM simChallenger
    dsimp only
    split_ifs with h hc
    · simp only [answerG_bind, answerG_readAll N T T' rd hrd, answerG_liftQ, List.map_map]
      rfl
    · rfl
    · rfl

omit [Fact n.Prime] [AddCommGroup E] [DecidableEq E] in
theorem answerG_rdFork (T : SigIn N X M → ZMod n) (z₀ : SigIn N X M) (s : ZMod n)
    (z : SigIn N X M) :
    answerG T (rdFork (E := E) N z₀ s z) = .done (update T z₀ s z) := by
  unfold rdFork
  split_ifs with h
  · rw [h, update_self]
    rfl
  · rw [update_of_ne h]
    rfl

variable {Coins : Type} (A : Adversary n N E X M Coins)

/-- `reductionBody` as an algorithm that queries the table. -/
def reductionBodyM (c : Coins) (s : ZMod n) : RM n N E X M (List (ZMod n)) :=
  Alg.interp (simChallengerM C nonceCoef N qs P U (rdTable N)) (A c P) ⟨⟨0, [], []⟩, [], []⟩ >>=
    fun r₁ =>
      match forkPointPub C N P r₁.1 r₁.2.signer with
      | none => .done []
      | some z =>
        Alg.interp (simChallengerM C nonceCoef N qs P U (rdFork N z s)) (A c P)
            ⟨⟨0, [], []⟩, [], r₁.2.cache⟩ >>= fun r₂ =>
          liftQ (solveSessions C qs P r₂.2.cache qs) >>= fun sols =>
            rdTable N z >>= fun Tz =>
              let cnt : ZMod n := ((r₁.1.L.filter fun e => decide (e = z.2.2)).length : ZMod n)
              let v := (r₁.1.sig.2 - r₂.1.sig.2) / (cnt * (Tz - s))
              let x := extractX C P r₁.1.τ v
              .done ((List.range (2 * qs + 1)).map fun i =>
                if i = 0 then x
                else if (i - 1) % 2 = 0 then ((sols.getD ((i - 1) / 2) fun _ => (0, 0)) x).1
                else ((sols.getD ((i - 1) / 2) fun _ => (0, 0)) x).2)

theorem answerG_reductionBodyM (T : SigIn N X M → ZMod n) (c : Coins) (s : ZMod n) :
    answerG T (reductionBodyM C nonceCoef N qs P U A c s) =
      reductionBody C nonceCoef N qs P U A (c, T, s) := by
  unfold reductionBodyM reductionBody
  rw [answerG_bind, answerG_interp T _ _
    (answerG_simChallengerM C nonceCoef N qs P U T T (rdTable N) fun z => rfl)]
  congr 1
  funext r₁
  cases hfp : forkPointPub C N P r₁.1 r₁.2.signer with
  | none => rfl
  | some z =>
    dsimp only
    rw [answerG_bind, answerG_interp T _ _
      (answerG_simChallengerM C nonceCoef N qs P U T (update T z s) (rdFork N z s)
        (answerG_rdFork N T z s))]
    congr 1
    funext r₂
    rw [answerG_bind, answerG_liftQ]
    rfl

/-- **The reduction as an algorithm that queries the table.** -/
def reductionM (c : Coins) (s : ZMod n) : RM n N E X M (List (ZMod n)) :=
  liftQ (getChals (2 * qs + 1)) >>= fun chals =>
    reductionBodyM C nonceCoef N qs (chals.getD 0 0)
      (fun k => (chals.getD (2 * k + 1) 0, chals.getD (2 * k + 2) 0)) A c s

/-- **With the table queries answered from a table it is `reduction`.** -/
theorem answerG_reductionM (T : SigIn N X M → ZMod n) (c : Coins) (s : ZMod n) :
    answerG T (reductionM C nonceCoef N qs A c s) = reduction C nonceCoef N qs A (c, T, s) := by
  unfold reductionM reduction
  rw [answerG_bind, answerG_liftQ]
  congr 1
  funext chals
  exact answerG_reductionBodyM C nonceCoef N qs _ _ A T c s

/-! ## The number of table queries -/

/-- A way to read the table that costs at most one query. -/
def OneRead (rd : SigIn N X M → RM n N E X M (ZMod n)) : Prop :=
  ∀ z c, RP (fun _ => True) (fun _ => c) (rd z) (c + 1)

omit [Fact n.Prime] [AddCommGroup E] [DecidableEq E] [DecidableEq X] [DecidableEq M] in
theorem oneRead_rdTable : OneRead (n := n) (E := E) (X := X) (M := M) N (rdTable N) :=
  fun _ c => ⟨Nat.succ_pos c, fun _ => ⟨trivial, by simp⟩⟩

omit [Fact n.Prime] [AddCommGroup E] [DecidableEq E] in
theorem oneRead_rdFork (z₀ : SigIn N X M) (s : ZMod n) : OneRead (E := E) N (rdFork N z₀ s) := by
  intro z c
  unfold rdFork
  split_ifs
  · exact ⟨trivial, Nat.le_succ c⟩
  · exact ⟨Nat.succ_pos c, fun _ => ⟨trivial, by simp⟩⟩

omit [Fact n.Prime] [AddCommGroup E] [DecidableEq E] [DecidableEq X] [DecidableEq M] in
theorem rp_readAll {rd : SigIn N X M → RM n N E X M (ZMod n)} (hrd : OneRead N rd)
    (l : List (SigIn N X M)) (c : ℕ) :
    RP (fun _ => True) (fun _ => c) (readAll N rd l) (c + l.length) := by
  induction l generalizing c with
  | nil => exact ⟨trivial, le_rfl⟩
  | cons d l ih =>
    have h1 := hrd d (c + l.length)
    refine RP.bind (h1.mono (by simp only [List.length_cons]; omega)) fun a _ => ?_
    exact RP.bind (ih c) fun cs _ => ⟨trivial, le_rfl⟩

theorem allLeaves_simSign (rec0 : CloseRec n E X M) (sg : SignerState X M)
    (st : SimState n E X M) :
    AllLeaves (fun p => p.2.signer = sg) (simSign C qs P U rec0 sg st) := by
  unfold simSign
  split
  · rfl
  · exact fun _ => rfl

/-- One query of the forger: the table queries are paid by the hash budget
and by a slot that gets closed. -/
theorem rp_simChallengerM {rd : SigIn N X M → RM n N E X M (ZMod n)} (hrd : OneRead N rd)
    (q : AdvQ n N E X M) (st : SimState n E X M) (hst : ClosedOk qs st.signer) (qh : ℕ)
    (hq : hashCost q ≤ qh) :
    RP (fun p => ClosedOk qs p.2.signer)
      (fun p => (qh - hashCost q) + (qs - p.2.signer.closed.length))
      (simChallengerM C nonceCoef N qs P U rd q st) (qh + (qs - st.signer.closed.length)) := by
  cases q with
  | hash z =>
    simp only [hashCost] at hq ⊢
    refine RP.bind ((hrd z ((qh - 1) + (qs - st.signer.closed.length))).mono (by omega))
      fun c _ => ⟨hst, le_rfl⟩
  | openSession =>
    simp only [simChallengerM, hashCost]
    split_ifs with h
    · exact ⟨⟨hst.1, fun k hk => Nat.lt_succ_of_lt (hst.2.1 k hk), h⟩, by simp⟩
    · exact ⟨hst, by simp⟩
  | close k τ m agg pm pubnonces =>
    unfold simChallengerM
    dsimp only
    simp only [hashCost]
    split_ifs with h
    · cases signPrePub C (H₀ nonceCoef N) (U k).2 (τ.pk C P) m agg pm pubnonces with
      | none => exact ⟨hst, by simp⟩
      | some Rb =>
        have hst' : ClosedOk qs (X := X) (M := M)
            { st.signer with closed := k :: st.signer.closed
                             signed := (pm, C.x (τ.pk C P), m) :: st.signer.signed } :=
          ⟨List.nodup_cons.mpr ⟨h.2.2.1, hst.1⟩, by
            intro j hj
            rcases List.mem_cons.mp hj with rfl | hj
            · exact h.2.1
            · exact hst.2.1 j hj, hst.2.2⟩
        have hlen := hst'.length_le
        simp only [List.length_cons] at hlen
        dsimp only
        refine RP.bind ((hrd _ (qh + (qs - (st.signer.closed.length + 1)))).mono (by omega))
          fun c _ => ?_
        refine RP.bind (RP_liftQ (Post := fun p => p.2.signer = _)
          (cost := fun _ => qh + (qs - (st.signer.closed.length + 1)))
          (allLeaves_simSign C qs P U _ _ st) fun _ _ => le_rfl) fun p hp => ?_
        refine ⟨?_, ?_⟩
        · change ClosedOk qs p.2.signer
          rw [hp]
          exact hst'
        · change qh - 0 + (qs - p.2.signer.closed.length) ≤ _
          rw [hp]
          simp
    · exact ⟨hst, by simp⟩
  | single items =>
    unfold simChallengerM
    dsimp only
    simp only [hashCost] at hq ⊢
    have hcl : ∀ (sg : List (List (X × M) × X × M)) (h : st.signer.opened < qs),
        ClosedOk qs (X := X) (M := M)
          { opened := st.signer.opened + 1, closed := st.signer.opened :: st.signer.closed,
            signed := sg } :=
      fun sg h => ⟨List.nodup_cons.mpr ⟨fun hm => lt_irrefl _ (hst.2.1 _ hm), hst.1⟩, by
        intro j hj
        rcases List.mem_cons.mp hj with rfl | hj
        · exact Nat.lt_succ_self _
        · exact Nat.lt_succ_of_lt (hst.2.1 j hj), h⟩
    split_ifs with h hc
    · have hst' := hcl ((singleKeysPub C P items).map
        (fun e => (singleKeysPub C P items, e.1, e.2)) ++ st.signer.signed) h
      have hlen := hst'.length_le
      simp only [List.length_cons] at hlen
      have hk : (singleKeysPub C P items).length = items.length := by simp [singleKeysPub]
      have hra := rp_readAll (E := E) N hrd ((singleKeysPub C P items).map fun e =>
        ((⟨singleKeysPub C P items, hc.2.1⟩ : BList N X M),
          C.x ((U st.signer.opened).1 +
            (ncHash nonceCoef (singleNcIn (singleKeysPub C P items))).val •
              (U st.signer.opened).2), e))
        ((qh - items.length) + (qs - (st.signer.closed.length + 1)))
      refine RP.bind (hra.mono (by rw [List.length_map, hk]; omega)) fun cs _ => ?_
      refine RP.bind (RP_liftQ (Post := fun p => p.2.signer = _)
        (cost := fun _ => (qh - items.length) + (qs - (st.signer.closed.length + 1)))
        (allLeaves_simSign C qs P U _ _ st) fun _ _ => le_rfl) fun p hp => ?_
      refine ⟨?_, ?_⟩
      · change ClosedOk qs p.2.signer
        rw [hp]
        exact hst'
      · change qh - items.length + (qs - p.2.signer.closed.length) ≤ _
        rw [hp]
        simp
    · have hst' := hcl st.signer.signed h
      have hlen := hst'.length_le
      simp only [List.length_cons] at hlen
      exact ⟨hst', by simp; omega⟩
    · exact ⟨hst, by simp⟩

/-- The table queries of the forger run by the reduction. -/
theorem nbound_interp {rd : SigIn N X M → RM n N E X M (ZMod n)} (hrd : OneRead N rd)
    {α : Type} (t : Alg (AdvQ n N E X M) AdvR α) (qh : ℕ) (ht : HashBound t qh)
    (st : SimState n E X M) (hst : ClosedOk qs st.signer) :
    NBound (Alg.interp (simChallengerM C nonceCoef N qs P U rd) t st)
      (qh + (qs - st.signer.closed.length)) := by
  induction t generalizing st qh with
  | done a => trivial
  | ask q f ih =>
    obtain ⟨hc, hf⟩ := hashBound_ask ht
    rw [Alg.interp_ask]
    exact RP.bind_nbound (rp_simChallengerM C nonceCoef N qs P U hrd q st hst qh hc)
      fun p hp => ih p.1 (qh - hashCost q) (hf _) p.2 hp

/-- **The reduction makes at most `2⋅(qh + qs) + 1` table queries.** -/
theorem nbound_reductionM (qh : ℕ) (hA : ∀ coins P, HashBound (A coins P) qh) (c : Coins)
    (s : ZMod n) : NBound (reductionM C nonceCoef N qs A c s) (2 * (qh + qs) + 1) := by
  have h0 : ClosedOk qs (X := X) (M := M) ⟨0, [], []⟩ := ⟨List.nodup_nil, by simp, Nat.zero_le _⟩
  unfold reductionM
  refine (NBound.bind (a := 0) (b := 2 * (qh + qs) + 1) (nbound_liftQ _ 0) fun chals => ?_).mono
    (by omega)
  unfold reductionBodyM
  have b1 := nbound_interp C nonceCoef N qs (chals.getD 0 0)
    (fun k => (chals.getD (2 * k + 1) 0, chals.getD (2 * k + 2) 0)) (oneRead_rdTable N)
    (A c (chals.getD 0 0)) qh (hA _ _) ⟨⟨0, [], []⟩, [], []⟩ h0
  refine (NBound.bind (b := (qh + qs) + 1) b1 fun r₁ => ?_).mono (by simp; omega)
  cases forkPointPub C N (chals.getD 0 0) r₁.1 r₁.2.signer with
  | none => trivial
  | some z =>
    dsimp only
    have b2 := nbound_interp C nonceCoef N qs (chals.getD 0 0)
      (fun k => (chals.getD (2 * k + 1) 0, chals.getD (2 * k + 2) 0)) (oneRead_rdFork N z s)
      (A c (chals.getD 0 0)) qh (hA _ _) ⟨⟨0, [], []⟩, [], r₁.2.cache⟩ h0
    refine (NBound.bind (b := 1) b2 fun r₂ => ?_).mono (by simp)
    refine (NBound.bind (a := 0) (b := 1) (nbound_liftQ _ 0) fun sols => ?_).mono (by omega)
    exact ⟨Nat.one_pos, fun _ => trivial⟩

/-! ## The lazily sampling reduction -/

/-- **The reduction with a lazily sampled random oracle.** Its coins are the
forger's coins, `q` scalars for the answers of the oracle, and the new value
at the fork point. -/
def reductionLazy (q : ℕ) : OmdlAdversary n E (Coins × (Fin q → ZMod n) × ZMod n) := fun ρ =>
  answerLazy (QTree.stream ρ.2.1) 0 [] (reductionM C nonceCoef N qs A ρ.1 ρ.2.2)

/-- Samples of the AOMDL game with the table, or the answers, last. -/
def tableLast (c : ℕ) (Tb : Type) :
    ((Fin c → (ZMod n)ˣ) × Coins × ZMod n) × Tb ≃ (Fin c → (ZMod n)ˣ) × (Coins × Tb × ZMod n) where
  toFun p := (p.1.1, p.1.2.1, p.2, p.1.2.2)
  invFun ω := ((ω.1, ω.2.1, ω.2.2.2), ω.2.2.1)
  left_inv _ := rfl
  right_inv _ := rfl

variable [Fintype Coins] [Fintype (SigIn N X M)]

set_option synthInstance.maxSize 4000 in
/-- **The lazily sampling reduction wins the AOMDL game as often as
`reduction`.** -/
theorem omdlAdvantage_reduction_eq_lazy (qh : ℕ) (hA : ∀ coins P, HashBound (A coins P) qh) :
    omdlAdvantage C (2 * qs + 1) (reduction C nonceCoef N qs A) =
      omdlAdvantage C (2 * qs + 1)
        (reductionLazy C nonceCoef N qs A (2 * (qh + qs) + 1)) := by
  unfold omdlAdvantage
  rw [← prob_equiv (tableLast (n := n) (Coins := Coins) (2 * qs + 1) (SigIn N X M → ZMod n))
      (omdlExperiment C (2 * qs + 1) (reduction C nonceCoef N qs A)),
    ← prob_equiv (tableLast (n := n) (Coins := Coins) (2 * qs + 1)
      (Fin (2 * (qh + qs) + 1) → ZMod n))
      (omdlExperiment C (2 * qs + 1) (reductionLazy C nonceCoef N qs A (2 * (qh + qs) + 1)))]
  refine prob_prod_congr _ _ fun a => ?_
  have key := prob_answerG_eq_lazy (omdlChallenger C a.1) (0, 0)
    (reductionM C nonceCoef N qs A a.2.1 a.2.2)
    (fun out : List (ZMod n) × (ℕ × ℕ) => out.1 = chalLogs a.1 out.2.1 ∧ out.2.2 < out.2.1)
    (2 * (qh + qs) + 1) (nbound_reductionM C nonceCoef N qs A qh hA a.2.1 a.2.2)
  refine Eq.trans ?_ (key.trans ?_)
  · congr 1
    funext T
    rw [answerG_reductionM]
    rfl
  · rfl

set_option synthInstance.maxSize 4000 in
/-- **BIP 459 is unforgeable under AOMDL, with a reduction that samples the
random oracle lazily.** The statement of `unforgeable_sqrt` for
`reductionLazy`. -/
theorem unforgeable_sqrt_lazy (hN : N < n) (qh : ℕ) (hA : ∀ coins P, HashBound (A coins P) qh) :
    forgeAdvantage C nonceCoef N qs A ≤
      Real.sqrt ((qh + qs + 1 : ℕ) *
        (omdlAdvantage C (2 * qs + 1) (reductionLazy C nonceCoef N qs A (2 * (qh + qs) + 1)) +
          collisionAdvantage C nonceCoef N qs A)) + (qh + qs + 1 : ℕ) / n + qs / (n - 1 : ℝ) := by
  rw [← omdlAdvantage_reduction_eq_lazy C nonceCoef N qs A qh hA]
  exact unforgeable_sqrt C nonceCoef N qs A hN qh hA

end Dahlias.Security
