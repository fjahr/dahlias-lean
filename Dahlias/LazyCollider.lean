import Dahlias.LazyReduction

/-!
# A collision finder that samples the random oracle lazily

The sample of `collider A` has a whole table of the random oracle.
`colliderLazy A` takes `2⋅(qh + qs)` scalars instead and answers every new
query of the forger with the next of them. This is what
`Dahlias.LazyReduction` does for the reduction.

* `logChallengerM` is the game's signer with its records, written as an
  algorithm that queries the table. `colliderM` is the collision finder
  written that way. `answerG_colliderM`: with the queries answered from a
  table it is `collider`.
* `nbound_colliderM`: it makes at most `2⋅(qh + qs)` table queries.
* `collisionAdvantage_eq_lazy`: `colliderLazy A` outputs a collision with the
  same probability as `collider A`.
* `unforgeable_sqrt_lazy_both`: the security theorem with `reductionLazy` and
  `colliderLazy`. Neither algorithm in it needs an object of exponential size.
-/

set_option linter.unusedSectionVars false

namespace Dahlias.Security

open Taproot QTree Function

variable {n : ℕ} [Fact n.Prime] {E X M : Type} [AddCommGroup E] [DecidableEq E] [DecidableEq X]
  [DecidableEq M] (C : Curve n E X) (nonceCoef : E → E → List (X × M × E) → ZMod n) (N qs : ℕ)

/-- Interpreting with a handler that asks nothing is running with it. -/
theorem interp_done_eq_run {Q Q' : Type} {R : Q → Type} {R' : Q' → Type} {σ α : Type}
    (h : (q : Q) → σ → Alg Q' R' (R q × σ)) (g : (q : Q) → σ → R q × σ)
    (hg : ∀ q s, h q s = .done (g q s)) (t : Alg Q R α) (s : σ) :
    Alg.interp h t s = .done (t.run g s) := by
  induction t generalizing s with
  | done a => rfl
  | ask q f ih =>
    rw [Alg.interp_ask, hg]
    exact ih _ _

/-! ## The game with its records, as an algorithm that queries the table -/

/-- `logChallenger`, reading the table through `rd`. -/
def logChallengerM (rd : SigIn N X M → RM n N E X M (ZMod n)) (x : ZMod n)
    (nonces : Fin qs → SecNonce n) :
    (q : AdvQ n N E X M) → SignerState X M × List (CloseRec n E X M) →
      RM n N E X M (AdvR q × (SignerState X M × List (CloseRec n E X M)))
  | .hash z, st => rd z >>= fun c => .done (c, st)
  | .openSession, st =>
    .done (if h : st.1.opened < qs then
        (some (C.mulG (nonces ⟨st.1.opened, h⟩).1, C.mulG (nonces ⟨st.1.opened, h⟩).2),
          ({ st.1 with opened := st.1.opened + 1 }, st.2))
      else (none, st))
  | .close k τ m agg pm pubnonces, st =>
    if h : k < qs ∧ k < st.1.opened ∧ k ∉ st.1.closed ∧ τ.2 ≠ 0 ∧ pm.length ≤ N then
      match signPre C.ops (H₀ nonceCoef N) (nonces ⟨k, h.1⟩) (τ.sk x) m agg pm pubnonces with
      | some Rb =>
        rd (⟨pm, h.2.2.2.2⟩, C.x Rb.1, (C.x (C.mulG (τ.sk x)), m)) >>= fun c =>
          .done (some (signPost C.ops (nonces ⟨k, h.1⟩) (τ.sk x) Rb c),
            ({ st.1 with closed := k :: st.1.closed
                         signed := (pm, C.x (C.mulG (τ.sk x)), m) :: st.1.signed },
              ⟨k, [(τ, m, c)], agg, pm, pubnonces, Rb,
                signPost C.ops (nonces ⟨k, h.1⟩) (τ.sk x) Rb c⟩ :: st.2))
      | none => .done (none, st)
    else .done (none, st)
  | .single items, st =>
    if h : st.1.opened < qs then
      let r := singleNonce true nonceCoef (singleKeys C x items) (nonces ⟨st.1.opened, h⟩)
      if hc : items ≠ [] ∧ (singleKeys C x items).length ≤ N ∧ r ≠ 0 ∧
          ∀ i ∈ items, i.1.2 ≠ 0 ∧ i.1.sk x ≠ 0 then
        readAll N rd ((singleKeys C x items).map fun e =>
            ((⟨singleKeys C x items, hc.2.1⟩ : BList N X M), C.x (C.mulG r), e)) >>= fun cs =>
          .done (some (C.x (C.mulG r), singleS C x items r cs),
            ({ opened := st.1.opened + 1
               closed := st.1.opened :: st.1.closed
               signed := (singleKeys C x items).map
                 (fun e => (singleKeys C x items, e.1, e.2)) ++ st.1.signed },
              ⟨st.1.opened, singleTerms items cs, (0, 0), singleKeys C x items,
                (singleKeys C x items).map fun _ => (0, 0),
                (C.mulG r, ncHash nonceCoef (singleNcIn (singleKeys C x items))),
                singleS C x items r cs⟩ :: st.2))
      else .done (none, ({ st.1 with opened := st.1.opened + 1,
                                     closed := st.1.opened :: st.1.closed }, st.2))
    else .done (none, st)

/-- With the table queries answered, `logChallengerM` is `logChallenger`. -/
theorem answerG_logChallengerM (T T' : SigIn N X M → ZMod n)
    (rd : SigIn N X M → RM n N E X M (ZMod n)) (hrd : ∀ z, answerG T (rd z) = .done (T' z))
    (x : ZMod n) (nonces : Fin qs → SecNonce n) (q : AdvQ n N E X M)
    (st : SignerState X M × List (CloseRec n E X M)) :
    answerG T (logChallengerM C nonceCoef N qs rd x nonces q st) =
      .done (logChallenger C nonceCoef N qs x nonces T' q st) := by
  cases q with
  | hash z =>
    simp only [logChallengerM, logChallenger, answerG_bind, hrd]
    rfl
  | openSession =>
    simp only [logChallengerM, logChallenger, challengerG]
    split_ifs <;> rfl
  | close k τ m agg pm pubnonces =>
    unfold logChallengerM logChallenger
    dsimp only
    split_ifs with h
    · cases signPre C.ops (H₀ nonceCoef N) (nonces ⟨k, h.1⟩) (τ.sk x) m agg pm pubnonces with
      | none => rfl
      | some Rb =>
        simp only [answerG_bind, hrd]
        rfl
    · rfl
  | single items =>
    unfold logChallengerM logChallenger
    dsimp only
    split_ifs with h hc
    · simp only [answerG_bind, answerG_readAll N T T' rd hrd, List.map_map]
      rfl
    · rfl
    · rfl

/-! ## The number of table queries -/

/-- One query of the forger: the table queries are paid by the hash budget
and by a slot that gets closed. -/
theorem rp_logChallengerM {rd : SigIn N X M → RM n N E X M (ZMod n)} (hrd : OneRead N rd)
    (x : ZMod n) (nonces : Fin qs → SecNonce n) (q : AdvQ n N E X M)
    (st : SignerState X M × List (CloseRec n E X M)) (hst : ClosedOk qs st.1) (qh : ℕ)
    (hq : hashCost q ≤ qh) :
    RP (fun p => ClosedOk qs p.2.1)
      (fun p => (qh - hashCost q) + (qs - p.2.1.closed.length))
      (logChallengerM C nonceCoef N qs rd x nonces q st) (qh + (qs - st.1.closed.length)) := by
  cases q with
  | hash z =>
    simp only [hashCost] at hq ⊢
    exact RP.bind ((hrd z ((qh - 1) + (qs - st.1.closed.length))).mono (by omega))
      fun c _ => ⟨hst, le_rfl⟩
  | openSession =>
    simp only [logChallengerM, hashCost]
    split_ifs with h
    · exact ⟨⟨hst.1, fun k hk => Nat.lt_succ_of_lt (hst.2.1 k hk), h⟩, by simp⟩
    · exact ⟨hst, by simp⟩
  | close k τ m agg pm pubnonces =>
    unfold logChallengerM
    dsimp only
    simp only [hashCost]
    split_ifs with h
    · cases signPre C.ops (H₀ nonceCoef N) (nonces ⟨k, h.1⟩) (τ.sk x) m agg pm pubnonces with
      | none => exact ⟨hst, by simp⟩
      | some Rb =>
        have hst' : ClosedOk qs (X := X) (M := M)
            { st.1 with closed := k :: st.1.closed
                        signed := (pm, C.x (C.mulG (τ.sk x)), m) :: st.1.signed } :=
          ⟨List.nodup_cons.mpr ⟨h.2.2.1, hst.1⟩, by
            intro j hj
            rcases List.mem_cons.mp hj with rfl | hj
            · exact h.2.1
            · exact hst.2.1 j hj, hst.2.2⟩
        have hlen := hst'.length_le
        simp only [List.length_cons] at hlen
        dsimp only
        refine RP.bind ((hrd _ (qh + (qs - (st.1.closed.length + 1)))).mono (by omega))
          fun c _ => ⟨hst', ?_⟩
        simp
    · exact ⟨hst, by simp⟩
  | single items =>
    unfold logChallengerM
    dsimp only
    simp only [hashCost] at hq ⊢
    have hcl : ∀ (sg : List (List (X × M) × X × M)) (h : st.1.opened < qs),
        ClosedOk qs (X := X) (M := M)
          { opened := st.1.opened + 1, closed := st.1.opened :: st.1.closed, signed := sg } :=
      fun sg h => ⟨List.nodup_cons.mpr ⟨fun hm => lt_irrefl _ (hst.2.1 _ hm), hst.1⟩, by
        intro j hj
        rcases List.mem_cons.mp hj with rfl | hj
        · exact Nat.lt_succ_self _
        · exact Nat.lt_succ_of_lt (hst.2.1 j hj), h⟩
    split_ifs with h hc
    · have hst' := hcl ((singleKeys C x items).map
        (fun e => (singleKeys C x items, e.1, e.2)) ++ st.1.signed) h
      have hlen := hst'.length_le
      simp only [List.length_cons] at hlen
      have hk : (singleKeys C x items).length = items.length := by simp [singleKeys]
      have hra := rp_readAll (E := E) N hrd ((singleKeys C x items).map fun e =>
        ((⟨singleKeys C x items, hc.2.1⟩ : BList N X M),
          C.x (C.mulG (singleNonce true nonceCoef (singleKeys C x items)
            (nonces ⟨st.1.opened, h⟩))), e))
        ((qh - items.length) + (qs - (st.1.closed.length + 1)))
      refine RP.bind (hra.mono (by rw [List.length_map, hk]; omega)) fun cs _ => ⟨hst', ?_⟩
      simp
    · have hst' := hcl st.1.signed h
      have hlen := hst'.length_le
      simp only [List.length_cons] at hlen
      exact ⟨hst', by simp; omega⟩
    · exact ⟨hst, by simp⟩

/-- The table queries of the forger in the game. -/
theorem nbound_interp_log {rd : SigIn N X M → RM n N E X M (ZMod n)} (hrd : OneRead N rd)
    (x : ZMod n) (nonces : Fin qs → SecNonce n) {α : Type} (t : Alg (AdvQ n N E X M) AdvR α)
    (qh : ℕ) (ht : HashBound t qh) (st : SignerState X M × List (CloseRec n E X M))
    (hst : ClosedOk qs st.1) :
    NBound (Alg.interp (logChallengerM C nonceCoef N qs rd x nonces) t st)
      (qh + (qs - st.1.closed.length)) := by
  induction t generalizing st qh with
  | done a => trivial
  | ask q f ih =>
    obtain ⟨hc, hf⟩ := hashBound_ask ht
    rw [Alg.interp_ask]
    exact RP.bind_nbound (rp_logChallengerM C nonceCoef N qs hrd x nonces q st hst qh hc)
      fun p hp => ih p.1 (qh - hashCost q) (hf _) p.2 hp

/-! ## The collision finder as an algorithm that queries the table -/

variable {Coins : Type} (A : Adversary n N E X M Coins)

/-- `gameRecs`, reading the table through `rd`. -/
def gameRecsM (rd : SigIn N X M → RM n N E X M (ZMod n)) (x : (ZMod n)ˣ)
    (ν : Fin qs → (ZMod n)ˣ × (ZMod n)ˣ) (c : Coins) :
    RM n N E X M (Forgery n X M × SignerState X M × List (CloseRec n E X M)) :=
  Alg.interp (logChallengerM C nonceCoef N qs rd (x : ZMod n) (noncesOf qs ν))
    (A c (C.mulG (x : ZMod n))) (⟨0, [], []⟩, [])

theorem answerG_gameRecsM (T T' : SigIn N X M → ZMod n)
    (rd : SigIn N X M → RM n N E X M (ZMod n)) (hrd : ∀ z, answerG T (rd z) = .done (T' z))
    (x : (ZMod n)ˣ) (ν : Fin qs → (ZMod n)ˣ × (ZMod n)ˣ) (c : Coins)
    (T₀ : SigIn N X M → ZMod n) :
    answerG T (gameRecsM C nonceCoef N qs A rd x ν c) =
      .done (gameRecs C nonceCoef N qs A (x, ν, c, T₀) T') := by
  unfold gameRecsM gameRecs
  rw [answerG_interp T _
    (fun q st => .done (logChallenger C nonceCoef N qs (x : ZMod n) (noncesOf qs ν) T' q st))
    (answerG_logChallengerM C nonceCoef N qs T T' rd hrd _ _)]
  exact interp_done_eq_run _ _ (fun _ _ => rfl) _ _

open Classical in
/-- **The collision finder as an algorithm that queries the table.** -/
noncomputable def colliderM (x : (ZMod n)ˣ) (ν : Fin qs → (ZMod n)ˣ × (ZMod n)ˣ) (c : Coins)
    (s : ZMod n) : RM n N E X M ((E × E × List (X × M × E)) × (E × E × List (X × M × E))) :=
  gameRecsM C nonceCoef N qs A (rdTable N) x ν c >>= fun r₁ =>
    match forkPoint C N (x : ZMod n) r₁.1 r₁.2.1 with
    | none => .done ((0, 0, []), (0, 0, []))
    | some z =>
      gameRecsM C nonceCoef N qs A (rdFork N z s) x ν c >>= fun r₂ =>
        .done (((r₁.2.2.product r₂.2.2).find? fun ab =>
          decide (ab.1.k = ab.2.k ∧ IsCollision nonceCoef (ab.1.ncIn, ab.2.ncIn))).elim
            ((0, 0, []), (0, 0, [])) fun ab => (ab.1.ncIn, ab.2.ncIn))

open Classical in
/-- **With the table queries answered from a table it is `collider`.** -/
theorem answerG_colliderM (T : SigIn N X M → ZMod n) (x : (ZMod n)ˣ)
    (ν : Fin qs → (ZMod n)ˣ × (ZMod n)ˣ) (c : Coins) (s : ZMod n) :
    answerG T (colliderM C nonceCoef N qs A x ν c s) =
      .done (collider C nonceCoef N qs A ((x, ν, c, T), s)) := by
  unfold colliderM collider
  rw [answerG_bind, answerG_gameRecsM C nonceCoef N qs A T T (rdTable N) (fun z => rfl) x ν c T]
  dsimp only
  simp only [Alg.done_bind]
  cases forkPoint C N (x : ZMod n) (gameRecs C nonceCoef N qs A (x, ν, c, T) T).1
      (gameRecs C nonceCoef N qs A (x, ν, c, T) T).2.1 with
  | none => rfl
  | some z =>
    dsimp only
    rw [answerG_bind, answerG_gameRecsM C nonceCoef N qs A T (update T z s) (rdFork N z s)
      (answerG_rdFork N T z s) x ν c T]
    rfl

/-- **The collision finder makes at most `2⋅(qh + qs)` table queries.** -/
theorem nbound_colliderM (qh : ℕ) (hA : ∀ coins P, HashBound (A coins P) qh) (x : (ZMod n)ˣ)
    (ν : Fin qs → (ZMod n)ˣ × (ZMod n)ˣ) (c : Coins) (s : ZMod n) :
    NBound (colliderM C nonceCoef N qs A x ν c s) (2 * (qh + qs)) := by
  have h0 : ClosedOk qs (X := X) (M := M) ⟨0, [], []⟩ := ⟨List.nodup_nil, by simp, Nat.zero_le _⟩
  unfold colliderM gameRecsM
  have b1 := nbound_interp_log C nonceCoef N qs (oneRead_rdTable N) (x : ZMod n) (noncesOf qs ν)
    (A c (C.mulG (x : ZMod n))) qh (hA _ _) (⟨0, [], []⟩, []) h0
  refine (NBound.bind (b := qh + qs) b1 fun r₁ => ?_).mono (by simp; omega)
  cases forkPoint C N (x : ZMod n) r₁.1 r₁.2.1 with
  | none => trivial
  | some z =>
    dsimp only
    have b2 := nbound_interp_log C nonceCoef N qs (oneRead_rdFork N z s) (x : ZMod n)
      (noncesOf qs ν) (A c (C.mulG (x : ZMod n))) qh (hA _ _) (⟨0, [], []⟩, []) h0
    refine (NBound.bind (b := 0) b2 fun r₂ => ?_).mono (by simp)
    exact trivial

/-! ## The lazily sampling collision finder -/

/-- A handler for the AOMDL queries, which the collision finder never makes. -/
def noOmdl : (q : OmdlQ n) → Unit → OmdlR E q × Unit
  | .chal, u => (none, u)
  | .dlog _ _, u => ((0 : ZMod n), u)

/-- The sample of `colliderLazy`: the secret key, the nonces, the forger's
coins and `q` scalars for the answers of the oracle. -/
abbrev LazyColliderSample (n qs q : ℕ) (Coins : Type) :=
  (ZMod n)ˣ × (Fin qs → (ZMod n)ˣ × (ZMod n)ˣ) × Coins × (Fin q → ZMod n)

/-- **The collision finder with a lazily sampled random oracle.** It gets a
sample and the new value at the fork point. -/
noncomputable def colliderLazy (q : ℕ) (p : LazyColliderSample n qs q Coins × ZMod n) :
    (E × E × List (X × M × E)) × (E × E × List (X × M × E)) :=
  ((answerLazy (QTree.stream p.1.2.2.2) 0 []
    (colliderM C nonceCoef N qs A p.1.1 p.1.2.1 p.1.2.2.1 p.2)).run
      (noOmdl (n := n) (E := E)) ()).1

variable [Fintype Coins] [Fintype (SigIn N X M)]

/-- The probability that `colliderLazy A` outputs a collision of the nonce
coefficient hash. -/
noncomputable def collisionAdvantageLazy (q : ℕ) : ℝ :=
  prob fun p : LazyColliderSample n qs q Coins × ZMod n =>
    IsCollision nonceCoef (colliderLazy C nonceCoef N qs A q p)

/-- Samples of the collision finder with the table, or the answers, last. -/
def tableLastC (Tb : Type) :
    ((ZMod n)ˣ × (Fin qs → (ZMod n)ˣ × (ZMod n)ˣ) × Coins × ZMod n) × Tb ≃
      ((ZMod n)ˣ × (Fin qs → (ZMod n)ˣ × (ZMod n)ˣ) × Coins × Tb) × ZMod n where
  toFun p := ((p.1.1, p.1.2.1, p.1.2.2.1, p.2), p.1.2.2.2)
  invFun ω := ((ω.1.1, ω.1.2.1, ω.1.2.2.1, ω.2), ω.1.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

set_option synthInstance.maxSize 4000 in
/-- **The lazily sampling collision finder finds a collision as often as
`collider`.** -/
theorem collisionAdvantage_eq_lazy (qh : ℕ) (hA : ∀ coins P, HashBound (A coins P) qh) :
    collisionAdvantage C nonceCoef N qs A =
      collisionAdvantageLazy C nonceCoef N qs A (2 * (qh + qs)) := by
  unfold collisionAdvantage collisionAdvantageLazy
  rw [← prob_equiv (tableLastC (n := n) (Coins := Coins) qs (SigIn N X M → ZMod n))
      (fun p => IsCollision nonceCoef (collider C nonceCoef N qs A p)),
    ← prob_equiv (tableLastC (n := n) (Coins := Coins) qs (Fin (2 * (qh + qs)) → ZMod n))
      (fun p => IsCollision nonceCoef (colliderLazy C nonceCoef N qs A (2 * (qh + qs)) p))]
  refine prob_prod_congr _ _ fun a => ?_
  have key := prob_answerG_eq_lazy (noOmdl (n := n) (E := E)) ()
    (colliderM C nonceCoef N qs A a.1 a.2.1 a.2.2.1 a.2.2.2)
    (fun out => IsCollision nonceCoef out.1)
    (2 * (qh + qs)) (nbound_colliderM C nonceCoef N qs A qh hA a.1 a.2.1 a.2.2.1 a.2.2.2)
  refine Eq.trans ?_ (key.trans ?_)
  · congr 1
    funext T
    rw [answerG_colliderM]
    rfl
  · rfl

set_option synthInstance.maxSize 4000 in
/-- **BIP 459 is unforgeable under AOMDL, with a reduction and a collision
finder that sample the random oracle lazily.** The statement of
`unforgeable_sqrt` for `reductionLazy` and `colliderLazy`. -/
theorem unforgeable_sqrt_lazy_both (hN : N < n) (qh : ℕ)
    (hA : ∀ coins P, HashBound (A coins P) qh) :
    forgeAdvantage C nonceCoef N qs A ≤
      Real.sqrt ((qh + qs + 1 : ℕ) *
        (omdlAdvantage C (2 * qs + 1) (reductionLazy C nonceCoef N qs A (2 * (qh + qs) + 1)) +
          collisionAdvantageLazy C nonceCoef N qs A (2 * (qh + qs)))) +
        (qh + qs + 1 : ℕ) / n + qs / (n - 1 : ℝ) := by
  rw [← collisionAdvantage_eq_lazy C nonceCoef N qs A qh hA]
  exact unforgeable_sqrt_lazy C nonceCoef N qs A hN qh hA

end Dahlias.Security
