import Dahlias.Proofs.Reduction

/-!
# The records of the honest signer

`run_logChallenger`: the signer with records behaves like the signer of the
game. `run_logInv`: every record is a successful `Sign` of the honest signer
(`RecOk`), its session is closed and its entry is recorded as signed.
-/

set_option linter.unusedSectionVars false

namespace Dahlias.Security

open Taproot QTree Function

variable {n : ℕ} [Fact n.Prime] {E X M : Type} [AddCommGroup E] [DecidableEq E] [DecidableEq X]
  [DecidableEq M] (C : Curve n E X) (nonceCoef : E → E → List (X × M × E) → ZMod n) (N qs : ℕ)
  (x : ZMod n) (nonces : Fin qs → SecNonce n) (T : SigIn N X M → ZMod n)

theorem logChallenger_proj (q : AdvQ n N E X M)
    (st : SignerState X M × List (CloseRec n E X M)) :
    (logChallenger C nonceCoef N qs x nonces T q st).1 =
        (challengerG true C nonceCoef N qs x nonces T q st.1).1 ∧
      (logChallenger C nonceCoef N qs x nonces T q st).2.1 =
        (challengerG true C nonceCoef N qs x nonces T q st.1).2 := by
  cases q with
  | hash z => exact ⟨rfl, rfl⟩
  | openSession => exact ⟨rfl, rfl⟩
  | close k τ m agg pm pubnonces =>
    unfold logChallenger challengerG
    dsimp only
    split_ifs with h
    · rw [sign_eq, signPre_congr C.ops (H := hashesOf N nonceCoef T) (H' := H₀ nonceCoef N) rfl]
      generalize signPre C.ops (H₀ nonceCoef N) (nonces ⟨k, h.1⟩) (τ.sk x) m agg pm pubnonces = p
      cases p with
      | none => exact ⟨rfl, rfl⟩
      | some Rb => simp [hashesOf, h.2.2.2.2]; rfl
    · exact ⟨rfl, rfl⟩
  | single items =>
    unfold logChallenger challengerG
    dsimp only
    split_ifs <;> exact ⟨rfl, rfl⟩

/-- **The signer with records behaves like the signer of the game.** -/
theorem run_logChallenger {α : Type} (t : Alg (AdvQ n N E X M) AdvR α)
    (st : SignerState X M × List (CloseRec n E X M)) :
    (t.run (logChallenger C nonceCoef N qs x nonces T) st).1 =
        (t.run (challengerG true C nonceCoef N qs x nonces T) st.1).1 ∧
      (t.run (logChallenger C nonceCoef N qs x nonces T) st).2.1 =
        (t.run (challengerG true C nonceCoef N qs x nonces T) st.1).2 := by
  have := Alg.run_rel (logChallenger C nonceCoef N qs x nonces T)
    (challengerG true C nonceCoef N qs x nonces T) (fun s s' => s.1 = s')
    (fun q s s' hs => by
      subst hs
      exact logChallenger_proj C nonceCoef N qs x nonces T q s) t st st.1 rfl
  exact this

/-! ## What the checks of `Sign` determine -/

theorem getSessionValues_some {H : Hashes n E X M} {agg : PubNonce E} {pm : List (X × M)}
    {pubs : List (PubNonce E)} {Rb : E × ZMod n}
    (h : getSessionValues C.ops H agg pm pubs = some Rb) :
    pm.length = pubs.length ∧ Rb.2 = H.nonceCoef agg.1 agg.2 (coefItems pm pubs) ∧
      Rb.1 = agg.1 + Rb.2.val • agg.2 ∧ agg.1 ≠ 0 := by
  unfold getSessionValues at h
  dsimp only at h
  split_ifs at h with h1 h2
  push Not at h1
  cases Option.some.inj h
  exact ⟨h1.2.1, rfl, rfl, h1.2.2.1⟩

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

omit [Fact n.Prime] [DecidableEq E] [DecidableEq X] [DecidableEq M] in
theorem coefItems_zero (L : List (X × M)) :
    coefItems L (L.map fun _ => ((0, 0) : PubNonce E)) = L.map fun e => (e.1, e.2, 0) := by
  induction L with
  | nil => rfl
  | cons a L ih => simp only [coefItems, List.map_cons, List.zipWith_cons_cons] at ih ⊢; rw [ih]

omit [Fact n.Prime] [AddCommGroup E] [DecidableEq E] [DecidableEq X] [DecidableEq M] in
theorem singleTerms_map (items : List (Tweak n × M)) (h : Tweak n × M → ZMod n) :
    singleTerms items (items.map h) = items.map fun i => (i.1, i.2, h i) := by
  induction items with
  | nil => rfl
  | cons a l ih => simp only [singleTerms, List.map_cons, List.zipWith_cons_cons] at ih ⊢; rw [ih]

omit [DecidableEq E] [DecidableEq X] [DecidableEq M] in
theorem singleS_eq (items : List (Tweak n × M)) (r : ZMod n) (h : Tweak n × M → ZMod n) :
    singleS C x items r (items.map h) =
      (if C.hasEvenY (C.mulG r) then r else -r) +
        keySk C x (singleTerms items (items.map h)) := by
  rw [singleTerms_map]
  unfold singleS keySk
  congr 1
  induction items with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, List.zipWith_cons_cons, List.sum_cons, ih]

/-! ## Valid records -/

/-- A record of a signature of the honest signer on the table `T`: the
coefficient `b` is the nonce coefficient hash of the record's input, the
scalar is the signer's, the challenges are the table's, and the record is
either a `Sign` of a session or a single-party signature. -/
def RecOk (r : CloseRec n E X M) : Prop :=
  ∃ (hk : r.k < qs) (hN : r.pm.length ≤ N),
    r.pm.length = r.pubs.length ∧
    r.Rb.2 = ncHash nonceCoef r.ncIn ∧
    r.s = sigOf C (nonces ⟨r.k, hk⟩) r.Rb (keySk C x r.keys) ∧
    (∀ κ ∈ r.keys, κ.1.sk x ≠ 0 ∧
      κ.2.2 = T (⟨r.pm, hN⟩, C.x r.Rb.1, (C.x (C.mulG (κ.1.sk x)), κ.2.1))) ∧
    ((∃ τ m c, r.keys = [(τ, m, c)] ∧
        signPre C.ops (H₀ nonceCoef N) (nonces ⟨r.k, hk⟩) (τ.sk x) m r.agg r.pm r.pubs =
          some r.Rb) ∨
      (r.agg = (0, 0) ∧
        r.keys.map (fun κ => (C.x (C.mulG (κ.1.sk x)), κ.2.1)) = r.pm ∧
        r.Rb.1 = C.mulG ((nonces ⟨r.k, hk⟩).1 + r.Rb.2 * (nonces ⟨r.k, hk⟩).2)))

/-- The closed slots were opened, every record is valid, its slot is closed
and its entries are signed. -/
def LogInv (st : SignerState X M × List (CloseRec n E X M)) : Prop :=
  (∀ k ∈ st.1.closed, k < st.1.opened) ∧
    ∀ r ∈ st.2, RecOk C nonceCoef N qs x nonces T r ∧ r.k ∈ st.1.closed ∧
      ∀ κ ∈ r.keys, (r.pm, C.x (C.mulG (κ.1.sk x)), κ.2.1) ∈ st.1.signed

theorem logInv_step (q : AdvQ n N E X M) (st : SignerState X M × List (CloseRec n E X M))
    (hst : LogInv C nonceCoef N qs x nonces T st) :
    LogInv C nonceCoef N qs x nonces T (logChallenger C nonceCoef N qs x nonces T q st).2 := by
  obtain ⟨hcl, hrec⟩ := hst
  cases q with
  | hash z => exact ⟨hcl, hrec⟩
  | openSession =>
    simp only [logChallenger, challengerG]
    split_ifs
    · exact ⟨fun k hk => Nat.lt_succ_of_lt (hcl k hk), hrec⟩
    · exact ⟨hcl, hrec⟩
  | close k τ m agg pm pubnonces =>
    unfold logChallenger
    dsimp only
    split_ifs with h
    · rcases hp : signPre C.ops (H₀ nonceCoef N) (nonces ⟨k, h.1⟩) (τ.sk x) m agg pm pubnonces
        with _ | Rb
      · exact ⟨hcl, hrec⟩
      · refine ⟨fun j hj => ?_, fun r hr => ?_⟩
        · rcases List.mem_cons.mp hj with rfl | hj
          · exact h.2.1
          · exact hcl j hj
        rcases List.mem_cons.mp hr with rfl | hr
        · obtain ⟨hd, j, -, -, hsv⟩ := signPre_some C hp
          refine ⟨⟨h.1, h.2.2.2.2, (getSessionValues_some C hsv).1,
            (getSessionValues_some C hsv).2.1, ?_, ?_,
            Or.inl ⟨τ, m, _, rfl, hp⟩⟩, by simp, ?_⟩
          · simp only [signPost, sigOf, keySk, List.map_cons, List.map_nil, List.sum_cons,
              List.sum_nil, add_zero]
            rfl
          · intro κ hκ
            rw [List.mem_singleton] at hκ
            subst hκ
            exact ⟨hd, rfl⟩
          · intro κ hκ
            rw [List.mem_singleton] at hκ
            subst hκ
            simp
        · obtain ⟨h1, h2, h3⟩ := hrec r hr
          exact ⟨h1, List.mem_cons_of_mem _ h2, fun κ hκ => List.mem_cons_of_mem _ (h3 κ hκ)⟩
    · exact ⟨hcl, hrec⟩
  | single items =>
    unfold logChallenger
    dsimp only
    have hcl' : ∀ j ∈ st.1.opened :: st.1.closed, j < st.1.opened + 1 := by
      intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact Nat.lt_succ_self _
      · exact Nat.lt_succ_of_lt (hcl j hj)
    split_ifs with h hc
    · refine ⟨hcl', fun r hr => ?_⟩
      rcases List.mem_cons.mp hr with rfl | hr
      · have hcs : ((singleKeys C x items).map fun e =>
            T (⟨singleKeys C x items, hc.2.1⟩,
              C.x (C.mulG (singleNonce true nonceCoef (singleKeys C x items)
                (nonces ⟨st.1.opened, h⟩))), e)) =
            items.map fun i => T (⟨singleKeys C x items, hc.2.1⟩,
              C.x (C.mulG (singleNonce true nonceCoef (singleKeys C x items)
                (nonces ⟨st.1.opened, h⟩))), (C.x (C.mulG (i.1.sk x)), i.2)) := by
          simp only [singleKeys, List.map_map]
          rfl
        dsimp only
        rw [hcs]
        have hlen : ((singleKeys C x items).map fun _ => ((0, 0) : PubNonce E)).length =
            (singleKeys C x items).length := List.length_map _
        refine ⟨⟨h, hc.2.1, hlen.symm, ?_, ?_, ?_, Or.inr ⟨rfl, ?_, rfl⟩⟩, by simp, ?_⟩
        · simp only [CloseRec.ncIn, coefItems_zero]
          rfl
        · rw [singleS_eq]
          rfl
        · intro κ hκ
          rw [singleTerms_map] at hκ
          obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hκ
          exact ⟨(hc.2.2.2 i hi).2, rfl⟩
        · rw [singleTerms_map, List.map_map]
          rfl
        · intro κ hκ
          rw [singleTerms_map] at hκ
          obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hκ
          refine List.mem_append_left _ (List.mem_map.mpr ⟨(C.x (C.mulG (i.1.sk x)), i.2), ?_, rfl⟩)
          exact List.mem_map.mpr ⟨i, hi, rfl⟩
      · obtain ⟨h1, h2, h3⟩ := hrec r hr
        exact ⟨h1, List.mem_cons_of_mem _ h2, fun κ hκ => List.mem_append_right _ (h3 κ hκ)⟩
    · exact ⟨hcl', fun r hr => by
        obtain ⟨h1, h2, h3⟩ := hrec r hr
        exact ⟨h1, List.mem_cons_of_mem _ h2, h3⟩⟩
    · exact ⟨hcl, hrec⟩

theorem run_logInv {α : Type} (t : Alg (AdvQ n N E X M) AdvR α)
    (st : SignerState X M × List (CloseRec n E X M))
    (hst : LogInv C nonceCoef N qs x nonces T st) :
    LogInv C nonceCoef N qs x nonces T
      (t.run (logChallenger C nonceCoef N qs x nonces T) st).2 :=
  Alg.run_inv _ _ (fun q s hs => logInv_step C nonceCoef N qs x nonces T q s hs) t st hst

end Dahlias.Security
