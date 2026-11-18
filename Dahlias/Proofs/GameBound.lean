import Dahlias.Proofs.Game

/-!
# The game algorithm makes at most `qh + qs + 1` different queries

`length_fresh_gameTree`: the adversary's `qh` hash queries, one query for each
closed session, and the query of the fork point.
-/

set_option linter.unusedSectionVars false

namespace Dahlias.Security

open Taproot QTree

variable {n : ℕ} [Fact n.Prime] {E X M : Type} [AddCommGroup E] [DecidableEq E] [DecidableEq X]
  [DecidableEq M] (C : Curve n E X) (nonceCoef : E → E → List (X × M × E) → ZMod n) (N qs : ℕ)
  (x : ZMod n) (nonces : Fin qs → SecNonce n)

/-- The closed sessions are distinct and below `qs`. -/
def ClosedOk (qs : ℕ) (st : SignerState X M) : Prop := st.closed.Nodup ∧ ∀ k ∈ st.closed, k < qs

theorem ClosedOk.length_le {st : SignerState X M} (h : ClosedOk qs st) : st.closed.length ≤ qs := by
  have hsub : st.closed ⊆ List.range qs := fun k hk => List.mem_range.mpr (h.2 k hk)
  simpa using (List.subperm_of_subset h.1 hsub).length_le

/-- The number of hash queries in one query of the adversary. -/
def hashCost {N : ℕ} : AdvQ n N E X M → ℕ
  | .hash _ => 1
  | _ => 0

theorem hashBound_ask {N : ℕ} {α : Type} {q : AdvQ n N E X M}
    {f : AdvR q → Alg (AdvQ n N E X M) AdvR α} {qh : ℕ} (h : HashBound (.ask q f) qh) :
    hashCost q ≤ qh ∧ ∀ r, HashBound (f r) (qh - hashCost q) := by
  cases q with
  | hash z => exact ⟨h.1, h.2⟩
  | openSession => exact ⟨Nat.zero_le _, h⟩
  | close k τ m agg pm pubnonces => exact ⟨Nat.zero_le _, h⟩

/-- One query of the adversary: the fresh queries and the closed sessions
together grow by at most one for a hash query and not at all otherwise. -/
theorem step_bound (T : SigIn N X M → ZMod n) (q : AdvQ n N E X M) (st : SignerState X M)
    (l : List (SigIn N X M)) (hst : ClosedOk qs st) :
    ClosedOk qs (eval T (treeChallenger C nonceCoef N qs x nonces q st)).2 ∧
      (flog T l (treeChallenger C nonceCoef N qs x nonces q st)).length +
          (qs - (eval T (treeChallenger C nonceCoef N qs x nonces q st)).2.closed.length) ≤
        l.length + (qs - st.closed.length) + hashCost q := by
  cases q with
  | hash z =>
    refine ⟨hst, ?_⟩
    simp only [treeChallenger, eval, hashCost]
    refine le_trans (Nat.add_le_add_right (length_flog_ask_done T l z _) _) ?_
    omega
  | openSession =>
    simp only [treeChallenger, challenger, eval, flog]
    split_ifs <;> exact ⟨hst, by simp⟩
  | close k τ m agg pm pubnonces =>
    unfold treeChallenger
    dsimp only
    split_ifs with h
    · generalize signPre C.ops (H₀ nonceCoef N) (nonces ⟨k, h.1⟩) (τ.sk x) m agg pm pubnonces = p
      cases p with
      | none => exact ⟨hst, by simp [eval, flog]⟩
      | some Rb =>
        have hst' : ClosedOk qs (X := X) (M := M)
            { st with closed := k :: st.closed
                      signed := (pm, C.x (C.mulG (τ.sk x)), m) :: st.signed } :=
          ⟨List.nodup_cons.mpr ⟨h.2.2.1, hst.1⟩, by
            intro j hj
            rcases List.mem_cons.mp hj with rfl | hj
            · exact h.1
            · exact hst.2 j hj⟩
        refine ⟨hst', ?_⟩
        have hlen := hst'.length_le
        simp only [eval, List.length_cons] at hlen ⊢
        refine le_trans (Nat.add_le_add_right (length_flog_ask_done T l _ _) _) ?_
        simp only [hashCost]
        omega
    · exact ⟨hst, by simp [eval, flog]⟩

/-- The fresh queries of the adversary with the honest signer. -/
theorem length_flog_interp (T : SigIn N X M → ZMod n) {α : Type}
    (t : Alg (AdvQ n N E X M) AdvR α) (qh : ℕ) (ht : HashBound t qh) (st : SignerState X M)
    (l : List (SigIn N X M)) (hst : ClosedOk qs st) :
    (flog T l (Alg.interp (treeChallenger C nonceCoef N qs x nonces) t st)).length ≤
      l.length + qh + (qs - st.closed.length) := by
  induction t generalizing st l qh with
  | done a =>
    change l.length ≤ _
    omega
  | ask q f ih =>
    rw [Alg.interp_ask, flog_bind]
    obtain ⟨hst', hstep⟩ := step_bound C nonceCoef N qs x nonces T q st l hst
    obtain ⟨hc, hf⟩ := hashBound_ask ht
    have := ih (eval T (treeChallenger C nonceCoef N qs x nonces q st)).1 (qh - hashCost q)
      (hf _) (eval T (treeChallenger C nonceCoef N qs x nonces q st)).2
      (flog T l (treeChallenger C nonceCoef N qs x nonces q st)) hst'
    omega

variable {Coins : Type} (A : Adversary n N E X M Coins) (coins : Coins)

/-- **The game algorithm makes at most `qh + qs + 1` different queries.** -/
theorem length_fresh_gameTree (T : SigIn N X M → ZMod n) (qh : ℕ)
    (hA : HashBound (A coins (C.mulG x)) qh) :
    (fresh T (gameTree C nonceCoef N qs x nonces A coins)).length ≤ qh + qs + 1 := by
  unfold gameTree
  rw [fresh_bind]
  have h := length_flog_interp C nonceCoef N qs x nonces T (A coins (C.mulG x)) qh hA
    ⟨0, [], []⟩ [] ⟨List.nodup_nil, by simp⟩
  simp only [List.length_nil, zero_add, Nat.sub_zero] at h
  split
  · rename_i z _
    have := length_flog_ask_done T
      (flog T [] (Alg.interp (treeChallenger C nonceCoef N qs x nonces) (A coins (C.mulG x))
        ⟨0, [], []⟩)) z fun _ => eval T (Alg.interp (treeChallenger C nonceCoef N qs x nonces)
          (A coins (C.mulG x)) ⟨0, [], []⟩)
    exact this.trans (by omega)
  · exact (le_of_eq rfl).trans (h.trans (by omega))

end Dahlias.Security
