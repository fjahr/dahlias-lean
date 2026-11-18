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
        (challenger C nonceCoef N qs x nonces T q st.1).1 ∧
      (logChallenger C nonceCoef N qs x nonces T q st).2.1 =
        (challenger C nonceCoef N qs x nonces T q st.1).2 := by
  cases q with
  | hash z => exact ⟨rfl, rfl⟩
  | openSession => exact ⟨rfl, rfl⟩
  | close k τ m agg pm pubnonces =>
    unfold logChallenger challenger
    dsimp only
    split_ifs with h
    · rw [sign_eq, signPre_congr C.ops (H := hashesOf N nonceCoef T) (H' := H₀ nonceCoef N) rfl]
      generalize signPre C.ops (H₀ nonceCoef N) (nonces ⟨k, h.1⟩) (τ.sk x) m agg pm pubnonces = p
      cases p with
      | none => exact ⟨rfl, rfl⟩
      | some Rb => simp [hashesOf, h.2.2.2.2]; rfl
    · exact ⟨rfl, rfl⟩

/-- **The signer with records behaves like the signer of the game.** -/
theorem run_logChallenger {α : Type} (t : Alg (AdvQ n N E X M) AdvR α)
    (st : SignerState X M × List (CloseRec n E X M)) :
    (t.run (logChallenger C nonceCoef N qs x nonces T) st).1 =
        (t.run (challenger C nonceCoef N qs x nonces T) st.1).1 ∧
      (t.run (logChallenger C nonceCoef N qs x nonces T) st).2.1 =
        (t.run (challenger C nonceCoef N qs x nonces T) st.1).2 := by
  have := Alg.run_rel (logChallenger C nonceCoef N qs x nonces T)
    (challenger C nonceCoef N qs x nonces T) (fun s s' => s.1 = s')
    (fun q s s' hs => by
      subst hs
      exact logChallenger_proj C nonceCoef N qs x nonces T q s) t st st.1 rfl
  exact this

/-- A record of a successful `Sign` of the honest signer on the table `T`. -/
def RecOk (r : CloseRec n E X M) : Prop :=
  ∃ (hk : r.k < qs) (hN : r.pm.length ≤ N), r.τ.2 ≠ 0 ∧
    signPre C.ops (H₀ nonceCoef N) (nonces ⟨r.k, hk⟩) (r.τ.sk x) r.m r.agg r.pm r.pubs =
      some r.Rb ∧
    r.c = T (⟨r.pm, hN⟩, C.x r.Rb.1, (C.x (C.mulG (r.τ.sk x)), r.m)) ∧
    r.s = signPost C.ops (nonces ⟨r.k, hk⟩) (r.τ.sk x) r.Rb r.c

/-- Every record is valid, its session is closed and its entry is signed. -/
def LogInv (st : SignerState X M × List (CloseRec n E X M)) : Prop :=
  ∀ r ∈ st.2, RecOk C nonceCoef N qs x nonces T r ∧ r.k ∈ st.1.closed ∧
    (r.pm, C.x (C.mulG (r.τ.sk x)), r.m) ∈ st.1.signed

theorem logInv_step (q : AdvQ n N E X M) (st : SignerState X M × List (CloseRec n E X M))
    (hst : LogInv C nonceCoef N qs x nonces T st) :
    LogInv C nonceCoef N qs x nonces T (logChallenger C nonceCoef N qs x nonces T q st).2 := by
  cases q with
  | hash z => exact hst
  | openSession =>
    intro r hr
    obtain ⟨h1, h2, h3⟩ := hst r hr
    refine ⟨h1, ?_, ?_⟩ <;>
    · simp only [logChallenger, challenger]
      split_ifs <;> assumption
  | close k τ m agg pm pubnonces =>
    unfold logChallenger
    dsimp only
    split_ifs with h
    · rcases hp : signPre C.ops (H₀ nonceCoef N) (nonces ⟨k, h.1⟩) (τ.sk x) m agg pm pubnonces
        with _ | Rb
      · exact hst
      · intro r hr
        rcases List.mem_cons.mp hr with rfl | hr
        · exact ⟨⟨h.1, h.2.2.2.2, h.2.2.2.1, hp, rfl, rfl⟩, by simp, by simp⟩
        · obtain ⟨h1, h2, h3⟩ := hst r hr
          exact ⟨h1, List.mem_cons_of_mem _ h2, List.mem_cons_of_mem _ h3⟩
    · exact hst

theorem run_logInv {α : Type} (t : Alg (AdvQ n N E X M) AdvR α)
    (st : SignerState X M × List (CloseRec n E X M))
    (hst : LogInv C nonceCoef N qs x nonces T st) :
    LogInv C nonceCoef N qs x nonces T
      (t.run (logChallenger C nonceCoef N qs x nonces T) st).2 :=
  Alg.run_inv _ _ (fun q s hs => logInv_step C nonceCoef N qs x nonces T q s hs) t st hst

end Dahlias.Security
