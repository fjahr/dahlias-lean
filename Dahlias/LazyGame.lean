import Dahlias.Lazy
import Dahlias.Proofs.GameBound

/-!
# The unforgeability game with a lazily sampled random oracle

`forgeAdvantage` is defined with a random oracle whose whole table is part of
the sample. `forgeAdvantage_eq_lazy` restates it without the table: the
adversary, the honest signer and the verifier run as one algorithm, and every
new query of `hash_BIP0459/sig` gets the next of `qh + qs + N` independent
uniform scalars.
-/

set_option linter.unusedSectionVars false

namespace Dahlias.Security

open Taproot QTree

variable {n : ℕ} [Fact n.Prime] {E X M : Type} [AddCommGroup E] [DecidableEq E] [DecidableEq X]
  [DecidableEq M]

/-- `Verify` with the challenges given as a list. -/
def verifyWith (O : Ops n E X) (pm : List (X × M)) (sig : X × ZMod n) (cs : List (ZMod n)) :
    Bool :=
  match O.liftX sig.1 with
  | none => false
  | some R =>
    !pm.isEmpty && pm.all (fun pkm => (O.liftX pkm.1).isSome) &&
      decide (O.mulG sig.2 =
        R + ((pm.zip cs).map fun p => O.smul p.2 ((O.liftX p.1.1).getD 0)).sum)

theorem zip_map_self {α β γ : Type} (l : List α) (g : α → β) (F : α × β → γ) :
    (l.zip (l.map g)).map F = l.map fun a => F (a, g a) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

variable (C : Curve n E X) (nonceCoef : E → E → List (X × M × E) → ZMod n) (N qs : ℕ)
  (x : ZMod n) (nonces : Fin qs → SecNonce n)

theorem verifyWith_eq (T : SigIn N X M → ZMod n) (pm : List (X × M)) (h : pm.length ≤ N)
    (sig : X × ZMod n) :
    verifyWith C.ops pm sig (pm.map fun e => T (⟨pm, h⟩, sig.1, e)) =
      verify C.ops (hashesOf N nonceCoef T) pm sig := by
  unfold verifyWith verify keySum
  rw [zip_map_self]
  simp only [hashesOf, h, ↓reduceDIte]
  rfl

variable {Coins : Type} (A : Adversary n N E X M Coins) (coins : Coins)

open Classical in
/-- **The whole game as one algorithm**: the adversary with the honest signer,
then the verifier. The output says whether the adversary wins. -/
noncomputable def winTree : QTree (SigIn N X M) (ZMod n) Bool :=
  Alg.interp (treeChallenger C nonceCoef N qs x nonces) (A coins (C.mulG x)) ⟨0, [], []⟩ >>=
    fun out =>
      if h : out.1.L.length ≤ N then
        askAll (out.1.L.map fun e => ((⟨out.1.L, h⟩ : BList N X M), out.1.sig.1, e)) >>= fun cs =>
          .done (decide (out.1.τ.2 ≠ 0 ∧ out.1.τ.sk x ≠ 0 ∧
              ∃ m, (C.x (C.mulG (out.1.τ.sk x)), m) ∈ out.1.L ∧
                (out.1.L, C.x (C.mulG (out.1.τ.sk x)), m) ∉ out.2.signed) &&
            verifyWith C.ops out.1.L out.1.sig cs)
      else .done false

open Classical in
theorem eval_winTree (T : SigIn N X M → ZMod n) :
    eval T (winTree C nonceCoef N qs x nonces A coins) = true ↔
      Wins C nonceCoef N x T
        ((A coins (C.mulG x)).run (challenger C nonceCoef N qs x nonces T) ⟨0, [], []⟩).1
        ((A coins (C.mulG x)).run (challenger C nonceCoef N qs x nonces T) ⟨0, [], []⟩).2 := by
  unfold winTree
  rw [eval_bind, eval_interp]
  set out := (A coins (C.mulG x)).run (challenger C nonceCoef N qs x nonces T) ⟨0, [], []⟩
  by_cases h : out.1.L.length ≤ N
  · rw [dite_eq_left_of_eq_true (eq_true h), eval_bind, eval_askAll, List.map_map]
    change (decide _ && verifyWith C.ops out.1.L out.1.sig
      (out.1.L.map fun e => T (⟨out.1.L, h⟩, out.1.sig.1, e))) = true ↔ _
    rw [verifyWith_eq C nonceCoef N T out.1.L h, Bool.and_eq_true, decide_eq_true_eq]
    unfold Wins
    tauto
  · rw [dite_eq_right_of_eq_false (eq_false h)]
    unfold Wins
    change false = true ↔ _
    simp only [Bool.false_eq_true, false_iff]
    tauto

/-- **The game makes at most `qh + qs + N` different queries.** -/
theorem length_fresh_winTree (T : SigIn N X M → ZMod n) (qh : ℕ)
    (hA : HashBound (A coins (C.mulG x)) qh) :
    (fresh T (winTree C nonceCoef N qs x nonces A coins)).length ≤ qh + qs + N := by
  unfold winTree
  rw [fresh_bind]
  have h := length_flog_interp C nonceCoef N qs x nonces T (A coins (C.mulG x)) qh hA
    ⟨0, [], []⟩ [] ⟨List.nodup_nil, by simp⟩
  simp only [List.length_nil, zero_add, Nat.sub_zero] at h
  split_ifs with hL
  · rw [flog_bind]
    change (flog T _ (askAll _)).length ≤ _
    refine (length_flog_askAll T _ _).trans ?_
    rw [List.length_map]
    exact Nat.add_le_add h hL
  · exact (le_of_eq rfl).trans (h.trans (by omega))

variable [Fintype Coins] [Fintype (SigIn N X M)]

/-- The sample of the game with a lazily sampled random oracle: the secret
key, the nonces, the adversary's coins and `q` answers. -/
abbrev LazySample (n qs q : ℕ) (Coins : Type) :=
  (ZMod n)ˣ × (Fin qs → (ZMod n)ˣ × (ZMod n)ˣ) × Coins × (Fin q → ZMod n)

/-- The game with a lazily sampled random oracle, on one sample. -/
def lazyExperiment (q : ℕ) (ω : LazySample n qs q Coins) : Prop :=
  evalLazy (stream ω.2.2.2) 0 []
    (winTree C nonceCoef N qs (ω.1 : ZMod n) (fun k => ((ω.2.1 k).1, (ω.2.1 k).2)) A ω.2.2.1) =
      true

/-- **The game with a lazily sampled random oracle has the same advantage.** -/
theorem forgeAdvantage_eq_lazy (qh : ℕ) (hA : ∀ coins P, HashBound (A coins P) qh) :
    forgeAdvantage C nonceCoef N qs A = prob (lazyExperiment C nonceCoef N qs A (qh + qs + N)) := by
  unfold forgeAdvantage
  refine prob_prod_congr _ _ fun u => prob_prod_congr _ _ fun ν => prob_prod_congr _ _ fun c => ?_
  have h := prob_eval_eq_lazy (fun b : Bool => b = true) (qh + qs + N)
    (winTree C nonceCoef N qs (u : ZMod n) (fun k => ((ν k).1, (ν k).2)) A c)
    fun T => length_fresh_winTree C nonceCoef N qs _ _ A c T qh (hA c _)
  refine Eq.trans ?_ h
  congr 1
  funext T
  exact propext (eval_winTree C nonceCoef N qs _ _ A c T).symm

end Dahlias.Security
