import Dahlias.Single
import Dahlias.Derived

/-!
# The game's single-party signature is `signSingle`

`challenger_single`: the answer of the unforgeability game to a single-party
signing query is the output of `Dahlias.signSingle` for the tweaked secret
keys, with the first nonce of the next free slot. So `unforgeable_sqrt` is a
statement about that algorithm.
-/

set_option linter.unusedSectionVars false
set_option linter.deprecated false

namespace Dahlias.Security

open Taproot

variable {n : ℕ} [Fact n.Prime] {E X M : Type} [AddCommGroup E] [DecidableEq E] [DecidableEq X]
  [DecidableEq M] (C : Curve n E X) (nonceCoef : E → E → List (X × M × E) → ZMod n) (N qs : ℕ)
  (x : ZMod n) (nonces : Fin qs → SecNonce n) (T : SigIn N X M → ZMod n)

theorem sum_zipWith_map_self {α β γ : Type} [AddCommMonoid γ] (l : List α) (h : α → β)
    (g : β → α → γ) : (List.zipWith g (l.map h) l).sum = (l.map fun a => g (h a) a).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, List.zipWith_cons_cons, List.sum_cons, ih]

/-- **The game answers a single-party signing query with `signSingle`**, when
a slot is left, the list has at most `N` entries and the tweaks are valid. -/
theorem challenger_single (items : List (Tweak n × M)) (st : SignerState X M)
    (h : st.opened < qs) (hN : items.length ≤ N) (hτ : ∀ i ∈ items, i.1.2 ≠ 0) :
    (challenger C nonceCoef N qs x nonces T (.single items) st).1 =
      signSingle C.ops (hashesOf N nonceCoef T) (nonces ⟨st.opened, h⟩).1
        (items.map fun i => (i.1.sk x, i.2)) := by
  have hL : singleList C.ops (items.map fun i => (i.1.sk x, i.2)) = singleKeys C x items := by
    simp [singleList, singleKeys]
  have hlen : (singleKeys C x items).length ≤ N := by simpa [singleKeys] using hN
  rw [challenger, challengerG_single false C nonceCoef N qs x T nonces items st h]
  change (singleStep C N x T items st (nonces ⟨st.opened, h⟩).1).1 = _
  unfold singleStep signSingle
  by_cases hc : items ≠ [] ∧ (singleKeys C x items).length ≤ N ∧ (nonces ⟨st.opened, h⟩).1 ≠ 0 ∧
      ∀ i ∈ items, i.1.2 ≠ 0 ∧ i.1.sk x ≠ 0
  · have hno : ¬((nonces ⟨st.opened, h⟩).1 = 0 ∨ (items.map fun i => (i.1.sk x, i.2)) = [] ∨
        ∃ σ ∈ items.map fun i => (i.1.sk x, i.2), σ.1 = 0) := by
      rintro (h0 | h0 | ⟨σ, hσ, h0⟩)
      · exact hc.2.2.1 h0
      · exact hc.1 (by simpa using h0)
      · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hσ
        exact (hc.2.2.2 i hi).2 h0
    rw [dif_pos hc, if_neg hno, hL]
    refine congrArg some (Prod.ext rfl ?_)
    unfold singleS
    simp only [singleKeys, List.map_map, sum_zipWith_map_self, hashesOf, ops_hasEvenY, ops_mulG,
      ops_x, ops_evenScalar]
    congr 2
    refine List.map_congr_left fun i _ => ?_
    simp only [Function.comp_apply]
    rw [dif_pos (by simpa [singleKeys] using hlen)]
  · have hyes : (nonces ⟨st.opened, h⟩).1 = 0 ∨ (items.map fun i => (i.1.sk x, i.2)) = [] ∨
        ∃ σ ∈ items.map fun i => (i.1.sk x, i.2), σ.1 = 0 := by
      by_contra hno
      push Not at hno
      refine hc ⟨fun h0 => hno.2.1 (by simp [h0]), hlen, hno.1, fun i hi => ⟨hτ i hi, ?_⟩⟩
      exact hno.2.2 (i.1.sk x, i.2) (List.mem_map.mpr ⟨i, hi, rfl⟩)
    rw [dif_neg hc, if_pos hyes]

end Dahlias.Security
