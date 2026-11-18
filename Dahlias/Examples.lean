import Dahlias.Unforgeability

/-!
# The unforgeability game can be won

A sanity check of the definitions in `Dahlias.Security`: the game is not
unwinnable for a trivial reason. `guesser` guesses the secret key and a nonce
with its coins, makes one random oracle query and outputs the single-signer
signature for the guessed key. It wins whenever the guess is right
(`guesser_wins`), so its advantage is positive (`guesser_advantage_pos`), and
it satisfies the hypothesis of the unforgeability theorem with `qh = 1`
(`guesser_hashBound`).
-/

set_option linter.unusedSectionVars false

namespace Dahlias.Security

open Taproot

variable {n : ℕ} [Fact n.Prime] {E X M : Type} [AddCommGroup E] [DecidableEq E] [DecidableEq X]
  [DecidableEq M] (C : Curve n E X) (nonceCoef : E → E → List (X × M × E) → ZMod n) (N qs : ℕ)

/-- A forger that guesses the secret key. -/
def guesser (m₀ : M) : Adversary n N E X M ((ZMod n)ˣ × (ZMod n)ˣ) := fun ρ P =>
  if h : 1 ≤ N then
    .ask (.hash (⟨[(C.x P, m₀)], by simpa using h⟩, C.x (C.mulG (ρ.2 : ZMod n)), (C.x P, m₀)))
      fun (c : ZMod n) =>
        .done ⟨[(C.x P, m₀)], (0, 1), (C.x (C.mulG (ρ.2 : ZMod n)),
          (if C.hasEvenY (C.mulG (ρ.2 : ZMod n)) then (ρ.2 : ZMod n) else -(ρ.2 : ZMod n)) +
            c * C.evenScalar (ρ.1 : ZMod n))⟩
  else .done ⟨[], (0, 1), (C.x P, 0)⟩

theorem guesser_hashBound (m₀ : M) (ρ : (ZMod n)ˣ × (ZMod n)ˣ) (P : E) :
    HashBound (guesser C N m₀ ρ P) 1 := by
  by_cases h : 1 ≤ N
  · simp only [guesser, h, ↓reduceDIte]
    exact ⟨Nat.one_pos, fun _ => trivial⟩
  · simp only [guesser, h, ↓reduceDIte]
    trivial

/-- **The guesser wins when it guesses the secret key.** -/
theorem guesser_wins (hN : 1 ≤ N) (m₀ : M) (x r : (ZMod n)ˣ)
    (ν : Fin qs → (ZMod n)ˣ × (ZMod n)ˣ) (T : SigIn N X M → ZMod n) :
    forgeExperiment C nonceCoef N qs (guesser C N m₀) (x, ν, (x, r), T) := by
  have hx : (x : ZMod n) ≠ 0 := Units.ne_zero x
  have hr : (r : ZMod n) ≠ 0 := Units.ne_zero r
  have hsk : Tweak.sk ((0, 1) : Tweak n) (x : ZMod n) = x := by simp [Tweak.sk]
  have hL : ([(C.x (C.mulG (x : ZMod n)), m₀)] : List (X × M)).length ≤ N := by simpa using hN
  have hrun : (guesser C N m₀ (x, r) (C.mulG (x : ZMod n))).run
      (challenger C nonceCoef N qs (x : ZMod n) (fun k => ((ν k).1, (ν k).2)) T) ⟨0, [], []⟩ =
      (⟨[(C.x (C.mulG (x : ZMod n)), m₀)], (0, 1), (C.x (C.mulG (r : ZMod n)),
        (if C.hasEvenY (C.mulG (r : ZMod n)) then (r : ZMod n) else -(r : ZMod n)) +
          T (⟨[(C.x (C.mulG (x : ZMod n)), m₀)], hL⟩, C.x (C.mulG (r : ZMod n)),
            (C.x (C.mulG (x : ZMod n)), m₀)) * C.evenScalar (x : ZMod n))⟩, ⟨0, [], []⟩) := by
    simp only [guesser, hN, ↓reduceDIte]
    rfl
  unfold forgeExperiment
  dsimp only
  rw [hrun]
  refine ⟨one_ne_zero, by rw [hsk]; exact hx, hL, ⟨m₀, by simp [hsk], by simp⟩, ?_⟩
  unfold verify
  simp only [ops_liftX, ops_mulG, liftX_x_signOf C (C.mulG_ne_zero hr),
    C.liftX_x_mulG hx, List.isEmpty_cons, Bool.not_false, List.all_cons, Option.isSome_some,
    List.all_nil, Bool.and_true, Bool.true_and, decide_eq_true_eq, keySum, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, add_zero, Option.getD_some, ops_smul,
    C.val_smul_mulG, map_add, Ops.signOf, ops_hasEvenY, hashesOf, hL, ↓reduceDIte]
  by_cases he : C.hasEvenY (C.mulG (r : ZMod n)) = true <;> simp [he]

variable [Fintype (SigIn N X M)]

set_option synthInstance.maxSize 2000 in
/-- **The guesser's advantage is positive.** -/
theorem guesser_advantage_pos (hN : 1 ≤ N) (m₀ : M) :
    0 < forgeAdvantage C nonceCoef N qs (guesser C N m₀) := by
  unfold forgeAdvantage
  apply prob_pos
  exact ⟨(1, fun _ => (1, 1), (1, 1), fun _ => 0), guesser_wins C nonceCoef N qs hN m₀ 1 1 _ _⟩

end Dahlias.Security
