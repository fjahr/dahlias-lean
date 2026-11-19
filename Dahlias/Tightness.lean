import Dahlias.Unforgeability
import Dahlias.NonceProb

/-!
# The additive term of the bound is needed

`unforgeable_sqrt` bounds a forger's success probability by
`sqrt (q * (omdl + coll)) + q / n + qs / (n - 1)` with `q = qh + qs + 1`. This
file shows that a term of the order `q / n` has to be there.

`grinder` is a forger that never calls the signer and computes no discrete
logarithm. For each of `q` different messages `m` it asks the random oracle
for the challenge `c` of the one-entry list `[(pk, m)]` with `R = pk`. If
`c = -1` it outputs the signature `(pk, 0)` for that list, which is valid
because `0⋅G = P + (-1)⋅P`.

* `grinder_hashBound`: the grinder makes at most `q` random oracle queries.
* `grinder_advantage`: it wins with probability at least `1 - ((n - 1) / n)^q`.
* `grinder_advantage_ge`: that is at least `q / (n + q)`.

For `qs = 0` the bound of `unforgeable_sqrt` on this forger is
`sqrt (…) + (q + 1) / n`, so its additive term is tight up to the factor
`(1 + 1 / q) * (1 + q / n)`.
-/

set_option linter.unusedSectionVars false

namespace Dahlias

open Finset

/-! ## Two facts about probabilities -/

section Prob

variable {Ω : Type} [Fintype Ω]

open Classical in
theorem prob_not [Nonempty Ω] (p : Ω → Prop) : prob (fun ω => ¬p ω) = 1 - prob p := by
  have h : (0 : ℝ) < Fintype.card Ω := Nat.cast_pos.mpr Fintype.card_pos
  rw [prob_eq_sum, prob_eq_sum, eq_sub_iff_add_eq, ← add_div, ← Finset.sum_add_distrib,
    div_eq_one_iff_eq h.ne']
  refine (Finset.sum_congr rfl fun ω _ => (?_ : _ = (1 : ℝ))).trans (by simp)
  by_cases hp : p ω <;> simp [hp]

/-- The functions that avoid the value `t` on the set `A`. -/
theorem filter_forall_ne {D S : Type} [Fintype D] [DecidableEq D] [Fintype S] [DecidableEq S]
    (A : Finset D) (t : S) {inst : DecidablePred fun T : D → S => ∀ d ∈ A, T d ≠ t} :
    @Finset.filter _ (fun T : D → S => ∀ d ∈ A, T d ≠ t) inst Finset.univ =
      Fintype.piFinset fun d => if d ∈ A then Finset.univ.erase t else Finset.univ := by
  ext T
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
  refine ⟨fun h d => ?_, fun h d hd => ?_⟩
  · split_ifs with hd
    · exact Finset.mem_erase.mpr ⟨h d hd, Finset.mem_univ _⟩
    · exact Finset.mem_univ _
  · have hT := h d
    simp only [hd, ↓reduceIte] at hT
    exact (Finset.mem_erase.mp hT).1

/-- **Independent uniform values avoid a point.** A uniform function avoids
the value `t` on a set of `a` points with probability `((|S| - 1) / |S|)^a`. -/
theorem prob_forall_ne {D S : Type} [Fintype D] [DecidableEq D] [Fintype S] [DecidableEq S]
    [Nonempty S] (A : Finset D) (t : S) :
    prob (fun T : D → S => ∀ d ∈ A, T d ≠ t) =
      (((Fintype.card S : ℝ) - 1) / Fintype.card S) ^ A.card := by
  have hS : (0 : ℝ) < Fintype.card S := Nat.cast_pos.mpr Fintype.card_pos
  have hcard : ∀ d : D, (if d ∈ A then Finset.univ.erase t else Finset.univ : Finset S).card =
      if d ∈ A then Fintype.card S - 1 else Fintype.card S := fun d => by
    split_ifs
    · rw [Finset.card_erase_of_mem (Finset.mem_univ t), Finset.card_univ]
    · exact Finset.card_univ
  have hA : (Finset.univ.filter fun d : D => d ∈ A) = A := by
    ext d
    simp
  have hsplit := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset D))
    (fun d => d ∈ A)
  rw [hA, Finset.card_univ] at hsplit
  unfold prob
  rw [filter_forall_ne, Fintype.card_piFinset, Finset.prod_congr rfl fun d _ => hcard d,
    Finset.prod_ite, Finset.prod_const, Finset.prod_const, hA, Fintype.card_fun, ← hsplit,
    pow_add]
  push_cast [Nat.cast_pred Fintype.card_pos]
  rw [div_pow]
  field_simp

end Prob

namespace Security

open Taproot

variable {n : ℕ} [Fact n.Prime] {E X M : Type} [AddCommGroup E] [DecidableEq E] [DecidableEq X]
  [DecidableEq M] (C : Curve n E X) (nonceCoef : E → E → List (X × M × E) → ZMod n) (N qs : ℕ)

/-! ## The forger -/

/-- The grinder's random oracle query for the message `m`: the challenge of
the list `[(pk, m)]` with `R = pk`. -/
def grindIn (hN : 1 ≤ N) (pk : X) (m : M) : SigIn N X M :=
  (⟨[(pk, m)], by simpa using hN⟩, pk, (pk, m))

/-- The grinder's forgery for the message `m`: the signature `(pk, 0)` for the
list `[(pk, m)]` and the untweaked key. -/
def grindOut (pk : X) (m : M) : Forgery n X M := ⟨[(pk, m)], (0, 1), (pk, 0)⟩

/-- Ask for the challenges of the messages one by one and stop at the first
that is `-1`. -/
def grindAlg (hN : 1 ≤ N) (pk : X) : List M → Alg (AdvQ n N E X M) AdvR (Forgery n X M)
  | [] => .done ⟨[], (0, 1), (pk, 0)⟩
  | m :: ms => .ask (.hash (grindIn N hN pk m)) fun (c : ZMod n) =>
      if c = -1 then .done (grindOut pk m) else grindAlg hN pk ms

/-- A forger that needs no signature and no discrete logarithm. -/
def grinder (ms : List M) : Adversary n N E X M Unit := fun _ P =>
  if hN : 1 ≤ N then grindAlg N hN (C.x P) ms else .done ⟨[], (0, 1), (C.x P, 0)⟩

theorem hashBound_grindAlg (hN : 1 ≤ N) (pk : X) :
    ∀ ms : List M, HashBound (grindAlg (n := n) (E := E) N hN pk ms) ms.length
  | [] => trivial
  | m :: ms => by
    refine ⟨Nat.succ_pos _, fun (c : ZMod n) => ?_⟩
    change HashBound (if c = -1 then Alg.done (grindOut pk m) else grindAlg N hN pk ms) ms.length
    split_ifs
    · exact trivial
    · exact hashBound_grindAlg hN pk ms

/-- The grinder makes at most one random oracle query for every message. -/
theorem grinder_hashBound (ms : List M) (u : Unit) (P : E) :
    HashBound (grinder C N ms u P) ms.length := by
  by_cases hN : 1 ≤ N
  · simp only [grinder, hN, ↓reduceDIte]
    exact hashBound_grindAlg N hN _ ms
  · simp only [grinder, hN, ↓reduceDIte]
    trivial

/-! ## The forger wins if a challenge is `-1` -/

theorem run_grindAlg_cons (hN : 1 ≤ N) (pk : X) (x : ZMod n) (nonces : Fin qs → SecNonce n)
    (T : SigIn N X M → ZMod n) (st : SignerState X M) (m : M) (ms : List M) :
    (grindAlg N hN pk (m :: ms)).run (challenger C nonceCoef N qs x nonces T) st =
      if T (grindIn N hN pk m) = -1 then (grindOut pk m, st)
      else (grindAlg N hN pk ms).run (challenger C nonceCoef N qs x nonces T) st := by
  change (if T (grindIn N hN pk m) = -1 then Alg.done (grindOut pk m)
    else grindAlg N hN pk ms).run (challenger C nonceCoef N qs x nonces T) st = _
  split_ifs <;> rfl

theorem run_grindAlg (hN : 1 ≤ N) (pk : X) (x : ZMod n) (nonces : Fin qs → SecNonce n)
    (T : SigIn N X M → ZMod n) (st : SignerState X M) :
    ∀ ms : List M, (∃ m ∈ ms, T (grindIn N hN pk m) = -1) →
      ∃ m ∈ ms, T (grindIn N hN pk m) = -1 ∧
        (grindAlg N hN pk ms).run (challenger C nonceCoef N qs x nonces T) st =
          (grindOut pk m, st)
  | [], h => by simp at h
  | m :: ms, h => by
    by_cases hm : T (grindIn N hN pk m) = -1
    · exact ⟨m, List.mem_cons_self, hm, by simp only [run_grindAlg_cons, hm, ↓reduceIte]⟩
    · have h' : ∃ m' ∈ ms, T (grindIn N hN pk m') = -1 := by
        obtain ⟨m₀, h₀, hT₀⟩ := h
        rcases List.mem_cons.mp h₀ with rfl | h₀
        · exact absurd hT₀ hm
        · exact ⟨m₀, h₀, hT₀⟩
      obtain ⟨m', hm', hT, hrun⟩ := run_grindAlg hN pk x nonces T st ms h'
      exact ⟨m', List.mem_cons_of_mem _ hm', hT, by
        simp only [run_grindAlg_cons, hm, ↓reduceIte, hrun]⟩

/-- The signature `(pk, 0)` is valid for `[(pk, m)]` if the challenge is `-1`,
and nobody signed. -/
theorem wins_grindOut (hN : 1 ≤ N) {x : ZMod n} (hx : x ≠ 0) (T : SigIn N X M → ZMod n) (m : M)
    (hT : T (grindIn N hN (C.x (C.mulG x)) m) = -1) :
    Wins C nonceCoef N x T (grindOut (C.x (C.mulG x)) m) ⟨0, [], []⟩ := by
  have hsk : Tweak.sk ((0, 1) : Tweak n) x = x := by simp [Tweak.sk]
  have hL : ([(C.x (C.mulG x), m)] : List (X × M)).length ≤ N := by simpa using hN
  have hT' : T (⟨[(C.x (C.mulG x), m)], hL⟩, C.x (C.mulG x), (C.x (C.mulG x), m)) = -1 := hT
  refine ⟨one_ne_zero, by simpa [grindOut, hsk] using hx, hL,
    ⟨m, by simp [hsk, grindOut], by simp⟩, ?_⟩
  unfold verify
  simp only [grindOut, ops_liftX, ops_mulG, C.liftX_x_mulG hx, List.isEmpty_cons, Bool.not_false,
    List.all_cons, Option.isSome_some, List.all_nil, Bool.and_true, Bool.true_and,
    decide_eq_true_eq, keySum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero, Option.getD_some, ops_smul, C.val_smul_mulG, hashesOf, hL, ↓reduceDIte, hT']
  simp

/-- **The grinder wins when a challenge is `-1`.** -/
theorem grinder_wins (hN : 1 ≤ N) (ms : List M) (ω : ForgeSample n N qs X M Unit)
    (h : ∃ m ∈ ms, ω.2.2.2 (grindIn N hN (C.x (C.mulG (ω.1 : ZMod n))) m) = -1) :
    forgeExperiment C nonceCoef N qs (grinder C N ms) ω := by
  obtain ⟨x, ν, u, T⟩ := ω
  obtain ⟨m, -, hT, hrun⟩ := run_grindAlg C nonceCoef N qs hN (C.x (C.mulG (x : ZMod n)))
    (x : ZMod n) (fun k => ((ν k).1, (ν k).2)) T ⟨0, [], []⟩ ms h
  have hg : grinder C N ms u (C.mulG (x : ZMod n)) =
      grindAlg N hN (C.x (C.mulG (x : ZMod n))) ms := by
    simp only [grinder, hN, ↓reduceDIte]
  unfold forgeExperiment forgeExperimentG
  dsimp only
  rw [hg, hrun]
  exact wins_grindOut C nonceCoef N hN (Units.ne_zero x) T m hT

/-! ## The forger's success probability -/

variable [Fintype (SigIn N X M)]

set_option synthInstance.maxSize 2000 in
/-- **The additive term is needed.** With `q` different messages the grinder
makes at most `q` random oracle queries and no signing queries, and it forges
with probability at least `1 - ((n - 1) / n)^q`. -/
theorem grinder_advantage (hN : 1 ≤ N) (ms : List M) (hms : ms.Nodup) :
    1 - (((n : ℝ) - 1) / n) ^ ms.length ≤ forgeAdvantage C nonceCoef N qs (grinder C N ms) := by
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast (Fact.out : n.Prime).one_le
  have hc : 0 ≤ (((n : ℝ) - 1) / n) ^ ms.length :=
    pow_nonneg (div_nonneg (sub_nonneg.mpr hn) (Nat.cast_nonneg n)) _
  unfold forgeAdvantage forgeAdvantageG
  refine le_trans ?_ (prob_mono fun ω h => grinder_wins C nonceCoef N qs hN ms ω h)
  have hnot : (fun ω : ForgeSample n N qs X M Unit =>
      ∃ m ∈ ms, ω.2.2.2 (grindIn N hN (C.x (C.mulG (ω.1 : ZMod n))) m) = -1) =
      fun ω => ¬∀ m ∈ ms, ω.2.2.2 (grindIn N hN (C.x (C.mulG (ω.1 : ZMod n))) m) ≠ -1 := by
    funext ω
    simp
  rw [hnot, prob_not]
  refine sub_le_sub_left ?_ 1
  refine prob_prod_le' _ _ hc fun x => ?_
  refine prob_prod_le' _ _ hc fun ν => ?_
  refine prob_prod_le' _ _ hc fun u => ?_
  have hinj : Function.Injective (grindIn (M := M) N hN (C.x (C.mulG (x : ZMod n)))) :=
    fun m m' h => by simpa [grindIn] using h
  have hev : (fun T : SigIn N X M → ZMod n =>
      ∀ m ∈ ms, T (grindIn N hN (C.x (C.mulG (x : ZMod n))) m) ≠ -1) =
      fun T => ∀ d ∈ (ms.map (grindIn N hN (C.x (C.mulG (x : ZMod n))))).toFinset, T d ≠ -1 := by
    funext T
    simp
  change prob (fun T : SigIn N X M → ZMod n =>
    ∀ m ∈ ms, T (grindIn N hN (C.x (C.mulG (x : ZMod n))) m) ≠ -1) ≤ _
  rw [hev, prob_forall_ne, List.toFinset_card_of_nodup (hms.map hinj), List.length_map, ZMod.card]

/-- `1 - ((n - 1) / n)^q` is at least `q / (n + q)`. -/
theorem one_sub_pow_ge (q : ℕ) : (q : ℝ) / (n + q) ≤ 1 - (((n : ℝ) - 1) / n) ^ q := by
  have hn : (2 : ℝ) ≤ n := by exact_mod_cast (Fact.out : n.Prime).two_le
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hn0 : (0 : ℝ) < n := by linarith
  -- Bernoulli: `(n / (n - 1))^q ≥ 1 + q / (n - 1)`
  have hb : 1 + (q : ℝ) * (1 / ((n : ℝ) - 1)) ≤ (1 + 1 / ((n : ℝ) - 1)) ^ q :=
    one_add_mul_le_pow (by have : (0 : ℝ) ≤ 1 / ((n : ℝ) - 1) := by positivity
                           linarith) q
  have hinv : ((n : ℝ) - 1) / n = (1 + 1 / ((n : ℝ) - 1))⁻¹ := by
    field_simp
    ring
  have hpos : (0 : ℝ) < 1 + (q : ℝ) * (1 / ((n : ℝ) - 1)) := by positivity
  have hle : (((n : ℝ) - 1) / n) ^ q ≤ (1 + (q : ℝ) * (1 / ((n : ℝ) - 1)))⁻¹ := by
    rw [hinv, inv_pow]
    exact inv_anti₀ hpos hb
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hden : (0 : ℝ) < (n : ℝ) - 1 + q := by linarith
  have hfin : (q : ℝ) / (n + q) ≤ 1 - (1 + (q : ℝ) * (1 / ((n : ℝ) - 1)))⁻¹ := by
    have h1 : 1 + (q : ℝ) * (1 / ((n : ℝ) - 1)) = ((n : ℝ) - 1 + q) / ((n : ℝ) - 1) := by
      field_simp
    rw [h1, inv_div, one_sub_div hden.ne', add_sub_cancel_left]
    exact div_le_div_of_nonneg_left hq hden (by linarith)
  linarith

/-- **The additive term is needed**, in closed form: the grinder forges with
probability at least `q / (n + q)`. -/
theorem grinder_advantage_ge (hN : 1 ≤ N) (ms : List M) (hms : ms.Nodup) :
    (ms.length : ℝ) / (n + ms.length) ≤ forgeAdvantage C nonceCoef N qs (grinder C N ms) :=
  (one_sub_pow_ge ms.length).trans (grinder_advantage C nonceCoef N qs hN ms hms)

end Security

end Dahlias
