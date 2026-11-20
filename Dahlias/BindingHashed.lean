import Dahlias.Binding
import Dahlias.Hashed

/-!
# Strong binding with the challenge hash reduced modulo `n`

`strongly_binding` models `hash_BIP0459/sig` as a random oracle with scalar
answers. BIP 459 reduces a 256-bit hash output modulo `n`. In the game of this
file (`bindExperimentH`) the oracle returns a uniform element of a type `H` of
hash outputs. The adversary sees the outputs, and `Verify` turns them into
scalars with `red`. This is the step that `Dahlias.Hashed` makes for
unforgeability.

* `prob_eval_le_mapTree`: a query algorithm with at most `q` different
  queries tells an oracle with uniform outputs in `H` from one with outputs
  `g(c)` for uniform `c` with probability at most `q ⋅ (|H| - |S|) / |H|`.
* `bindAdvantageH_le`: so the game with hash outputs is won at most
  `(qh + 2⋅N) ⋅ (|H| - n) / |H|` more often than the game with scalar
  answers, against the adversary that reduces what it reads.
* `strongly_binding_hashed`, `strongly_binding_fin`: the bound of
  `strongly_binding` plus that term. For `H = {0, …, 2^256 - 1}` and
  `red h = h mod n` the term is at most `(qh + 2⋅N) / 2^127`
  (`Dahlias.Security.hash_gap`).
-/

set_option linter.unusedSectionVars false

namespace Dahlias

open QTree Function

/-- **An oracle with outputs in a larger set.** If `g` embeds `S` into `H`, a
query algorithm with at most `q` different queries accepts a uniform table of
outputs in `H` at most `q ⋅ (|H| - |S|) / |H|` more often than a table of
outputs `g(c)` for uniform `c` in `S`. -/
theorem prob_eval_le_mapTree {D S H : Type} [Fintype D] [DecidableEq D] [Fintype S]
    [DecidableEq S] [Inhabited S] [Fintype H] [DecidableEq H] (g : S → H) (hg : Injective g)
    (q : ℕ) (t : QTree D H Bool) (hfresh : ∀ Tab : D → H, (fresh Tab t).length ≤ q) :
    prob (fun Tab : D → H => eval Tab t = true) ≤
      prob (fun T : D → S => eval T (mapTree g t) = true) +
        q * ((Fintype.card H - Fintype.card S : ℝ) / Fintype.card H) := by
  let _ : Inhabited H := ⟨g default⟩
  -- a uniform table is a lazily sampled one
  have h1 := prob_eval_eq_lazy (fun b : Bool => b = true) q t hfresh
  -- the sampled outputs are in the range of `g`, up to the error term
  have h2 := prob_section (ι := Fin q) g hg (fun v => evalLazy (stream v) 0 [] t = true)
  have hstream : ∀ w : Fin q → S, stream (g ∘ w) = fun i => g (stream w i) := by
    intro w
    funext i
    unfold stream
    split_ifs <;> rfl
  have h3 : (fun w : Fin q → S => evalLazy (stream (g ∘ w)) 0 [] t = true) =
      fun w => evalLazy (stream w) 0 [] (mapTree g t) = true := by
    funext w
    rw [evalLazy_mapTree, hstream]
    rfl
  have h4 := prob_eval_eq_lazy (fun b : Bool => b = true) q (mapTree g t) fun T => by
    rw [fresh, flog_mapTree]
    exact hfresh _
  rw [h1, h4, ← h3]
  refine h2.trans (le_of_eq ?_)
  rw [Fintype.card_fin]

namespace Security

open Taproot

variable {n : ℕ} [Fact n.Prime] {E X M : Type} [AddCommGroup E] [DecidableEq E] [DecidableEq X]
  [DecidableEq M] {H : Type}

/-! ## The game -/

/-- A binding adversary whose oracle answers with hash outputs in `H`. -/
abbrev BindAdversaryH (n N : ℕ) (X M H Coins : Type) :=
  Coins → QTree (SigIn N X M) H (List (X × M) × List (X × M) × (X × ZMod n))

variable (C : Curve n E X) (nonceCoef : E → E → List (X × M × E) → ZMod n) (N : ℕ)
  (red : H → ZMod n)

/-- **The strong binding game with hash outputs** on one sample. The oracle is
a table of hash outputs, which the adversary sees, and `Verify` reduces them
to scalars with `red`. -/
def bindExperimentH {Coins : Type} (A : BindAdversaryH n N X M H Coins)
    (ω : Coins × (SigIn N X M → H)) : Prop :=
  (eval ω.2 (A ω.1)).1 ≠ (eval ω.2 (A ω.1)).2.1 ∧
    (eval ω.2 (A ω.1)).1.length ≤ N ∧ (eval ω.2 (A ω.1)).2.1.length ≤ N ∧
    verify C.ops (hashesOf N nonceCoef fun z => red (ω.2 z)) (eval ω.2 (A ω.1)).1
      (eval ω.2 (A ω.1)).2.2 = true ∧
    verify C.ops (hashesOf N nonceCoef fun z => red (ω.2 z)) (eval ω.2 (A ω.1)).2.1
      (eval ω.2 (A ω.1)).2.2 = true

/-! ## The game as a query algorithm -/

open Classical in
/-- The verifier's part of the game: query the challenges of both lists and
say whether the adversary wins. -/
noncomputable def bindTail (out : List (X × M) × List (X × M) × (X × ZMod n)) :
    QTree (SigIn N X M) (ZMod n) Bool :=
  if h : out.1.length ≤ N ∧ out.2.1.length ≤ N then
    askAll (keysOf N out.1 h.1 out.2.2.1) >>= fun cs₁ =>
      askAll (keysOf N out.2.1 h.2 out.2.2.1) >>= fun cs₂ =>
        .done (decide (out.1 ≠ out.2.1) && verifyWith C.ops out.1 out.2.2 cs₁ &&
          verifyWith C.ops out.2.1 out.2.2 cs₂)
  else .done false

open Classical in
theorem eval_bindTail (T : SigIn N X M → ZMod n)
    (out : List (X × M) × List (X × M) × (X × ZMod n)) :
    eval T (bindTail C N out) = true ↔
      out.1 ≠ out.2.1 ∧ out.1.length ≤ N ∧ out.2.1.length ≤ N ∧
        verify C.ops (hashesOf N nonceCoef T) out.1 out.2.2 = true ∧
        verify C.ops (hashesOf N nonceCoef T) out.2.1 out.2.2 = true := by
  unfold bindTail
  by_cases h : out.1.length ≤ N ∧ out.2.1.length ≤ N
  · rw [dite_eq_left_of_eq_true (eq_true h), eval_bind, eval_askAll, eval_bind, eval_askAll]
    unfold keysOf
    rw [List.map_map, List.map_map]
    change (decide _ && verifyWith C.ops out.1 out.2.2
        (out.1.map fun e => T (⟨out.1, h.1⟩, out.2.2.1, e)) &&
      verifyWith C.ops out.2.1 out.2.2
        (out.2.1.map fun e => T (⟨out.2.1, h.2⟩, out.2.2.1, e))) = true ↔ _
    rw [verifyWith_eq C nonceCoef N T out.1 h.1, verifyWith_eq C nonceCoef N T out.2.1 h.2,
      Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    tauto
  · rw [dite_eq_right_of_eq_false (eq_false h)]
    constructor
    · intro hf
      exact absurd hf Bool.false_ne_true
    · rintro ⟨-, h1, h2, -⟩
      exact absurd ⟨h1, h2⟩ h

theorem length_flog_bindTail (T : SigIn N X M → ZMod n) (l : List (SigIn N X M))
    (out : List (X × M) × List (X × M) × (X × ZMod n)) :
    (flog T l (bindTail C N out)).length ≤ l.length + 2 * N := by
  unfold bindTail
  by_cases h : out.1.length ≤ N ∧ out.2.1.length ≤ N
  · rw [dite_eq_left_of_eq_true (eq_true h), flog_bind, flog_bind]
    have h1 := length_flog_askAll T l (keysOf N out.1 h.1 out.2.2.1)
    have h2 := length_flog_askAll T (flog T l (askAll (keysOf N out.1 h.1 out.2.2.1)))
      (keysOf N out.2.1 h.2 out.2.2.1)
    have e1 : (keysOf N out.1 h.1 out.2.2.1).length = out.1.length := by simp [keysOf]
    have e2 : (keysOf N out.2.1 h.2 out.2.2.1).length = out.2.1.length := by simp [keysOf]
    change (flog T _ (Alg.done _)).length ≤ _
    simp only [flog]
    omega
  · rw [dite_eq_right_of_eq_false (eq_false h)]
    simp [flog]

variable {Coins : Type} (A : BindAdversaryH n N X M H Coins) (coins : Coins)

/-- The game with hash outputs for fixed coins: the adversary, then the
verifier, who reduces the outputs it reads. -/
noncomputable def bindTreeH : QTree (SigIn N X M) H Bool :=
  A coins >>= fun out => mapTree red (bindTail C N out)

theorem eval_bindTreeH (Tab : SigIn N X M → H) :
    eval Tab (bindTreeH C N red A coins) = true ↔
      bindExperimentH C nonceCoef N red A (coins, Tab) := by
  unfold bindTreeH bindExperimentH
  rw [eval_bind, eval_mapTree]
  exact eval_bindTail C nonceCoef N _ _

theorem length_fresh_bindTreeH (Tab : SigIn N X M → H) (qh : ℕ)
    (hA : (fresh Tab (A coins)).length ≤ qh) :
    (fresh Tab (bindTreeH C N red A coins)).length ≤ qh + 2 * N := by
  unfold bindTreeH
  rw [fresh_bind, flog_mapTree]
  exact (length_flog_bindTail C N _ _ _).trans (by omega)

/-! ## The bound -/

/-- The adversary for the game with scalar answers: it reads `g(c)` where the
oracle answers `c`. -/
def liftBind (g : ZMod n → H) (A : BindAdversaryH n N X M H Coins) :
    BindAdversary n N X M Coins := fun coins => mapTree g (A coins)

variable [Fintype Coins] [Fintype (SigIn N X M)] [Fintype H] [DecidableEq H]

/-- **From hash outputs to scalars.** If every scalar is the reduction of an
output (`g`), the game with hash outputs is won at most
`(qh + 2⋅N) ⋅ (|H| - n) / |H|` more often than the game with scalar answers. -/
theorem bindAdvantageH_le (g : ZMod n → H) (hg : ∀ c, red (g c) = c) (qh : ℕ)
    (hA : ∀ coins (Tab : SigIn N X M → H), (fresh Tab (A coins)).length ≤ qh) :
    prob (bindExperimentH C nonceCoef N red A) ≤
      prob (bindExperiment C nonceCoef N (liftBind N g A)) +
        (qh + 2 * N : ℕ) * ((Fintype.card H - n : ℝ) / Fintype.card H) := by
  have hinj : Injective g := fun a b h => by rw [← hg a, ← hg b, h]
  have hle : n ≤ Fintype.card H := by
    simpa [ZMod.card] using Fintype.card_le_of_injective g hinj
  have hc : (0 : ℝ) ≤ (qh + 2 * N : ℕ) * ((Fintype.card H - n : ℝ) / Fintype.card H) := by
    have : (0 : ℝ) ≤ Fintype.card H - n := sub_nonneg.mpr (Nat.cast_le.mpr hle)
    positivity
  refine prob_prod_mono _ _ _ hc fun c => ?_
  have h0 : (fun Tab : SigIn N X M → H => bindExperimentH C nonceCoef N red A (c, Tab)) =
      fun Tab => eval Tab (bindTreeH C N red A c) = true := by
    funext Tab
    exact propext (eval_bindTreeH C nonceCoef N red A c Tab).symm
  have h1 : (fun T : SigIn N X M → ZMod n => bindExperiment C nonceCoef N (liftBind N g A) (c, T)) =
      fun T => eval T (mapTree g (bindTreeH C N red A c)) = true := by
    funext T
    rw [eval_mapTree]
    refine propext (Iff.trans ?_ (eval_bindTreeH C nonceCoef N red A c _).symm)
    unfold bindExperiment bindExperimentH liftBind
    simp only [eval_mapTree]
    have hT : (fun z => red (g (T z))) = T := funext fun z => hg _
    rw [hT]
  rw [h0, h1]
  have h := prob_eval_le_mapTree g hinj (qh + 2 * N) (bindTreeH C N red A c) fun Tab =>
    length_fresh_bindTreeH C N red A c Tab qh (hA c Tab)
  rwa [ZMod.card] at h

/-- **Strong binding with the challenge hash reduced to a scalar**: the bound
of `strongly_binding` and the term for the reduction. -/
theorem strongly_binding_hashed (g : ZMod n → H) (hg : ∀ c, red (g c) = c)
    (hE : Curve.PrimeOrder n E) (hN : N < n) (qh : ℕ)
    (hA : ∀ coins (Tab : SigIn N X M → H), (fresh Tab (A coins)).length ≤ qh) :
    prob (bindExperimentH C nonceCoef N red A) ≤
      ((qh + 2 * N : ℕ) : ℝ) ^ 2 / n +
        (qh + 2 * N : ℕ) * ((Fintype.card H - n : ℝ) / Fintype.card H) := by
  have h1 := bindAdvantageH_le C nonceCoef N red A g hg qh hA
  have h2 := strongly_binding C nonceCoef N (liftBind N g A) hE hN qh fun coins T => by
    unfold liftBind
    rw [fresh, flog_mapTree]
    exact hA coins _
  linarith

omit [DecidableEq H] [Fintype H] in
/-- **Strong binding with BIP 459's challenge hash**: an `m`-valued random
oracle reduced modulo `n`, for `m = 2²⁵⁶`. A signature is valid for two
different lists with probability at most the bound of `strongly_binding` plus
`(qh + 2⋅N) ⋅ (m - n) / m`. -/
theorem strongly_binding_fin {m : ℕ} (hm : n ≤ m) (A : BindAdversaryH n N X M (Fin m) Coins)
    (hE : Curve.PrimeOrder n E) (hN : N < n) (qh : ℕ)
    (hA : ∀ coins (Tab : SigIn N X M → Fin m), (fresh Tab (A coins)).length ≤ qh) :
    prob (bindExperimentH C nonceCoef N (redFin m) A) ≤
      ((qh + 2 * N : ℕ) : ℝ) ^ 2 / n + (qh + 2 * N : ℕ) * ((m - n : ℝ) / m) := by
  have h := strongly_binding_hashed C nonceCoef N (redFin m) A (liftFin hm)
    (fun c => ZMod.natCast_zmod_val c) hE hN qh hA
  rwa [Fintype.card_fin] at h

end Security

end Dahlias
