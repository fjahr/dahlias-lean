import Dahlias.QueryRun
import Dahlias.Prob

/-!
# A random function is a lazily sampled oracle

The security games of this project sample the whole table of the random
oracle before the adversary runs. `prob_eval_eq_lazy`: for an algorithm that
makes at most `q` different queries, that is the same as answering every new
query with the next of `q` independent uniform values and repeated queries
from memory (`evalLazy`).
-/

set_option linter.unusedSectionVars false

namespace Dahlias

open Finset Function

/-! ## One coordinate of a uniform function -/

/-- If `g` does not depend on coordinate `i`, the functions with a given value
at `i` carry the fraction `1 / |β|` of the sum of `g`. -/
theorem sum_fiber {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β] [DecidableEq β] (i : ι)
    (g : (ι → β) → ℝ) (hg : ∀ v s, g (update v i s) = g v) (s₀ : β) :
    (Fintype.card β : ℝ) * ∑ v : ι → β, (if v i = s₀ then g v else 0) = ∑ v : ι → β, g v := by
  have hA : ∀ s : β, ∑ v : ι → β, (if v i = s then g v else 0) =
      ∑ v : ι → β, (if v i = s₀ then g v else 0) := by
    intro s
    let e : (ι → β) → (ι → β) := fun v => update v i (Equiv.swap s s₀ (v i))
    have he : Involutive e := by
      intro v
      simp [e]
    rw [← Equiv.sum_comp (Involutive.toPerm e he)]
    refine sum_congr rfl fun v _ => ?_
    have h1 : ((Involutive.toPerm e he) v) i = Equiv.swap s s₀ (v i) := by simp [e]
    have h2 : g ((Involutive.toPerm e he) v) = g v := hg v _
    rw [h1, h2]
    by_cases hv : v i = s₀
    · simp [hv]
    · have : Equiv.swap s s₀ (v i) ≠ s := by
        intro h
        apply hv
        have := congrArg (Equiv.swap s s₀) h
        simpa using this
      simp [hv, this]
  have hsplit : ∑ v : ι → β, g v = ∑ s : β, ∑ v : ι → β, (if v i = s then g v else 0) := by
    rw [sum_comm]
    refine sum_congr rfl fun v _ => ?_
    simp
  rw [hsplit, sum_congr rfl fun s _ => hA s]
  simp [sum_const, card_univ]

/-- Two games with a common part of the sample have the same probability if
they do for every value of the common part. -/
theorem prob_prod_congr {A B B' : Type} [Fintype A] [Fintype B] [Fintype B'] (p : A × B → Prop)
    (p' : A × B' → Prop) (h : ∀ a, prob (fun b => p (a, b)) = prob (fun b => p' (a, b))) :
    prob p = prob p' := by
  classical
  have key : ∀ (B : Type) [Fintype B] (p : A × B → Prop),
      prob p = (∑ a, prob (fun b => p (a, b))) / Fintype.card A := by
    intro B _ p
    simp only [prob_eq_sum]
    rw [Fintype.sum_prod_type, ← Finset.sum_div, div_div, Fintype.card_prod, Nat.cast_mul,
      mul_comm]
  rw [key B p, key B' p', Finset.sum_congr rfl fun a _ => h a]

namespace QTree

variable {D S α : Type} [DecidableEq D]

/-- The remembered answer to a query. -/
def memo (μ : List (D × S)) (d : D) : Option S :=
  (μ.find? fun p => decide (p.1 = d)).map Prod.snd

/-- Run with a lazily sampled oracle: a new query gets the next value of the
stream `v`, starting at position `k`; a repeated query gets the remembered
answer in `μ`. -/
def evalLazy (v : ℕ → S) : ℕ → List (D × S) → QTree D S α → α
  | _, _, .done a => a
  | k, μ, .ask d f =>
    match memo μ d with
    | some s => evalLazy v k μ (f s)
    | none => evalLazy v (k + 1) (μ ++ [(d, v k)]) (f (v k))

/-- The lazy run reads the stream only from position `k` on. -/
theorem evalLazy_congr {v v' : ℕ → S} (k : ℕ) (h : ∀ i, k ≤ i → v i = v' i)
    (μ : List (D × S)) (t : QTree D S α) : evalLazy v k μ t = evalLazy v' k μ t := by
  induction t generalizing k μ with
  | done a => rfl
  | ask d f ih =>
    unfold evalLazy
    cases memo μ d with
    | some s => exact ih s k h μ
    | none =>
      simp only [h k le_rfl]
      exact ih _ (k + 1) (fun i hi => h i (by omega)) _

/-! ## Answers of another type -/

variable {S₂ β : Type}

/-- A query algorithm for answers in `S`, fed with answers in `S₂` through
`ψ`. -/
def mapTree (ψ : S₂ → S) : QTree D S α → QTree D S₂ α
  | .done a => .done a
  | .ask d f => .ask d fun s => mapTree ψ (f (ψ s))

omit [DecidableEq D] in
theorem eval_mapTree (ψ : S₂ → S) (T : D → S₂) (t : QTree D S α) :
    eval T (mapTree ψ t) = eval (fun d => ψ (T d)) t := by
  induction t with
  | done a => rfl
  | ask d f ih => exact ih _

theorem flog_mapTree (ψ : S₂ → S) (T : D → S₂) (l : List D) (t : QTree D S α) :
    flog T l (mapTree ψ t) = flog (fun d => ψ (T d)) l t := by
  induction t generalizing l with
  | done a => rfl
  | ask d f ih => exact ih _ _

theorem memo_map (ψ : S₂ → S) (μ : List (D × S₂)) (d : D) :
    memo (μ.map fun p => (p.1, ψ p.2)) d = (memo μ d).map ψ := by
  unfold memo
  induction μ with
  | nil => rfl
  | cons p μ ih =>
    by_cases h : p.1 = d
    · simp [h]
    · simp only [List.map_cons, List.find?_cons, h, decide_false]
      exact ih

/-- The lazy run of `mapTree ψ t` is the lazy run of `t` on the mapped stream
and memory. -/
theorem evalLazy_mapTree (ψ : S₂ → S) (v : ℕ → S₂) (k : ℕ) (μ : List (D × S₂))
    (t : QTree D S α) :
    evalLazy v k μ (mapTree ψ t) =
      evalLazy (fun i => ψ (v i)) k (μ.map fun p => (p.1, ψ p.2)) t := by
  induction t generalizing k μ with
  | done a => rfl
  | ask d f ih =>
    simp only [mapTree, evalLazy, memo_map]
    cases memo μ d with
    | some s => exact ih _ _ _
    | none =>
      simp only [Option.map_none]
      rw [ih]
      simp

/-! ## Tables that extend a memory -/

/-- The table `T` agrees with the remembered answers. -/
def Ext (μ : List (D × S)) (T : D → S) : Prop := ∀ p ∈ μ, T p.1 = p.2

theorem memo_eq_some {μ : List (D × S)} {d : D} {s : S} (h : memo μ d = some s) :
    d ∈ μ.map Prod.fst ∧ ∀ T, Ext μ T → T d = s := by
  unfold memo at h
  obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp h
  have hmem := List.mem_of_find?_eq_some hp
  have hd := List.find?_some hp
  simp only [decide_eq_true_eq] at hd
  exact ⟨List.mem_map.mpr ⟨p, hmem, hd⟩, fun T hT => hd ▸ hT p hmem⟩

theorem memo_eq_none {μ : List (D × S)} {d : D} (h : memo μ d = none) :
    d ∉ μ.map Prod.fst := by
  unfold memo at h
  rw [Option.map_eq_none_iff, List.find?_eq_none] at h
  intro hd
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hd
  exact h p hp (by simp)

theorem ext_append {μ : List (D × S)} {d : D} {s : S} {T : D → S} :
    Ext (μ ++ [(d, s)]) T ↔ T d = s ∧ Ext μ T := by
  unfold Ext
  constructor
  · intro h
    exact ⟨h (d, s) (by simp), fun p hp => h p (by simp [hp])⟩
  · rintro ⟨h1, h2⟩ p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact h2 p hp
    · simp only [List.mem_singleton] at hp
      subst hp
      exact h1

theorem ext_update {μ : List (D × S)} {d : D} (hd : d ∉ μ.map Prod.fst) (T : D → S) (s : S) :
    Ext μ (update T d s) ↔ Ext μ T := by
  unfold Ext
  refine forall₂_congr fun p hp => ?_
  have : p.1 ≠ d := fun h => hd (List.mem_map.mpr ⟨p, hp, h⟩)
  rw [update_of_ne this]

/-! ## Lazy sampling -/

variable [Fintype D] [Fintype S] [DecidableEq S] [Inhabited S]

/-- A stream that starts with the `q` values of `v`. -/
def stream {q : ℕ} (v : Fin q → S) (i : ℕ) : S := if h : i < q then v ⟨i, h⟩ else default

open Classical in
/-- The cross-multiplied form of the equality of the two probabilities, for a
run that continues at stream position `k` with the memory `μ`. -/
theorem lazy_count (P : α → Prop) (q : ℕ) (t : QTree D S α) (k : ℕ) (μ : List (D × S))
    (hk : k ≤ q) (hden : ∃ T : D → S, Ext μ T)
    (hfit : ∀ T, Ext μ T → (flog T (μ.map Prod.fst) t).length ≤ (μ.map Prod.fst).length + (q - k)) :
    (∑ v : Fin q → S, if P (evalLazy (stream v) k μ t) then (1 : ℝ) else 0) *
        (∑ T : D → S, if Ext μ T then (1 : ℝ) else 0) =
      (Fintype.card S : ℝ) ^ q * ∑ T : D → S, if Ext μ T ∧ P (eval T t) then (1 : ℝ) else 0 := by
  have hσ : (0 : ℝ) < Fintype.card S := Nat.cast_pos.mpr Fintype.card_pos
  induction t generalizing k μ with
  | done a =>
    by_cases hP : P a
    · simp [evalLazy, eval, hP, sum_const, card_univ]
    · simp [evalLazy, eval, hP]
  | ask d f ih =>
    cases hm : memo μ d with
    | some s =>
      obtain ⟨hdk, hT⟩ := memo_eq_some hm
      have hnum : (∑ T : D → S, if Ext μ T ∧ P (eval T (.ask d f)) then (1 : ℝ) else 0) =
          ∑ T : D → S, if Ext μ T ∧ P (eval T (f s)) then (1 : ℝ) else 0 := by
        refine sum_congr rfl fun T _ => ?_
        by_cases hE : Ext μ T
        · simp [hE, eval, hT T hE]
        · simp [hE]
      have hlz : ∀ v : Fin q → S, evalLazy (stream v) k μ (.ask d f) =
          evalLazy (stream v) k μ (f s) := by
        intro v
        simp [evalLazy, hm]
      rw [hnum, sum_congr rfl fun v _ => by rw [hlz v]]
      refine ih s k μ hk hden fun T hE => ?_
      have := hfit T hE
      simp only [flog, hdk, ↓reduceIte, hT T hE] at this
      exact this
    | none =>
      have hdk := memo_eq_none hm
      obtain ⟨T₀, hT₀⟩ := hden
      -- one more value of the stream is available
      have hkq : k < q := by
        have h := hfit T₀ hT₀
        have hpre := (prefix_flog T₀ (μ.map Prod.fst ++ [d]) (f (T₀ d))).length_le
        simp only [flog, hdk, ↓reduceIte] at h
        simp only [List.length_append, List.length_cons, List.length_nil] at hpre
        omega
      -- the tables that extend the memory, by their value at `d`
      have hden_s : ∀ s : S, (Fintype.card S : ℝ) *
          (∑ T : D → S, if Ext (μ ++ [(d, s)]) T then (1 : ℝ) else 0) =
          ∑ T : D → S, if Ext μ T then (1 : ℝ) else 0 := by
        intro s
        rw [← sum_fiber d (fun T : D → S => if Ext μ T then (1 : ℝ) else 0)
          (fun T s' => by simp only [ext_update hdk]) s]
        congr 1
        refine sum_congr rfl fun T _ => ?_
        by_cases h1 : T d = s <;> simp [ext_append, h1]
      have hnum : (∑ T : D → S, if Ext μ T ∧ P (eval T (.ask d f)) then (1 : ℝ) else 0) =
          ∑ s : S, ∑ T : D → S,
            if Ext (μ ++ [(d, s)]) T ∧ P (eval T (f s)) then (1 : ℝ) else 0 := by
        rw [sum_comm]
        refine sum_congr rfl fun T _ => ?_
        rw [sum_eq_single (T d) (fun s _ hs => by simp [ext_append, Ne.symm hs]) (by simp)]
        simp [ext_append, eval]
        congr
      -- the streams, by their value at position `k`
      have hlz : (Fintype.card S : ℝ) *
          (∑ v : Fin q → S, if P (evalLazy (stream v) k μ (.ask d f)) then (1 : ℝ) else 0) =
          ∑ s : S, ∑ v : Fin q → S,
            if P (evalLazy (stream v) (k + 1) (μ ++ [(d, s)]) (f s)) then (1 : ℝ) else 0 := by
        have hstep : ∀ v : Fin q → S, evalLazy (stream v) k μ (.ask d f) =
            evalLazy (stream v) (k + 1) (μ ++ [(d, v ⟨k, hkq⟩)]) (f (v ⟨k, hkq⟩)) := by
          intro v
          simp [evalLazy, hm, stream, hkq]
        have hsplit : (∑ v : Fin q → S,
            if P (evalLazy (stream v) k μ (.ask d f)) then (1 : ℝ) else 0) =
            ∑ s : S, ∑ v : Fin q → S, if v ⟨k, hkq⟩ = s then
              (if P (evalLazy (stream v) (k + 1) (μ ++ [(d, s)]) (f s)) then (1 : ℝ) else 0)
              else 0 := by
          rw [sum_comm]
          refine sum_congr rfl fun v _ => ?_
          rw [sum_eq_single (v ⟨k, hkq⟩) (fun s _ hs => by simp [Ne.symm hs]) (by simp), hstep]
          simp
        rw [hsplit, mul_sum]
        refine sum_congr rfl fun s _ => ?_
        refine sum_fiber (⟨k, hkq⟩ : Fin q)
          (fun v => if P (evalLazy (stream v) (k + 1) (μ ++ [(d, s)]) (f s)) then (1 : ℝ) else 0)
          (fun v s' => ?_) s
        rw [evalLazy_congr (v := stream (update v ⟨k, hkq⟩ s')) (v' := stream v) (k + 1)]
        intro i hi
        unfold stream
        split_ifs with h
        · rw [update_of_ne]
          intro heq
          have := congrArg Fin.val heq
          simp at this
          omega
        · rfl
      -- the induction hypothesis for every value
      have hih : ∀ s : S,
          (∑ v : Fin q → S,
              if P (evalLazy (stream v) (k + 1) (μ ++ [(d, s)]) (f s)) then (1 : ℝ) else 0) *
            (∑ T : D → S, if Ext (μ ++ [(d, s)]) T then (1 : ℝ) else 0) =
          (Fintype.card S : ℝ) ^ q *
            ∑ T : D → S, if Ext (μ ++ [(d, s)]) T ∧ P (eval T (f s)) then (1 : ℝ) else 0 := by
        intro s
        refine ih s (k + 1) (μ ++ [(d, s)]) hkq ⟨update T₀ d s, ?_⟩ fun T hE => ?_
        · exact ext_append.mpr ⟨update_self d s T₀, (ext_update hdk T₀ s).mpr hT₀⟩
        · obtain ⟨hTd, hEμ⟩ := ext_append.mp hE
          have := hfit T hEμ
          simp only [flog, hdk, ↓reduceIte, hTd] at this
          simp only [List.map_append, List.map_cons, List.map_nil, List.length_append,
            List.length_cons, List.length_nil]
          omega
      -- put the pieces together
      have key : (Fintype.card S : ℝ) *
          ((∑ v : Fin q → S, if P (evalLazy (stream v) k μ (.ask d f)) then (1 : ℝ) else 0) *
            (∑ T : D → S, if Ext μ T then (1 : ℝ) else 0)) =
          (Fintype.card S : ℝ) * ((Fintype.card S : ℝ) ^ q *
            ∑ T : D → S, if Ext μ T ∧ P (eval T (.ask d f)) then (1 : ℝ) else 0) := by
        rw [← mul_assoc, hlz, hnum, sum_mul, mul_sum, mul_sum]
        refine sum_congr rfl fun s _ => ?_
        rw [← hden_s s, mul_comm (Fintype.card S : ℝ), ← mul_assoc, hih s]
        ring
      exact mul_left_cancel₀ hσ.ne' key

open Classical in
/-- **A random function is a lazily sampled oracle**: for an algorithm with at
most `q` different queries, an event of the output has the same probability
with a uniform table as with `q` uniform values handed out lazily. -/
theorem prob_eval_eq_lazy (P : α → Prop) (q : ℕ) (t : QTree D S α)
    (hq : ∀ T : D → S, (fresh T t).length ≤ q) :
    prob (fun T : D → S => P (eval T t)) =
      prob (fun v : Fin q → S => P (evalLazy (stream v) 0 [] t)) := by
  have h := lazy_count P q t 0 [] (Nat.zero_le q) ⟨fun _ => default, fun p hp => by simp at hp⟩
    (fun T _ => by simpa [fresh] using hq T)
  have hσ : (0 : ℝ) < Fintype.card S := Nat.cast_pos.mpr Fintype.card_pos
  have hM : (0 : ℝ) < Fintype.card (D → S) := Nat.cast_pos.mpr Fintype.card_pos
  have hE : ∀ T : D → S, Ext ([] : List (D × S)) T := fun T p hp => by simp at hp
  simp only [hE, true_and, ↓reduceIte, sum_const, card_univ, nsmul_eq_mul, mul_one] at h
  rw [prob_eq_sum, prob_eq_sum, Fintype.card_fun (α := Fin q), Fintype.card_fin, Nat.cast_pow,
    div_eq_div_iff hM.ne' (pow_pos hσ q).ne']
  linarith

/-! ## The lazily sampled run as an expectation -/

theorem memo_append_self {μ : List (D × S)} {d : D} (h : memo μ d = none) (s : S) :
    memo (μ ++ [(d, s)]) d = some s := by
  unfold memo at h ⊢
  rw [Option.map_eq_none_iff] at h
  simp [List.find?_append, h]

theorem memo_append_ne {μ : List (D × S)} {d d' : D} (h : d ≠ d') (s : S) :
    memo (μ ++ [(d, s)]) d' = memo μ d' := by
  unfold memo
  rw [List.find?_append]
  cases hf : μ.find? fun p => decide (p.1 = d') with
  | some p => simp
  | none => simp [h]

/-- The expectation of `F` on the output and the final memory of a run with a
lazily sampled oracle that starts with the memory `μ`: a new query averages
over all answers. -/
noncomputable def exL (F : List (D × S) → α → ℝ) : List (D × S) → QTree D S α → ℝ
  | μ, .done a => F μ a
  | μ, .ask d f =>
    match memo μ d with
    | some s => exL F μ (f s)
    | none => (∑ s : S, exL F (μ ++ [(d, s)]) (f s)) / Fintype.card S

theorem exL_done (F : List (D × S) → α → ℝ) (μ : List (D × S)) (a : α) :
    exL F μ (.done a) = F μ a := by
  unfold exL
  rfl

theorem exL_ask_some (F : List (D × S) → α → ℝ) {μ : List (D × S)} {d : D} {s : S}
    (h : memo μ d = some s) (f : S → QTree D S α) : exL F μ (.ask d f) = exL F μ (f s) := by
  rw [exL]
  simp only [h]

theorem exL_ask_none (F : List (D × S) → α → ℝ) {μ : List (D × S)} {d : D}
    (h : memo μ d = none) (f : S → QTree D S α) :
    exL F μ (.ask d f) = (∑ s : S, exL F (μ ++ [(d, s)]) (f s)) / Fintype.card S := by
  rw [exL]
  simp only [h]

/-- Averages of functions that are termwise close are close. -/
theorem avg_le_avg_add {ι : Type} [Fintype ι] [Nonempty ι] (A B : ι → ℝ) (e : ℝ)
    (h : ∀ i, A i ≤ B i + e) :
    (∑ i, A i) / Fintype.card ι ≤ (∑ i, B i) / Fintype.card ι + e := by
  have hc : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  rw [div_add' _ _ _ hc.ne', div_le_div_iff_of_pos_right hc]
  calc ∑ i, A i ≤ ∑ i, (B i + e) := sum_le_sum fun i _ => h i
    _ = ∑ i, B i + e * Fintype.card ι := by
      rw [sum_add_distrib]
      simp [mul_comm]

theorem exL_bind {β : Type} (F : List (D × S) → β → ℝ) (μ : List (D × S)) (t : QTree D S α)
    (g : α → QTree D S β) :
    exL F μ (t >>= g) = exL (fun μ' a => exL F μ' (g a)) μ t := by
  induction t generalizing μ with
  | done a => rfl
  | ask d f ih =>
    change exL F μ (Alg.ask d fun s => f s >>= g) = _
    unfold exL
    cases memo μ d with
    | some s => exact ih s μ
    | none =>
      simp only
      congr 1
      exact sum_congr rfl fun s _ => ih s _

theorem exL_nonneg (F : List (D × S) → α → ℝ) (hF : ∀ μ a, 0 ≤ F μ a) (μ : List (D × S))
    (t : QTree D S α) : 0 ≤ exL F μ t := by
  induction t generalizing μ with
  | done a => exact hF μ a
  | ask d f ih =>
    unfold exL
    cases memo μ d with
    | some s => exact ih s μ
    | none => exact div_nonneg (sum_nonneg fun s _ => ih s _) (Nat.cast_nonneg _)

theorem exL_le_one (F : List (D × S) → α → ℝ) (hF : ∀ μ a, F μ a ≤ 1) (μ : List (D × S))
    (t : QTree D S α) : exL F μ t ≤ 1 := by
  have hσ : (0 : ℝ) < Fintype.card S := Nat.cast_pos.mpr Fintype.card_pos
  induction t generalizing μ with
  | done a => exact hF μ a
  | ask d f ih =>
    unfold exL
    cases memo μ d with
    | some s => exact ih s μ
    | none =>
      simp only
      rw [div_le_one hσ]
      calc ∑ s : S, exL F (μ ++ [(d, s)]) (f s) ≤ ∑ _s : S, (1 : ℝ) :=
            sum_le_sum fun s _ => ih s _
        _ = Fintype.card S := by simp

open Classical in
/-- The sum of `F` over the tables that extend a memory is the lazily sampled
expectation times the number of those tables. -/
theorem sum_ext_eq_exL (F : α → ℝ) (t : QTree D S α) (μ : List (D × S)) :
    ∑ T : D → S, (if Ext μ T then F (eval T t) else 0) =
      exL (fun _ a => F a) μ t * ∑ T : D → S, (if Ext μ T then (1 : ℝ) else 0) := by
  have hσ : (0 : ℝ) < Fintype.card S := Nat.cast_pos.mpr Fintype.card_pos
  induction t generalizing μ with
  | done a =>
    rw [mul_sum]
    refine sum_congr rfl fun T _ => ?_
    split_ifs <;> simp [exL, eval]
  | ask d f ih =>
    cases hm : memo μ d with
    | some s =>
      obtain ⟨-, hT⟩ := memo_eq_some hm
      have hl : ∑ T : D → S, (if Ext μ T then F (eval T (.ask d f)) else 0) =
          ∑ T : D → S, (if Ext μ T then F (eval T (f s)) else 0) := by
        refine sum_congr rfl fun T _ => ?_
        by_cases hE : Ext μ T
        · simp [hE, eval, hT T hE]
        · simp [hE]
      rw [hl, ih s μ]
      simp [exL, hm]
    | none =>
      have hdk := memo_eq_none hm
      have hden_s : ∀ s : S, (Fintype.card S : ℝ) *
          (∑ T : D → S, if Ext (μ ++ [(d, s)]) T then (1 : ℝ) else 0) =
          ∑ T : D → S, if Ext μ T then (1 : ℝ) else 0 := by
        intro s
        rw [← sum_fiber d (fun T : D → S => if Ext μ T then (1 : ℝ) else 0)
          (fun T s' => by simp only [ext_update hdk]) s]
        congr 1
        refine sum_congr rfl fun T _ => ?_
        by_cases h1 : T d = s <;> simp [ext_append, h1]
      have hnum : ∑ T : D → S, (if Ext μ T then F (eval T (.ask d f)) else 0) =
          ∑ s : S, ∑ T : D → S,
            (if Ext (μ ++ [(d, s)]) T then F (eval T (f s)) else 0) := by
        rw [sum_comm]
        refine sum_congr rfl fun T _ => ?_
        rw [sum_eq_single (T d) (fun s _ hs => by simp [ext_append, Ne.symm hs]) (by simp)]
        simp [ext_append, eval]
      rw [hnum, sum_congr rfl fun s _ => ih s _]
      simp only [exL, hm]
      rw [div_mul_eq_mul_div, eq_div_iff hσ.ne', sum_mul, sum_mul]
      refine sum_congr rfl fun s _ => ?_
      rw [← hden_s s]
      ring

open Classical in
/-- **The probability of an event of the output is its lazily sampled
expectation.** -/
theorem prob_eval_eq_exL (P : α → Prop) (t : QTree D S α) :
    prob (fun T : D → S => P (eval T t)) = exL (fun _ a => if P a then 1 else 0) [] t := by
  have h := sum_ext_eq_exL (fun a => if P a then (1 : ℝ) else 0) t []
  have hE : ∀ T : D → S, Ext ([] : List (D × S)) T := fun T p hp => by simp at hp
  have hM : (0 : ℝ) < Fintype.card (D → S) := Nat.cast_pos.mpr Fintype.card_pos
  simp only [hE, ↓reduceIte, sum_const, card_univ, nsmul_eq_mul, mul_one] at h
  rw [prob_eq_sum, h, mul_div_assoc, div_self hM.ne', mul_one]

end QTree

end Dahlias
