import Dahlias.Lazy

/-!
# Algorithms with a second oracle

An algorithm for the queries `Q ⊕ D` makes the queries `Q` of a game and
queries `D` to a table, a random oracle.

* `answerG G t` answers the table queries from the table `G`.
* `answerLazy v k μ t` answers them lazily: a new query gets the next value of
  the stream `v`, a repeated query the remembered one.
* `prob_answerG_eq_lazy`: with a uniform table and with uniform stream values
  the algorithm behaves alike, if it makes at most `q` table queries.
-/

set_option linter.unusedSectionVars false

namespace Dahlias.Security

open QTree

section Second

variable {Q : Type} {R : Q → Type} {D W α σ : Type}

/-- The answers to the queries `Q` and to the queries of `G`. -/
def SumR (R : Q → Type) (W : Type) : Q ⊕ D → Type
  | .inl q => R q
  | .inr _ => W

/-- Answer the queries of `G` from a table. -/
def answerG (G : D → W) : Alg (Q ⊕ D) (SumR R W) α → Alg Q R α
  | .done a => .done a
  | .ask (.inl q) f => .ask q fun r => answerG G (f r)
  | .ask (.inr z) f => answerG G (f (G z))

/-- The queries to `G` in a run. -/
def gLog (G : D → W) (h : (q : Q) → σ → R q × σ) : Alg (Q ⊕ D) (SumR R W) α → σ → List D
  | .done _, _ => []
  | .ask (.inl q) f, s => gLog G h (f (h q s).1) (h q s).2
  | .ask (.inr z) f, s => z :: gLog G h (f (G z)) s

/-- At most `q` queries to `G`, whatever the answers. -/
def NBound : Alg (Q ⊕ D) (SumR R W) α → ℕ → Prop
  | .done _, _ => True
  | .ask (.inl _) f, q => ∀ r, NBound (f r) q
  | .ask (.inr _) f, q => 0 < q ∧ ∀ r, NBound (f r) (q - 1)

theorem length_gLog (G : D → W) (h : (q : Q) → σ → R q × σ)
    (t : Alg (Q ⊕ D) (SumR R W) α) (s : σ) (q : ℕ) (ht : NBound t q) :
    (gLog G h t s).length ≤ q := by
  induction t generalizing s q with
  | done a => simp [gLog]
  | ask x f ih =>
    cases x with
    | inl x => exact ih _ _ _ (ht _)
    | inr z =>
      obtain ⟨hq, hr⟩ : 0 < q ∧ ∀ r, NBound (f r) (q - 1) := ht
      have := ih (G z) s (q - 1) (hr _)
      simp only [gLog, List.length_cons]
      omega

/-- A run depends on `G` only at the points it queries. -/
theorem answerG_congr (G G' : D → W) (h : (q : Q) → σ → R q × σ)
    (t : Alg (Q ⊕ D) (SumR R W) α) (s : σ) (hG : ∀ z ∈ gLog G h t s, G' z = G z) :
    (answerG G' t).run h s = (answerG G t).run h s := by
  induction t generalizing s with
  | done a => rfl
  | ask x f ih =>
    cases x with
    | inl x => exact ih _ _ hG
    | inr z =>
      have hz : G' z = G z := hG z (by simp [gLog])
      change (answerG G' (f (G' z))).run h s = (answerG G (f (G z))).run h s
      rw [hz]
      exact ih _ _ fun y hy => hG y (by simp [gLog, hy])

/-- A handler for the queries `Q` extended by a table for the queries of `G`. -/
def handG (G : D → W) (h : (q : Q) → σ → R q × σ) : (q : Q ⊕ D) → σ → SumR R W q × σ
  | .inl q, s => h q s
  | .inr z, s => (G z, s)

theorem run_answerG (G : D → W) (h : (q : Q) → σ → R q × σ)
    (t : Alg (Q ⊕ D) (SumR R W) α) (s : σ) :
    (answerG G t).run h s = t.run (handG G h) s := by
  induction t generalizing s with
  | done a => rfl
  | ask x f ih =>
    cases x with
    | inl x => exact ih _ _
    | inr z => exact ih _ _

/-! ## Building algorithms with table queries -/

variable {β : Type}

/-- An algorithm without table queries. -/
def liftQ : Alg Q R α → Alg (Q ⊕ D) (SumR R W) α
  | .done a => .done a
  | .ask q f => .ask (.inl q) fun r => liftQ (f r)

theorem answerG_liftQ (G : D → W) (t : Alg Q R α) : answerG G (liftQ t) = t := by
  induction t with
  | done a => rfl
  | ask q f ih =>
    simp only [liftQ, answerG]
    congr 1
    funext r
    exact ih r

theorem answerG_bind (G : D → W) (t : Alg (Q ⊕ D) (SumR R W) α)
    (g : α → Alg (Q ⊕ D) (SumR R W) β) :
    answerG G (t >>= g) = answerG G t >>= fun a => answerG G (g a) := by
  induction t with
  | done a => rfl
  | ask x f ih =>
    cases x with
    | inl x =>
      simp only [Alg.ask_bind, answerG]
      congr 1
      funext r
      exact ih r
    | inr z => exact ih _

theorem answerG_interp {Q' : Type} {R' : Q' → Type} (G : D → W)
    (hM : (q : Q') → σ → Alg (Q ⊕ D) (SumR R W) (R' q × σ)) (h : (q : Q') → σ → Alg Q R (R' q × σ))
    (hh : ∀ q s, answerG G (hM q s) = h q s) (t : Alg Q' R' α) (s : σ) :
    answerG G (Alg.interp hM t s) = Alg.interp h t s := by
  induction t generalizing s with
  | done a => rfl
  | ask q f ih =>
    rw [Alg.interp_ask, Alg.interp_ask, answerG_bind, hh]
    congr 1
    funext p
    exact ih _ _

/-! ## Counting table queries -/

theorem NBound.mono {t : Alg (Q ⊕ D) (SumR R W) α} {q q' : ℕ} (h : NBound t q) (hq : q ≤ q') :
    NBound t q' := by
  induction t generalizing q q' with
  | done a => trivial
  | ask x f ih =>
    cases x with
    | inl x => exact fun r => ih r (h r) hq
    | inr z =>
      obtain ⟨h0, hr⟩ : 0 < q ∧ ∀ r, NBound (f r) (q - 1) := h
      exact ⟨by omega, fun r => ih r (hr r) (by omega)⟩

theorem NBound.bind {t : Alg (Q ⊕ D) (SumR R W) α} {g : α → Alg (Q ⊕ D) (SumR R W) β}
    {a b : ℕ} (ht : NBound t a) (hg : ∀ r, NBound (g r) b) : NBound (t >>= g) (a + b) := by
  induction t generalizing a with
  | done r => exact (hg r).mono (by omega)
  | ask x f ih =>
    cases x with
    | inl x => exact fun r => ih r (ht r)
    | inr z =>
      obtain ⟨h0, hr⟩ : 0 < a ∧ ∀ r, NBound (f r) (a - 1) := ht
      refine ⟨by omega, fun r => ?_⟩
      have := ih r (hr r)
      exact this.mono (by omega)

theorem nbound_liftQ (t : Alg Q R α) (q : ℕ) : NBound (liftQ (D := D) (W := W) t) q := by
  induction t with
  | done a => trivial
  | ask x f ih => exact fun r => ih r

/-- On every path the number of table queries plus the cost of the result is
at most `total`, and every result satisfies `Post`. -/
def RP (Post : α → Prop) (cost : α → ℕ) : Alg (Q ⊕ D) (SumR R W) α → ℕ → Prop
  | .done a, total => Post a ∧ cost a ≤ total
  | .ask (.inl _) f, total => ∀ r, RP Post cost (f r) total
  | .ask (.inr _) f, total => 0 < total ∧ ∀ r, RP Post cost (f r) (total - 1)

theorem RP.mono {Post : α → Prop} {cost : α → ℕ} {t : Alg (Q ⊕ D) (SumR R W) α} {a b : ℕ}
    (h : RP Post cost t a) (hab : a ≤ b) : RP Post cost t b := by
  induction t generalizing a b with
  | done r => exact ⟨h.1, h.2.trans hab⟩
  | ask x f ih =>
    cases x with
    | inl x => exact fun r => ih r (h r) hab
    | inr z =>
      obtain ⟨h0, hr⟩ : 0 < a ∧ ∀ r, RP Post cost (f r) (a - 1) := h
      exact ⟨by omega, fun r => ih r (hr r) (by omega)⟩

theorem RP.bind {P₁ : α → Prop} {c₁ : α → ℕ} {P₂ : β → Prop} {c₂ : β → ℕ}
    {t : Alg (Q ⊕ D) (SumR R W) α} {g : α → Alg (Q ⊕ D) (SumR R W) β} {total : ℕ}
    (ht : RP P₁ c₁ t total) (hg : ∀ a, P₁ a → RP P₂ c₂ (g a) (c₁ a)) :
    RP P₂ c₂ (t >>= g) total := by
  induction t generalizing total with
  | done r => exact (hg r ht.1).mono ht.2
  | ask x f ih =>
    cases x with
    | inl x => exact fun r => ih r (ht r)
    | inr z =>
      obtain ⟨h0, hr⟩ : 0 < total ∧ ∀ r, RP P₁ c₁ (f r) (total - 1) := ht
      exact ⟨h0, fun r => ih r (hr r)⟩

theorem RP.bind_nbound {P₁ : α → Prop} {c₁ : α → ℕ}
    {t : Alg (Q ⊕ D) (SumR R W) α} {g : α → Alg (Q ⊕ D) (SumR R W) β} {total : ℕ}
    (ht : RP P₁ c₁ t total) (hg : ∀ a, P₁ a → NBound (g a) (c₁ a)) :
    NBound (t >>= g) total := by
  induction t generalizing total with
  | done r => exact (hg r ht.1).mono ht.2
  | ask x f ih =>
    cases x with
    | inl x => exact fun r => ih r (ht r)
    | inr z =>
      obtain ⟨h0, hr⟩ : 0 < total ∧ ∀ r, RP P₁ c₁ (f r) (total - 1) := ht
      exact ⟨h0, fun r => ih r (hr r)⟩

/-- Every result of the algorithm satisfies `Post`. -/
def AllLeaves (Post : α → Prop) : Alg Q R α → Prop
  | .done a => Post a
  | .ask _ f => ∀ r, AllLeaves Post (f r)

theorem RP_liftQ {Post : α → Prop} {cost : α → ℕ} {t : Alg Q R α} {total : ℕ}
    (h : AllLeaves Post t) (hc : ∀ a, Post a → cost a ≤ total) :
    RP Post cost (liftQ (D := D) (W := W) t) total := by
  induction t with
  | done a => exact ⟨h, hc a h⟩
  | ask x f ih => exact fun r => ih r (h r)

end Second

/-! ## Lazy answers -/

section Lazy

variable {Q : Type} {R : Q → Type} {D W α σ : Type} [DecidableEq D]

/-- Answer the queries of `G` lazily from the stream `v`. -/
def answerLazy (v : ℕ → W) : ℕ → List (D × W) → Alg (Q ⊕ D) (SumR R W) α → Alg Q R α
  | _, _, .done a => .done a
  | k, μ, .ask (.inl q) f => .ask q fun r => answerLazy v k μ (f r)
  | k, μ, .ask (.inr z) f =>
    match memo μ z with
    | some s => answerLazy v k μ (f s)
    | none => answerLazy v (k + 1) (μ ++ [(z, v k)]) (f (v k))

/-- The algorithm with a handler for its game queries, as a query algorithm
for the table. -/
def toTree (h : (q : Q) → σ → R q × σ) : Alg (Q ⊕ D) (SumR R W) α → σ → QTree D W (α × σ)
  | .done a, s => .done (a, s)
  | .ask (.inl q) f, s => toTree h (f (h q s).1) (h q s).2
  | .ask (.inr z) f, s => .ask z fun w => toTree h (f w) s

omit [DecidableEq D] in
theorem eval_toTree (G : D → W) (h : (q : Q) → σ → R q × σ)
    (t : Alg (Q ⊕ D) (SumR R W) α) (s : σ) :
    eval G (toTree h t s) = (answerG G t).run h s := by
  induction t generalizing s with
  | done a => rfl
  | ask x f ih =>
    cases x with
    | inl x => exact ih _ _
    | inr z => exact ih _ _

theorem evalLazy_toTree (v : ℕ → W) (h : (q : Q) → σ → R q × σ)
    (t : Alg (Q ⊕ D) (SumR R W) α) (s : σ) (k : ℕ) (μ : List (D × W)) :
    evalLazy v k μ (toTree h t s) = (answerLazy v k μ t).run h s := by
  induction t generalizing s k μ with
  | done a => rfl
  | ask x f ih =>
    cases x with
    | inl x => exact ih _ _ _ _
    | inr z =>
      simp only [toTree, evalLazy, answerLazy]
      cases memo μ z with
      | some w => exact ih _ _ _ _
      | none => exact ih _ _ _ _

theorem length_flog_toTree (G : D → W) (h : (q : Q) → σ → R q × σ)
    (t : Alg (Q ⊕ D) (SumR R W) α) (s : σ) (l : List D) (q : ℕ) (ht : NBound t q) :
    (flog G l (toTree h t s)).length ≤ l.length + q := by
  induction t generalizing s l q with
  | done a => simp [toTree, flog]
  | ask x f ih =>
    cases x with
    | inl x => exact ih _ _ _ _ (ht _)
    | inr z =>
      obtain ⟨hq, hr⟩ : 0 < q ∧ ∀ r, NBound (f r) (q - 1) := ht
      have := ih (G z) s (if z ∈ l then l else l ++ [z]) (q - 1) (hr _)
      simp only [toTree, flog]
      split_ifs at this ⊢ <;> simp at this ⊢ <;> omega

variable [Fintype D] [Fintype W] [DecidableEq W] [Inhabited W]

/-- **A uniform table and lazily sampled answers give the same behaviour.** -/
theorem prob_answerG_eq_lazy (h : (q : Q) → σ → R q × σ) (s : σ)
    (t : Alg (Q ⊕ D) (SumR R W) α) (P : α × σ → Prop) (q : ℕ) (hq : NBound t q) :
    prob (fun G : D → W => P ((answerG G t).run h s)) =
      prob (fun v : Fin q → W => P ((answerLazy (stream v) 0 [] t).run h s)) := by
  have key := prob_eval_eq_lazy P q (toTree h t s) fun G => by
    have := length_flog_toTree G h t s [] q hq
    simpa [fresh] using this
  simp only [eval_toTree, evalLazy_toTree] at key
  exact key

end Lazy

end Dahlias.Security
