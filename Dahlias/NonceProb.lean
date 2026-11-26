import Dahlias.Lazy

/-!
# Probability lemmas for derived nonces

The counting facts behind the analysis of `NonceGen` (`Dahlias.NonceGen`):

* `prob_section`: a value derived from a uniform `w : W` is uniform on `U`
  up to the fraction of `W` outside a copy of `U`.
* `prob_hit` and `prob_not_injective`: independent uniform values rarely hit a
  short list and rarely collide.
-/

set_option linter.unusedSectionVars false

namespace Dahlias

open Finset Function

/-! ## General facts -/

section General

variable {Ω : Type} [Fintype Ω]

open Classical in
theorem prob_const [Nonempty Ω] (c : Prop) [Decidable c] :
    prob (fun _ : Ω => c) = if c then 1 else 0 := by
  have h : (0 : ℝ) < Fintype.card Ω := Nat.cast_pos.mpr Fintype.card_pos
  rw [prob_eq_sum]
  by_cases hc : c <;> simp [hc, h.ne']

open Classical in
theorem prob_le_one (p : Ω → Prop) : prob p ≤ 1 := by
  unfold prob
  rcases isEmpty_or_nonempty Ω with h | h
  · simp
  · have hpos : (0 : ℝ) < Fintype.card Ω := Nat.cast_pos.mpr Fintype.card_pos
    rw [div_le_one hpos]
    exact_mod_cast card_le_univ _

open Classical in
/-- The union bound over a finite type. -/
theorem prob_exists_fintype_le {ι : Type} [Fintype ι] (p : ι → Ω → Prop) :
    prob (fun ω => ∃ i, p i ω) ≤ ∑ i, prob (p i) := by
  unfold prob
  rw [← Finset.sum_div]
  gcongr
  have hsub : (univ.filter fun ω => ∃ i, p i ω) ⊆ univ.biUnion fun i => univ.filter (p i) := by
    intro ω hω
    obtain ⟨i, hi⟩ := (mem_filter.mp hω).2
    exact mem_biUnion.mpr ⟨i, mem_univ _, mem_filter.mpr ⟨mem_univ _, hi⟩⟩
  have h : (((univ.filter fun ω => ∃ i, p i ω).card : ℕ) : ℝ) ≤
      ((∑ i, (univ.filter (p i)).card : ℕ) : ℝ) :=
    Nat.cast_le.mpr ((card_le_card hsub).trans card_biUnion_le)
  push_cast at h
  convert h

open Classical in
/-- A bound for every value of the second part of the sample is a bound. -/
theorem prob_prod_le {A B : Type} [Fintype A] [Fintype B] (p : A × B → Prop) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ b, prob (fun a => p (a, b)) ≤ c) : prob p ≤ c := by
  rcases isEmpty_or_nonempty B with hB | hB
  · unfold prob
    simp [hc]
  have hpos : (0 : ℝ) < Fintype.card B := Nat.cast_pos.mpr Fintype.card_pos
  have key : prob p = (∑ b, prob (fun a => p (a, b))) / Fintype.card B := by
    simp only [prob_eq_sum]
    rw [Fintype.sum_prod_type_right, ← Finset.sum_div, div_div, Fintype.card_prod, Nat.cast_mul]
  rw [key, div_le_iff₀ hpos]
  calc ∑ b, prob (fun a => p (a, b)) ≤ ∑ _b : B, c := sum_le_sum fun b _ => h b
    _ = c * Fintype.card B := by simp [mul_comm]

open Classical in
theorem prob_prod_eq_sum {A B : Type} [Fintype A] [Fintype B] (p : A × B → Prop) :
    prob p = (∑ a, prob (fun b => p (a, b))) / Fintype.card A := by
  simp only [prob_eq_sum]
  rw [Fintype.sum_prod_type, ← Finset.sum_div, div_div, Fintype.card_prod, Nat.cast_mul,
    mul_comm]

/-- A bound for every value of the first part of the sample, up to `c`, is a
bound up to `c`. -/
theorem prob_prod_mono {A B B' : Type} [Fintype A] [Fintype B] [Fintype B'] (p : A × B → Prop)
    (p' : A × B' → Prop) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ a, prob (fun b => p (a, b)) ≤ prob (fun b => p' (a, b)) + c) :
    prob p ≤ prob p' + c := by
  rcases isEmpty_or_nonempty A with hA | hA
  · have : prob p = 0 := by
      unfold prob
      simp
    rw [this]
    exact add_nonneg (prob_nonneg _) hc
  · have hpos : (0 : ℝ) < Fintype.card A := Nat.cast_pos.mpr Fintype.card_pos
    rw [prob_prod_eq_sum p, prob_prod_eq_sum p', div_add' _ _ _ hpos.ne',
      div_le_div_iff_of_pos_right hpos]
    calc ∑ a, prob (fun b => p (a, b)) ≤ ∑ a, (prob (fun b => p' (a, b)) + c) :=
          sum_le_sum fun a _ => h a
      _ = ∑ a, prob (fun b => p' (a, b)) + c * Fintype.card A := by
          rw [sum_add_distrib]
          simp [mul_comm]

theorem prob_prod_le' {A B : Type} [Fintype A] [Fintype B] (p : A × B → Prop) (c : ℝ)
    (hc : 0 ≤ c) (h : ∀ a, prob (fun b => p (a, b)) ≤ c) : prob p ≤ c := by
  rw [← prob_equiv (Equiv.prodComm B A) p]
  exact prob_prod_le _ c hc h

open Classical in
/-- An event of the first part of the sample. -/
theorem prob_fst {A B : Type} [Fintype A] [Fintype B] [Nonempty B] (q : A → Prop) :
    prob (fun x : A × B => q x.1) = prob q := by
  rw [prob_prod_congr (fun x : A × B => q x.1) (fun x : A × Unit => q x.1)
    fun a => by
      change prob (fun _ => q a) = prob (fun _ => q a)
      rw [prob_const, prob_const]]
  exact prob_equiv (Equiv.prodPUnit A) q

open Classical in
/-- An event of one coordinate of a uniform function. -/
theorem prob_coord {ι W : Type} [Fintype ι] [DecidableEq ι] [Fintype W] [Nonempty W] (i : ι)
    (q : W → Prop) : prob (fun w : ι → W => q (w i)) = prob q := by
  rw [← prob_equiv (Equiv.funSplitAt i W).symm (fun w : ι → W => q (w i))]
  have h1 : (fun x : W × ({j // j ≠ i} → W) => q (((Equiv.funSplitAt i W).symm x) i)) =
      fun x => q x.1 := by
    funext x
    simp [Equiv.funSplitAt, Equiv.piSplitAt]
  rw [h1, prob_prod_congr (fun x : W × ({j // j ≠ i} → W) => q x.1) (fun x : W × Unit => q x.1)
    fun a => by
      change prob (fun _ => q a) = prob (fun _ => q a)
      rw [prob_const, prob_const]]
  exact prob_equiv (Equiv.prodPUnit W) q

end General

/-! ## Entries of a uniform table -/

section Overwrite

variable {ι D W : Type}

open Classical in
/-- The table `G` with the value `w i` at the point `p i`. -/
noncomputable def overwrite (p : ι → D) (G : D → W) (w : ι → W) : D → W :=
  fun d => if h : ∃ i, p i = d then w h.choose else G d

theorem overwrite_apply {p : ι → D} (hp : Injective p) (G : D → W) (w : ι → W) (i : ι) :
    overwrite p G w (p i) = w i := by
  unfold overwrite
  have h : ∃ j, p j = p i := ⟨i, rfl⟩
  rw [dite_eq_left_of_eq_true (eq_true h), hp h.choose_spec]

theorem overwrite_of_ne {p : ι → D} (G : D → W) (w : ι → W) {d : D} (h : ∀ i, p i ≠ d) :
    overwrite p G w d = G d := by
  unfold overwrite
  have hn : ¬∃ i, p i = d := fun ⟨i, hi⟩ => h i hi
  rw [dite_eq_right_of_eq_false (eq_false hn)]

/-- Exchange the entries of the table at the points `p` with the values `w`. -/
noncomputable def swapAt (p : ι → D) (x : (D → W) × (ι → W)) : (D → W) × (ι → W) :=
  (overwrite p x.1 x.2, fun i => x.1 (p i))

theorem swapAt_involutive {p : ι → D} (hp : Injective p) :
    Involutive (swapAt (W := W) p) := by
  rintro ⟨G, w⟩
  refine Prod.ext ?_ ?_
  · funext d
    by_cases h : ∃ i, p i = d
    · obtain ⟨i, rfl⟩ := h
      exact overwrite_apply hp _ _ i
    · push Not at h
      change overwrite p (overwrite p G w) _ d = G d
      rw [overwrite_of_ne _ _ h, overwrite_of_ne _ _ h]
  · funext i
    exact overwrite_apply hp _ _ i

end Overwrite

/-! ## Reduction modulo the group order -/

section Section

variable {ι U W : Type} [Fintype ι] [DecidableEq ι] [Fintype U] [Fintype W] [Nonempty U]

open Classical in
/-- **Derived values are almost uniform.** If `g` embeds `U` into `W`, an
event of `ι` independent uniform values of `W` is at most the event on the
embedded values of `U` plus `|ι| ⋅ (|W| - |U|) / |W|`. -/
theorem prob_section (g : U → W) (hg : Injective g) (P : (ι → W) → Prop) :
    prob P ≤ prob (fun u : ι → U => P (g ∘ u)) +
      Fintype.card ι * ((Fintype.card W - Fintype.card U : ℝ) / Fintype.card W) := by
  have : Nonempty W := ⟨g (Classical.arbitrary U)⟩
  have hle : Fintype.card U ≤ Fintype.card W := Fintype.card_le_of_injective g hg
  refine (prob_le_add (q := fun w : ι → W => (∀ i, w i ∈ Set.range g) ∧ P w)
    (r := fun w => ∃ i, w i ∉ Set.range g) fun w hw => ?_).trans (add_le_add ?_ ?_)
  · by_cases h : ∀ i, w i ∈ Set.range g
    · exact Or.inl ⟨h, hw⟩
    · push Not at h
      exact Or.inr h
  · -- all values in the copy of `U`
    unfold prob
    have hinj : Injective fun u : ι → U => g ∘ u := fun u u' h => by
      funext i
      exact hg (congrFun h i)
    have hsub : (univ.filter fun w : ι → W => (∀ i, w i ∈ Set.range g) ∧ P w) ⊆
        (univ.filter fun u : ι → U => P (g ∘ u)).image fun u => g ∘ u := by
      intro w hw
      obtain ⟨hr, hP⟩ := (mem_filter.mp hw).2
      choose u hu using hr
      have : g ∘ u = w := funext hu
      exact mem_image.mpr ⟨u, mem_filter.mpr ⟨mem_univ _, this ▸ hP⟩, this⟩
    have hc := (card_le_card hsub).trans card_image_le
    have hU : (0 : ℝ) < Fintype.card (ι → U) := Nat.cast_pos.mpr Fintype.card_pos
    have hUW : (Fintype.card (ι → U) : ℝ) ≤ Fintype.card (ι → W) := by
      exact_mod_cast Fintype.card_le_of_injective _ hinj
    have hfin : ((univ.filter fun w : ι → W => (∀ i, w i ∈ Set.range g) ∧ P w).card : ℝ) /
          Fintype.card (ι → W) ≤
        ((univ.filter fun u : ι → U => P (g ∘ u)).card : ℝ) / Fintype.card (ι → U) := by
      exact (div_le_div_of_nonneg_right (by exact_mod_cast hc) (Nat.cast_nonneg _)).trans
        (div_le_div_of_nonneg_left (Nat.cast_nonneg _) hU hUW)
    convert hfin
  · -- some value outside
    refine (prob_exists_fintype_le _).trans ?_
    have h1 : ∀ i : ι, prob (fun w : ι → W => w i ∉ Set.range g) =
        (Fintype.card W - Fintype.card U : ℝ) / Fintype.card W := by
      intro i
      rw [prob_coord i (fun s : W => s ∉ Set.range g)]
      unfold prob
      congr 1
      have : (univ.filter fun s : W => s ∉ Set.range g) = univ \ univ.image g := by
        ext s
        simp
      have hc : ((univ.filter fun s : W => s ∉ Set.range g).card : ℝ) =
          Fintype.card W - Fintype.card U := by
        rw [this, card_sdiff_of_subset (subset_univ _), card_image_of_injective _ hg, card_univ,
          card_univ, Nat.cast_sub hle]
      convert hc
    rw [sum_congr rfl fun i _ => h1 i]
    simp [sum_const, card_univ]

end Section

/-! ## Hits and collisions -/

section Hit

variable {R : Type} [Fintype R] [Nonempty R] {qs : ℕ}

open Classical in
/-- Independent uniform values hit a list `S` with probability at most
`qs ⋅ |S| / |R|`. -/
theorem prob_hit (S : List R) :
    prob (fun r : Fin qs → R => ∃ k, r k ∈ S) ≤ qs * (S.length / Fintype.card R) := by
  refine (prob_exists_fintype_le _).trans ?_
  have h1 : ∀ k : Fin qs, prob (fun r : Fin qs → R => r k ∈ S) ≤
      (S.length : ℝ) / Fintype.card R := by
    intro k
    rw [prob_coord k (fun s : R => s ∈ S)]
    unfold prob
    gcongr
    have : (univ.filter fun s : R => s ∈ S) ⊆ S.toFinset := fun s hs => by simpa using hs
    convert (card_le_card this).trans (List.toFinset_card_le S)
  calc ∑ k : Fin qs, prob (fun r : Fin qs → R => r k ∈ S)
      ≤ ∑ _k : Fin qs, (S.length : ℝ) / Fintype.card R := sum_le_sum fun k _ => h1 k
    _ = qs * (S.length / Fintype.card R) := by simp

open Classical in
/-- Independent uniform values collide with probability at most `qs² / |R|`. -/
theorem prob_not_injective :
    prob (fun r : Fin qs → R => ¬Injective r) ≤ (qs : ℝ) ^ 2 / Fintype.card R := by
  have hR : (0 : ℝ) < Fintype.card R := Nat.cast_pos.mpr Fintype.card_pos
  have hpair : ∀ k k' : Fin qs, k ≠ k' →
      prob (fun r : Fin qs → R => r k = r k') ≤ 1 / Fintype.card R := by
    intro k k' hkk
    have hN : (0 : ℝ) < Fintype.card (Fin qs → R) := Nat.cast_pos.mpr Fintype.card_pos
    rw [prob_eq_sum, div_le_iff₀ hN]
    have hs : ∀ s : R, (Fintype.card R : ℝ) *
        ∑ v : Fin qs → R, (if v k = s then (if v k' = s then (1 : ℝ) else 0) else 0) =
        ∑ v : Fin qs → R, if v k' = s then (1 : ℝ) else 0 :=
      fun s => sum_fiber k (fun v : Fin qs → R => if v k' = s then (1 : ℝ) else 0)
        (fun v s' => by rw [update_of_ne (Ne.symm hkk)]) s
    have h2 : ∑ v : Fin qs → R, (if v k = v k' then (1 : ℝ) else 0) =
        ∑ s : R, ∑ v : Fin qs → R,
          (if v k = s then (if v k' = s then (1 : ℝ) else 0) else 0) := by
      rw [sum_comm]
      refine sum_congr rfl fun v _ => ?_
      rw [sum_eq_single (v k) (fun s _ hs => by simp [Ne.symm hs]) (by simp)]
      simp [eq_comm]
    have h3 : ∑ s : R, ∑ v : Fin qs → R, (if v k' = s then (1 : ℝ) else 0) =
        Fintype.card (Fin qs → R) := by
      rw [sum_comm]
      simp
    have h4 : (Fintype.card R : ℝ) * ∑ v : Fin qs → R, (if v k = v k' then (1 : ℝ) else 0) =
        Fintype.card (Fin qs → R) := by
      rw [h2, mul_sum, sum_congr rfl fun s _ => hs s, h3]
    rw [one_div, inv_mul_eq_div, le_div_iff₀ hR, mul_comm, h4]
  have hsub : prob (fun r : Fin qs → R => ¬Injective r) ≤
      ∑ k : Fin qs, ∑ k' : Fin qs, prob (fun r : Fin qs → R => k ≠ k' ∧ r k = r k') := by
    refine (prob_mono (q := fun r : Fin qs → R => ∃ k, ∃ k', k ≠ k' ∧ r k = r k')
      fun r hr => ?_).trans
      ((prob_exists_fintype_le _).trans (sum_le_sum fun k _ => prob_exists_fintype_le _))
    unfold Injective at hr
    push Not at hr
    obtain ⟨k, k', h1, h2⟩ := hr
    exact ⟨k, k', h2, h1⟩
  refine hsub.trans ?_
  have hb : ∀ k k' : Fin qs, prob (fun r : Fin qs → R => k ≠ k' ∧ r k = r k') ≤
      1 / Fintype.card R := by
    intro k k'
    by_cases hkk : k = k'
    · have : prob (fun r : Fin qs → R => k ≠ k' ∧ r k = r k') = 0 := by
        unfold prob
        simp [hkk]
      rw [this]
      positivity
    · exact (prob_mono fun r hr => hr.2).trans (hpair k k' hkk)
  calc ∑ k : Fin qs, ∑ k' : Fin qs, prob (fun r : Fin qs → R => k ≠ k' ∧ r k = r k')
      ≤ ∑ _k : Fin qs, ∑ _k' : Fin qs, (1 : ℝ) / Fintype.card R :=
        sum_le_sum fun k _ => sum_le_sum fun k' _ => hb k k'
    _ = (qs : ℝ) ^ 2 / Fintype.card R := by
        simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end Hit

/-! ## Values of a random oracle at secret points -/

section Hop

/-- Samples with the secret values moved to the end. -/
def moveLast {Θ Rs Gt Ws : Type} : (Θ × Rs) × (Gt × Ws) ≃ ((Θ × Gt) × Ws) × Rs where
  toFun s := (((s.1.1, s.2.1), s.2.2), s.1.2)
  invFun t := ((t.1.1.1, t.2), (t.1.1.2, t.1.2))
  left_inv _ := rfl
  right_inv _ := rfl

variable {Θ D W ι Rnd : Type} [Fintype Θ] [Fintype D] [DecidableEq D] [Fintype W] [Nonempty W]
  [Fintype ι] [DecidableEq ι] [Fintype Rnd] [Nonempty Rnd] {qs : ℕ}

/-- **Oracle values at secret points are fresh.** A game uses the values of a
uniform table `G` at points `p r i` that are distinct for distinct uniform
secrets `r`, and it reads `G` elsewhere only at the points of `log`. Each point
`p r i` carries one of the secrets (`key`). Then the game is won at most as
often as with independent uniform values `v` in place of the table's, plus the
probability that two secrets collide or that a logged point carries a secret. -/
theorem oracle_hop (p : (Fin qs → Rnd) → ι → D) (hp : ∀ r, Injective r → Injective (p r))
    (key : D → Rnd) (hkey : ∀ r i, ∃ k, key (p r i) = r k)
    (win : Θ → (D → W) → (ι → W) → Prop) (log : Θ → (D → W) → (ι → W) → List D)
    (hcongr : ∀ θ G G' v, (∀ z ∈ log θ G v, G' z = G z) → (win θ G' v ↔ win θ G v))
    (qn : ℕ) (hlen : ∀ θ G v, (log θ G v).length ≤ qn) :
    prob (fun ω : (Θ × (Fin qs → Rnd)) × (D → W) => win ω.1.1 ω.2 fun i => ω.2 (p ω.1.2 i)) ≤
      prob (fun s : (Θ × (D → W)) × (ι → W) => win s.1.1 s.1.2 s.2) +
        (qs : ℝ) ^ 2 / Fintype.card Rnd + qs * (qn / Fintype.card Rnd) := by
  have hRnd : (0 : ℝ) < Fintype.card Rnd := Nat.cast_pos.mpr Fintype.card_pos
  let ideal : (Θ × (D → W)) × (ι → W) → Prop := fun s => win s.1.1 s.1.2 s.2
  let bad : ((Θ × (D → W)) × (ι → W)) × (Fin qs → Rnd) → Prop :=
    fun t => ∃ k, t.2 k ∈ (log t.1.1.1 t.1.1.2 t.1.2).map key
  -- for distinct secrets
  have hreal : ∀ (θ : Θ) (r : Fin qs → Rnd), Injective r →
      prob (fun G : D → W => win θ G fun i => G (p r i)) ≤
        prob (fun y : (D → W) × (ι → W) =>
          win θ y.1 y.2 ∨ ∃ k, r k ∈ (log θ y.1 y.2).map key) := by
    intro θ r hinj
    have hpr := hp r hinj
    rw [← prob_fst (B := ι → W) (fun G : D → W => win θ G fun i => G (p r i))]
    rw [← prob_equiv (Involutive.toPerm _ (swapAt_involutive (W := W) hpr))
      (fun y : (D → W) × (ι → W) => win θ y.1 y.2 ∨ ∃ k, r k ∈ (log θ y.1 y.2).map key)]
    refine prob_mono ?_
    rintro ⟨G, w⟩ hR
    change win θ (overwrite (p r) G w) (fun i => G (p r i)) ∨
      ∃ k, r k ∈ (log θ (overwrite (p r) G w) fun i => G (p r i)).map key
    by_cases hb : ∃ k, r k ∈ (log θ (overwrite (p r) G w) fun i => G (p r i)).map key
    · exact Or.inr hb
    · refine Or.inl ((hcongr θ _ G _ fun z hz => ?_).mp hR)
      refine (overwrite_of_ne G w fun i hi => ?_).symm
      obtain ⟨k, hk⟩ := hkey r i
      exact hb ⟨k, List.mem_map.mpr ⟨z, hz, by rw [← hi, hk]⟩⟩
  have h1 := prob_le_add
    (p := fun ω : (Θ × (Fin qs → Rnd)) × (D → W) => win ω.1.1 ω.2 fun i => ω.2 (p ω.1.2 i))
    (q := fun ω => ¬Injective ω.1.2)
    (r := fun ω => Injective ω.1.2 ∧ win ω.1.1 ω.2 fun i => ω.2 (p ω.1.2 i))
    fun ω hω => by
      by_cases h : Injective ω.1.2
      · exact Or.inr ⟨h, hω⟩
      · exact Or.inl h
  have h2 : prob (fun ω : (Θ × (Fin qs → Rnd)) × (D → W) => ¬Injective ω.1.2) ≤
      (qs : ℝ) ^ 2 / Fintype.card Rnd :=
    prob_prod_le _ _ (by positivity) fun G =>
      prob_prod_le' (fun a : Θ × (Fin qs → Rnd) => ¬Injective a.2) _
        (by positivity) fun θ => prob_not_injective
  have h3 : prob (fun ω : (Θ × (Fin qs → Rnd)) × (D → W) =>
      Injective ω.1.2 ∧ win ω.1.1 ω.2 fun i => ω.2 (p ω.1.2 i)) ≤
      prob (fun s : (Θ × (Fin qs → Rnd)) × ((D → W) × (ι → W)) =>
        ideal (moveLast s).1 ∨ bad (moveLast s)) + 0 := by
    refine prob_prod_mono _ _ 0 le_rfl fun a => ?_
    rw [add_zero]
    by_cases hinj : Injective a.2
    · refine le_trans (prob_mono ?_) (hreal a.1 a.2 hinj)
      intro G h
      exact h.2
    · have h0 : prob (fun _ : D → W => False) = 0 := by
        unfold prob
        simp
      refine le_trans (prob_mono (q := fun _ => False) ?_) (h0.le.trans (prob_nonneg _))
      intro G h
      exact hinj h.1
  rw [add_zero] at h3
  have h4 := prob_le_add
    (p := fun s : (Θ × (Fin qs → Rnd)) × ((D → W) × (ι → W)) =>
      ideal (moveLast s).1 ∨ bad (moveLast s))
    (q := fun s => ideal (moveLast s).1) (r := fun s => bad (moveLast s)) fun s h => h
  have h5 : prob (fun s : (Θ × (Fin qs → Rnd)) × ((D → W) × (ι → W)) =>
      ideal (moveLast s).1) = prob ideal := by
    rw [prob_equiv moveLast (fun t => ideal t.1)]
    exact prob_fst ideal
  have h6 : prob (fun s : (Θ × (Fin qs → Rnd)) × ((D → W) × (ι → W)) => bad (moveLast s)) ≤
      qs * (qn / Fintype.card Rnd) := by
    rw [prob_equiv moveLast bad]
    refine prob_prod_le' bad _ (by positivity) fun a => ?_
    have hh := prob_hit (qs := qs) ((log a.1.1 a.1.2 a.2).map key)
    have hl : ((log a.1.1 a.1.2 a.2).map key).length ≤ qn := by
      rw [List.length_map]
      exact hlen _ _ _
    refine hh.trans ?_
    gcongr
  calc _ ≤ (qs : ℝ) ^ 2 / Fintype.card Rnd + (prob ideal + qs * (qn / Fintype.card Rnd)) :=
        h1.trans (add_le_add h2 (h3.trans (h4.trans (add_le_add (le_of_eq h5) h6))))
    _ = _ := by ring

end Hop

end Dahlias
