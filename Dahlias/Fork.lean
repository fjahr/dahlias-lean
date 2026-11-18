import Dahlias.LocalFork
import Dahlias.QueryRun
import Dahlias.Prob

/-!
# The local forking lemma for query algorithms

`QTree.localFork`: the local forking lemma for a deterministic algorithm with
adaptive queries (`QTree`) that makes at most `q` different queries. The
algorithm accepts on `T` if `sel`, which sees `T` and the output, selects a
point `z` that the algorithm queried.
The fork succeeds on `(T, s)` if it accepts on `T` with `z`, accepts with the
same `z` on the function that has `s` at `z`, and `s` differs from `T z`.
-/

namespace Dahlias.QTree

open Finset Function LocalFork

variable {D S α : Type} [Fintype D] [DecidableEq D] [Fintype S] [DecidableEq S]
  (t : QTree D S α) (sel : (D → S) → α → Option D)

/-- The algorithm accepts on `T`: its output selects one of its queries. -/
def Accepts (T : D → S) : Prop := ∃ z, sel T (eval T t) = some z ∧ z ∈ fresh T t

/-- The fork succeeds on `(T, s)`. -/
def Forks (T : D → S) (s : S) : Prop :=
  ∃ z, sel T (eval T t) = some z ∧ z ∈ fresh T t ∧
    sel (update T z s) (eval (update T z s) t) = some z ∧ s ≠ T z

/-- The index of the selected query among the fresh queries. -/
def selIdx (q : ℕ) (T : D → S) : Option (Fin q) :=
  (sel T (eval T t)).bind fun z =>
    if h : z ∈ fresh T t ∧ (fresh T t).idxOf z < q then some ⟨(fresh T t).idxOf z, h.2⟩ else none

omit [Fintype D] [Fintype S] [DecidableEq S] in
theorem selIdx_eq_some {q : ℕ} {T : D → S} {i : Fin q} (h : selIdx t sel q T = some i) :
    ∃ z, sel T (eval T t) = some z ∧ z ∈ fresh T t ∧ (fresh T t)[(i : ℕ)]? = some z := by
  unfold selIdx at h
  obtain ⟨z, hz, h⟩ := Option.bind_eq_some_iff.mp h
  split_ifs at h with hm
  cases h
  exact ⟨z, hz, hm.1, by simp [List.getElem?_idxOf hm.1]⟩

open Classical in
/-- **The local forking lemma for query algorithms**, as a count over all
functions `T` and new values `s`. -/
theorem localFork {q : ℕ} (hq : ∀ T, (fresh T t).length ≤ q) :
    (Fintype.card S : ℝ) * (∑ T, if Accepts t sel T then (1 : ℝ) else 0) ^ 2 ≤
      q * Fintype.card (D → S) *
        ((∑ T, ∑ s, if Forks t sel T s then (1 : ℝ) else 0) +
          ∑ T, if Accepts t sel T then (1 : ℝ) else 0) := by
  have hacc : accCount (selIdx t sel q) = ∑ T, if Accepts t sel T then (1 : ℝ) else 0 := by
    refine Finset.sum_congr rfl fun T _ => ?_
    have : (selIdx t sel q T).isSome ↔ Accepts t sel T := by
      constructor
      · intro h
        obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp h
        obtain ⟨z, hz, hm, -⟩ := selIdx_eq_some t sel hi
        exact ⟨z, hz, hm⟩
      · rintro ⟨z, hz, hm⟩
        have hlt : (fresh T t).idxOf z < q := (List.idxOf_lt_length_of_mem hm).trans_le (hq T)
        simp [selIdx, hz, hm, hlt]
    simp only [this]
  have hfork : forkCount (selIdx t sel q) (fun i T => (fresh T t)[(i : ℕ)]?) ≤
      ∑ T, ∑ s, if Forks t sel T s then (1 : ℝ) else 0 := by
    refine Finset.sum_le_sum fun T _ => Finset.sum_le_sum fun s _ => ?_
    split_ifs with h1 h2 h2
    · exact le_rfl
    · exfalso
      obtain ⟨i, d, hi, hd, hi', hs⟩ := h1
      obtain ⟨z, hz, hm, hzi⟩ := selIdx_eq_some t sel hi
      obtain ⟨z', hz', -, hzi'⟩ := selIdx_eq_some t sel hi'
      have hdz : d = z := Option.some.inj (hd.symm.trans hzi)
      subst hdz
      have := fresh_update T d s t hzi
      have hzz : z' = d := Option.some.inj (hzi'.symm.trans this)
      subst hzz
      exact h2 ⟨z', hz, hm, hz', hs⟩
    · exact zero_le_one
    · exact le_rfl
  have h := LocalFork.localFork (selIdx t sel q) (fun i T => (fresh T t)[(i : ℕ)]?)
    (fun i T hi => by
      obtain ⟨z, -, -, hzi⟩ := selIdx_eq_some t sel hi
      simp [hzi])
    (fun i T d s hd => fresh_update T d s t hd)
  rw [hacc] at h
  refine h.trans ?_
  gcongr

/-- **The local forking lemma for a family of query algorithms**, as
probabilities. The sample is an index `ω`, a function `T` and a new value
`s`, all uniform; `ω` stands for everything else that is random. With `acc`
the probability of accepting, `acc * (acc / q - 1 / |S|) ≤ fork`. -/
theorem localFork_prob {Ω : Type} [Fintype Ω] [Nonempty S] {q : ℕ} (hq0 : 0 < q)
    (t : Ω → QTree D S α) (sel : Ω → (D → S) → α → Option D)
    (hq : ∀ ω T, (fresh T (t ω)).length ≤ q) :
    let acc := prob fun p : Ω × (D → S) => Accepts (t p.1) (sel p.1) p.2
    acc * (acc / q - 1 / Fintype.card S) ≤
      prob fun p : (Ω × (D → S)) × S => Forks (t p.1.1) (sel p.1.1) p.1.2 p.2 := by
  classical
  intro acc
  set σ : ℝ := (Fintype.card S : ℝ)
  set Mt : ℝ := (Fintype.card (D → S) : ℝ)
  set K : ℝ := (Fintype.card Ω : ℝ)
  set a : Ω → ℝ := fun ω => ∑ T, if Accepts (t ω) (sel ω) T then (1 : ℝ) else 0
  set F : Ω → ℝ := fun ω => ∑ T, ∑ s, if Forks (t ω) (sel ω) T s then (1 : ℝ) else 0
  have hacc : acc = (∑ ω, a ω) / (K * Mt) := by
    simp only [acc, prob_eq_sum, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul]
    rfl
  have hfork : (prob fun p : (Ω × (D → S)) × S => Forks (t p.1.1) (sel p.1.1) p.1.2 p.2) =
      (∑ ω, F ω) / (K * Mt * σ) := by
    simp only [prob_eq_sum, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul]
    rfl
  have hσ : 0 < σ := Nat.cast_pos.mpr Fintype.card_pos
  have hMt : 0 < Mt := Nat.cast_pos.mpr Fintype.card_pos
  have hq' : (0 : ℝ) < q := Nat.cast_pos.mpr hq0
  have ha0 : ∀ ω, 0 ≤ a ω := fun ω => Finset.sum_nonneg fun T _ => by split_ifs <;> simp
  have hF0 : ∀ ω, 0 ≤ F ω := fun ω =>
    Finset.sum_nonneg fun T _ => Finset.sum_nonneg fun s _ => by split_ifs <;> simp
  rcases isEmpty_or_nonempty Ω with hΩ | hΩ
  · have : acc = 0 := by rw [hacc]; simp
    rw [this, zero_mul]
    exact prob_nonneg _
  have hK : 0 < K := Nat.cast_pos.mpr Fintype.card_pos
  -- the lemma for every index, summed, with the Cauchy-Schwarz inequality
  have hone : ∀ ω, σ * a ω ^ 2 ≤ q * Mt * (F ω + a ω) := fun ω => localFork (t ω) (sel ω) (hq ω)
  have hsum : σ * ∑ ω, a ω ^ 2 ≤ q * Mt * ((∑ ω, F ω) + ∑ ω, a ω) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_le_sum fun ω _ => hone ω
  have hcs : (∑ ω, a ω) ^ 2 ≤ K * ∑ ω, a ω ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset Ω)) (f := a)
    simpa [K, Finset.card_univ] using this
  have hmain : σ * (∑ ω, a ω) ^ 2 ≤ K * (q * Mt * ((∑ ω, F ω) + ∑ ω, a ω)) := by
    calc σ * (∑ ω, a ω) ^ 2 ≤ σ * (K * ∑ ω, a ω ^ 2) := by gcongr
      _ = K * (σ * ∑ ω, a ω ^ 2) := by ring
      _ ≤ K * (q * Mt * ((∑ ω, F ω) + ∑ ω, a ω)) := by gcongr
  rw [hfork, hacc]
  have key : (∑ ω, F ω) / (K * Mt * σ) -
      (∑ ω, a ω) / (K * Mt) * ((∑ ω, a ω) / (K * Mt) / q - 1 / σ) =
      (K * (q * Mt * ((∑ ω, F ω) + ∑ ω, a ω)) - σ * (∑ ω, a ω) ^ 2) /
        (K ^ 2 * Mt ^ 2 * q * σ) := by
    field_simp
    ring
  rw [← sub_nonneg, key]
  exact div_nonneg (sub_nonneg.mpr hmain) (by positivity)

end Dahlias.QTree
