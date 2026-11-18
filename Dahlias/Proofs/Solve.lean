import Dahlias.Proofs.Extract

/-!
# Solving for the session nonces

`run_solveSessions`: after the two runs the reduction asks, for every session,
as many discrete logarithm queries as it needs to have two, and then knows both
nonces of every session as a function of the secret key.
-/

set_option linter.unusedSectionVars false

namespace Dahlias.Security

open Taproot Function

variable {n : ℕ} [Fact n.Prime] {E X M : Type} [AddCommGroup E] [DecidableEq E] [DecidableEq X]
  [DecidableEq M] (C : Curve n E X) (qs : ℕ) (xu : (ZMod n)ˣ)
  (ν : Fin qs → (ZMod n)ˣ × (ZMod n)ˣ)

/-- The entries of session `k`. -/
abbrev entries (k : ℕ) (cache : List (CloseRec n E X M)) : List (CloseRec n E X M) :=
  cache.filter fun r => decide (r.k = k)

set_option linter.flexible false in
theorem run_solveSession {k : ℕ} (hk : k < qs) (cache : List (CloseRec n E X M)) (d : ℕ)
    (hsig : ∀ r ∈ cache, RecSig C qs xu ν r)
    (hb : ∀ a a' rest, entries k cache = a :: a' :: rest → a.Rb.2 ≠ a'.Rb.2) :
    let res := (solveSession C qs (C.mulG (xu : ZMod n)) k cache).run
      (omdlChallenger C (merge xu ν)) (2 * qs + 1, d)
    res.1 xu = noncesOf qs ν ⟨k, hk⟩ ∧ res.2.1 = 2 * qs + 1 ∧
      res.2.2 + min 2 (entries k cache).length = d + 2 := by
  have hw : ∀ a ∈ entries k cache, a.w C (C.mulG (xu : ZMod n)) xu =
      (noncesOf qs ν ⟨k, hk⟩).1 + a.Rb.2 * (noncesOf qs ν ⟨k, hk⟩).2 := by
    intro a ha
    obtain ⟨hac, hak⟩ := List.mem_filter.mp ha
    simp only [decide_eq_true_eq] at hak
    obtain ⟨hk', hw⟩ := CloseRec.w_eq C qs xu ν (hsig a hac)
    have : (⟨a.k, hk'⟩ : Fin qs) = ⟨k, hk⟩ := Fin.ext hak
    rw [hw, this]
  unfold solveSession
  rcases he : entries k cache with _ | ⟨a, _ | ⟨a', rest⟩⟩
  · simp only [he, run_dlog, Alg.run_done, chalLogs_eq, zero_add]
    rw [coefVec_eval _ _ _ (by simp; omega), coefVec_eval _ _ _ (by simp; omega)]
    simp [logAt_merge_odd xu ν hk, logAt_merge_even xu ν hk, noncesOf]
  · have hwa := hw a (by rw [he]; simp)
    simp only [he, run_dlog, Alg.run_done, chalLogs_eq, zero_add]
    rw [coefVec_eval _ _ _ (by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> simp <;> omega)]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      logAt_merge_odd xu ν hk, logAt_merge_even xu ν hk, hwa, List.length_cons, List.length_nil]
    refine ⟨?_, trivial, by omega⟩
    simp only [noncesOf]
    refine Prod.ext ?_ ?_ <;> simp <;> ring
  · have hwa := hw a (by rw [he]; simp)
    have hwa' := hw a' (by rw [he]; simp)
    have hbb : a.Rb.2 - a'.Rb.2 ≠ 0 := sub_ne_zero.mpr (hb a a' rest he)
    simp only [he, Alg.run_done, hwa, hwa', List.length_cons]
    refine ⟨?_, trivial, by omega⟩
    refine Prod.ext ?_ ?_ <;> simp <;> (field_simp; try ring)

/-- Splitting the entries below `K + 1`. -/
theorem length_filter_lt_succ (cache : List (CloseRec n E X M)) (K : ℕ) :
    (cache.filter fun r => decide (r.k < K + 1)).length =
      (cache.filter fun r => decide (r.k < K)).length + (entries K cache).length := by
  induction cache with
  | nil => rfl
  | cons r cache ih =>
    simp only [List.filter_cons, entries, decide_eq_true_eq] at ih ⊢
    split_ifs <;> (try simp only [List.length_cons]) <;> omega

/-- **The reduction solves for all session nonces with two discrete logarithm
queries per session.** -/
theorem run_solveSessions (cache : List (CloseRec n E X M))
    (hsig : ∀ r ∈ cache, RecSig C qs xu ν r)
    (hlen : ∀ k, (entries k cache).length ≤ 2)
    (hb : ∀ k a a' rest, entries k cache = a :: a' :: rest → a.Rb.2 ≠ a'.Rb.2)
    (K : ℕ) (hK : K ≤ qs) (d : ℕ) :
    let res := (solveSessions C qs (C.mulG (xu : ZMod n)) cache K).run
      (omdlChallenger C (merge xu ν)) (2 * qs + 1, d)
    res.1.length = K ∧
      (∀ k (hk : k < K), (res.1.getD k fun _ => (0, 0)) xu = noncesOf qs ν ⟨k, by omega⟩) ∧
      res.2.1 = 2 * qs + 1 ∧
      res.2.2 + (cache.filter fun r => decide (r.k < K)).length = d + 2 * K := by
  induction K with
  | zero => simp [solveSessions]
  | succ K ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih (by omega)
    set res := (solveSessions C qs (C.mulG (xu : ZMod n)) cache K).run
      (omdlChallenger C (merge xu ν)) (2 * qs + 1, d) with hres
    have hst : res.2 = (2 * qs + 1, res.2.2) := Prod.ext h3 rfl
    obtain ⟨g1, g2, g3⟩ := run_solveSession C qs xu ν (k := K) (by omega) cache res.2.2 hsig
      (hb K)
    simp only [solveSessions, Alg.run_bind, Alg.run_done, ← hres]
    rw [hst]
    refine ⟨by simp [h1], ?_, g2, ?_⟩
    · intro k hk
      by_cases hkK : k < K
      · rw [List.getD_append _ _ _ _ (by omega)]
        exact h2 k hkK
      · have : k = K := by omega
        subst this
        rw [List.getD_append_right _ _ _ _ (by omega)]
        simpa [h1] using g1
    · rw [length_filter_lt_succ]
      have := hlen K
      omega

end Dahlias.Security
