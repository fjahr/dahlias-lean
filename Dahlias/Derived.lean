import Dahlias.Lazy
import Dahlias.NonceProb
import Dahlias.Proofs.ForkGame

/-!
# The nonce of a single-party signature

In the game a single-party signature uses the first nonce `r₁` of its slot.
The reduction to AOMDL needs the form `r₁ + b⋅r₂` with a coefficient `b`
derived from the signed list (`singleNonce true`): it runs the adversary
twice, and with that form two signatures of the same slot for different lists
give two independent equations in `r₁` and `r₂`.

`forgeAdvantage_le_derived`: the adversary wins the game at most `qs / (n - 1)`
more often than the game with the derived nonce. For a uniform pair
`(r₁, r₂)` of nonzero scalars, `r₁ + b⋅r₂` is uniform over the nonzero scalars
except when it is zero, and the coefficient is fixed before the slot's nonces
are read.

The proof views the nonces as an oracle that the game queries by slot and
compares the two games query by query with lazily sampled nonces (`exL`).
-/

set_option linter.unusedSectionVars false
set_option linter.deprecated false

namespace Dahlias.Security

open Taproot QTree Finset Function

variable {n : ℕ} [Fact n.Prime] {E X M : Type} [AddCommGroup E] [DecidableEq E] [DecidableEq X]
  [DecidableEq M] (der : Bool) (C : Curve n E X)
  (nonceCoef : E → E → List (X × M × E) → ZMod n) (N qs : ℕ) (x : ZMod n)
  (T : SigIn N X M → ZMod n)

/-- A pair of nonzero nonces. -/
abbrev NPair (n : ℕ) := (ZMod n)ˣ × (ZMod n)ˣ

/-! ## The game with the nonces as an oracle -/

/-- The slot whose nonces a query reads, if it reads any. -/
def needs (qs : ℕ) : AdvQ n N E X M → SignerState X M → Option (Fin qs)
  | .hash _, _ => none
  | .openSession, st => if h : st.opened < qs then some ⟨st.opened, h⟩ else none
  | .close k _ _ _ _ _, st =>
    if h : k < qs ∧ k < st.opened ∧ k ∉ st.closed then some ⟨k, h.1⟩ else none
  | .single _, st => if h : st.opened < qs then some ⟨st.opened, h⟩ else none

/-- The same nonces in every slot. -/
def constN (qs : ℕ) (y : NPair n) : Fin qs → SecNonce n := fun _ => ((y.1 : ZMod n), (y.2 : ZMod n))

/-- `challengerG`, with the nonces as an oracle. -/
def nonceChallenger (q : AdvQ n N E X M) (st : SignerState X M) :
    QTree (Fin qs) (NPair n) (AdvR q × SignerState X M) :=
  match needs N qs q st with
  | some k => .ask k fun y => .done (challengerG der C nonceCoef N qs x (constN qs y) T q st)
  | none => .done (challengerG der C nonceCoef N qs x (fun _ => (0, 0)) T q st)

theorem nonceChallenger_none {q : AdvQ n N E X M} {st : SignerState X M}
    (h : needs N qs q st = none) :
    nonceChallenger der C nonceCoef N qs x T q st =
      .done (challengerG der C nonceCoef N qs x (fun _ => (0, 0)) T q st) := by
  unfold nonceChallenger
  rw [h]

theorem nonceChallenger_some {q : AdvQ n N E X M} {st : SignerState X M} {k : Fin qs}
    (h : needs N qs q st = some k) :
    nonceChallenger der C nonceCoef N qs x T q st =
      .ask k fun y => .done (challengerG der C nonceCoef N qs x (constN qs y) T q st) := by
  unfold nonceChallenger
  rw [h]

/-- The game's answer to a single-party signing query with the nonce `r`. -/
def singleStep (items : List (Tweak n × M)) (st : SignerState X M) (r : ZMod n) :
    Option (X × ZMod n) × SignerState X M :=
  if hc : items ≠ [] ∧ (singleKeys C x items).length ≤ N ∧ r ≠ 0 ∧
      ∀ i ∈ items, i.1.2 ≠ 0 ∧ i.1.sk x ≠ 0 then
    (some (C.x (C.mulG r), singleS C x items r ((singleKeys C x items).map fun e =>
        T (⟨singleKeys C x items, hc.2.1⟩, C.x (C.mulG r), e))),
      { opened := st.opened + 1
        closed := st.opened :: st.closed
        signed := (singleKeys C x items).map (fun e => (singleKeys C x items, e.1, e.2)) ++
          st.signed })
  else (none, { st with opened := st.opened + 1, closed := st.opened :: st.closed })

theorem challengerG_single (nonces : Fin qs → SecNonce n) (items : List (Tweak n × M))
    (st : SignerState X M) (h : st.opened < qs) :
    challengerG der C nonceCoef N qs x nonces T (.single items) st =
      singleStep C N x T items st
        (singleNonce der nonceCoef (singleKeys C x items) (nonces ⟨st.opened, h⟩)) := by
  unfold challengerG singleStep
  simp only [h, ↓reduceDIte]
  rfl

theorem singleStep_state (items : List (Tweak n × M)) (st : SignerState X M) (r : ZMod n) :
    (singleStep C N x T items st r).2.opened = st.opened + 1 ∧
      (singleStep C N x T items st r).2.closed = st.opened :: st.closed := by
  unfold singleStep
  split_ifs <;> exact ⟨rfl, rfl⟩

/-- A query that reads no nonces is answered alike in both games and leaves
the state as it is. -/
theorem challengerG_of_needs_none (nonces nonces' : Fin qs → SecNonce n) (q : AdvQ n N E X M)
    (st : SignerState X M) (h : needs N qs q st = none) :
    challengerG der C nonceCoef N qs x nonces T q st =
        challengerG false C nonceCoef N qs x nonces' T q st ∧
      (challengerG false C nonceCoef N qs x nonces' T q st).2 = st := by
  cases q with
  | hash z => exact ⟨rfl, rfl⟩
  | openSession =>
    have ho : ¬st.opened < qs := fun ho => by simp [needs, ho] at h
    simp [challengerG, ho]
  | close k τ m agg pm pubnonces =>
    have hc : ¬(k < qs ∧ k < st.opened ∧ k ∉ st.closed) := fun hc => by simp [needs, hc] at h
    have hc' : ¬(k < qs ∧ k < st.opened ∧ k ∉ st.closed ∧ τ.2 ≠ 0 ∧ pm.length ≤ N) :=
      fun h' => hc ⟨h'.1, h'.2.1, h'.2.2.1⟩
    simp [challengerG, hc']
  | single items =>
    have ho : ¬st.opened < qs := fun ho => by simp [needs, ho] at h
    simp [challengerG, ho]

/-- On a table of nonces the oracle version is the game. -/
theorem eval_nonceChallenger (ν : Fin qs → NPair n) (q : AdvQ n N E X M)
    (st : SignerState X M) :
    eval ν (nonceChallenger der C nonceCoef N qs x T q st) =
      challengerG der C nonceCoef N qs x (noncesOf qs ν) T q st := by
  unfold nonceChallenger
  cases hn : needs N qs q st with
  | none =>
    exact ((challengerG_of_needs_none der C nonceCoef N qs x T _ (fun _ => (0, 0)) q st hn).1.trans
      (challengerG_of_needs_none der C nonceCoef N qs x T (noncesOf qs ν) _ q st hn).1.symm)
  | some k =>
    change challengerG der C nonceCoef N qs x (constN qs (ν k)) T q st = _
    cases q with
    | hash z => rfl
    | openSession =>
      by_cases ho : st.opened < qs
      · simp only [needs, ho, ↓reduceDIte, Option.some.injEq] at hn
        subst hn
        simp [challengerG, ho, constN, noncesOf]
      · simp [needs, ho] at hn
    | close j τ m agg pm pubnonces =>
      by_cases hc : j < qs ∧ j < st.opened ∧ j ∉ st.closed
      · have hk : k = ⟨j, hc.1⟩ := by
          have : needs N qs (.close j τ m agg pm pubnonces) st = some ⟨j, hc.1⟩ := by
            unfold needs
            exact dif_pos hc
          exact Option.some.inj (hn.symm.trans this)
        subst hk
        unfold challengerG
        dsimp only
        by_cases hc' : j < qs ∧ j < st.opened ∧ j ∉ st.closed ∧ τ.2 ≠ 0 ∧ pm.length ≤ N
        · rw [dif_pos hc', dif_pos hc']
          rfl
        · rw [dif_neg hc', dif_neg hc']
      · simp [needs, hc] at hn
    | single items =>
      by_cases ho : st.opened < qs
      · simp only [needs, ho, ↓reduceDIte, Option.some.injEq] at hn
        subst hn
        rw [challengerG_single der C nonceCoef N qs x T _ items st ho,
          challengerG_single der C nonceCoef N qs x T _ items st ho]
        rfl
      · simp [needs, ho] at hn

/-! ## One slot: a uniform nonce against the derived one -/

open Classical in
/-- Summing over the nonce pairs of a slot: a function of `r₁` against a
function of `r₁ + β⋅r₂`. The pairs with `r₁ = β⋅r₂` have no partner. -/
theorem sum_twist (β : ZMod n) (H₁ H₂ : ZMod n → NPair n → ℝ) (e : ℝ) (he : 0 ≤ e)
    (hIH : ∀ r y y', H₁ r y ≤ H₂ r y' + e) (h0 : ∀ r y, 0 ≤ H₂ r y) (h1 : ∀ r y, H₁ r y ≤ 1) :
    (∑ y : NPair n, H₁ y.1 y) / Fintype.card (NPair n) ≤
      (∑ y : NPair n, H₂ (y.1 + β * y.2) y) / Fintype.card (NPair n) + e +
        1 / Fintype.card (ZMod n)ˣ := by
  have hc : (0 : ℝ) < Fintype.card (ZMod n)ˣ := Nat.cast_pos.mpr Fintype.card_pos
  have hc2 : (Fintype.card (NPair n) : ℝ) = Fintype.card (ZMod n)ˣ * Fintype.card (ZMod n)ˣ := by
    rw [Fintype.card_prod, Nat.cast_mul]
  have hc2pos : (0 : ℝ) < Fintype.card (NPair n) := by rw [hc2]; positivity
  let bad : NPair n → Prop := fun y => (y.1 : ZMod n) - β * y.2 = 0
  let φ : NPair n → NPair n := fun y =>
    if h : (y.1 : ZMod n) - β * y.2 = 0 then y else (Units.mk0 _ h, y.2)
  let K : NPair n → ℝ := fun z => H₂ (z.1 + β * z.2) z
  have hφ' : ∀ y, ¬bad y → ∃ h : (y.1 : ZMod n) - β * y.2 ≠ 0, φ y = (Units.mk0 _ h, y.2) :=
    fun y hy => ⟨hy, dif_neg hy⟩
  have hφ : ∀ y, ¬bad y → ((φ y).1 : ZMod n) + β * (φ y).2 = y.1 := by
    intro y hy
    obtain ⟨h, hy'⟩ := hφ' y hy
    rw [hy']
    simp
  -- every pair against its partner
  have hpt : ∀ y : NPair n, H₁ y.1 y ≤
      (if bad y then 1 else 0) + (if ¬bad y then K (φ y) else 0) + e := by
    intro y
    by_cases hy : bad y
    · simp only [hy, ↓reduceIte, not_true_eq_false]
      linarith [h1 y.1 y]
    · simp only [hy, ↓reduceIte, not_false_eq_true, K, hφ y hy]
      linarith [hIH y.1 y (φ y)]
  -- the pairs without a partner
  have hbad : (∑ y : NPair n, if bad y then (1 : ℝ) else 0) ≤ Fintype.card (ZMod n)ˣ := by
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
    have : (univ.filter bad).card ≤ (univ : Finset (ZMod n)ˣ).card := by
      refine card_le_card_of_injOn (fun y => y.2) (fun _ _ => mem_univ _) ?_
      intro y hy y' hy' h2
      have hb : (y.1 : ZMod n) - β * y.2 = 0 := (mem_filter.mp hy).2
      have hb' : (y'.1 : ZMod n) - β * y'.2 = 0 := (mem_filter.mp hy').2
      have h2' : y.2 = y'.2 := h2
      refine Prod.ext (Units.ext ?_) h2'
      rw [sub_eq_zero] at hb hb'
      rw [hb, hb', h2']
    exact_mod_cast this
  -- the partners are different pairs
  have hgood : (∑ y : NPair n, if ¬bad y then K (φ y) else 0) ≤ ∑ z : NPair n, K z := by
    rw [← sum_filter]
    have hinj : Set.InjOn φ (univ.filter fun y => ¬bad y : Finset (NPair n)) := by
      intro y hy y' hy' heq
      obtain ⟨h, e1⟩ := hφ' y (mem_filter.mp hy).2
      obtain ⟨h', e2⟩ := hφ' y' (mem_filter.mp hy').2
      rw [e1, e2] at heq
      have h2 : y.2 = y'.2 := (Prod.mk.inj heq).2
      have h1' : (y.1 : ZMod n) - β * y.2 = (y'.1 : ZMod n) - β * y'.2 :=
        congrArg Units.val (Prod.mk.inj heq).1
      refine Prod.ext (Units.ext ?_) h2
      rw [h2] at h1'
      exact sub_left_injective h1'
    rw [← sum_image hinj]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun z _ _ => h0 _ _
  have hsum : ∑ y : NPair n, H₁ y.1 y ≤
      Fintype.card (ZMod n)ˣ + ∑ z : NPair n, K z + Fintype.card (NPair n) * e := by
    calc ∑ y : NPair n, H₁ y.1 y
        ≤ ∑ y : NPair n, ((if bad y then 1 else 0) + (if ¬bad y then K (φ y) else 0) + e) :=
          sum_le_sum fun y _ => hpt y
      _ = (∑ y : NPair n, if bad y then (1 : ℝ) else 0) +
            (∑ y : NPair n, if ¬bad y then K (φ y) else 0) + Fintype.card (NPair n) * e := by
          rw [sum_add_distrib, sum_add_distrib]
          simp
      _ ≤ _ := by linarith
  rw [div_le_iff₀ hc2pos]
  have h3 : ((∑ y : NPair n, H₂ (y.1 + β * y.2) y) / Fintype.card (NPair n) + e +
      1 / Fintype.card (ZMod n)ˣ) * Fintype.card (NPair n) =
      ∑ z : NPair n, K z + Fintype.card (NPair n) * e + Fintype.card (ZMod n)ˣ := by
    rw [hc2]
    field_simp
    rfl
  rw [h3]
  linarith

/-! ## The two games, query by query -/

/-- The memories of the two games: slots that are open have the same nonces in
both, slots that are not opened yet have none. Closed slots may differ. -/
def NRel (st : SignerState X M) (μ₁ μ₂ : List (Fin qs × NPair n)) : Prop :=
  st.opened ≤ qs ∧ (∀ j ∈ st.closed, j < st.opened) ∧
    (∀ k : Fin qs, k.val < st.opened → k.val ∉ st.closed →
      ∃ y, memo μ₁ k = some y ∧ memo μ₂ k = some y) ∧
    ∀ k : Fin qs, st.opened ≤ k.val → memo μ₁ k = none ∧ memo μ₂ k = none

/-- A slot is opened and its nonces are read; it stays open or is closed at once. -/
theorem NRel.step {st st' : SignerState X M} {μ₁ μ₂ : List (Fin qs × NPair n)}
    (h : NRel qs st μ₁ μ₂) (ho : st.opened < qs) (y y' : NPair n)
    (h1 : st'.opened = st.opened + 1)
    (h2 : st'.closed = st.closed ∧ y = y' ∨ st'.closed = st.opened :: st.closed) :
    NRel qs st' (μ₁ ++ [(⟨st.opened, ho⟩, y)]) (μ₂ ++ [(⟨st.opened, ho⟩, y')]) := by
  obtain ⟨-, hcl, hopen, hnew⟩ := h
  refine ⟨by omega, ?_, ?_, ?_⟩
  · intro j hj
    rcases h2 with ⟨h2, -⟩ | h2
    · rw [h2] at hj
      have := hcl j hj
      omega
    · rw [h2] at hj
      rcases List.mem_cons.mp hj with rfl | hj
      · omega
      · have := hcl j hj
        omega
  · intro k hk hkc
    by_cases hks : k.val = st.opened
    · have hk' : k = ⟨st.opened, ho⟩ := Fin.ext hks
      subst hk'
      rcases h2 with ⟨-, rfl⟩ | h2
      · exact ⟨y, memo_append_self (hnew _ le_rfl).1 y, memo_append_self (hnew _ le_rfl).2 y⟩
      · exact absurd (by rw [h2]; simp) hkc
    · have hne : (⟨st.opened, ho⟩ : Fin qs) ≠ k := fun h => hks (congrArg Fin.val h).symm
      rw [memo_append_ne hne, memo_append_ne hne]
      refine hopen k (by omega) fun hm => hkc ?_
      rcases h2 with ⟨h2, -⟩ | h2 <;> rw [h2]
      · exact hm
      · exact List.mem_cons_of_mem _ hm
  · intro k hk
    have hne : (⟨st.opened, ho⟩ : Fin qs) ≠ k := fun h => by
      have := congrArg Fin.val h
      simp only at this
      omega
    rw [memo_append_ne hne, memo_append_ne hne]
    exact hnew k (by omega)

/-- A session is closed, or nothing changes. -/
theorem NRel.close {st st' : SignerState X M} {μ₁ μ₂ : List (Fin qs × NPair n)}
    (h : NRel qs st μ₁ μ₂) (h1 : st'.opened = st.opened) {j : ℕ} (hj : j < st.opened)
    (h2 : st'.closed = st.closed ∨ st'.closed = j :: st.closed) : NRel qs st' μ₁ μ₂ := by
  obtain ⟨hq, hcl, hopen, hnew⟩ := h
  refine ⟨by omega, ?_, ?_, ?_⟩
  · intro i hi
    rcases h2 with h2 | h2 <;> rw [h2] at hi
    · have := hcl i hi
      omega
    · rcases List.mem_cons.mp hi with rfl | hi
      · omega
      · have := hcl i hi
        omega
  · intro k hk hkc
    refine hopen k (by omega) fun hm => hkc ?_
    rcases h2 with h2 | h2 <;> rw [h2]
    · exact hm
    · exact List.mem_cons_of_mem _ hm
  · intro k hk
    exact hnew k (by omega)

theorem close_state (nonces : Fin qs → SecNonce n) (j : ℕ) (τ : Tweak n) (m : M)
    (agg : PubNonce E) (pm : List (X × M)) (pubnonces : List (PubNonce E))
    (st : SignerState X M) :
    (challengerG der C nonceCoef N qs x nonces T (.close j τ m agg pm pubnonces) st).2.opened =
        st.opened ∧
      ((challengerG der C nonceCoef N qs x nonces T (.close j τ m agg pm pubnonces) st).2.closed =
          st.closed ∨
        (challengerG der C nonceCoef N qs x nonces T (.close j τ m agg pm pubnonces)
          st).2.closed = j :: st.closed) := by
  unfold challengerG
  dsimp only
  split_ifs with h
  · rcases sign C.ops (hashesOf N nonceCoef T) (nonces ⟨j, h.1⟩) (τ.sk x) m agg pm pubnonces
      with _ | s
    · exact ⟨rfl, Or.inl rfl⟩
    · exact ⟨rfl, Or.inr rfl⟩
  · exact ⟨rfl, Or.inl rfl⟩

/-- A query that reads the nonces of a slot is answered alike for nonces that
agree on that slot. -/
theorem challengerG_of_needs_some (nonces nonces' : Fin qs → SecNonce n) (q : AdvQ n N E X M)
    (st : SignerState X M) {k : Fin qs} (h : needs N qs q st = some k)
    (hk : nonces k = nonces' k) :
    challengerG der C nonceCoef N qs x nonces T q st =
      challengerG der C nonceCoef N qs x nonces' T q st := by
  cases q with
  | hash z => rfl
  | openSession =>
    by_cases ho : st.opened < qs
    · simp only [needs, ho, ↓reduceDIte, Option.some.injEq] at h
      subst h
      simp only [challengerG, ho, ↓reduceDIte, hk]
    · simp [needs, ho] at h
  | close j τ m agg pm pubnonces =>
    by_cases hc : j < qs ∧ j < st.opened ∧ j ∉ st.closed
    · have hk' : k = ⟨j, hc.1⟩ := by
        have : needs N qs (.close j τ m agg pm pubnonces) st = some ⟨j, hc.1⟩ := by
          unfold needs
          exact dif_pos hc
        exact Option.some.inj (h.symm.trans this)
      subst hk'
      unfold challengerG
      dsimp only
      by_cases hc' : j < qs ∧ j < st.opened ∧ j ∉ st.closed ∧ τ.2 ≠ 0 ∧ pm.length ≤ N
      · rw [dif_pos hc', dif_pos hc', hk]
      · rw [dif_neg hc', dif_neg hc']
    · have : needs N qs (.close j τ m agg pm pubnonces) st = none := by
        unfold needs
        exact dif_neg hc
      rw [this] at h
      exact absurd h (by simp)
  | single items =>
    by_cases ho : st.opened < qs
    · simp only [needs, ho, ↓reduceDIte, Option.some.injEq] at h
      subst h
      rw [challengerG_single der C nonceCoef N qs x T _ items st ho,
        challengerG_single der C nonceCoef N qs x T _ items st ho, hk]
    · simp [needs, ho] at h

/-- A query that reads the nonces of slot `k` either opens `k`, or `k` is an
open session that the query may close. -/
theorem needs_some_cases (nonces : Fin qs → SecNonce n) (q : AdvQ n N E X M)
    (st : SignerState X M) {k : Fin qs} (h : needs N qs q st = some k) :
    (k.val = st.opened ∧
        (challengerG der C nonceCoef N qs x nonces T q st).2.opened = st.opened + 1 ∧
        ((challengerG der C nonceCoef N qs x nonces T q st).2.closed = st.closed ∨
          (challengerG der C nonceCoef N qs x nonces T q st).2.closed =
            st.opened :: st.closed)) ∨
      (k.val < st.opened ∧ k.val ∉ st.closed ∧
        (challengerG der C nonceCoef N qs x nonces T q st).2.opened = st.opened ∧
        ((challengerG der C nonceCoef N qs x nonces T q st).2.closed = st.closed ∨
          (challengerG der C nonceCoef N qs x nonces T q st).2.closed = k.val :: st.closed)) := by
  cases q with
  | hash z => simp [needs] at h
  | openSession =>
    by_cases ho : st.opened < qs
    · simp only [needs, ho, ↓reduceDIte, Option.some.injEq] at h
      subst h
      exact Or.inl ⟨rfl, by simp [challengerG, ho], Or.inl (by simp [challengerG, ho])⟩
    · simp [needs, ho] at h
  | close j τ m agg pm pubnonces =>
    by_cases hc : j < qs ∧ j < st.opened ∧ j ∉ st.closed
    · have hk' : k = ⟨j, hc.1⟩ := by
        have : needs N qs (.close j τ m agg pm pubnonces) st = some ⟨j, hc.1⟩ := by
          unfold needs
          exact dif_pos hc
        exact Option.some.inj (h.symm.trans this)
      subst hk'
      obtain ⟨h1, h2⟩ := close_state der C nonceCoef N qs x T nonces j τ m agg pm pubnonces st
      exact Or.inr ⟨hc.2.1, hc.2.2, h1, h2⟩
    · have : needs N qs (.close j τ m agg pm pubnonces) st = none := by
        unfold needs
        exact dif_neg hc
      rw [this] at h
      exact absurd h (by simp)
  | single items =>
    by_cases ho : st.opened < qs
    · simp only [needs, ho, ↓reduceDIte, Option.some.injEq] at h
      subst h
      rw [challengerG_single der C nonceCoef N qs x T _ items st ho]
      obtain ⟨h1, h2⟩ := singleStep_state C N x T items st
        (singleNonce der nonceCoef (singleKeys C x items) (nonces ⟨st.opened, ho⟩))
      exact Or.inl ⟨rfl, h1, Or.inr h2⟩
    · simp [needs, ho] at h

variable {α : Type}

open Classical in
/-- **The game with a uniform single-party nonce against the game with the
derived one**, from any point of the run: the expectation grows by at most
`1 / (n - 1)` for every slot that is not opened yet. -/
theorem derived_couple (G : α × SignerState X M → ℝ) (hG0 : ∀ p, 0 ≤ G p) (hG1 : ∀ p, G p ≤ 1)
    (a : Alg (AdvQ n N E X M) AdvR α) (st : SignerState X M)
    (μ₁ μ₂ : List (Fin qs × NPair n)) (h : NRel qs st μ₁ μ₂) :
    exL (fun _ p => G p) μ₁ (Alg.interp (nonceChallenger false C nonceCoef N qs x T) a st) ≤
      exL (fun _ p => G p) μ₂ (Alg.interp (nonceChallenger true C nonceCoef N qs x T) a st) +
        ((qs - st.opened : ℕ) : ℝ) / Fintype.card (ZMod n)ˣ := by
  have hc : (0 : ℝ) < Fintype.card (ZMod n)ˣ := Nat.cast_pos.mpr Fintype.card_pos
  have hpot : ∀ k : ℕ, (0 : ℝ) ≤ (k : ℝ) / Fintype.card (ZMod n)ˣ := fun k => by positivity
  induction a generalizing st μ₁ μ₂ with
  | done a =>
    rw [Alg.interp_done, Alg.interp_done, exL_done, exL_done]
    linarith [hpot (qs - st.opened)]
  | ask q f ih =>
    rw [Alg.interp_ask, Alg.interp_ask, exL_bind, exL_bind]
    cases hn : needs N qs q st with
    | none =>
      rw [nonceChallenger_none _ C nonceCoef N qs x T hn,
        nonceChallenger_none _ C nonceCoef N qs x T hn, exL_done, exL_done]
      obtain ⟨e1, e2⟩ := challengerG_of_needs_none true C nonceCoef N qs x T (fun _ => (0, 0))
        (fun _ => (0, 0)) q st hn
      rw [e1]
      have hrel : NRel qs (challengerG false C nonceCoef N qs x (fun _ => (0, 0)) T q st).2
          μ₁ μ₂ := by
        rw [e2]
        exact h
      have key := ih (challengerG false C nonceCoef N qs x (fun _ => (0, 0)) T q st).1 _ μ₁ μ₂
        hrel
      rw [show (challengerG false C nonceCoef N qs x (fun _ => (0, 0)) T q st).2.opened =
        st.opened from by rw [e2]] at key
      exact key
    | some k =>
      rw [nonceChallenger_some _ C nonceCoef N qs x T hn,
        nonceChallenger_some _ C nonceCoef N qs x T hn]
      cases q with
      | hash z => simp [needs] at hn
      | openSession =>
        by_cases ho : st.opened < qs
        · simp only [needs, ho, ↓reduceDIte, Option.some.injEq] at hn
          subst hn
          obtain ⟨hm1, hm2⟩ := h.2.2.2 ⟨st.opened, ho⟩ le_rfl
          rw [exL_ask_none _ hm1, exL_ask_none _ hm2]
          have hmono : ((qs - (st.opened + 1) : ℕ) : ℝ) / Fintype.card (ZMod n)ˣ ≤
              ((qs - st.opened : ℕ) : ℝ) / Fintype.card (ZMod n)ˣ := by
            gcongr
            omega
          refine le_trans ?_ (add_le_add_right hmono _)
          refine avg_le_avg_add _ _ _ fun y => ?_
          · rw [exL_done, exL_done]
            have hst : (challengerG false C nonceCoef N qs x (constN qs y) T .openSession
                st).2.opened = st.opened + 1 ∧
                (challengerG false C nonceCoef N qs x (constN qs y) T .openSession st).2.closed =
                  st.closed := by
              simp [challengerG, ho]
            have key := ih (challengerG false C nonceCoef N qs x (constN qs y) T .openSession st).1
              _ _ _ (h.step qs ho y y hst.1 (Or.inl ⟨hst.2, rfl⟩))
            rw [hst.1] at key
            exact key
        · simp [needs, ho] at hn
      | close j τ m agg pm pubnonces =>
        by_cases hcj : j < qs ∧ j < st.opened ∧ j ∉ st.closed
        · have hk : k = ⟨j, hcj.1⟩ := by
            have : needs N qs (.close j τ m agg pm pubnonces) st = some ⟨j, hcj.1⟩ := by
              unfold needs
              exact dif_pos hcj
            exact Option.some.inj (hn.symm.trans this)
          subst hk
          obtain ⟨y, hm1, hm2⟩ := h.2.2.1 ⟨j, hcj.1⟩ hcj.2.1 hcj.2.2
          rw [exL_ask_some _ hm1, exL_ask_some _ hm2, exL_done, exL_done]
          obtain ⟨hs1, hs2⟩ := close_state false C nonceCoef N qs x T (constN qs y) j τ m agg pm
            pubnonces st
          have key := ih (challengerG false C nonceCoef N qs x (constN qs y) T
            (.close j τ m agg pm pubnonces) st).1 _ μ₁ μ₂ (h.close qs hs1 hcj.2.1 hs2)
          rw [hs1] at key
          exact key
        · have : needs N qs (.close j τ m agg pm pubnonces) st = none := by
            unfold needs
            exact dif_neg hcj
          rw [this] at hn
          exact absurd hn (by simp)
      | single items =>
        by_cases ho : st.opened < qs
        · simp only [needs, ho, ↓reduceDIte, Option.some.injEq] at hn
          subst hn
          obtain ⟨hm1, hm2⟩ := h.2.2.2 ⟨st.opened, ho⟩ le_rfl
          rw [exL_ask_none _ hm1, exL_ask_none _ hm2]
          have hL : ∀ (d : Bool) (μ : List (Fin qs × NPair n)) (y : NPair n),
              exL (fun μ' a => exL (fun _ p => G p) μ'
                  (Alg.interp (nonceChallenger d C nonceCoef N qs x T) (f a.1) a.2))
                (μ ++ [(⟨st.opened, ho⟩, y)])
                (.done (challengerG d C nonceCoef N qs x (constN qs y) T (.single items) st)) =
              exL (fun _ p => G p) (μ ++ [(⟨st.opened, ho⟩, y)])
                (Alg.interp (nonceChallenger d C nonceCoef N qs x T)
                  (f (singleStep C N x T items st (singleNonce d nonceCoef (singleKeys C x items)
                    (constN qs y ⟨st.opened, ho⟩))).1)
                  (singleStep C N x T items st (singleNonce d nonceCoef (singleKeys C x items)
                    (constN qs y ⟨st.opened, ho⟩))).2) := by
            intro d μ y
            rw [exL_done, challengerG_single d C nonceCoef N qs x T _ items st ho]
          rw [sum_congr rfl fun y _ => hL false μ₁ y, sum_congr rfl fun y _ => hL true μ₂ y]
          have hsub : ((qs - st.opened : ℕ) : ℝ) / Fintype.card (ZMod n)ˣ =
              ((qs - (st.opened + 1) : ℕ) : ℝ) / Fintype.card (ZMod n)ˣ +
                1 / Fintype.card (ZMod n)ˣ := by
            rw [← add_div]
            congr 1
            have : qs - st.opened = qs - (st.opened + 1) + 1 := by omega
            rw [this]
            push_cast
            ring
          rw [hsub, ← add_assoc]
          refine sum_twist (nonceCoef 0 0 (singleNcIn (E := E) (singleKeys C x items)).2.2)
            (fun r y => exL (fun _ p => G p) (μ₁ ++ [(⟨st.opened, ho⟩, y)])
              (Alg.interp (nonceChallenger false C nonceCoef N qs x T)
                (f (singleStep C N x T items st r).1) (singleStep C N x T items st r).2))
            (fun r y => exL (fun _ p => G p) (μ₂ ++ [(⟨st.opened, ho⟩, y)])
              (Alg.interp (nonceChallenger true C nonceCoef N qs x T)
                (f (singleStep C N x T items st r).1) (singleStep C N x T items st r).2))
            _ (hpot _) (fun r y y' => ?_) (fun r y => exL_nonneg _ (fun _ p => hG0 p) _ _)
            (fun r y => exL_le_one _ (fun _ p => hG1 p) _ _)
          obtain ⟨hs1, hs2⟩ := singleStep_state C N x T items st r
          have key := ih (singleStep C N x T items st r).1 _ _ _
            (h.step qs ho y y' hs1 (Or.inr hs2))
          rw [hs1] at key
          exact key
        · simp [needs, ho] at hn

/-! ## The advantages -/

variable {Coins : Type} (A : Adversary n N E X M Coins)

/-- The samples of the game with the nonces last. -/
def noncesLast : ((ZMod n)ˣ × Coins × (SigIn N X M → ZMod n)) × (Fin qs → NPair n) ≃
    ForgeSample n N qs X M Coins where
  toFun p := (p.1.1, p.2, p.1.2.1, p.1.2.2)
  invFun ω := ((ω.1, ω.2.2.1, ω.2.2.2), ω.2.1)
  left_inv _ := rfl
  right_inv _ := rfl

open Classical in
/-- For a fixed key, fixed coins and a fixed table, the game is the lazily
sampled run of the nonce oracle version. -/
theorem prob_nonces_eq_exL (θ : (ZMod n)ˣ × Coins × (SigIn N X M → ZMod n)) :
    prob (fun ν : Fin qs → NPair n =>
        forgeExperimentG der C nonceCoef N qs A (noncesLast N qs (θ, ν))) =
      exL (fun _ p => if Wins C nonceCoef N (θ.1 : ZMod n) θ.2.2 p.1 p.2 then (1 : ℝ) else 0) []
        (Alg.interp (nonceChallenger der C nonceCoef N qs (θ.1 : ZMod n) θ.2.2)
          (A θ.2.1 (C.mulG (θ.1 : ZMod n))) ⟨0, [], []⟩) := by
  rw [← prob_eval_eq_exL (fun p : Forgery n X M × SignerState X M =>
    Wins C nonceCoef N (θ.1 : ZMod n) θ.2.2 p.1 p.2)]
  congr 1
  funext ν
  rw [eval_interp_of _ _ ν (eval_nonceChallenger der C nonceCoef N qs (θ.1 : ZMod n) θ.2.2 ν)]
  rfl

variable [Fintype Coins] [Fintype (SigIn N X M)]

open Classical in
/-- **A uniform nonce for single-party signatures is as good as the derived
one**: the adversary wins the game at most `qs / (n - 1)` more often than the
game in which a single-party signature uses the nonce `r₁ + b⋅r₂`. -/
theorem forgeAdvantage_le_derived :
    forgeAdvantage C nonceCoef N qs A ≤
      forgeAdvantageG true C nonceCoef N qs A + qs / (n - 1 : ℝ) := by
  have hn : 0 < n := (Fact.out : n.Prime).pos
  have hcard : (Fintype.card (ZMod n)ˣ : ℝ) = n - 1 := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime Fact.out, Nat.cast_sub hn, Nat.cast_one]
  have hc : (0 : ℝ) < Fintype.card (ZMod n)ˣ := Nat.cast_pos.mpr Fintype.card_pos
  change prob (forgeExperimentG false C nonceCoef N qs A) ≤
    prob (forgeExperimentG true C nonceCoef N qs A) + _
  rw [← prob_equiv (noncesLast N qs) (forgeExperimentG false C nonceCoef N qs A),
    ← prob_equiv (noncesLast N qs) (forgeExperimentG true C nonceCoef N qs A), ← hcard]
  refine prob_prod_mono _ _ _ (by positivity) fun θ => ?_
  rw [prob_nonces_eq_exL false C nonceCoef N qs A θ, prob_nonces_eq_exL true C nonceCoef N qs A θ]
  have key := derived_couple C nonceCoef N qs (θ.1 : ZMod n) θ.2.2
    (fun p : Forgery n X M × SignerState X M =>
      if Wins C nonceCoef N (θ.1 : ZMod n) θ.2.2 p.1 p.2 then (1 : ℝ) else 0)
    (fun p => by split_ifs <;> norm_num) (fun p => by split_ifs <;> norm_num)
    (A θ.2.1 (C.mulG (θ.1 : ZMod n))) ⟨0, [], []⟩ [] []
    ⟨Nat.zero_le _, by simp, fun k hk => absurd hk (Nat.not_lt_zero _), fun k _ => ⟨rfl, rfl⟩⟩
  simpa using key

end Dahlias.Security
