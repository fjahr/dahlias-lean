import Dahlias.NonceGenHashed
import Dahlias.LazyCollider

/-!
# `NonceGen` with lazily sampled hash functions

In `nonceGen_unforgeable_hashed` and `nonceGenSk_unforgeable_hashed` the
forger that the reduction runs has a whole table of `hash_BIP0459/nonce` in
its coins, and with the `sk` argument of `NonceGen` one of `hash_BIP0459/aux`
as well. Here the forger answers these queries from `qn` and `qa` values in
its coins, and the reduction and the collision finder are the lazily sampling
ones. No algorithm in the statements needs an object of exponential size.

* `withStream q A` and `withAuxStream q A` answer the queries to
  `hash_BIP0459/nonce` and to `hash_BIP0459/aux` lazily.
* `forgeAdvantage_withTable_eq_lazy`, `forgeAdvantage_withAux_eq_lazy`: the
  forger wins the game as often as with a table.
* `lazy_of_tables`: every path of a lazily answered algorithm is a path with
  some table. So the bounds on the queries carry over.
* `nonceGen_unforgeable_lazy`, `nonceGenSk_unforgeable_lazy`: the security
  theorems. `nonceGen_unforgeable_fin` and `nonceGenSk_unforgeable_fin` are
  the case of hash outputs `0, …, m - 1` reduced modulo `n`.
-/

set_option linter.unusedSectionVars false

namespace Dahlias.Security

open Taproot Function QTree

/-! ## Every path of a lazily answered algorithm is a path with some table -/

section Paths

variable {Q : Type} {R : Q → Type} {D W α β : Type} [DecidableEq D]

/-- **Every path of a lazily answered algorithm is a path with some table.**
Let `Φ` be a family of properties of algorithms in which the property of
`ask q f` is a condition on `q` and the properties of `f r` for the answers
`r` that count. If `Φ b` holds with every table that extends the memory, it
holds for the lazily answered algorithm. -/
theorem lazy_of_tables (Φ : β → Alg Q R α → Prop) (S : β → Q → Prop)
    (Adm : β → (q : Q) → R q → Prop) (nxt : β → (q : Q) → R q → β)
    (hstep : ∀ b q (f : R q → Alg Q R α),
      Φ b (.ask q f) ↔ S b q ∧ ∀ r, Adm b q r → Φ (nxt b q r) (f r))
    (v : ℕ → W) (t : Alg (Q ⊕ D) (SumR R W) α) (k : ℕ) (μ : List (D × W)) (b : β)
    (hden : ∃ G : D → W, Ext μ G) (h : ∀ G : D → W, Ext μ G → Φ b (answerG G t)) :
    Φ b (answerLazy v k μ t) := by
  induction t generalizing k μ b with
  | done a =>
    obtain ⟨G, hG⟩ := hden
    exact h G hG
  | ask x f ih =>
    cases x with
    | inl q =>
      have h' : ∀ G : D → W, Ext μ G → Φ b (.ask q fun r => answerG G (f r)) := h
      obtain ⟨G₀, hG₀⟩ := hden
      change Φ b (.ask q fun r => answerLazy v k μ (f r))
      refine (hstep b q _).mpr ⟨((hstep b q _).mp (h' G₀ hG₀)).1, fun r hr => ?_⟩
      exact ih r k μ _ ⟨G₀, hG₀⟩ fun G hG => ((hstep b q _).mp (h' G hG)).2 r hr
    | inr z =>
      have h' : ∀ G : D → W, Ext μ G → Φ b (answerG G (f (G z))) := h
      simp only [answerLazy]
      cases hm : memo μ z with
      | some s =>
        refine ih s k μ b hden fun G hG => ?_
        have := h' G hG
        rwa [(memo_eq_some hm).2 G hG] at this
      | none =>
        obtain ⟨G₀, hG₀⟩ := hden
        refine ih (v k) (k + 1) _ b
          ⟨update G₀ z (v k), ext_append.mpr ⟨update_self _ _ _,
            (ext_update (memo_eq_none hm) G₀ _).mpr hG₀⟩⟩ fun G hG => ?_
        obtain ⟨hz, hG'⟩ := ext_append.mp hG
        have := h' G hG'
        rwa [hz] at this

/-- The answers that count when the queries of a table are answered by `G`. -/
def admG (G : D → W) : (x : Q ⊕ D) → SumR R W x → Prop
  | .inl _, _ => True
  | .inr d, w => w = G d

variable [Inhabited W]

/-- **Lazy answers keep a bound on the queries to another table**, if the
bound holds with every table. -/
theorem nbound_answerLazy {Q' : Type} {R' : Q' → Type} {D' W' : Type} (v : ℕ → W)
    (t : Alg ((Q' ⊕ D') ⊕ D) (SumR (SumR R' W') W) α) (q : ℕ)
    (h : ∀ G : D → W, NBound (answerG G t) q) : NBound (answerLazy v 0 [] t) q :=
  lazy_of_tables (Q := Q' ⊕ D') (R := SumR R' W') (fun b s => NBound s b)
    (fun b x => Sum.elim (fun _ => True) (fun _ => 0 < b) x) (fun _ _ _ => True)
    (fun b x _ => Sum.elim (fun _ => b) (fun _ => b - 1) x)
    (fun b x f => by
      cases x with
      | inl q => exact ⟨fun h => ⟨trivial, fun r _ => h r⟩, fun h r => h.2 r trivial⟩
      | inr d => exact ⟨fun h => ⟨h.1, fun r _ => h.2 r⟩, fun h => ⟨h.1, fun r => h.2 r trivial⟩⟩)
    v t 0 [] q ⟨fun _ => default, fun p hp => by simp at hp⟩ fun G _ => h G

end Paths

variable {n : ℕ} [Fact n.Prime] {E X M : Type} [AddCommGroup E] [DecidableEq E] [DecidableEq X]
  [DecidableEq M]

section HashBounds

variable {N : ℕ} {Ex D W α : Type} [DecidableEq D] [Inhabited W]
  {R : AdvQ n N E X M → Type}

omit [Fact n.Prime] [AddCommGroup E] [DecidableEq E] [DecidableEq X] [DecidableEq M]
  [DecidableEq D] [Inhabited W] in
theorem hashBound_ask_iff (q : AdvQ n N E X M) (f : R q → Alg (AdvQ n N E X M) R α) (qh : ℕ) :
    HashBound (.ask q f) qh ↔ hashCost q ≤ qh ∧ ∀ r, HashBound (f r) (qh - hashCost q) := by
  cases q with
  | hash z => exact Iff.rfl
  | openSession => exact ⟨fun h => ⟨Nat.zero_le _, h⟩, fun h => h.2⟩
  | close k τ m agg pm pubnonces => exact ⟨fun h => ⟨Nat.zero_le _, h⟩, fun h => h.2⟩
  | single items => exact Iff.rfl

omit [Fact n.Prime] [AddCommGroup E] [DecidableEq E] [DecidableEq X] [DecidableEq M] in
/-- **Lazy answers keep the bound on the hash queries**, if it holds with
every table. -/
theorem hashBound_answerLazy (v : ℕ → W)
    (t : Alg ((AdvQ n N E X M ⊕ Ex) ⊕ D) (SumR (SumR R Unit) W) α) (qh : ℕ)
    (h : ∀ G : D → W, HashBound (answerG (fun _ : Ex => ()) (answerG G t)) qh) :
    HashBound (answerG (fun _ : Ex => ()) (answerLazy v 0 [] t)) qh :=
  lazy_of_tables (Q := AdvQ n N E X M ⊕ Ex) (R := SumR R Unit)
    (fun b s => HashBound (answerG (fun _ : Ex => ()) s) b)
    (fun b x => Sum.elim (fun q => hashCost q ≤ b) (fun _ => True) x) (fun _ _ _ => True)
    (fun b x _ => Sum.elim (fun q => b - hashCost q) (fun _ => b) x)
    (fun b x f => by
      cases x with
      | inl q =>
        refine (hashBound_ask_iff q (fun r => answerG (fun _ : Ex => ()) (f r)) b).trans ?_
        exact ⟨fun h => ⟨h.1, fun r _ => h.2 r⟩, fun h => ⟨h.1, fun r => h.2 r trivial⟩⟩
      | inr e => exact ⟨fun h => ⟨trivial, fun r _ => h⟩, fun h => h.2 () trivial⟩)
    v t 0 [] qh ⟨fun _ => default, fun p hp => by simp at hp⟩ fun G _ => h G

omit [Fact n.Prime] [AddCommGroup E] [DecidableEq E] [DecidableEq X] [DecidableEq M] in
/-- **Lazy answers below a table keep the bound on the hash queries**, if it
holds with every table. -/
theorem hashBound_answerG_answerLazy {D₁ W₁ : Type} (G₁ : D₁ → W₁) (v : ℕ → W)
    (t : Alg (((AdvQ n N E X M ⊕ Ex) ⊕ D₁) ⊕ D) (SumR (SumR (SumR R Unit) W₁) W) α) (qh : ℕ)
    (h : ∀ G : D → W, HashBound (answerG (fun _ : Ex => ()) (answerG G₁ (answerG G t))) qh) :
    HashBound (answerG (fun _ : Ex => ()) (answerG G₁ (answerLazy v 0 [] t))) qh :=
  lazy_of_tables (Q := (AdvQ n N E X M ⊕ Ex) ⊕ D₁) (R := SumR (SumR R Unit) W₁)
    (fun b s => HashBound (answerG (fun _ : Ex => ()) (answerG G₁ s)) b)
    (fun b x => Sum.elim (Sum.elim (fun q => hashCost q ≤ b) (fun _ => True)) (fun _ => True) x)
    (fun _ x r => admG G₁ x r)
    (fun b x _ => Sum.elim (Sum.elim (fun q => b - hashCost q) (fun _ => b)) (fun _ => b) x)
    (fun b x f => by
      cases x with
      | inl y =>
        cases y with
        | inl q =>
          refine (hashBound_ask_iff q
            (fun r => answerG (fun _ : Ex => ()) (answerG G₁ (f r))) b).trans ?_
          exact ⟨fun h => ⟨h.1, fun r _ => h.2 r⟩, fun h => ⟨h.1, fun r => h.2 r trivial⟩⟩
        | inr e => exact ⟨fun h => ⟨trivial, fun r _ => h⟩, fun h => h.2 () trivial⟩
      | inr d =>
        refine ⟨fun h => ⟨trivial, fun r hr => ?_⟩, fun h => h.2 (G₁ d) rfl⟩
        have hr' : r = G₁ d := hr
        rw [hr']
        exact h)
    v t 0 [] qh ⟨fun _ => default, fun p hp => by simp at hp⟩ fun G _ => h G

end HashBounds

/-! ## Forgers that answer the queries to the hash functions of `NonceGen` -/

variable (C : Curve n E X) (nonceCoef : E → E → List (X × M × E) → ZMod n) (N qs : ℕ)
  {H Rnd Rp Ex W Coins : Type}

/-- The adversary for the game with uniform nonces that answers the queries
to `hash_BIP0459/nonce` lazily, from `q` values in its coins, and drops the
`extra_in`. -/
def withStream [DecidableEq Rnd] [DecidableEq Ex] [Inhabited W] (q : ℕ)
    (A : NAdversary n N E X M Rnd Ex W Coins) : Adversary n N E X M (Coins × (Fin q → W)) :=
  fun c P => answerG (fun _ : Ex => ()) (answerLazy (stream c.2) 0 [] (A c.1 P))

/-- The adversary for the game of `Dahlias.NonceGen` that answers the queries
to `hash_BIP0459/aux` lazily, from `q` values in its coins. -/
def withAuxStream [DecidableEq Rp] [Inhabited Rnd] (q : ℕ)
    (A : SkAdversary n N E X M Rnd Rp Ex W Coins) :
    NAdversary n N E X M Rnd Ex W (Coins × (Fin q → Rnd)) :=
  fun c P => answerLazy (stream c.2) 0 [] (A c.1 P)

/-- Samples of the game with the second part of the coins last. -/
def coinsLast {U V K T Tb : Type} : (U × V × K × T) × Tb ≃ U × V × (K × Tb) × T where
  toFun p := (p.1.1, p.1.2.1, (p.1.2.2.1, p.2), p.1.2.2.2)
  invFun ω := ((ω.1, ω.2.1, ω.2.2.1.1, ω.2.2.2), ω.2.2.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Samples of the game with the middle part of the coins last. -/
def auxLast {U V K G T Tb : Type} : (U × V × (K × G) × T) × Tb ≃ U × V × ((K × Tb) × G) × T where
  toFun p := (p.1.1, p.1.2.1, ((p.1.2.2.1.1, p.2), p.1.2.2.1.2), p.1.2.2.2)
  invFun ω := ((ω.1, ω.2.1, (ω.2.2.1.1.1, ω.2.2.1.2), ω.2.2.2), ω.2.2.1.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

variable [Fintype Coins] [Fintype (SigIn N X M)] [Fintype Rnd] [DecidableEq Rnd] [Fintype Ex]
  [DecidableEq Ex] [Fintype W] [DecidableEq W] [Inhabited W]

set_option synthInstance.maxSize 4000 in
/-- **A table of `hash_BIP0459/nonce` and lazily sampled answers give the
forger the same advantage.** -/
theorem forgeAdvantage_withTable_eq_lazy (A : NAdversary n N E X M Rnd Ex W Coins) (q : ℕ)
    (hA : ∀ c P, NBound (A c P) q) :
    forgeAdvantage C nonceCoef N qs (withTable N A) =
      forgeAdvantage C nonceCoef N qs (withStream N q A) := by
  change prob (forgeExperiment C nonceCoef N qs (withTable N A)) =
    prob (forgeExperiment C nonceCoef N qs (withStream N q A))
  rw [← prob_equiv (coinsLast (Tb := Rnd × Ex × Bool → W))
      (forgeExperiment C nonceCoef N qs (withTable N A)),
    ← prob_equiv (coinsLast (Tb := Fin q → W))
      (forgeExperiment C nonceCoef N qs (withStream N q A))]
  refine prob_prod_congr _ _ fun a => ?_
  have key := prob_answerG_eq_lazy
    (handG (fun _ : Ex => ()) (challenger C nonceCoef N qs (a.1 : ZMod n)
      (fun k => ((a.2.1 k).1, (a.2.1 k).2)) a.2.2.2))
    (⟨0, [], []⟩ : SignerState X M) (A a.2.2.1 (C.mulG (a.1 : ZMod n)))
    (fun out => Wins C nonceCoef N (a.1 : ZMod n) a.2.2.2 out.1 out.2) q (hA _ _)
  refine Eq.trans ?_ (key.trans ?_)
  · congr 1
    funext G
    rw [← run_answerG]
    rfl
  · congr 1
    funext v
    rw [← run_answerG]
    rfl

variable [Fintype Rp] [DecidableEq Rp] [Inhabited Rnd]

set_option synthInstance.maxSize 4000 in
/-- **A table of `hash_BIP0459/aux` and lazily sampled answers give the forger
the same advantage.** -/
theorem forgeAdvantage_withAux_eq_lazy (A : SkAdversary n N E X M Rnd Rp Ex W Coins) (q : ℕ)
    (hA : ∀ c P, NBound (A c P) q) :
    forgeAdvantage C nonceCoef N qs (withTable N (withAux N A)) =
      forgeAdvantage C nonceCoef N qs (withTable N (withAuxStream N q A)) := by
  change prob (forgeExperiment C nonceCoef N qs (withTable N (withAux N A))) =
    prob (forgeExperiment C nonceCoef N qs (withTable N (withAuxStream N q A)))
  rw [← prob_equiv (auxLast (Tb := Rp → Rnd))
      (forgeExperiment C nonceCoef N qs (withTable N (withAux N A))),
    ← prob_equiv (auxLast (Tb := Fin q → Rnd))
      (forgeExperiment C nonceCoef N qs (withTable N (withAuxStream N q A)))]
  refine prob_prod_congr _ _ fun a => ?_
  have key := prob_answerG_eq_lazy
    (handG a.2.2.1.2 (handG (fun _ : Ex => ()) (challenger C nonceCoef N qs (a.1 : ZMod n)
      (fun k => ((a.2.1 k).1, (a.2.1 k).2)) a.2.2.2)))
    (⟨0, [], []⟩ : SignerState X M) (A a.2.2.1.1 (C.mulG (a.1 : ZMod n)))
    (fun out => Wins C nonceCoef N (a.1 : ZMod n) a.2.2.2 out.1 out.2) q (hA _ _)
  refine Eq.trans ?_ (key.trans ?_)
  · congr 1
    funext Aux
    rw [← run_answerG, ← run_answerG]
    rfl
  · congr 1
    funext v
    rw [← run_answerG, ← run_answerG]
    rfl

/-! ## The security theorems -/

variable (red : H → ZMod n) [Fintype H] [DecidableEq H] (e₀ : Ex)

set_option synthInstance.maxSize 4000 in
/-- **Unforgeability with `NonceGen` and the challenge hash reduced to a
scalar, with all random oracles sampled lazily.** The statement of
`nonceGen_unforgeable_hashed` for the forger `withStream`, `reductionLazy` and
`colliderLazy`. -/
theorem nonceGen_unforgeable_lazy [Nonempty Rnd] (A : NAdversaryH n N E X M Rnd Ex W H Coins)
    (ρ : W → ZMod n) (g : ZMod n → H) (hg : ∀ c, red (g c) = c) (gW : (ZMod n)ˣ → W)
    (hgW : Injective gW) (hρ : ∀ u, ρ (gW u) = u) (hN : N < n) (qh qn : ℕ)
    (hA : ∀ c P, NBound (A c P) qn)
    (hH : ∀ c P G, HashBound (answerG (fun _ : Ex => ()) (answerG G (A c P))) qh) :
    nonceGenAdvantageH C nonceCoef N qs red A ρ e₀ ≤
      Real.sqrt ((qh + qs + 1 : ℕ) *
          (omdlAdvantage C (2 * qs + 1)
              (reductionLazy C nonceCoef N qs (withStream N qn (liftHashN N g A))
                (2 * (qh + qs) + 1)) +
            collisionAdvantageLazy C nonceCoef N qs (withStream N qn (liftHashN N g A))
              (2 * (qh + qs)))) +
        (qh + qs + 1 : ℕ) / n + qs / (n - 1 : ℝ) +
        (qh + qs + N : ℕ) * ((Fintype.card H - n : ℝ) / Fintype.card H) +
        (qs : ℝ) ^ 2 / Fintype.card Rnd + qs * (qn / Fintype.card Rnd) +
        (2 * qs : ℕ) * ((Fintype.card W - Fintype.card (ZMod n)ˣ : ℝ) / Fintype.card W) := by
  have hL : ∀ c P, NBound (liftHashN N g A c P) qn := fun c P => nbound_mapAns _ _ _ (hA c P)
  have hHL : ∀ c P G,
      HashBound (answerG (fun _ : Ex => ()) (answerG G (liftHashN N g A c P))) qh := by
    intro c P G
    change HashBound (answerG (fun _ : Ex => ()) (answerG G
      (mapAns (sumAns (sumAns (hashAns N g))) (A c P)))) qh
    rw [answerG_mapAns, answerG_mapAns]
    exact hashBound_mapAns N g _ qh (hH _ _ _)
  have h1 := nonceGenAdvantageH_le C nonceCoef N qs red e₀ A ρ g hg qh hH
  have h2 := nonceGen_advantage C nonceCoef N qs (liftHashN N g A) ρ e₀ gW hgW hρ qn hL
  rw [forgeAdvantage_withTable_eq_lazy C nonceCoef N qs _ qn hL] at h2
  have h3 := unforgeable_sqrt_lazy_both C nonceCoef N qs (withStream N qn (liftHashN N g A)) hN qh
    fun c P => hashBound_answerLazy _ _ qh (hHL c.1 P)
  linarith

set_option synthInstance.maxSize 4000 in
/-- **Unforgeability with `NonceGen`, its `sk` argument and the challenge hash
reduced to a scalar, with all random oracles sampled lazily.** The statement
of `nonceGenSk_unforgeable_hashed` for the forger
`withStream (withAuxStream …)`, `reductionLazy` and `colliderLazy`. -/
theorem nonceGenSk_unforgeable_lazy (A : SkAdversaryH n N E X M Rnd Rp Ex W H Coins)
    (ρ : W → ZMod n) (mask : (ZMod n)ˣ → Fin qs → Rnd ≃ Rnd) [Nonempty Rp] (g : ZMod n → H)
    (hg : ∀ c, red (g c) = c) (gW : (ZMod n)ˣ → W) (hgW : Injective gW)
    (hρ : ∀ u, ρ (gW u) = u) (hN : N < n) (qh qn qa : ℕ) (hA : ∀ c P, NBound (A c P) qa)
    (hG : ∀ c P (Aux : Rp → Rnd), NBound (answerG Aux (A c P)) qn)
    (hH : ∀ c P G (Aux : Rp → Rnd),
      HashBound (answerG (fun _ : Ex => ()) (answerG G (answerG Aux (A c P)))) qh) :
    nonceGenSkAdvantageH C nonceCoef N qs red A ρ e₀ mask ≤
      Real.sqrt ((qh + qs + 1 : ℕ) *
          (omdlAdvantage C (2 * qs + 1)
              (reductionLazy C nonceCoef N qs
                (withStream N qn (withAuxStream N qa (liftHashSk N g A))) (2 * (qh + qs) + 1)) +
            collisionAdvantageLazy C nonceCoef N qs
              (withStream N qn (withAuxStream N qa (liftHashSk N g A))) (2 * (qh + qs)))) +
        (qh + qs + 1 : ℕ) / n + qs / (n - 1 : ℝ) +
        (qh + qs + N : ℕ) * ((Fintype.card H - n : ℝ) / Fintype.card H) +
        (qs : ℝ) ^ 2 / Fintype.card Rnd + qs * (qn / Fintype.card Rnd) +
        (2 * qs : ℕ) * ((Fintype.card W - Fintype.card (ZMod n)ˣ : ℝ) / Fintype.card W) +
        (qs : ℝ) ^ 2 / Fintype.card Rp + qs * (qa / Fintype.card Rp) := by
  have hLA : ∀ c P, NBound (liftHashSk N g A c P) qa := fun c P => nbound_mapAns _ _ _ (hA c P)
  have hLG : ∀ c P (Aux : Rp → Rnd), NBound (answerG Aux (liftHashSk N g A c P)) qn := by
    intro c P Aux
    change NBound (answerG Aux (mapAns (sumAns (sumAns (sumAns (hashAns N g)))) (A c P))) qn
    rw [answerG_mapAns]
    exact nbound_mapAns _ _ _ (hG c P Aux)
  have hLH : ∀ c P G (Aux : Rp → Rnd), HashBound (answerG (fun _ : Ex => ())
      (answerG G (answerG Aux (liftHashSk N g A c P)))) qh := by
    intro c P G Aux
    change HashBound (answerG (fun _ : Ex => ()) (answerG G (answerG Aux
      (mapAns (sumAns (sumAns (sumAns (hashAns N g)))) (A c P))))) qh
    rw [answerG_mapAns, answerG_mapAns, answerG_mapAns]
    exact hashBound_mapAns N g _ qh (hH _ _ _ _)
  have hLS : ∀ c P, NBound (withAuxStream N qa (liftHashSk N g A) c P) qn :=
    fun c P => nbound_answerLazy _ _ qn fun Aux => hLG c.1 P Aux
  have h1 := nonceGenSkAdvantageH_le C nonceCoef N qs red e₀ A ρ mask g hg qh hH
  have h2 := nonceGenSk_advantage C nonceCoef N qs (liftHashSk N g A) ρ e₀ mask gW hgW hρ qn qa
    hLA hLG
  rw [forgeAdvantage_withAux_eq_lazy C nonceCoef N qs _ qa hLA,
    forgeAdvantage_withTable_eq_lazy C nonceCoef N qs _ qn hLS] at h2
  have h3 := unforgeable_sqrt_lazy_both C nonceCoef N qs
    (withStream N qn (withAuxStream N qa (liftHashSk N g A))) hN qh
    fun c P => hashBound_answerLazy _ _ qh fun G =>
      hashBound_answerG_answerLazy G _ _ qh fun Aux => hLH c.1.1 P G Aux
  linarith

/-! ## Outputs `0, …, m - 1` reduced modulo `n` -/

omit [Fintype H] [DecidableEq H] [Inhabited W] [Fintype W] [DecidableEq W] in
set_option synthInstance.maxSize 4000 in
/-- **BIP 459's `NonceGen` without its `sk` argument and the challenge hash**:
`m`-valued random oracles reduced modulo `n`, for `m = 2²⁵⁶`. The forger, the
reduction and the collision finder sample all random oracles lazily. -/
theorem nonceGen_unforgeable_fin [Nonempty Rnd] {m : ℕ} [NeZero m] (hm : n ≤ m)
    (A : NAdversaryH n N E X M Rnd Ex (Fin m) (Fin m) Coins) (hN : N < n) (qh qn : ℕ)
    (hA : ∀ c P, NBound (A c P) qn)
    (hH : ∀ c P G, HashBound (answerG (fun _ : Ex => ()) (answerG G (A c P))) qh) :
    nonceGenAdvantageH C nonceCoef N qs (redFin m) A (redFin m) e₀ ≤
      Real.sqrt ((qh + qs + 1 : ℕ) *
          (omdlAdvantage C (2 * qs + 1)
              (reductionLazy C nonceCoef N qs (withStream N qn (liftHashN N (liftFin hm) A))
                (2 * (qh + qs) + 1)) +
            collisionAdvantageLazy C nonceCoef N qs
              (withStream N qn (liftHashN N (liftFin hm) A)) (2 * (qh + qs)))) +
        (qh + qs + 1 : ℕ) / n + qs / (n - 1 : ℝ) +
        (qh + qs + N : ℕ) * ((m - n : ℝ) / m) +
        (qs : ℝ) ^ 2 / Fintype.card Rnd + qs * (qn / Fintype.card Rnd) +
        (2 * qs : ℕ) * ((m - (n - 1) : ℝ) / m) := by
  have hn : 0 < n := (Fact.out : n.Prime).pos
  have h := nonceGen_unforgeable_lazy C nonceCoef N qs (redFin m) e₀ A (redFin m) (liftFin hm)
    (fun c => ZMod.natCast_zmod_val c)
    (fun u => ⟨(u : ZMod n).val, lt_of_lt_of_le (ZMod.val_lt _) hm⟩)
    (fun u u' h => Units.ext (ZMod.val_injective n (Fin.mk.inj h)))
    (fun u => ZMod.natCast_zmod_val _) hN qh qn hA hH
  rw [ZMod.card_units_eq_totient, Nat.totient_prime Fact.out, Fintype.card_fin,
    Nat.cast_sub hn, Nat.cast_one] at h
  exact h

omit [Fintype H] [DecidableEq H] [Inhabited W] [Fintype W] [DecidableEq W] in
set_option synthInstance.maxSize 4000 in
/-- **BIP 459's `NonceGen` with its `sk` argument and the challenge hash**:
`m`-valued random oracles reduced modulo `n`, for `m = 2²⁵⁶`. The forger, the
reduction and the collision finder sample all random oracles lazily. -/
theorem nonceGenSk_unforgeable_fin (mask : (ZMod n)ˣ → Fin qs → Rnd ≃ Rnd) [Nonempty Rp] {m : ℕ}
    [NeZero m] (hm : n ≤ m) (A : SkAdversaryH n N E X M Rnd Rp Ex (Fin m) (Fin m) Coins)
    (hN : N < n) (qh qn qa : ℕ) (hA : ∀ c P, NBound (A c P) qa)
    (hG : ∀ c P (Aux : Rp → Rnd), NBound (answerG Aux (A c P)) qn)
    (hH : ∀ c P G (Aux : Rp → Rnd),
      HashBound (answerG (fun _ : Ex => ()) (answerG G (answerG Aux (A c P)))) qh) :
    nonceGenSkAdvantageH C nonceCoef N qs (redFin m) A (redFin m) e₀ mask ≤
      Real.sqrt ((qh + qs + 1 : ℕ) *
          (omdlAdvantage C (2 * qs + 1)
              (reductionLazy C nonceCoef N qs
                (withStream N qn (withAuxStream N qa (liftHashSk N (liftFin hm) A)))
                (2 * (qh + qs) + 1)) +
            collisionAdvantageLazy C nonceCoef N qs
              (withStream N qn (withAuxStream N qa (liftHashSk N (liftFin hm) A)))
              (2 * (qh + qs)))) +
        (qh + qs + 1 : ℕ) / n + qs / (n - 1 : ℝ) +
        (qh + qs + N : ℕ) * ((m - n : ℝ) / m) +
        (qs : ℝ) ^ 2 / Fintype.card Rnd + qs * (qn / Fintype.card Rnd) +
        (2 * qs : ℕ) * ((m - (n - 1) : ℝ) / m) +
        (qs : ℝ) ^ 2 / Fintype.card Rp + qs * (qa / Fintype.card Rp) := by
  have hn : 0 < n := (Fact.out : n.Prime).pos
  have h := nonceGenSk_unforgeable_lazy C nonceCoef N qs (redFin m) e₀ A (redFin m) mask
    (liftFin hm) (fun c => ZMod.natCast_zmod_val c)
    (fun u => ⟨(u : ZMod n).val, lt_of_lt_of_le (ZMod.val_lt _) hm⟩)
    (fun u u' h => Units.ext (ZMod.val_injective n (Fin.mk.inj h)))
    (fun u => ZMod.natCast_zmod_val _) hN qh qn qa hA hG hH
  rw [ZMod.card_units_eq_totient, Nat.totient_prime Fact.out, Fintype.card_fin,
    Nat.cast_sub hn, Nat.cast_one] at h
  exact h

end Dahlias.Security
