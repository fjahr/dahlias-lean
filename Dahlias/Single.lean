import Dahlias.Correctness

/-!
# Signing by a single party that holds all keys

BIP 459 does not specify how a party that holds all secret keys of a list,
such as a wallet that spends several of its own inputs, can sign without
running the protocol with itself. The method sketched on the bitcoin-dev
mailing list is: draw one nonce `r`, let `R = r⋅G`, and let
`s = r + c₀⋅d₀ + … + c_{u-1}⋅d_{u-1}`. `signSingle` is that method with the
conventions of BIP 459 (x-only `R`, even-y keys).

* `verify_signSingle`: its output passes `Verify`.
* `verify_unique`: for a list and an `r` there is at most one `s` that
  `Verify` accepts.
* `sigAgg_eq_signSingle`: the signature of an honest session of the protocol
  is the output of `signSingle` for the same keys and messages and the nonce
  `r = Σ (r₁,ᵢ + b⋅r₂,ᵢ)`.

So `signSingle` and the protocol produce the same signature for the same
`R`: the only valid one. They differ in how `R` is distributed, uniform for
`signSingle` and `R₁ + b⋅R₂` for the protocol.

The unforgeability game of `Dahlias.Security` lets the adversary ask the
honest signer for such signatures, next to its sessions
(`Dahlias.Security.challenger_single`), and `unforgeable_sqrt` covers them.
-/

set_option linter.unusedSectionVars false
set_option linter.deprecated false

namespace Dahlias

open Taproot Taproot.Curve

variable {n : ℕ} [Fact n.Prime] {E X M : Type} [AddCommGroup E] [DecidableEq E] [DecidableEq X]
  [DecidableEq M]

/-- The list `L` of a party's secret keys and messages. -/
def singleList (O : Ops n E X) (signers : List (ZMod n × M)) : List (X × M) :=
  signers.map fun σ => (O.x (O.mulG σ.1), σ.2)

/-- **Signing by a single party**: one nonce `r` for the whole list. -/
def signSingle (O : Ops n E X) (H : Hashes n E X M) (r : ZMod n) (signers : List (ZMod n × M)) :
    Option (X × ZMod n) :=
  if r = 0 ∨ signers = [] ∨ ∃ σ ∈ signers, σ.1 = 0 then none else
  some (O.x (O.mulG r), (if O.hasEvenY (O.mulG r) then r else -r) +
    (signers.map fun σ =>
      H.sig (singleList O signers) (O.x (O.mulG r)) (O.x (O.mulG σ.1), σ.2) *
        O.evenScalar σ.1).sum)

variable (C : Curve n E X) (H : Hashes n E X M)

/-- The key sum of a list of the party's own keys. -/
theorem keySum_single (L : List (X × M)) (r : X) (signers : List (ZMod n × M))
    (hs : ∀ σ ∈ signers, σ.1 ≠ 0) :
    ((singleList C.ops signers).map fun pkm =>
        C.ops.smul (H.sig L r pkm) ((C.ops.liftX pkm.1).getD 0)).sum =
      C.mulG (signers.map fun σ =>
        H.sig L r (C.x (C.mulG σ.1), σ.2) * C.evenScalar σ.1).sum := by
  induction signers with
  | nil => simp [singleList]
  | cons σ signers ih =>
    have h0 : σ.1 ≠ 0 := hs σ List.mem_cons_self
    have := ih fun τ hτ => hs τ (List.mem_cons_of_mem _ hτ)
    simp only [singleList, List.map_cons, List.sum_cons, map_add, ops_x, ops_mulG, ops_liftX,
      ops_smul, C.liftX_x_mulG h0, Option.getD_some, C.val_smul_mulG] at this ⊢
    rw [this]

/-- **The single-party signature verifies.** -/
theorem verify_signSingle {r : ZMod n} {signers : List (ZMod n × M)} {sig : X × ZMod n}
    (h : signSingle C.ops H r signers = some sig) :
    verify C.ops H (singleList C.ops signers) sig = true := by
  unfold signSingle at h
  by_cases h0 : r = 0 ∨ signers = [] ∨ ∃ σ ∈ signers, σ.1 = 0
  · rw [if_pos h0] at h
    exact absurd h (by simp)
  rw [if_neg h0] at h
  push Not at h0
  obtain ⟨hr, hne, hs⟩ := h0
  cases Option.some.inj h
  have hR : C.mulG r ≠ 0 := C.mulG_ne_zero hr
  have hlift : C.ops.liftX (C.ops.x (C.ops.mulG r)) =
      some (C.ops.signOf (C.mulG r) (C.mulG r)) := liftX_x_signOf C hR
  unfold verify
  dsimp only
  rw [hlift]
  dsimp only
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨by simpa [singleList] using hne, ?_⟩, ?_⟩
  · rw [List.all_eq_true]
    intro pkm hpkm
    obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hpkm
    change (C.liftX (C.x (C.mulG σ.1))).isSome = true
    rw [C.liftX_x_mulG (hs σ hσ)]
    rfl
  · change C.mulG ((if C.hasEvenY (C.mulG r) = true then r else -r) + _) =
      C.ops.signOf (C.mulG r) (C.mulG r) + _
    rw [map_add]
    congr 1
    · unfold Ops.signOf
      change _ = if C.hasEvenY (C.mulG r) = true then C.mulG r else -C.mulG r
      by_cases he : C.hasEvenY (C.mulG r) = true <;> simp [he]
    · exact (keySum_single C H (singleList C.ops signers) (C.x (C.mulG r)) signers hs).symm

omit [DecidableEq M] in
/-- **For a list and an `r`, at most one `s` verifies.** -/
theorem verify_unique {L : List (X × M)} {r : X} {s s' : ZMod n}
    (h : verify C.ops H L (r, s) = true) (h' : verify C.ops H L (r, s') = true) : s = s' := by
  unfold verify at h h'
  cases hR : C.ops.liftX r with
  | none => simp [hR] at h
  | some R =>
    simp only [hR, Bool.and_eq_true, decide_eq_true_eq] at h h'
    exact C.mulG_injective (h.2.trans h'.2.symm)

theorem sum_pubnonce_fst (signers : List (Signer n M)) :
    ((signers.map (Signer.pubnonce C)).map Prod.fst).sum = C.mulG (signers.map (·.r₁)).sum := by
  induction signers with
  | nil => simp
  | cons σ l ih =>
    simp only [List.map_cons, List.sum_cons, map_add, ih]
    rfl

theorem sum_pubnonce_snd (signers : List (Signer n M)) :
    ((signers.map (Signer.pubnonce C)).map Prod.snd).sum = C.mulG (signers.map (·.r₂)).sum := by
  induction signers with
  | nil => simp
  | cons σ l ih =>
    simp only [List.map_cons, List.sum_cons, map_add, ih]
    rfl

/-- **The protocol's signature is the single-party signature for the same
nonce.** If an honest session succeeds, its signature is the output of
`signSingle` on the signers' keys and messages with the nonce
`r = Σ r₁,ᵢ + b⋅Σ r₂,ᵢ`. -/
theorem sigAgg_eq_signSingle {signers : List (Signer n M)} {agg : PubNonce E}
    {psigs : List (ZMod n)} {sig : X × ZMod n}
    (hagg : nonceAgg (signers.map (Signer.pubnonce C)) = some agg)
    (hlen : psigs.length = signers.length)
    (hsign : ∀ (i : ℕ) (hi : i < signers.length),
      sign C.ops H (signers[i].r₁, signers[i].r₂) signers[i].sk signers[i].m agg
        (signers.map (Signer.pkm C)) (signers.map (Signer.pubnonce C)) = some (psigs[i]'(by omega)))
    (hsig : sigAgg C.ops H agg (signers.map (Signer.pkm C)) (signers.map (Signer.pubnonce C))
      psigs = some sig) :
    ∃ r, signSingle C.ops H r (signers.map fun σ => (σ.sk, σ.m)) = some sig := by
  have hv := verify_honest C H hagg hlen hsign hsig
  -- the session values
  have hsig' := hsig
  unfold sigAgg at hsig'
  split_ifs at hsig' with hl
  obtain ⟨⟨R, b⟩, hsv, rfl⟩ := Option.map_eq_some_iff.mp hsig'
  obtain ⟨hne, -, hR, hReq⟩ := getSessionValues_eq_some C H hsv
  have hagg' := nonceAgg_eq_some hagg
  set r := (signers.map (·.r₁)).sum + b * (signers.map (·.r₂)).sum with hr
  have hRr : C.mulG r = R := by
    rw [hReq, hagg', sum_pubnonce_fst, sum_pubnonce_snd, C.val_smul_mulG, ← map_add]
  have hr0 : r ≠ 0 := fun h => hR (by rw [← hRr, h, map_zero])
  have hsk : ∀ τ ∈ signers.map (fun σ : Signer n M => (σ.sk, σ.m)), τ.1 ≠ 0 := by
    intro τ hτ
    obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hτ
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hσ
    exact (sign_ne_zero H (hsign i hi)).2.2
  have hsne : signers.map (fun σ : Signer n M => (σ.sk, σ.m)) ≠ [] := by
    intro h
    exact hne (by simpa using h)
  have hlist : singleList C.ops (signers.map fun σ => (σ.sk, σ.m)) =
      signers.map (Signer.pkm C) := by
    simp [singleList, Signer.pkm]
  -- the single-party signature for `r`
  have hex : ∃ s₀, signSingle C.ops H r (signers.map fun σ => (σ.sk, σ.m)) =
      some (C.x (C.mulG r), s₀) := by
    unfold signSingle
    have h0 : ¬(r = 0 ∨ signers.map (fun σ : Signer n M => (σ.sk, σ.m)) = [] ∨
        ∃ σ ∈ signers.map (fun σ : Signer n M => (σ.sk, σ.m)), σ.1 = 0) := by
      push Not
      exact ⟨hr0, hsne, hsk⟩
    rw [if_neg h0]
    exact ⟨_, rfl⟩
  obtain ⟨s₀, hs₀⟩ := hex
  have hv₀ := verify_signSingle C H hs₀
  rw [hlist, hRr] at hv₀
  have := verify_unique C H hv hv₀
  refine ⟨r, ?_⟩
  rw [hs₀, hRr]
  exact congrArg some (Prod.ext rfl this.symm)

end Dahlias
