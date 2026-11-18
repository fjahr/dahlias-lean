import Dahlias.Security
import Dahlias.Fork

/-!
# The unforgeability game as a query algorithm

For a fixed secret key, fixed session nonces and fixed coins, the adversary
together with the honest signer is a deterministic algorithm that queries the
random oracle: `gameTree`. Its last query is the fork point, the oracle input
of an unsigned entry of the forgery. `forge_iff_accepts` says that the
adversary wins on a table exactly when `gameTree` accepts in the sense of the
forking lemma.
-/

set_option linter.unusedSectionVars false

namespace Dahlias.Security

open Taproot QTree

variable {n : ℕ} [Fact n.Prime] {E X M : Type} [AddCommGroup E] [DecidableEq E] [DecidableEq X]
  [DecidableEq M]

/-! ## `Sign` before and after its hash query -/

/-- The checks of `Sign` and the session values `(R, b)`: everything before
the challenge hash. -/
def signPre (O : Ops n E X) (H : Hashes n E X M) (secnonce : SecNonce n) (sk : ZMod n) (m : M)
    (agg : PubNonce E) (pm : List (X × M)) (pubnonces : List (PubNonce E)) :
    Option (E × ZMod n) :=
  if secnonce.1 = 0 ∨ secnonce.2 = 0 ∨ sk = 0 then none else
  match matchIdxs pubnonces (O.mulG secnonce.2) with
  | [j] =>
    if pm[j]? = some (O.x (O.mulG sk), m) then getSessionValues O H agg pm pubnonces else none
  | _ => none

/-- The partial signature, from the session values and the challenge. -/
def signPost (O : Ops n E X) (secnonce : SecNonce n) (sk : ZMod n) (Rb : E × ZMod n)
    (c : ZMod n) : ZMod n :=
  (if O.hasEvenY Rb.1 then secnonce.1 + Rb.2 * secnonce.2
    else -(secnonce.1 + Rb.2 * secnonce.2)) + c * O.evenScalar sk

theorem sign_eq (O : Ops n E X) (H : Hashes n E X M) (secnonce : SecNonce n) (sk : ZMod n)
    (m : M) (agg : PubNonce E) (pm : List (X × M)) (pubnonces : List (PubNonce E)) :
    sign O H secnonce sk m agg pm pubnonces =
      (signPre O H secnonce sk m agg pm pubnonces).map fun Rb =>
        signPost O secnonce sk Rb (H.sig pm (O.x Rb.1) (O.x (O.mulG sk), m)) := by
  obtain ⟨r₁, r₂⟩ := secnonce
  unfold sign signPre signPost
  dsimp only
  split_ifs with h0
  · rfl
  · rcases matchIdxs pubnonces (O.mulG r₂) with _ | ⟨j, _ | ⟨j', l⟩⟩
    · rfl
    · dsimp only
      split_ifs
      · cases getSessionValues O H agg pm pubnonces <;> rfl
      · rfl
    · rfl

/-- The session values do not depend on the challenge hash. -/
theorem getSessionValues_congr (O : Ops n E X) {H H' : Hashes n E X M}
    (h : H.nonceCoef = H'.nonceCoef) (agg : PubNonce E) (pm : List (X × M))
    (pubnonces : List (PubNonce E)) :
    getSessionValues O H agg pm pubnonces = getSessionValues O H' agg pm pubnonces := by
  unfold getSessionValues
  rw [h]

theorem signPre_congr (O : Ops n E X) {H H' : Hashes n E X M} (h : H.nonceCoef = H'.nonceCoef)
    (secnonce : SecNonce n) (sk : ZMod n) (m : M) (agg : PubNonce E) (pm : List (X × M))
    (pubnonces : List (PubNonce E)) :
    signPre O H secnonce sk m agg pm pubnonces = signPre O H' secnonce sk m agg pm pubnonces := by
  unfold signPre
  simp only [getSessionValues_congr O h]

/-! ## The honest signer as a query algorithm -/

variable (C : Curve n E X) (nonceCoef : E → E → List (X × M × E) → ZMod n) (N qs : ℕ)
  (x : ZMod n) (nonces : Fin qs → SecNonce n)

/-- The hash functions with a constant challenge hash, for the parts of the
protocol that do not use it. -/
abbrev H₀ : Hashes n E X M := hashesOf N nonceCoef fun _ => 0

/-- `challenger`, with the random oracle as an oracle. -/
def treeChallenger :
    (q : AdvQ n N E X M) → SignerState X M →
      QTree (SigIn N X M) (ZMod n) (AdvR q × SignerState X M)
  | .hash z, st => .ask z fun c => .done (c, st)
  | .openSession, st => .done (challenger C nonceCoef N qs x nonces (fun _ => 0) .openSession st)
  | .close k τ m agg pm pubnonces, st =>
    if h : k < qs ∧ k < st.opened ∧ k ∉ st.closed ∧ τ.2 ≠ 0 ∧ pm.length ≤ N then
      match signPre C.ops (H₀ nonceCoef N) (nonces ⟨k, h.1⟩) (τ.sk x) m agg pm pubnonces with
      | some Rb =>
        .ask (⟨pm, h.2.2.2.2⟩, C.x Rb.1, (C.x (C.mulG (τ.sk x)), m)) fun c =>
          .done (some (signPost C.ops (nonces ⟨k, h.1⟩) (τ.sk x) Rb c),
            { st with closed := k :: st.closed
                      signed := (pm, C.x (C.mulG (τ.sk x)), m) :: st.signed })
      | none => .done (none, st)
    else .done (none, st)

theorem eval_treeChallenger (T : SigIn N X M → ZMod n) (q : AdvQ n N E X M)
    (st : SignerState X M) :
    eval T (treeChallenger C nonceCoef N qs x nonces q st) =
      challenger C nonceCoef N qs x nonces T q st := by
  cases q with
  | hash z => rfl
  | openSession => rfl
  | close k τ m agg pm pubnonces =>
    unfold treeChallenger challenger
    dsimp only
    split_ifs with h
    · rw [sign_eq, signPre_congr C.ops (H := hashesOf N nonceCoef T) (H' := H₀ nonceCoef N) rfl]
      generalize signPre C.ops (H₀ nonceCoef N) (nonces ⟨k, h.1⟩) (τ.sk x) m agg pm pubnonces = p
      cases p with
      | none => rfl
      | some Rb => simp [eval, hashesOf, h.2.2.2.2]; rfl
    · rfl

theorem eval_interp (T : SigIn N X M → ZMod n) {α : Type} (t : Alg (AdvQ n N E X M) AdvR α)
    (st : SignerState X M) :
    eval T (Alg.interp (treeChallenger C nonceCoef N qs x nonces) t st) =
      t.run (challenger C nonceCoef N qs x nonces T) st := by
  induction t generalizing st with
  | done a => rfl
  | ask q f ih =>
    rw [Alg.interp_ask, eval_bind, eval_treeChallenger, Alg.run_ask]
    exact ih _ _

/-! ## The game -/

/-- The fork point of a forgery: the oracle input for the first entry of the
list with the honest signer's tweaked key that the signer did not sign. -/
def forkPoint (f : Forgery n X M) (st : SignerState X M) : Option (SigIn N X M) :=
  if h : f.L.length ≤ N ∧ f.τ.2 ≠ 0 ∧ f.τ.sk x ≠ 0 then
    (f.L.find? fun e => decide (e.1 = C.x (C.mulG (f.τ.sk x)) ∧
      (f.L, e.1, e.2) ∉ st.signed)).map fun e => (⟨f.L, h.1⟩, f.sig.1, e)
  else none

variable {Coins : Type} (A : Adversary n N E X M Coins) (coins : Coins)

/-- **The game as a query algorithm**: the adversary with the honest signer,
followed by a query of the fork point. -/
def gameTree : QTree (SigIn N X M) (ZMod n) (Forgery n X M × SignerState X M) :=
  Alg.interp (treeChallenger C nonceCoef N qs x nonces) (A coins (C.mulG x)) ⟨0, [], []⟩ >>=
    fun out =>
      match forkPoint C N x out.1 out.2 with
      | some z => .ask z fun _ => .done out
      | none => .done out

/-- The selected point: the fork point, if the forgery verifies. -/
def gameSel (T : SigIn N X M → ZMod n) (out : Forgery n X M × SignerState X M) :
    Option (SigIn N X M) :=
  if verify C.ops (hashesOf N nonceCoef T) out.1.L out.1.sig = true then
    forkPoint C N x out.1 out.2
  else none

theorem eval_gameTree (T : SigIn N X M → ZMod n) :
    eval T (gameTree C nonceCoef N qs x nonces A coins) =
      (A coins (C.mulG x)).run (challenger C nonceCoef N qs x nonces T) ⟨0, [], []⟩ := by
  unfold gameTree
  rw [eval_bind, eval_interp]
  split <;> rfl

omit [DecidableEq E] in
theorem forkPoint_isSome_iff (f : Forgery n X M) (st : SignerState X M) :
    (forkPoint C N x f st).isSome ↔
      f.τ.2 ≠ 0 ∧ f.τ.sk x ≠ 0 ∧ f.L.length ≤ N ∧
        ∃ m, (C.x (C.mulG (f.τ.sk x)), m) ∈ f.L ∧
          (f.L, C.x (C.mulG (f.τ.sk x)), m) ∉ st.signed := by
  unfold forkPoint
  split_ifs with h
  · simp only [Option.isSome_map, List.find?_isSome, decide_eq_true_eq, Prod.exists]
    constructor
    · rintro ⟨pk, m, hmem, rfl, hns⟩
      exact ⟨h.2.1, h.2.2, h.1, m, hmem, hns⟩
    · rintro ⟨-, -, -, m, hmem, hns⟩
      exact ⟨_, m, hmem, rfl, hns⟩
  · simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
    rintro ⟨h1, h2, h3, -⟩
    exact h ⟨h3, h1, h2⟩

/-- **The adversary wins exactly when the game algorithm accepts.** -/
theorem wins_iff_accepts (T : SigIn N X M → ZMod n) :
    Wins C nonceCoef N x T
        ((A coins (C.mulG x)).run (challenger C nonceCoef N qs x nonces T) ⟨0, [], []⟩).1
        ((A coins (C.mulG x)).run (challenger C nonceCoef N qs x nonces T) ⟨0, [], []⟩).2 ↔
      Accepts (gameTree C nonceCoef N qs x nonces A coins) (gameSel C nonceCoef N x) T := by
  rw [← eval_gameTree]
  set out := eval T (gameTree C nonceCoef N qs x nonces A coins) with hout
  have hmem : ∀ z, forkPoint C N x out.1 out.2 = some z →
      z ∈ fresh T (gameTree C nonceCoef N qs x nonces A coins) := by
    intro z hz
    have hev : out = (A coins (C.mulG x)).run (challenger C nonceCoef N qs x nonces T)
        ⟨0, [], []⟩ := eval_gameTree C nonceCoef N qs x nonces A coins T
    unfold gameTree
    rw [fresh_bind, eval_interp, ← hev, hz]
    exact mem_flog_ask T _ z _
  unfold Accepts Wins gameSel
  simp only [← hout]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp
      ((forkPoint_isSome_iff C N x out.1 out.2).mpr ⟨h1, h2, h3, h4⟩)
    exact ⟨z, by simp [h5, hz], hmem z hz⟩
  · rintro ⟨z, hz, -⟩
    split_ifs at hz with hv
    obtain ⟨h1, h2, h3, h4⟩ := (forkPoint_isSome_iff C N x out.1 out.2).mp (by simp [hz])
    exact ⟨h1, h2, h3, h4, hv⟩

end Dahlias.Security
