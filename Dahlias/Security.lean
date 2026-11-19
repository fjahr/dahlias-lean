import Dahlias.Alg
import Dahlias.Basic
import Dahlias.Prob

/-!
# Security definitions for BIP 459

The unforgeability game for the signing protocol of `Dahlias.Basic` and the
algebraic one-more discrete logarithm (AOMDL) game. Everything a reader has to
trust about the security theorem is in this file and in `Dahlias.Basic`.

## Model

* **Algorithms.** Adversaries are deterministic oracle algorithms (`Alg`) that
  take coins from a finite type. An experiment is a predicate on a finite
  sample, and its probability is the fraction of samples that satisfy it
  (`prob`, in `Dahlias.Prob`). There is no notion of running time; the theorems bound numbers of
  queries.
* **Hash functions.** `hash_BIP0459/sig` is a random oracle: a uniformly
  random table `T` on the inputs `(L, r, (pk, m))` with `L` of at most `N`
  entries. The adversary reaches it only through queries. With `X` and `M`
  finite the table is a finite object, and sampling it up front is the same as
  sampling it lazily. `hash_BIP0459/noncecoef` is a fixed function; the
  theorem measures how often a concrete algorithm finds a collision of it.
* **Signers per signature.** The game is for lists of at most `N` entries: the
  honest signer does not sign longer lists and longer forgeries do not count.

## The game (`forgeExperiment`)

This is the paper's co-EUF-CMA-TK game (ePrint 2025/692, Fig. 5) for the
algorithms of BIP 459, with two differences and one addition that are
explained below.

The honest signer has a secret key `x ≠ 0`. The adversary gets the point
`x⋅G` and may

* query the random oracle,
* open a signing session, which returns a fresh public nonce `(r₁⋅G, r₂⋅G)`
  of the honest signer,
* close an open session `k` with a tweak `(α, β)`, `β ≠ 0`, a message, an
  aggregate nonce and the lists of public keys, messages and public nonces.
  The signer runs `Sign` with the secret key `α + β⋅x`. Sessions can be closed
  concurrently and in any order, each at most once,
* ask for a single-party signature for a list of tweaks and messages (see
  the addition below).

Sessions and single-party signatures together use at most `qs` nonce slots.

The adversary outputs a list `L`, a tweak `(α, β)` and a signature. It wins if
the signature verifies for `L` and `L` contains an entry `(pk*, m)`, with
`pk*` the x-only public key of `α + β⋅x`, such that the signer never signed
`m` for the list `L` under the key `pk*`.

**Tweaks.** A tweak is an affine map `x ↦ α + β⋅x`. BIP 459's plain and x-only
tweaks, and any sequence of them, are of this form with `β = ±1`
(`Dahlias.Tweaks`).

**Difference 1: the game records tweaked keys, not tweaks.** The paper records
`(L, τ, m)` for every signing query and lets the forgery name any tweak `τ`
with `(L, τ, m)` unrecorded. Its proof needs that two different tweaks with
the same tweaked key reveal the secret key. For x-only keys that is false:
`(α, β)` and `(-α, -β)` give the same x-only key and the same signatures. The
game here records `(L, pk̃, m)` with `pk̃` the tweaked x-only key.

**Addition: single-party signatures.** The paper and BIP 459 do not say how a
party that holds all keys of a list signs without running the protocol with
itself. The query `single` models the method `Dahlias.signSingle`: for tweaks
`τ₀, …` with `βᵢ ≠ 0` and messages `m₀, …` the signer draws one uniform
nonzero nonce `r` and returns `(x(r⋅G), s)` with `s = ±r + Σ cᵢ⋅dᵢ` for the
list `L` of its tweaked keys and the messages. All entries of `L` count as
signed for `L`. The query uses up a nonce slot whether it succeeds or not.
`Dahlias.Security.challenger_single` proves that the answer is `signSingle`.
An adversary that never asks this query plays the game without the addition.

**Difference 2: a failed `Sign` does not close the session.** In the paper a
session is closed by any call. Here a call in which `Sign` fails leaves the
session open and records nothing, which gives the adversary more freedom.
-/

namespace Dahlias.Security

open Taproot

variable {n : ℕ} [Fact n.Prime] {E X M : Type} [AddCommGroup E] [DecidableEq E] [DecidableEq X]
  [DecidableEq M]

/-! ## The random oracle -/

/-- Lists of at most `N` public key and message pairs. -/
abbrev BList (N : ℕ) (X M : Type) := {L : List (X × M) // L.length ≤ N}

/-- An input of `hash_BIP0459/sig`: the list `L`, `xbytes(R)` and the signer's
`(pk, m)`. -/
abbrev SigIn (N : ℕ) (X M : Type) := BList N X M × X × (X × M)

/-- The hash functions of the protocol, with `hash_BIP0459/sig` given by the
table `T`. -/
def hashesOf (N : ℕ) (nonceCoef : E → E → List (X × M × E) → ZMod n)
    (T : SigIn N X M → ZMod n) : Hashes n E X M where
  nonceCoef := nonceCoef
  sig pm r pkm := if h : pm.length ≤ N then T (⟨pm, h⟩, r, pkm) else 0

/-! ## The unforgeability game -/

/-- A tweak `(α, β)`: the affine map `x ↦ α + β⋅x` on secret keys. -/
abbrev Tweak (n : ℕ) := ZMod n × ZMod n

/-- The tweaked secret key. -/
def Tweak.sk (τ : Tweak n) (x : ZMod n) : ZMod n := τ.1 + τ.2 * x

/-- The adversary's queries. -/
inductive AdvQ (n N : ℕ) (E X M : Type) where
  /-- A random oracle query. -/
  | hash (z : SigIn N X M)
  /-- Open a signing session. -/
  | openSession
  /-- Close session `k`: the honest signer's `Sign` with the tweak `τ`. -/
  | close (k : ℕ) (τ : Tweak n) (m : M) (agg : PubNonce E) (pm : List (X × M))
      (pubnonces : List (PubNonce E))
  /-- Sign alone for a list of the honest signer's own tweaked keys and
  messages, with one nonce. -/
  | single (items : List (Tweak n × M))

/-- The answers: a hash value, the signer's public nonce (if a session is
left), and the partial signature (if `Sign` succeeds). -/
def AdvR {N : ℕ} : AdvQ n N E X M → Type
  | .hash _ => ZMod n
  | .openSession => Option (PubNonce E)
  | .close .. => Option (ZMod n)
  | .single _ => Option (X × ZMod n)

/-- A forgery: the list, the tweak of the honest signer's key, the signature. -/
structure Forgery (n : ℕ) (X M : Type) where
  L : List (X × M)
  τ : Tweak n
  sig : X × ZMod n

/-- An adversary with coins in `Coins`. Its input is the honest signer's
public key point. -/
abbrev Adversary (n N : ℕ) (E X M Coins : Type) :=
  Coins → E → Alg (AdvQ n N E X M) AdvR (Forgery n X M)

/-- The honest signer's state: the number of opened sessions, the closed
sessions, and the recorded `(L, pk̃, m)`. -/
structure SignerState (X M : Type) where
  opened : ℕ
  closed : List ℕ
  signed : List (List (X × M) × X × M)

/-- The list `L` of a single-party signing query: the tweaked public keys with
their messages. -/
def singleKeys (C : Curve n E X) (x : ZMod n) (items : List (Tweak n × M)) : List (X × M) :=
  items.map fun i => (C.x (C.mulG (i.1.sk x)), i.2)

/-- The input of the nonce coefficient hash that the derived nonce of a
single-party signature uses. No session has this input: its first two entries
are the point at infinity. -/
def singleNcIn (L : List (X × M)) : E × E × List (X × M × E) :=
  (0, 0, L.map fun e => (e.1, e.2, 0))

/-- The nonce of a single-party signature from the nonce pair of its slot.
With `der = false` it is the first nonce: a uniform nonzero scalar. With
`der = true` it is `r₁ + b⋅r₂` for a coefficient `b` derived from the list.
The security proof works with the second form and shows that the adversary
cannot tell the two apart (`Dahlias.Security.forgeAdvantage_le_derived`). -/
def singleNonce (der : Bool) (nonceCoef : E → E → List (X × M × E) → ZMod n) (L : List (X × M))
    (ν : SecNonce n) : ZMod n :=
  if der then ν.1 + nonceCoef 0 0 ((singleNcIn (E := E) L).2.2) * ν.2 else ν.1

/-- The `s` of a single-party signature with nonce `r` and challenges `cs`. -/
def singleS (C : Curve n E X) (x : ZMod n) (items : List (Tweak n × M)) (r : ZMod n)
    (cs : List (ZMod n)) : ZMod n :=
  (if C.hasEvenY (C.mulG r) then r else -r) +
    (List.zipWith (fun c (i : Tweak n × M) => c * C.evenScalar (i.1.sk x)) cs items).sum

/-- The game's answers to the adversary's queries. Sessions and single-party
signatures draw their nonces from the same `qs` slots. -/
def challengerG (der : Bool) (C : Curve n E X) (nonceCoef : E → E → List (X × M × E) → ZMod n)
    (N qs : ℕ) (x : ZMod n) (nonces : Fin qs → SecNonce n) (T : SigIn N X M → ZMod n) :
    (q : AdvQ n N E X M) → SignerState X M → AdvR q × SignerState X M
  | .hash z, st => (T z, st)
  | .openSession, st =>
    if h : st.opened < qs then
      (some (C.mulG (nonces ⟨st.opened, h⟩).1, C.mulG (nonces ⟨st.opened, h⟩).2),
        { st with opened := st.opened + 1 })
    else (none, st)
  | .close k τ m agg pm pubnonces, st =>
    if h : k < qs ∧ k < st.opened ∧ k ∉ st.closed ∧ τ.2 ≠ 0 ∧ pm.length ≤ N then
      match sign C.ops (hashesOf N nonceCoef T) (nonces ⟨k, h.1⟩) (τ.sk x) m agg pm pubnonces with
      | some s => (some s, { st with closed := k :: st.closed
                                     signed := (pm, C.x (C.mulG (τ.sk x)), m) :: st.signed })
      | none => (none, st)
    else (none, st)
  | .single items, st =>
    if h : st.opened < qs then
      let r := singleNonce der nonceCoef (singleKeys C x items) (nonces ⟨st.opened, h⟩)
      if hc : items ≠ [] ∧ (singleKeys C x items).length ≤ N ∧ r ≠ 0 ∧
          ∀ i ∈ items, i.1.2 ≠ 0 ∧ i.1.sk x ≠ 0 then
        (some (C.x (C.mulG r), singleS C x items r ((singleKeys C x items).map fun e =>
            T (⟨singleKeys C x items, hc.2.1⟩, C.x (C.mulG r), e))),
          { opened := st.opened + 1
            closed := st.opened :: st.closed
            signed := (singleKeys C x items).map (fun e => (singleKeys C x items, e.1, e.2)) ++
              st.signed })
      else (none, { st with opened := st.opened + 1, closed := st.opened :: st.closed })
    else (none, st)

/-- The game: a single-party signature uses one uniform nonzero nonce. -/
abbrev challenger (C : Curve n E X) (nonceCoef : E → E → List (X × M × E) → ZMod n)
    (N qs : ℕ) (x : ZMod n) (nonces : Fin qs → SecNonce n) (T : SigIn N X M → ZMod n) :
    (q : AdvQ n N E X M) → SignerState X M → AdvR q × SignerState X M :=
  challengerG false C nonceCoef N qs x nonces T

/-- The winning condition on the adversary's output and the signer's final
state. -/
def Wins (C : Curve n E X) (nonceCoef : E → E → List (X × M × E) → ZMod n) (N : ℕ) (x : ZMod n)
    (T : SigIn N X M → ZMod n) (f : Forgery n X M) (st : SignerState X M) : Prop :=
  f.τ.2 ≠ 0 ∧ f.τ.sk x ≠ 0 ∧ f.L.length ≤ N ∧
    (∃ m, (C.x (C.mulG (f.τ.sk x)), m) ∈ f.L ∧ (f.L, C.x (C.mulG (f.τ.sk x)), m) ∉ st.signed) ∧
    verify C.ops (hashesOf N nonceCoef T) f.L f.sig = true

/-- The sample of the game: the secret key, the nonces of the `qs` sessions,
the adversary's coins and the random oracle. -/
abbrev ForgeSample (n N qs : ℕ) (X M Coins : Type) :=
  (ZMod n)ˣ × (Fin qs → (ZMod n)ˣ × (ZMod n)ˣ) × Coins × (SigIn N X M → ZMod n)

/-- The unforgeability game on one sample, for either form of the nonce of a
single-party signature. -/
def forgeExperimentG (der : Bool) (C : Curve n E X)
    (nonceCoef : E → E → List (X × M × E) → ZMod n) (N qs : ℕ)
    {Coins : Type} (A : Adversary n N E X M Coins) (ω : ForgeSample n N qs X M Coins) : Prop :=
  let x : ZMod n := ω.1
  let nonces : Fin qs → SecNonce n := fun k => ((ω.2.1 k).1, (ω.2.1 k).2)
  let T := ω.2.2.2
  let out := (A ω.2.2.1 (C.mulG x)).run (challengerG der C nonceCoef N qs x nonces T) ⟨0, [], []⟩
  Wins C nonceCoef N x T out.1 out.2

/-- **The unforgeability game** on one sample. -/
abbrev forgeExperiment (C : Curve n E X) (nonceCoef : E → E → List (X × M × E) → ZMod n)
    (N qs : ℕ) {Coins : Type} (A : Adversary n N E X M Coins)
    (ω : ForgeSample n N qs X M Coins) : Prop :=
  forgeExperimentG false C nonceCoef N qs A ω

/-- The probability of forging, for either form of the nonce of a single-party
signature. -/
noncomputable def forgeAdvantageG (der : Bool) (C : Curve n E X)
    (nonceCoef : E → E → List (X × M × E) → ZMod n) (N qs : ℕ) {Coins : Type} [Fintype Coins]
    [Fintype (SigIn N X M)] (A : Adversary n N E X M Coins) : ℝ :=
  prob (forgeExperimentG der C nonceCoef N qs A)

/-- The adversary's probability of forging. -/
noncomputable abbrev forgeAdvantage (C : Curve n E X)
    (nonceCoef : E → E → List (X × M × E) → ZMod n) (N qs : ℕ) {Coins : Type} [Fintype Coins]
    [Fintype (SigIn N X M)] (A : Adversary n N E X M Coins) : ℝ :=
  forgeAdvantageG false C nonceCoef N qs A

/-- The number of random oracle queries an algorithm makes is at most `qh`,
whatever the answers. A single-party signing query counts as one query for
every entry of its list. -/
def HashBound {N : ℕ} {α : Type} {R : AdvQ n N E X M → Type} :
    Alg (AdvQ n N E X M) R α → ℕ → Prop
  | .done _, _ => True
  | .ask (.hash _) f, qh => 0 < qh ∧ ∀ r, HashBound (f r) (qh - 1)
  | .ask .openSession f, qh => ∀ r, HashBound (f r) qh
  | .ask (.close ..) f, qh => ∀ r, HashBound (f r) qh
  | .ask (.single items) f, qh => items.length ≤ qh ∧ ∀ r, HashBound (f r) (qh - items.length)

/-! ## The algebraic one-more discrete logarithm game -/

/-- The queries of an AOMDL adversary. -/
inductive OmdlQ (n : ℕ) where
  /-- Ask for the next challenge point. -/
  | chal
  /-- Ask for the discrete logarithm of `a⋅G + b₁⋅X₁ + … + b_ℓ⋅X_ℓ`, with
  `X₁, …, X_ℓ` the challenges received so far. -/
  | dlog (a : ZMod n) (bs : List (ZMod n))

/-- The answers: a challenge point (if one is left) and a scalar. -/
def OmdlR (E : Type) : OmdlQ n → Type
  | .chal => Option E
  | .dlog .. => ZMod n

/-- An AOMDL adversary with coins in `Coins`. It outputs the discrete
logarithms of the challenges it received. -/
abbrev OmdlAdversary (n : ℕ) (E Coins : Type) := Coins → Alg (OmdlQ n) (OmdlR E) (List (ZMod n))

/-- The discrete logarithms of the first `ℓ` challenges. -/
def chalLogs {c : ℕ} (xs : Fin c → (ZMod n)ˣ) (ℓ : ℕ) : List (ZMod n) :=
  (List.range ℓ).map fun i => if h : i < c then ((xs ⟨i, h⟩ : (ZMod n)ˣ) : ZMod n) else 0

/-- The game's answers. The state is the number of challenges and of discrete
logarithm queries so far. -/
def omdlChallenger (C : Curve n E X) {c : ℕ} (xs : Fin c → (ZMod n)ˣ) :
    (q : OmdlQ n) → ℕ × ℕ → OmdlR E q × (ℕ × ℕ)
  | .chal, (ℓ, d) =>
    if h : ℓ < c then (some (C.mulG ((xs ⟨ℓ, h⟩ : (ZMod n)ˣ) : ZMod n)), (ℓ + 1, d))
    else (none, (ℓ, d))
  | .dlog a bs, (ℓ, d) =>
    (a + (List.zipWith (· * ·) bs (chalLogs xs ℓ)).sum, (ℓ, d + 1))

/-- **The AOMDL game** on one sample: at most `c` challenges with nonzero
discrete logarithms `xs`. The adversary wins if it outputs the discrete
logarithms of all challenges it received and made fewer discrete logarithm
queries than it received challenges. -/
def omdlExperiment (C : Curve n E X) (c : ℕ) {Coins : Type} (B : OmdlAdversary n E Coins)
    (ω : (Fin c → (ZMod n)ˣ) × Coins) : Prop :=
  let out := (B ω.2).run (omdlChallenger C ω.1) (0, 0)
  out.1 = chalLogs ω.1 out.2.1 ∧ out.2.2 < out.2.1

/-- The adversary's probability of winning the AOMDL game. -/
noncomputable def omdlAdvantage (C : Curve n E X) (c : ℕ) {Coins : Type} [Fintype Coins]
    (B : OmdlAdversary n E Coins) : ℝ :=
  prob (omdlExperiment C c B)

end Dahlias.Security
