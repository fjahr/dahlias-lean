import Dahlias.Proofs.ForkGame

/-!
# The reduction to AOMDL and the collision finder

`reduction A` is an AOMDL adversary that runs the forger `A` twice. It asks
for `2⋅qs + 1` challenges: the honest signer's public key `P` and the two
nonces of every session. It answers `Sign` with its discrete logarithm oracle
and remembers the answers, so that a query it has seen for the same session is
not asked again. After the second run it spends the queries it has left on the
sessions with fewer than two answers, which makes two queries per session, and
solves for all discrete logarithms.

`collider A` runs the game twice with the secret key and returns two inputs of
the nonce coefficient hash from the same session, one from each run, with the
same hash value.

This file has the definitions; the proofs follow in `Dahlias.Proofs.Simulate`
and `Dahlias.Proofs.Extract`.
-/

set_option linter.unusedSectionVars false

namespace Dahlias.Security

open Taproot QTree Function

variable {n : ℕ} [Fact n.Prime] {E X M : Type} [AddCommGroup E] [DecidableEq E] [DecidableEq X]
  [DecidableEq M] (C : Curve n E X) (nonceCoef : E → E → List (X × M × E) → ZMod n) (N qs : ℕ)

/-! ## Public versions of the signer's computations -/

/-- The tweaked public key point. -/
def Tweak.pk (C : Curve n E X) (τ : Tweak n) (P : E) : E := C.mulG τ.1 + τ.2.val • P

/-- `P` or `-P`, whichever has an even y. -/
def evenLift (C : Curve n E X) (P : E) : E := if C.hasEvenY P then P else -P

/-- `signPre` from the signer's public nonce `R₂` and public key point. -/
def signPrePub (H : Hashes n E X M) (R₂ Pt : E) (m : M) (agg : PubNonce E)
    (pm : List (X × M)) (pubnonces : List (PubNonce E)) : Option (E × ZMod n) :=
  if Pt = 0 then none else
  match matchIdxs pubnonces R₂ with
  | [j] => if pm[j]? = some (C.x Pt, m) then getSessionValues C.ops H agg pm pubnonces else none
  | _ => none

/-- The point whose discrete logarithm is the partial signature: `e⋅(R₁ + b⋅R₂) + c⋅P'` with
`P'` the even-y version of the tweaked key. -/
def dlogPoint (U : PubNonce E) (Pt : E) (Rb : E × ZMod n) (c : ZMod n) : E :=
  C.ops.signOf Rb.1 (U.1 + Rb.2.val • U.2) + c.val • evenLift C Pt

/-! ## Records of closed sessions -/

/-- A successful `Sign` of the honest signer: the session, the inputs, the
session values `(R, b)`, the challenge and the partial signature. -/
structure CloseRec (n : ℕ) (E X M : Type) where
  k : ℕ
  τ : Tweak n
  m : M
  agg : PubNonce E
  pm : List (X × M)
  pubs : List (PubNonce E)
  Rb : E × ZMod n
  c : ZMod n
  s : ZMod n

/-- The input of the nonce coefficient hash in a record. -/
def CloseRec.ncIn (r : CloseRec n E X M) : E × E × List (X × M × E) :=
  (r.agg.1, r.agg.2, coefItems r.pm r.pubs)

/-- The nonce coefficient hash on an input. -/
def ncHash (z : E × E × List (X × M × E)) : ZMod n := nonceCoef z.1 z.2.1 z.2.2

/-- The honest signer of `challenger`, keeping a record of every successful
`Sign`. -/
def logChallenger (x : ZMod n) (nonces : Fin qs → SecNonce n) (T : SigIn N X M → ZMod n) :
    (q : AdvQ n N E X M) → SignerState X M × List (CloseRec n E X M) →
      AdvR q × (SignerState X M × List (CloseRec n E X M))
  | .hash z, st => (T z, st)
  | .openSession, st =>
    ((challenger C nonceCoef N qs x nonces T .openSession st.1).1,
      ((challenger C nonceCoef N qs x nonces T .openSession st.1).2, st.2))
  | .close k τ m agg pm pubnonces, st =>
    if h : k < qs ∧ k < st.1.opened ∧ k ∉ st.1.closed ∧ τ.2 ≠ 0 ∧ pm.length ≤ N then
      match signPre C.ops (H₀ nonceCoef N) (nonces ⟨k, h.1⟩) (τ.sk x) m agg pm pubnonces with
      | some Rb =>
        let c := T (⟨pm, h.2.2.2.2⟩, C.x Rb.1, (C.x (C.mulG (τ.sk x)), m))
        let s := signPost C.ops (nonces ⟨k, h.1⟩) (τ.sk x) Rb c
        (some s, ({ st.1 with closed := k :: st.1.closed
                              signed := (pm, C.x (C.mulG (τ.sk x)), m) :: st.1.signed },
          ⟨k, τ, m, agg, pm, pubnonces, Rb, c, s⟩ :: st.2))
      | none => (none, st)
    else (none, st)

/-! ## The reduction -/

/-- The reduction's state while it runs the forger: the signer's state, the
records of this run, and the records of all discrete logarithm queries. -/
structure SimState (n : ℕ) (E X M : Type) where
  signer : SignerState X M
  recs : List (CloseRec n E X M)
  cache : List (CloseRec n E X M)

variable (P : E) (U : ℕ → PubNonce E)

/-- The discrete logarithm query point of a record. -/
def CloseRec.point (r : CloseRec n E X M) : E :=
  dlogPoint C (U r.k) (r.τ.pk C P) r.Rb r.c

/-- The representation of the query point of a `Sign` in the challenges
`P, U₀.1, U₀.2, U₁.1, …`. -/
def dlogRep (k : ℕ) (τ : Tweak n) (Rb : E × ZMod n) (c : ZMod n) : ZMod n × List (ZMod n) :=
  let ε : ZMod n := if C.hasEvenY (τ.pk C P) then 1 else -1
  let e : ZMod n := if C.hasEvenY Rb.1 then 1 else -1
  (c * ε * τ.1, (List.range (2 * qs + 1)).map fun i =>
    if i = 0 then c * ε * τ.2 else if i = 2 * k + 1 then e else if i = 2 * k + 2 then e * Rb.2
    else 0)

/-- The honest signer as the reduction simulates it. -/
def simChallenger (T : SigIn N X M → ZMod n) :
    (q : AdvQ n N E X M) → SimState n E X M →
      Alg (OmdlQ n) (OmdlR E) (AdvR q × SimState n E X M)
  | .hash z, st => .done (T z, st)
  | .openSession, st =>
    .done (if st.signer.opened < qs then
        (some (U st.signer.opened), { st with signer.opened := st.signer.opened + 1 })
      else (none, st))
  | .close k τ m agg pm pubnonces, st =>
    if h : k < qs ∧ k < st.signer.opened ∧ k ∉ st.signer.closed ∧ τ.2 ≠ 0 ∧ pm.length ≤ N then
      match signPrePub C (H₀ nonceCoef N) (U k).2 (τ.pk C P) m agg pm pubnonces with
      | some Rb =>
        let c := T (⟨pm, h.2.2.2.2⟩, C.x Rb.1, (C.x (τ.pk C P), m))
        let signer' : SignerState X M :=
          { st.signer with closed := k :: st.signer.closed
                           signed := (pm, C.x (τ.pk C P), m) :: st.signer.signed }
        match st.cache.find? fun r =>
            decide (r.k = k ∧ r.point C P U = dlogPoint C (U k) (τ.pk C P) Rb c) with
        | some r =>
          .done (some r.s, { st with signer := signer'
                                     recs := ⟨k, τ, m, agg, pm, pubnonces, Rb, c, r.s⟩ :: st.recs })
        | none =>
          .ask (.dlog (dlogRep C qs P k τ Rb c).1 (dlogRep C qs P k τ Rb c).2) fun (s : ZMod n) =>
            .done (some s, { signer := signer'
                             recs := ⟨k, τ, m, agg, pm, pubnonces, Rb, c, s⟩ :: st.recs
                             cache := ⟨k, τ, m, agg, pm, pubnonces, Rb, c, s⟩ :: st.cache })
      | none => .done (none, st)
    else .done (none, st)

/-- Ask for `c` challenges. -/
def getChals : ℕ → Alg (OmdlQ n) (OmdlR E) (List E)
  | 0 => .done []
  | c + 1 => .ask .chal fun p => getChals c >>= fun rest => .done (p.getD 0 :: rest)

/-- The fork point, from the public key point. -/
def forkPointPub (f : Forgery n X M) (st : SignerState X M) : Option (SigIn N X M) :=
  if h : f.L.length ≤ N ∧ f.τ.2 ≠ 0 ∧ f.τ.pk C P ≠ 0 then
    (f.L.find? fun e => decide (e.1 = C.x (f.τ.pk C P) ∧
      (f.L, e.1, e.2) ∉ st.signed)).map fun e => (⟨f.L, h.1⟩, f.sig.1, e)
  else none

/-- The secret key from the discrete logarithm `v` of the even-y version of
the tweaked key. -/
def extractX (τ : Tweak n) (v : ZMod n) : ZMod n :=
  if C.mulG ((v - τ.1) / τ.2) = P then (v - τ.1) / τ.2 else (-v - τ.1) / τ.2

/-- `r₁ + b⋅r₂` from a record, given the secret key `x`. -/
def CloseRec.w (r : CloseRec n E X M) (x : ZMod n) : ZMod n :=
  (if C.hasEvenY r.Rb.1 then (1 : ZMod n) else -1) *
    (r.s - r.c * (if C.hasEvenY (r.τ.pk C P) then r.τ.sk x else -r.τ.sk x))

/-- The queries the reduction has left for session `k`, and the session's two
nonces as a function of the secret key. -/
def solveSession (k : ℕ) (cache : List (CloseRec n E X M)) :
    Alg (OmdlQ n) (OmdlR E) (ZMod n → ZMod n × ZMod n) :=
  let unit (i : ℕ) (v : ZMod n) : List (ZMod n) :=
    (List.range (2 * qs + 1)).map fun j => if j = i then v else 0
  match cache.filter fun r => decide (r.k = k) with
  | [] =>
    .ask (.dlog 0 (unit (2 * k + 1) 1)) fun (v₁ : ZMod n) =>
      .ask (.dlog 0 (unit (2 * k + 2) 1)) fun (v₂ : ZMod n) => .done fun _ => (v₁, v₂)
  | [a] =>
    .ask (.dlog 0 ((List.range (2 * qs + 1)).map fun j =>
        if j = 2 * k + 1 then 1 else if j = 2 * k + 2 then a.Rb.2 + 1 else 0))
        fun (v : ZMod n) =>
      .done fun x => (a.w C P x - a.Rb.2 * (v - a.w C P x), v - a.w C P x)
  | a :: a' :: _ =>
    .done fun x =>
      let r₂ := (a.w C P x - a'.w C P x) / (a.Rb.2 - a'.Rb.2)
      (a.w C P x - a.Rb.2 * r₂, r₂)

/-- `solveSession` for the sessions `0, …, k - 1`. -/
def solveSessions (cache : List (CloseRec n E X M)) :
    ℕ → Alg (OmdlQ n) (OmdlR E) (List (ZMod n → ZMod n × ZMod n))
  | 0 => .done []
  | k + 1 => solveSessions cache k >>= fun l =>
      solveSession C qs P k cache >>= fun f => .done (l ++ [f])

variable {Coins : Type} (A : Adversary n N E X M Coins)

/-- **The reduction**: an AOMDL adversary from a forger. Its coins are the
forger's coins, the random oracle table and the new value at the fork point. -/
def reduction : OmdlAdversary n E (Coins × (SigIn N X M → ZMod n) × ZMod n) := fun ρ =>
  getChals (2 * qs + 1) >>= fun chals =>
    let P := chals.getD 0 0
    let U : ℕ → PubNonce E := fun k => (chals.getD (2 * k + 1) 0, chals.getD (2 * k + 2) 0)
    let T := ρ.2.1
    Alg.interp (simChallenger C nonceCoef N qs P U T) (A ρ.1 P) ⟨⟨0, [], []⟩, [], []⟩ >>=
      fun r₁ =>
        match forkPointPub C N P r₁.1 r₁.2.signer with
        | none => .done []
        | some z =>
          let T' := update T z ρ.2.2
          Alg.interp (simChallenger C nonceCoef N qs P U T') (A ρ.1 P)
              ⟨⟨0, [], []⟩, [], r₁.2.cache⟩ >>= fun r₂ =>
            solveSessions C qs P r₂.2.cache qs >>= fun sols =>
              let cnt : ZMod n := ((r₁.1.L.filter fun e => decide (e = z.2.2)).length : ZMod n)
              let v := (r₁.1.sig.2 - r₂.1.sig.2) / (cnt * (T z - ρ.2.2))
              let x := extractX C P r₁.1.τ v
              .done ((List.range (2 * qs + 1)).map fun i =>
                if i = 0 then x
                else if (i - 1) % 2 = 0 then ((sols.getD ((i - 1) / 2) fun _ => (0, 0)) x).1
                else ((sols.getD ((i - 1) / 2) fun _ => (0, 0)) x).2)

/-! ## The collision finder -/

/-- The records of the game on a sample with the table `T`. -/
def gameRecs (ω : ForgeSample n N qs X M Coins) (T : SigIn N X M → ZMod n) :
    Forgery n X M × SignerState X M × List (CloseRec n E X M) :=
  (A ω.2.2.1 (C.mulG (ω.1 : ZMod n))).run
    (logChallenger C nonceCoef N qs (ω.1 : ZMod n) (noncesOf qs ω.2.1) T) (⟨0, [], []⟩, [])

/-- A collision of the nonce coefficient hash. -/
def IsCollision (p : (E × E × List (X × M × E)) × (E × E × List (X × M × E))) : Prop :=
  p.1 ≠ p.2 ∧ ncHash nonceCoef p.1 = ncHash nonceCoef p.2

open Classical in
/-- **The collision finder**: run the game on the sample, fork it, and look
for two records of the same session, one from each run, whose nonce coefficient
inputs collide. -/
noncomputable def collider (p : ForgeSample n N qs X M Coins × ZMod n) :
    (E × E × List (X × M × E)) × (E × E × List (X × M × E)) :=
  let ω := p.1
  let T := ω.2.2.2
  let r₁ := gameRecs C nonceCoef N qs A ω T
  match forkPoint C N (ω.1 : ZMod n) r₁.1 r₁.2.1 with
  | none => ((0, 0, []), (0, 0, []))
  | some z =>
    let r₂ := gameRecs C nonceCoef N qs A ω (update T z p.2)
    ((r₁.2.2.product r₂.2.2).find? fun ab =>
      decide (ab.1.k = ab.2.k ∧ IsCollision nonceCoef (ab.1.ncIn, ab.2.ncIn))).elim
        ((0, 0, []), (0, 0, [])) fun ab => (ab.1.ncIn, ab.2.ncIn)

end Dahlias.Security
