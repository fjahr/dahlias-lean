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

/-- A key term of a signature of the honest signer: the tweak, the message and
the challenge. A partial signature has one, a single-party signature has one
for every entry of its list. -/
abbrev KeyTerm (n : ℕ) (M : Type) := Tweak n × M × ZMod n

/-- `c₀⋅P'₀ + c₁⋅P'₁ + …` with `P'ᵢ` the even-y versions of the tweaked keys. -/
def keyPoint (P : E) (keys : List (KeyTerm n M)) : E :=
  (keys.map fun κ => κ.2.2.val • evenLift C (κ.1.pk C P)).sum

/-- The discrete logarithm of `keyPoint`, from the secret key. -/
def keySk (x : ZMod n) (keys : List (KeyTerm n M)) : ZMod n :=
  (keys.map fun κ => κ.2.2 * C.evenScalar (κ.1.sk x)).sum

/-- The signature scalar: `e⋅(r₁ + b⋅r₂)` plus the key part. -/
def sigOf (secnonce : SecNonce n) (Rb : E × ZMod n) (ks : ZMod n) : ZMod n :=
  (if C.hasEvenY Rb.1 then secnonce.1 + Rb.2 * secnonce.2
    else -(secnonce.1 + Rb.2 * secnonce.2)) + ks

/-- The point whose discrete logarithm the honest signer returns:
`e⋅(R₁ + b⋅R₂)` plus the key part. -/
def dlogPoint (U : PubNonce E) (Rb : E × ZMod n) (K : E) : E :=
  C.ops.signOf Rb.1 (U.1 + Rb.2.val • U.2) + K

/-- The list of a single-party signing query, from the public key point. -/
def singleKeysPub (P : E) (items : List (Tweak n × M)) : List (X × M) :=
  items.map fun i => (C.x (i.1.pk C P), i.2)

/-- The key terms of a single-party signature. -/
def singleTerms (items : List (Tweak n × M)) (cs : List (ZMod n)) : List (KeyTerm n M) :=
  List.zipWith (fun (i : Tweak n × M) c => (i.1, i.2, c)) items cs

/-! ## Records of closed sessions -/

/-- A signature of the honest signer: the slot, the key terms, the inputs, the
values `(R, b)` and the signature scalar. A single-party signature is recorded
with the aggregate nonce `(0, 0)` and public nonces `(0, 0)`, which makes
`ncIn` the input its coefficient `b` is derived from. -/
structure CloseRec (n : ℕ) (E X M : Type) where
  k : ℕ
  keys : List (KeyTerm n M)
  agg : PubNonce E
  pm : List (X × M)
  pubs : List (PubNonce E)
  Rb : E × ZMod n
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
    ((challengerG true C nonceCoef N qs x nonces T .openSession st.1).1,
      ((challengerG true C nonceCoef N qs x nonces T .openSession st.1).2, st.2))
  | .close k τ m agg pm pubnonces, st =>
    if h : k < qs ∧ k < st.1.opened ∧ k ∉ st.1.closed ∧ τ.2 ≠ 0 ∧ pm.length ≤ N then
      match signPre C.ops (H₀ nonceCoef N) (nonces ⟨k, h.1⟩) (τ.sk x) m agg pm pubnonces with
      | some Rb =>
        let c := T (⟨pm, h.2.2.2.2⟩, C.x Rb.1, (C.x (C.mulG (τ.sk x)), m))
        let s := signPost C.ops (nonces ⟨k, h.1⟩) (τ.sk x) Rb c
        (some s, ({ st.1 with closed := k :: st.1.closed
                              signed := (pm, C.x (C.mulG (τ.sk x)), m) :: st.1.signed },
          ⟨k, [(τ, m, c)], agg, pm, pubnonces, Rb, s⟩ :: st.2))
      | none => (none, st)
    else (none, st)
  | .single items, st =>
    if h : st.1.opened < qs then
      let r := singleNonce true nonceCoef (singleKeys C x items) (nonces ⟨st.1.opened, h⟩)
      if hc : items ≠ [] ∧ (singleKeys C x items).length ≤ N ∧ r ≠ 0 ∧
          ∀ i ∈ items, i.1.2 ≠ 0 ∧ i.1.sk x ≠ 0 then
        let cs := (singleKeys C x items).map fun e =>
          T (⟨singleKeys C x items, hc.2.1⟩, C.x (C.mulG r), e)
        (some (C.x (C.mulG r), singleS C x items r cs),
          ({ opened := st.1.opened + 1
             closed := st.1.opened :: st.1.closed
             signed := (singleKeys C x items).map
               (fun e => (singleKeys C x items, e.1, e.2)) ++ st.1.signed },
            ⟨st.1.opened, singleTerms items cs, (0, 0), singleKeys C x items,
              (singleKeys C x items).map fun _ => (0, 0),
              (C.mulG r, ncHash nonceCoef (singleNcIn (singleKeys C x items))),
              singleS C x items r cs⟩ :: st.2))
      else (none, ({ st.1 with opened := st.1.opened + 1, closed := st.1.opened :: st.1.closed },
        st.2))
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
  dlogPoint C (U r.k) r.Rb (keyPoint C P r.keys)

/-- The coefficient list of length `L` with the given entries `(index, coefficient)`. -/
def coefVec (L : ℕ) (l : List (ℕ × ZMod n)) : List (ZMod n) :=
  (List.range L).map fun j => ((l.filter fun p => decide (p.1 = j)).map (·.2)).sum

/-- `1` if the tweaked key has an even y, otherwise `-1`. -/
def keySign (τ : Tweak n) : ZMod n := if C.hasEvenY (τ.pk C P) then 1 else -1

/-- The representation of a query point in the challenges
`P, U₀.1, U₀.2, U₁.1, …`. -/
def dlogRep (k : ℕ) (Rb : E × ZMod n) (keys : List (KeyTerm n M)) : ZMod n × List (ZMod n) :=
  let e : ZMod n := if C.hasEvenY Rb.1 then 1 else -1
  ((keys.map fun κ => κ.2.2 * keySign C P κ.1 * κ.1.1).sum,
    coefVec (2 * qs + 1) [(0, (keys.map fun κ => κ.2.2 * keySign C P κ.1 * κ.1.2).sum),
      (2 * k + 1, e), (2 * k + 2, e * Rb.2)])

/-- Answer a signing query whose record, up to the signature scalar, is
`rec0`: from the cache if the query point is there, otherwise with the
discrete logarithm oracle. -/
def simSign (rec0 : CloseRec n E X M) (signer' : SignerState X M) (st : SimState n E X M) :
    Alg (OmdlQ n) (OmdlR E) (ZMod n × SimState n E X M) :=
  match st.cache.find? fun r =>
      decide (r.k = rec0.k ∧ r.point C P U = rec0.point C P U) with
  | some r =>
    .done (r.s, { st with signer := signer', recs := { rec0 with s := r.s } :: st.recs })
  | none =>
    .ask (.dlog (dlogRep C qs P rec0.k rec0.Rb rec0.keys).1
        (dlogRep C qs P rec0.k rec0.Rb rec0.keys).2) fun (s : ZMod n) =>
      .done (s, { signer := signer'
                  recs := { rec0 with s := s } :: st.recs
                  cache := { rec0 with s := s } :: st.cache })

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
        simSign C qs P U ⟨k, [(τ, m, c)], agg, pm, pubnonces, Rb, 0⟩
            { st.signer with closed := k :: st.signer.closed
                             signed := (pm, C.x (τ.pk C P), m) :: st.signer.signed } st >>=
          fun p => .done (some p.1, p.2)
      | none => .done (none, st)
    else .done (none, st)
  | .single items, st =>
    if _ : st.signer.opened < qs then
      let L := singleKeysPub C P items
      let b := ncHash nonceCoef (singleNcIn L)
      let R := (U st.signer.opened).1 + b.val • (U st.signer.opened).2
      if hc : items ≠ [] ∧ L.length ≤ N ∧ R ≠ 0 ∧ ∀ i ∈ items, i.1.2 ≠ 0 ∧ i.1.pk C P ≠ 0 then
        let cs := L.map fun e => T (⟨L, hc.2.1⟩, C.x R, e)
        simSign C qs P U
            ⟨st.signer.opened, singleTerms items cs, (0, 0), L, L.map fun _ => (0, 0), (R, b), 0⟩
            { opened := st.signer.opened + 1
              closed := st.signer.opened :: st.signer.closed
              signed := L.map (fun e => (L, e.1, e.2)) ++ st.signer.signed } st >>=
          fun p => .done (some (C.x R, p.1), p.2)
      else .done (none, { st with signer := { st.signer with
        opened := st.signer.opened + 1, closed := st.signer.opened :: st.signer.closed } })
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
    (r.s - (r.keys.map fun κ => κ.2.2 * (keySign C P κ.1 * κ.1.sk x)).sum)

/-- The queries the reduction has left for session `k`, and the session's two
nonces as a function of the secret key. -/
def solveSession (k : ℕ) (cache : List (CloseRec n E X M)) :
    Alg (OmdlQ n) (OmdlR E) (ZMod n → ZMod n × ZMod n) :=
  match cache.filter fun r => decide (r.k = k) with
  | [] =>
    .ask (.dlog 0 (coefVec (2 * qs + 1) [(2 * k + 1, 1)])) fun (v₁ : ZMod n) =>
      .ask (.dlog 0 (coefVec (2 * qs + 1) [(2 * k + 2, 1)])) fun (v₂ : ZMod n) =>
        .done fun _ => (v₁, v₂)
  | [a] =>
    .ask (.dlog 0 (coefVec (2 * qs + 1) [(2 * k + 1, 1), (2 * k + 2, a.Rb.2 + 1)]))
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

/-- The reduction after it has received its challenges `P` and `U`. -/
def reductionBody (ρ : Coins × (SigIn N X M → ZMod n) × ZMod n) :
    Alg (OmdlQ n) (OmdlR E) (List (ZMod n)) :=
  Alg.interp (simChallenger C nonceCoef N qs P U ρ.2.1) (A ρ.1 P) ⟨⟨0, [], []⟩, [], []⟩ >>=
    fun r₁ =>
      match forkPointPub C N P r₁.1 r₁.2.signer with
      | none => .done []
      | some z =>
        Alg.interp (simChallenger C nonceCoef N qs P U (update ρ.2.1 z ρ.2.2)) (A ρ.1 P)
            ⟨⟨0, [], []⟩, [], r₁.2.cache⟩ >>= fun r₂ =>
          solveSessions C qs P r₂.2.cache qs >>= fun sols =>
            let cnt : ZMod n := ((r₁.1.L.filter fun e => decide (e = z.2.2)).length : ZMod n)
            let v := (r₁.1.sig.2 - r₂.1.sig.2) / (cnt * (ρ.2.1 z - ρ.2.2))
            let x := extractX C P r₁.1.τ v
            .done ((List.range (2 * qs + 1)).map fun i =>
              if i = 0 then x
              else if (i - 1) % 2 = 0 then ((sols.getD ((i - 1) / 2) fun _ => (0, 0)) x).1
              else ((sols.getD ((i - 1) / 2) fun _ => (0, 0)) x).2)

/-- **The reduction**: an AOMDL adversary from a forger. Its coins are the
forger's coins, the random oracle table and the new value at the fork point.
It asks for `2⋅qs + 1` challenges: the public key `P` and the nonces
`U₀.1, U₀.2, U₁.1, …` of the sessions. -/
def reduction : OmdlAdversary n E (Coins × (SigIn N X M → ZMod n) × ZMod n) := fun ρ =>
  getChals (2 * qs + 1) >>= fun chals =>
    reductionBody C nonceCoef N qs (chals.getD 0 0)
      (fun k => (chals.getD (2 * k + 1) 0, chals.getD (2 * k + 2) 0)) A ρ

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
