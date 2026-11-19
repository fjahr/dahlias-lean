# Reviewing dahlias-lean

Lean checks the proofs. A reviewer checks that the statements say what they should. Everything under `Dahlias/Proofs/` can stay unread, because a wrong proof does not compile. A wrong definition does.

## What to read

About 1,000 lines of definitions and statements decide whether the results mean anything. [The statements](#the-statements) at the end of this file prints them on one page.

1. `Dahlias/Basic.lean`, all of it. Compare the algorithms with BIP 459. The header lists the modelling choices.
2. `Dahlias/Security.lean`, all of it: the unforgeability game, the AOMDL game, and the places where the game differs from the paper's.
3. `Dahlias/Alg.lean`, the definitions `Alg`, `bind` and `run`, and `Dahlias/Prob.lean`, the definition `prob`.
4. `Dahlias/Unforgeability.lean`, the statements of `unforgeable` and `unforgeable_sqrt` and the definitions `collisionAdvantage` and `NoSingle`.
5. `Dahlias/Hashed.lean`, the game in which the random oracle returns hash outputs, and the statement of `unforgeable_sqrt_fin`.
6. `Dahlias/NonceGen.lean` and `Dahlias/NonceGenSk.lean`, the games with nonces derived as in `NonceGen`, and the statements.
7. `Dahlias/Binding.lean`, the header, `bindExperiment` and the statement of `strongly_binding`.
8. `Dahlias/Proofs/Reduction.lean`, the types of `reduction` and `collider`, and `reductionLazy` in `Dahlias/LazyReduction.lean`.
9. `Dahlias/Bytes.lean` and the statements of `Dahlias/Encoding.lean`, for BIP 459's bytes.

taproot-lean supplies the curve interface (`Taproot.Curve`), secp256k1 and SHA-256. A full review reads those definitions too.

The model was compared with BIP 459 at bitcoin/bips commit [`f3d1668`](https://github.com/bitcoin/bips/blob/f3d1668891fcdad99770245110bc6a22c87bce97/bip-0459.mediawiki). CI takes the test vectors and the Python reference from the same commit.

## Questions to ask

**Is the game the paper's?** `forgeExperiment` is the co-EUF-CMA-TK game of the DahLIAS paper (Fig. 5) with two changes and one addition. All three are described in the header of `Dahlias/Security.lean`.

- The game records the tweaked x-only public key of every signature, where the paper records the tweak. With x-only keys two different tweaks can give the same key without revealing anything: `(α, β)` and `(-α, -β)` always do. The paper's game would count a signature under one of them as a forgery under the other.
- A `Sign` call that fails leaves the session open. The paper closes it. The adversary here has more freedom.
- The adversary may also ask for single-party signatures: the honest signer signs a list of its own tweaked keys with one uniform nonce (`signSingle`, `challenger_single`). This is not in the paper. Sessions and single-party signatures share the `qs` nonce slots. `challengerG true` is a variant of the game that only the proof uses. The statements a reader has to trust are about `challenger`, which is `challengerG false`.

**Is the adversary restricted?** An `Adversary` is any function from coins of a finite type and the public key point to an oracle algorithm. It chooses all other public keys, all messages, all nonces of the other signers, the aggregate nonce and the tweaks, and it may leave sessions open and interleave them. It is not algebraic. The hypothesis `HashBound` bounds its random oracle queries, counting a single-party signing query once for every entry of its list. The game bounds the number of sessions and single-party signatures.

**Does the reduction cheat?** `reduction` has the type `OmdlAdversary`: it is an oracle algorithm for the AOMDL game and gets nothing else. It wins only if it makes fewer discrete logarithm queries than it received challenges, so the query count is part of the statement. `collider` is a function of a sample. It holds the secret key and runs the game by itself, which a collision finder may do.

**What is random?** The secret key and the nonces are uniform nonzero scalars. In `unforgeable` and `unforgeable_sqrt` the challenge hash is a uniform table of scalars, on inputs with lists of at most `N` entries. `forgeAdvantage_eq_lazy` proves that the game has the same advantage when the oracle answers every new query with the next of `qh + qs + N` uniform scalars. The coins of `reduction` contain a whole table. `reductionLazy` takes `2·(qh + qs) + 1` scalars instead and wins the AOMDL game with the same probability (`omdlAdvantage_reduction_eq_lazy`), and `unforgeable_sqrt_lazy` is the theorem with that reduction. The framework has no cost model, so there is no statement about running time.

**How is the challenge hash reduced modulo `n`?** BIP 459 computes `c = int(hash(…)) mod n` from a 256-bit hash. In the game of `Dahlias/Hashed.lean` the oracle returns a uniform element of a type `H` of hash outputs. The adversary sees the outputs, and `Sign` and `Verify` turn them into scalars with `red`. `forgeAdvantageH_le` reduces this game to the one with scalar answers. The game reads at most `qh + qs + N` oracle values, and each is outside a fixed set of `n` outputs, one for every scalar, with probability `(|H| - n) / |H|`. For `H = {0, …, 2^256 - 1}` and `red h = h mod n` that is at most `2^-127` (`hash_gap`), and `bytes_unforgeable_256` is the theorem for secp256k1.

**What is the nonce coefficient hash?** A fixed function into the scalars, `nonceCoef`. The theorem holds for every such function and measures how often `collider` outputs a collision of it. This is the usual way to state collision resistance for an unkeyed hash function. BIP 459's `int(hash_BIP0459/noncecoef(…)) mod n` is such a function (`nonceCoef32`). A collision of it is a pair of inputs whose SHA-256 values are equal or differ by `n`.

**What does the single-party query add?** BIP 459 leaves open how a party that holds all keys of a list signs without running the protocol with itself, and says that the method sketched on the mailing list needs a security analysis. `signSingle` is that method: one nonce `r`, `R = r⋅G`, `s = ±r + Σ cᵢ⋅dᵢ`. The game offers it to the adversary next to the sessions, and `unforgeable_sqrt` covers it at the cost of `qs / (n - 1)`. The reduction cannot answer two such queries of one slot with the same nonce in its two runs, so it works with a variant in which the nonce is `r₁ + b⋅r₂` for a coefficient `b` derived from the list (`challengerG true`). `forgeAdvantage_le_derived` shows that the adversary cannot tell the variant from the game.

**Is the theorem vacuous?** `Dahlias/Examples.lean` has a forger that satisfies `HashBound` and wins with positive probability. `Dahlias/Secp256k1.lean` instantiates the theorem for secp256k1.

**Is the binding game the paper's?** `bindExperiment` is the game of Fig. 11 with the random oracle of the unforgeability game: the adversary outputs two lists and one signature and wins if the lists differ and the signature verifies for both. The theorem counts the adversary's own oracle queries. The `2N` in the bound are the verifier's queries. It holds for groups of prime order, and `secp256k1_primeOrder` proves that secp256k1 is one.

**What does the bound say?** With `q = qh + qs + 1`, `unforgeable` states `adv * (adv / q - 1 / n) ≤ omdl + coll` for adversaries that ask for no single-party signatures (`NoSingle`). This is the bound of the paper's Theorem 2 up to the count of queries. `unforgeable_sqrt` holds for all adversaries: `adv ≤ sqrt (q * (omdl + coll)) + q / n + qs / (n - 1)`. The square root is the loss of the forking lemma, and `qs / (n - 1)` pays for the single-party signatures.

**What connects the theorems to BIP 459's bytes?** `Dahlias/Bytes.lean` defines the algorithms on bytes as parsing followed by the model's algorithms, and the 60 test vectors and the differential tests run them. `Dahlias/Encoding.lean` proves what the model takes for granted. The hash inputs are injective encodings of the structured inputs (`sigInput_injective`, `nonceCoefInput_injective`). `cpoint` accepts exactly the encodings `cbytes(P)`, so comparing nonces as bytes is comparing points (`cpoint_eq_some_iff`, `matchIdxs_bytes`). `sign_bytes` and `verify_bytes` say that `Sign` and `Verify` on bytes are `Sign` and `Verify` of the instance that `bytes_unforgeable` and `bytes_unforgeable_256` are about. A nonce that does not parse becomes the point `0` there, and the adversary of the game may send `0` as well.

## BIP 459's claims

What BIP 459 says about correctness and security, and the theorem for it.

| BIP 459 | Lean |
|---|---|
| General Signing Flow: if all signers behaved honestly, the result passes `Verify`. | `verify_honest` in the model, `Bytes.verify_honest` on bytes. |
| General Signing Flow: if the aggregate signature is invalid, the coordinator can find the disruptive signer with `PartialSigVerify`. `PartialSigVerify`: if it succeeds for all signers, `SigAgg` with the aggregate nonce from `NonceAgg` gives a valid signature. | `verify_sigAgg_of_partialSigVerify`. So an invalid aggregate has a partial signature that fails, and `partialSigVerify_sign` shows that an honest signer's never does. |
| General Signing Flow and Security: a `secnonce` must not be used twice. Three executions of `Sign` in different sessions reveal the secret key. Nonce Generation: the same holds for nonces derived deterministically. | `evenScalar_of_three_sessions`, if a determinant of public values is nonzero. `evenScalar_of_nonce_reuse` for two executions with the same session values and different challenges. |
| Nonce Generation: `NonceGen` with a uniform `rand'`. | `nonceGen_unforgeable`, with `hash_BIP0459/nonce` as a random oracle and an `extra_in` chosen by the adversary. `nonceGenSk_advantage` adds the optional `sk` argument. |
| Nonce Generation: the optional arguments may prevent key exposure if `rand'` is not uniform. | No theorem. Both theorems assume a uniform `rand'`. |
| Role of the Coordinator and Security: a malicious coordinator colluding with all but one signer cannot forge. | `unforgeable_sqrt`. The adversary of the game is the coordinator and every other signer. |
| List Ordering: a signature valid for a list is not valid for a non-trivial permutation of it, except with negligible probability. `Sign`: the aggregate signature is valid for exactly this list. Security: the scheme is strongly binding. | `strongly_binding`, `secp256k1_strongly_binding`: a signature is valid for two different lists with probability at most `(qh + 2N)² / n`. |
| Rationale: 32-byte messages keep the encoding of the list `L` unambiguous. | `sigInput_injective`, and `nonceCoefInput_injective` for the nonce coefficient. |
| Rationale: verifiers should hash the common prefix `L ‖ xbytes(R)` once. | No theorem. The model hashes every input from the start. libsecp256k1 hashes the prefix once, and the differential test compares the two. |
| Rationale: two nonces per signer prevent the ROS attack across concurrent sessions. | `unforgeable_sqrt`, for any number of concurrent sessions. No theorem about a scheme with one nonce per signer. |
| Rationale, Security and the footnote of `Sign`: the `R₂` uniqueness check and the message check are needed. Checking that the combination of public key, message and `R₂` is unique is not enough. | `ros_forgery`: with the weaker check, `ℓ ≥ log₂ n` concurrent sessions give a forgery. `msgSwap_wins`: without the message check a coordinator makes the signer sign any message. No theorem for the key extraction that the Security section mentions. |
| Rationale: key tweaking for BIP 32 and BIP 341. Key Tweaking: the signer uses `sk'`, the list has `xbytes(P')`. | `tweakPK_mulG`: `TweakSK` and `TweakPK` agree. `tweakSK_affine`: both kinds of tweak, and sequences of them, are tweaks of the game, so `unforgeable_sqrt` covers them. |
| Rationale: an optimized signing algorithm for a single party that knows all secret keys needs a security analysis before it can be specified. | `unforgeable_sqrt` covers the method `signSingle` (`challenger_single`), also when the party runs sessions with others at the same time. `verify_signSingle` and `sigAgg_eq_signSingle` show that it produces the signature of the protocol for the same `R`. |
| Security: a partial signature is not a signature. An adversary can produce one that verifies for any public key. | No theorem. |
| Security: proven under AOMDL in the concurrent setting with key tweaking, with `hash_BIP0459/sig` as a random oracle and a collision resistant `hash_BIP0459/noncecoef`. | `unforgeable`, `unforgeable_sqrt`. `bytes_unforgeable_256` is the statement for secp256k1 with 32-byte keys and messages, the BIP's nonce coefficient hash, and a 256-bit random oracle reduced modulo `n`. |
| Security, footnote: strong binding needs public keys other than the point at infinity, which `lift_x` guarantees. | `verify` fails unless every key lifts, and `strongly_binding` uses that. |
| The pseudocode of `Sign`, `Verify` and the other algorithms. | `Dahlias/Basic.lean` and `Dahlias/Bytes.lean` are transcriptions. No theorem says they are BIP 459's algorithms. The 60 test vectors and the differential tests against `reference.py` and libsecp256k1 compare them. |

## What the theorems do not say

- No theorem bounds running time. `reduction` runs the forger twice, which is visible in its definition. `reductionLazy` shows that it needs no table of exponential size.
- The game is for lists of at most `N` entries, with `N < n`.
- The nonces of the game are uniform. `nonceGen_unforgeable` and `nonceGenSk_advantage` derive them as `NonceGen` does, from a uniform `rand'` and with the hash functions of `NonceGen` as random oracles. They say nothing about a `rand'` that is not uniform, which is the case the optional arguments of `NonceGen` exist for.
- No theorem states a game in which the adversary sends bytes. In `bytes_unforgeable_256` public keys and messages are 32-byte arrays and the hashes are BIP 459's, but the adversary sends points for the nonces and scalars for the tweaks. `sign_bytes` and `verify_bytes` connect that instance to the functions on bytes.
- `hash_BIP0459/sig` is a random oracle on structured inputs with lists of at most `N` entries. SHA-256 on the bytes is a function of those inputs (`sigInput_injective`), and modelling it as a random function is the assumption.
- The challenges of the AOMDL game have nonzero discrete logarithms, because they stand for the secret key and the nonces, which are nonzero.
- A single-party signature of the game is for a list of keys that are all tweaks `α + β⋅x`, `β ≠ 0`, of the one honest key. The theorem does not cover a party that signs alone for several unrelated secret keys.

## Machine checks

- `lake build` compiles every proof and fails if the axioms of a main result change (`Dahlias/Summary.lean`).
- `scripts/check.sh` searches the sources for `sorry`, new axioms, unsafe code and stray `native_decide`. It also checks that every code block under [The statements](#the-statements) is in the sources word for word.
- `scripts/replay.sh` replays every project module in the kernel with `leanchecker`, without the elaborator, one process per module.
- CI runs all three, regenerates the test vector data from bitcoin/bips, and runs 300 cases of `scripts/fuzz.py` against the Python reference.

### Mutants of the model

`scripts/mutate_model.py` changes one definition at a time in a copy of the project and builds it. A mutant that still built would show that no theorem depends on the detail it changes. All ten fail. Lake does not build what depends on a module that failed, so the table names the declarations nearest to the changed definition, which are often lemmas and not main theorems.

| Mutant | Fails in |
|---|---|
| `Sign` accepts lists in which the signer's `R₂` appears more than once | `partialSigVerify_sign`, `sign_eq`, `signError_vectors` |
| `Sign` does not compare the message at the signer's index | `partialSigVerify_sign`, `sign_eq`, `signError_vectors` |
| The nonce coefficient does not cover the signers' `R₂` | `sign_vectors`, `partialSigVerify_vectors`, `msgSwap_wins`, `coefItems_fst`, `coefItems_snd` |
| A session can be closed twice | `eval_treeChallenger` |
| A forgery may be for an entry the signer signed | `wins_iff_accepts` |
| Hash queries are not counted | `hashBound_ask` |
| The AOMDL solver must make two queries fewer than it has challenges | `fork_to_omdl` |
| The derived nonce of a single-party signature ignores `r₂` | `derived_couple`, `logInv_step` |
| `Sign` does not negate the nonce for an `R` with odd y | `partialSigVerify_sign`, `sign_eq`, `sign_vectors` |
| `Verify` does not check that the public keys lift | `verify_sigAgg_of_partialSigVerify` |

For two of BIP 459's checks there is more than a proof that fails. `msgSwap_wins` is an attack on `Sign` without the message check, and `ros_forgery` is one on `Sign` with the weaker uniqueness check.

### Tests of the implementations

`scripts/fuzz.py` compares the algorithms on bytes with BIP 459's `reference.py` and with libsecp256k1's `fullagg` module, on honest sessions and on malformed inputs. `scripts/mutate_secp256k1.py` measures what those cases, the module's unit tests and the exhaustive tests on a small group notice. Of 57 small changes to the C module they notice 56. The README has the details and the one exception.

## The statements

The definitions and theorem statements a reviewer has to agree with, copied from the sources with their comments by `scripts/gen_review.py`. Proofs are left out.

Throughout, `n` is a prime, `E` is the group of curve points, `X` is the type of x-only encodings and `M` is the message type. `C : Curve n E X` is taproot-lean's curve interface, `nonceCoef` is the nonce coefficient hash, `N` bounds the length of a list and `qs` is the number of nonce slots.

Not printed here: the bodies of `reduction`, `collider` and `reductionM` (`Dahlias/Proofs/Reduction.lean`, `Dahlias/LazyReduction.lean`), the lazily sampled oracle (`Dahlias/Lazy.lean`, `Dahlias/Second.lean`), and the definitions of taproot-lean at the commit pinned in `lakefile.toml`.

<!-- statements:begin -->

### The algorithms of BIP 459

`Dahlias/Basic.lean`. `Ops` is the handful of curve operations the BIP uses, `Hashes` the two tagged hashes of the signing protocol. Points given as `0` stand for encodings that `cpoint` rejects.

```lean
/-- The curve operations BIP 459 uses. -/
structure Ops (n : ℕ) (E X : Type*) where
  /-- `k ↦ k⋅G`. -/
  mulG : ZMod n → E
  /-- `(k, P) ↦ k⋅P`. -/
  smul : ZMod n → E → E
  /-- `x(P)`. -/
  x : E → X
  /-- `has_even_y(P)`. -/
  hasEvenY : E → Bool
  /-- `lift_x`. -/
  liftX : X → Option E
```

```lean
/-- The two hash functions of the signing protocol. -/
structure Hashes (n : ℕ) (E X M : Type*) where
  /-- `hash_BIP0459/noncecoef`, on `R₁`, `R₂` and the `(pkᵢ, mᵢ, R₂,ᵢ)`. -/
  nonceCoef : E → E → List (X × M × E) → ZMod n
  /-- `hash_BIP0459/sig`, on the list `L`, `xbytes(R)` and the signer's `(pk, m)`. -/
  sig : List (X × M) → X → X × M → ZMod n
```

```lean
/-- `d` if `d⋅G` has an even y, otherwise `n - d`. -/
def evenScalar (d : ZMod n) : ZMod n := if O.hasEvenY (O.mulG d) then d else -d
```

```lean
/-- `P` if `has_even_y(R)`, otherwise `-P`: multiplication by the `e` of
`Sign` and `PartialSigVerify`. -/
def signOf (R P : E) : E := if O.hasEvenY R then P else -P
```

```lean
/-- `TweakSK`: plain (`sk + t`) or x-only (`d + t`, with `d` the even-y
normalization of `sk`). Fails if the result is zero. -/
def tweakSK (O : Ops n E X) (sk t : ZMod n) (xonly : Bool) : Option (ZMod n) :=
  let d := if xonly then O.evenScalar sk else sk
  if d + t = 0 then none else some (d + t)
```

```lean
/-- `TweakPK`: plain (`P + t⋅G`) or x-only (`lift_x(x(P)) + t⋅G`). Fails if
the result is the point at infinity. -/
def tweakPK (O : Ops n E X) (P : E) (t : ZMod n) (xonly : Bool) : Option E :=
  let P' := if xonly && !O.hasEvenY P then -P else P
  if P' + O.mulG t = 0 then none else some (P' + O.mulG t)
```

```lean
/-- `NonceGen`, from the two derived scalars
`rᵢ = int(hash_BIP0459/nonce(rand ‖ extra_in ‖ i)) mod n`. -/
def nonceGen (O : Ops n E X) (r₁ r₂ : ZMod n) : Option (SecNonce n × PubNonce E) :=
  if r₁ = 0 ∨ r₂ = 0 then none else some ((r₁, r₂), (O.mulG r₁, O.mulG r₂))
```

```lean
/-- `NonceAgg`. -/
def nonceAgg (pubnonces : List (PubNonce E)) : Option (PubNonce E) :=
  let R₁ := (pubnonces.map Prod.fst).sum
  let R₂ := (pubnonces.map Prod.snd).sum
  if pubnonces = [] ∨ (∃ N ∈ pubnonces, N.1 = 0 ∨ N.2 = 0) ∨ R₁ = 0 ∨ R₂ = 0 then none
  else some (R₁, R₂)
```

```lean
/-- The `(pkᵢ, mᵢ, R₂,ᵢ)` that enter the nonce coefficient. -/
def coefItems (pm : List (X × M)) (pubnonces : List (PubNonce E)) : List (X × M × E) :=
  List.zipWith (fun pkm N => (pkm.1, pkm.2, N.2)) pm pubnonces
```

```lean
/-- `GetSessionValues`, returning `(R, b)`. Only the second halves of the
public nonces are parsed. -/
def getSessionValues (O : Ops n E X) (H : Hashes n E X M) (agg : PubNonce E)
    (pm : List (X × M)) (pubnonces : List (PubNonce E)) : Option (E × ZMod n) :=
  if pm = [] ∨ pm.length ≠ pubnonces.length ∨ agg.1 = 0 ∨ agg.2 = 0 ∨
      (∃ N ∈ pubnonces, N.2 = 0) then none
  else
    let b := H.nonceCoef agg.1 agg.2 (coefItems pm pubnonces)
    let R := agg.1 + O.smul b agg.2
    if R = 0 then none else some (R, b)
```

```lean
/-- The indices `j` with `R₂,ⱼ = R₂`. -/
def matchIdxs (pubnonces : List (PubNonce E)) (R₂ : E) : List ℕ :=
  (List.range pubnonces.length).filter fun j => (pubnonces[j]?).map Prod.snd = some R₂
```

```lean
/-- `Sign`. -/
def sign (O : Ops n E X) (H : Hashes n E X M) (secnonce : SecNonce n) (sk : ZMod n) (m : M)
    (agg : PubNonce E) (pm : List (X × M)) (pubnonces : List (PubNonce E)) : Option (ZMod n) :=
  let (r₁, r₂) := secnonce
  if r₁ = 0 ∨ r₂ = 0 ∨ sk = 0 then none else
  let P := O.mulG sk
  match matchIdxs pubnonces (O.mulG r₂) with
  | [j] =>
    if pm[j]? = some (O.x P, m) then
      (getSessionValues O H agg pm pubnonces).map fun (R, b) =>
        let k := r₁ + b * r₂
        let c := H.sig pm (O.x R) (O.x P, m)
        (if O.hasEvenY R then k else -k) + c * O.evenScalar sk
    else none
  | _ => none
```

```lean
/-- `SigAgg`, returning `(xbytes(R), s)`. -/
def sigAgg (O : Ops n E X) (H : Hashes n E X M) (agg : PubNonce E) (pm : List (X × M))
    (pubnonces : List (PubNonce E)) (psigs : List (ZMod n)) : Option (X × ZMod n) :=
  if psigs.length ≠ pm.length then none else
  (getSessionValues O H agg pm pubnonces).map fun (R, _) => (O.x R, psigs.sum)
```

```lean
/-- `PartialSigVerify`. -/
def partialSigVerify (O : Ops n E X) (H : Hashes n E X M) (psig : ZMod n) (pm : List (X × M))
    (pubnonces : List (PubNonce E)) (i : ℕ) : Bool :=
  match pm[i]?, pubnonces[i]? with
  | some pkm, some N =>
    if N.1 = 0 ∨ N.2 = 0 then false else
    match O.liftX pkm.1, (nonceAgg pubnonces).bind (getSessionValues O H · pm pubnonces) with
    | some P, some (R, b) =>
      let c := H.sig pm (O.x R) pkm
      decide (O.mulG psig = O.signOf R (N.1 + O.smul b N.2) + O.smul c P)
    | _, _ => false
  | _, _ => false
```

```lean
/-- `c₀⋅P₀ + … + c_{u-1}⋅P_{u-1}`, with a failed `lift_x` read as `0` (the
verifier checks the lifts separately). -/
def keySum (O : Ops n E X) (H : Hashes n E X M) (pm : List (X × M)) (r : X) : E :=
  (pm.map fun pkm => O.smul (H.sig pm r pkm) ((O.liftX pkm.1).getD 0)).sum
```

```lean
/-- `Verify`, for the signature `(r, s)`. -/
def verify (O : Ops n E X) (H : Hashes n E X M) (pm : List (X × M)) (sig : X × ZMod n) : Bool :=
  match O.liftX sig.1 with
  | none => false
  | some R =>
    !pm.isEmpty && pm.all (fun pkm => (O.liftX pkm.1).isSome) &&
      decide (O.mulG sig.2 = R + keySum O H pm sig.1)
```

### Oracle algorithms and probabilities

`Dahlias/Alg.lean` and `Dahlias/Prob.lean`. An adversary is a function from coins to a deterministic algorithm that makes queries. A probability is a fraction of a finite sample space.

```lean
/-- A deterministic algorithm with queries `q : Q` answered in `R q`. -/
inductive Alg (Q : Type) (R : Q → Type) (α : Type) where
  | done : α → Alg Q R α
  | ask : (q : Q) → (R q → Alg Q R α) → Alg Q R α
```

```lean
/-- Sequential composition. -/
def bind : Alg Q R α → (α → Alg Q R β) → Alg Q R β
  | done a, g => g a
  | ask q f, g => ask q fun r => bind (f r) g
```

```lean
/-- Run with a stateful handler for the queries. -/
def run (h : (q : Q) → σ → R q × σ) : Alg Q R α → σ → α × σ
  | done a, s => (a, s)
  | ask q f, s => run h (f (h q s).1) (h q s).2
```

```lean
/-- The fraction of samples that satisfy `p`. -/
noncomputable def prob {Ω : Type} [Fintype Ω] (p : Ω → Prop) : ℝ :=
  ((Finset.univ.filter p).card : ℝ) / Fintype.card Ω
```

### The unforgeability game

`Dahlias/Security.lean`. `challengerG false` is the game. `challengerG true` is the variant the reduction works with: a single-party signature takes its nonce from both nonces of its slot.

```lean
/-- Lists of at most `N` public key and message pairs. -/
abbrev BList (N : ℕ) (X M : Type) := {L : List (X × M) // L.length ≤ N}
```

```lean
/-- An input of `hash_BIP0459/sig`: the list `L`, `xbytes(R)` and the signer's
`(pk, m)`. -/
abbrev SigIn (N : ℕ) (X M : Type) := BList N X M × X × (X × M)
```

```lean
/-- The hash functions of the protocol, with `hash_BIP0459/sig` given by the
table `T`. -/
def hashesOf (N : ℕ) (nonceCoef : E → E → List (X × M × E) → ZMod n)
    (T : SigIn N X M → ZMod n) : Hashes n E X M where
  nonceCoef := nonceCoef
  sig pm r pkm := if h : pm.length ≤ N then T (⟨pm, h⟩, r, pkm) else 0
```

```lean
/-- A tweak `(α, β)`: the affine map `x ↦ α + β⋅x` on secret keys. -/
abbrev Tweak (n : ℕ) := ZMod n × ZMod n
```

```lean
/-- The tweaked secret key. -/
def Tweak.sk (τ : Tweak n) (x : ZMod n) : ZMod n := τ.1 + τ.2 * x
```

```lean
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
```

```lean
/-- The answers: a hash value, the signer's public nonce (if a session is
left), and the partial signature (if `Sign` succeeds). -/
def AdvR {N : ℕ} : AdvQ n N E X M → Type
  | .hash _ => ZMod n
  | .openSession => Option (PubNonce E)
  | .close .. => Option (ZMod n)
  | .single _ => Option (X × ZMod n)
```

```lean
/-- A forgery: the list, the tweak of the honest signer's key, the signature. -/
structure Forgery (n : ℕ) (X M : Type) where
  L : List (X × M)
  τ : Tweak n
  sig : X × ZMod n
```

```lean
/-- An adversary with coins in `Coins`. Its input is the honest signer's
public key point. -/
abbrev Adversary (n N : ℕ) (E X M Coins : Type) :=
  Coins → E → Alg (AdvQ n N E X M) AdvR (Forgery n X M)
```

```lean
/-- The honest signer's state: the number of opened sessions, the closed
sessions, and the recorded `(L, pk̃, m)`. -/
structure SignerState (X M : Type) where
  opened : ℕ
  closed : List ℕ
  signed : List (List (X × M) × X × M)
```

```lean
/-- The list `L` of a single-party signing query: the tweaked public keys with
their messages. -/
def singleKeys (C : Curve n E X) (x : ZMod n) (items : List (Tweak n × M)) : List (X × M) :=
  items.map fun i => (C.x (C.mulG (i.1.sk x)), i.2)
```

```lean
/-- The input of the nonce coefficient hash that the derived nonce of a
single-party signature uses. No session has this input: its first two entries
are the point at infinity. -/
def singleNcIn (L : List (X × M)) : E × E × List (X × M × E) :=
  (0, 0, L.map fun e => (e.1, e.2, 0))
```

```lean
/-- The nonce of a single-party signature from the nonce pair of its slot.
With `der = false` it is the first nonce: a uniform nonzero scalar. With
`der = true` it is `r₁ + b⋅r₂` for a coefficient `b` derived from the list.
The security proof works with the second form and shows that the adversary
cannot tell the two apart (`Dahlias.Security.forgeAdvantage_le_derived`). -/
def singleNonce (der : Bool) (nonceCoef : E → E → List (X × M × E) → ZMod n) (L : List (X × M))
    (ν : SecNonce n) : ZMod n :=
  if der then ν.1 + nonceCoef 0 0 ((singleNcIn (E := E) L).2.2) * ν.2 else ν.1
```

```lean
/-- The `s` of a single-party signature with nonce `r` and challenges `cs`. -/
def singleS (C : Curve n E X) (x : ZMod n) (items : List (Tweak n × M)) (r : ZMod n)
    (cs : List (ZMod n)) : ZMod n :=
  (if C.hasEvenY (C.mulG r) then r else -r) +
    (List.zipWith (fun c (i : Tweak n × M) => c * C.evenScalar (i.1.sk x)) cs items).sum
```

```lean
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
```

```lean
/-- The game: a single-party signature uses one uniform nonzero nonce. -/
abbrev challenger (C : Curve n E X) (nonceCoef : E → E → List (X × M × E) → ZMod n)
    (N qs : ℕ) (x : ZMod n) (nonces : Fin qs → SecNonce n) (T : SigIn N X M → ZMod n) :
    (q : AdvQ n N E X M) → SignerState X M → AdvR q × SignerState X M :=
  challengerG false C nonceCoef N qs x nonces T
```

```lean
/-- The winning condition on the adversary's output and the signer's final
state. -/
def Wins (C : Curve n E X) (nonceCoef : E → E → List (X × M × E) → ZMod n) (N : ℕ) (x : ZMod n)
    (T : SigIn N X M → ZMod n) (f : Forgery n X M) (st : SignerState X M) : Prop :=
  f.τ.2 ≠ 0 ∧ f.τ.sk x ≠ 0 ∧ f.L.length ≤ N ∧
    (∃ m, (C.x (C.mulG (f.τ.sk x)), m) ∈ f.L ∧ (f.L, C.x (C.mulG (f.τ.sk x)), m) ∉ st.signed) ∧
    verify C.ops (hashesOf N nonceCoef T) f.L f.sig = true
```

```lean
/-- The sample of the game: the secret key, the nonces of the `qs` sessions,
the adversary's coins and the random oracle. -/
abbrev ForgeSample (n N qs : ℕ) (X M Coins : Type) :=
  (ZMod n)ˣ × (Fin qs → (ZMod n)ˣ × (ZMod n)ˣ) × Coins × (SigIn N X M → ZMod n)
```

```lean
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
```

```lean
/-- **The unforgeability game** on one sample. -/
abbrev forgeExperiment (C : Curve n E X) (nonceCoef : E → E → List (X × M × E) → ZMod n)
    (N qs : ℕ) {Coins : Type} (A : Adversary n N E X M Coins)
    (ω : ForgeSample n N qs X M Coins) : Prop :=
  forgeExperimentG false C nonceCoef N qs A ω
```

```lean
/-- The probability of forging, for either form of the nonce of a single-party
signature. -/
noncomputable def forgeAdvantageG (der : Bool) (C : Curve n E X)
    (nonceCoef : E → E → List (X × M × E) → ZMod n) (N qs : ℕ) {Coins : Type} [Fintype Coins]
    [Fintype (SigIn N X M)] (A : Adversary n N E X M Coins) : ℝ :=
  prob (forgeExperimentG der C nonceCoef N qs A)
```

```lean
/-- The adversary's probability of forging. -/
noncomputable abbrev forgeAdvantage (C : Curve n E X)
    (nonceCoef : E → E → List (X × M × E) → ZMod n) (N qs : ℕ) {Coins : Type} [Fintype Coins]
    [Fintype (SigIn N X M)] (A : Adversary n N E X M Coins) : ℝ :=
  forgeAdvantageG false C nonceCoef N qs A
```

```lean
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
```

### The single-party signature of the game

`Dahlias/Single.lean` and `Dahlias/SingleGame.lean`. The game's answer to a `single` query is the algorithm `signSingle`.

```lean
/-- The list `L` of a party's secret keys and messages. -/
def singleList (O : Ops n E X) (signers : List (ZMod n × M)) : List (X × M) :=
  signers.map fun σ => (O.x (O.mulG σ.1), σ.2)
```

```lean
/-- **Signing by a single party**: one nonce `r` for the whole list. -/
def signSingle (O : Ops n E X) (H : Hashes n E X M) (r : ZMod n) (signers : List (ZMod n × M)) :
    Option (X × ZMod n) :=
  if r = 0 ∨ signers = [] ∨ ∃ σ ∈ signers, σ.1 = 0 then none else
  some (O.x (O.mulG r), (if O.hasEvenY (O.mulG r) then r else -r) +
    (signers.map fun σ =>
      H.sig (singleList O signers) (O.x (O.mulG r)) (O.x (O.mulG σ.1), σ.2) *
        O.evenScalar σ.1).sum)
```

```lean
/-- **The game answers a single-party signing query with `signSingle`**, when
a slot is left, the list has at most `N` entries and the tweaks are valid. -/
theorem challenger_single (items : List (Tweak n × M)) (st : SignerState X M)
    (h : st.opened < qs) (hN : items.length ≤ N) (hτ : ∀ i ∈ items, i.1.2 ≠ 0) :
    (challenger C nonceCoef N qs x nonces T (.single items) st).1 =
      signSingle C.ops (hashesOf N nonceCoef T) (nonces ⟨st.opened, h⟩).1
        (items.map fun i => (i.1.sk x, i.2))
```

### The AOMDL game

`Dahlias/Security.lean`.

```lean
/-- The queries of an AOMDL adversary. -/
inductive OmdlQ (n : ℕ) where
  /-- Ask for the next challenge point. -/
  | chal
  /-- Ask for the discrete logarithm of `a⋅G + b₁⋅X₁ + … + b_ℓ⋅X_ℓ`, with
  `X₁, …, X_ℓ` the challenges received so far. -/
  | dlog (a : ZMod n) (bs : List (ZMod n))
```

```lean
/-- The answers: a challenge point (if one is left) and a scalar. -/
def OmdlR (E : Type) : OmdlQ n → Type
  | .chal => Option E
  | .dlog .. => ZMod n
```

```lean
/-- An AOMDL adversary with coins in `Coins`. It outputs the discrete
logarithms of the challenges it received. -/
abbrev OmdlAdversary (n : ℕ) (E Coins : Type) := Coins → Alg (OmdlQ n) (OmdlR E) (List (ZMod n))
```

```lean
/-- The discrete logarithms of the first `ℓ` challenges. -/
def chalLogs {c : ℕ} (xs : Fin c → (ZMod n)ˣ) (ℓ : ℕ) : List (ZMod n) :=
  (List.range ℓ).map fun i => if h : i < c then ((xs ⟨i, h⟩ : (ZMod n)ˣ) : ZMod n) else 0
```

```lean
/-- The game's answers. The state is the number of challenges and of discrete
logarithm queries so far. -/
def omdlChallenger (C : Curve n E X) {c : ℕ} (xs : Fin c → (ZMod n)ˣ) :
    (q : OmdlQ n) → ℕ × ℕ → OmdlR E q × (ℕ × ℕ)
  | .chal, (ℓ, d) =>
    if h : ℓ < c then (some (C.mulG ((xs ⟨ℓ, h⟩ : (ZMod n)ˣ) : ZMod n)), (ℓ + 1, d))
    else (none, (ℓ, d))
  | .dlog a bs, (ℓ, d) =>
    (a + (List.zipWith (· * ·) bs (chalLogs xs ℓ)).sum, (ℓ, d + 1))
```

```lean
/-- **The AOMDL game** on one sample: at most `c` challenges with nonzero
discrete logarithms `xs`. The adversary wins if it outputs the discrete
logarithms of all challenges it received and made fewer discrete logarithm
queries than it received challenges. -/
def omdlExperiment (C : Curve n E X) (c : ℕ) {Coins : Type} (B : OmdlAdversary n E Coins)
    (ω : (Fin c → (ZMod n)ˣ) × Coins) : Prop :=
  let out := (B ω.2).run (omdlChallenger C ω.1) (0, 0)
  out.1 = chalLogs ω.1 out.2.1 ∧ out.2.2 < out.2.1
```

```lean
/-- The adversary's probability of winning the AOMDL game. -/
noncomputable def omdlAdvantage (C : Curve n E X) (c : ℕ) {Coins : Type} [Fintype Coins]
    (B : OmdlAdversary n E Coins) : ℝ :=
  prob (omdlExperiment C c B)
```

### Unforgeability

`Dahlias/Unforgeability.lean`, `Dahlias/Proofs/Reduction.lean` and `Dahlias/LazyReduction.lean`. Of the reduction and the collision finder only the types are printed.

```lean
/-- The nonce coefficient hash on an input. -/
def ncHash (z : E × E × List (X × M × E)) : ZMod n := nonceCoef z.1 z.2.1 z.2.2
```

```lean
/-- A collision of the nonce coefficient hash. -/
def IsCollision (p : (E × E × List (X × M × E)) × (E × E × List (X × M × E))) : Prop :=
  p.1 ≠ p.2 ∧ ncHash nonceCoef p.1 = ncHash nonceCoef p.2
```

```lean
/-- **The reduction**: an AOMDL adversary from a forger. Its coins are the
forger's coins, the random oracle table and the new value at the fork point.
It asks for `2⋅qs + 1` challenges: the public key `P` and the nonces
`U₀.1, U₀.2, U₁.1, …` of the sessions. -/
def reduction : OmdlAdversary n E (Coins × (SigIn N X M → ZMod n) × ZMod n)
```

```lean
/-- **The collision finder**: run the game on the sample, fork it, and look
for two records of the same session, one from each run, whose nonce coefficient
inputs collide. -/
noncomputable def collider (p : ForgeSample n N qs X M Coins × ZMod n) :
    (E × E × List (X × M × E)) × (E × E × List (X × M × E))
```

```lean
/-- The probability that `collider A` outputs a collision of the nonce
coefficient hash. -/
noncomputable def collisionAdvantage : ℝ :=
  prob fun p : ForgeSample n N qs X M Coins × ZMod n =>
    IsCollision nonceCoef (collider C nonceCoef N qs A p)
```

```lean
/-- The algorithm makes no single-party signing query. -/
def NoSingle {α : Type} : Alg (AdvQ n N E X M) AdvR α → Prop
  | .done _ => True
  | .ask (.hash _) f => ∀ r, NoSingle (f r)
  | .ask .openSession f => ∀ r, NoSingle (f r)
  | .ask (.close ..) f => ∀ r, NoSingle (f r)
  | .ask (.single _) _ => False
```

```lean
/-- **BIP 459 is unforgeable under AOMDL**, with the challenge hash as a random
oracle and a collision resistant nonce coefficient hash: the bound of the
paper's Theorem 2 before solving for the advantage, for adversaries that make
no single-party signing queries. -/
theorem unforgeable (hN : N < n) (qh : ℕ) (hA : ∀ coins P, HashBound (A coins P) qh)
    (hS : ∀ coins P, NoSingle N (A coins P)) :
    forgeAdvantage C nonceCoef N qs A *
        (forgeAdvantage C nonceCoef N qs A / (qh + qs + 1 : ℕ) - 1 / n) ≤
      omdlAdvantage C (2 * qs + 1) (reduction C nonceCoef N qs A) +
        collisionAdvantage C nonceCoef N qs A
```

```lean
/-- **BIP 459 is unforgeable under AOMDL**, sessions and single-party
signatures together. With `q = qh + qs + 1`, where `qh` counts a single-party
signing query once for every entry of its list, the forger's success
probability is at most `sqrt (q * (omdl + coll)) + q / n + qs / (n - 1)`. The
last term pays for the single-party signatures and is not needed without them
(`unforgeable`). -/
theorem unforgeable_sqrt (hN : N < n) (qh : ℕ) (hA : ∀ coins P, HashBound (A coins P) qh) :
    forgeAdvantage C nonceCoef N qs A ≤
      Real.sqrt ((qh + qs + 1 : ℕ) * (omdlAdvantage C (2 * qs + 1) (reduction C nonceCoef N qs A) +
        collisionAdvantage C nonceCoef N qs A)) + (qh + qs + 1 : ℕ) / n + qs / (n - 1 : ℝ)
```

```lean
/-- **The reduction with a lazily sampled random oracle.** Its coins are the
forger's coins, `q` scalars for the answers of the oracle, and the new value
at the fork point. -/
def reductionLazy (q : ℕ) : OmdlAdversary n E (Coins × (Fin q → ZMod n) × ZMod n) := fun ρ =>
  answerLazy (QTree.stream ρ.2.1) 0 [] (reductionM C nonceCoef N qs A ρ.1 ρ.2.2)
```

```lean
/-- **BIP 459 is unforgeable under AOMDL, with a reduction that samples the
random oracle lazily.** The statement of `unforgeable_sqrt` for
`reductionLazy`. -/
theorem unforgeable_sqrt_lazy (hN : N < n) (qh : ℕ) (hA : ∀ coins P, HashBound (A coins P) qh) :
    forgeAdvantage C nonceCoef N qs A ≤
      Real.sqrt ((qh + qs + 1 : ℕ) *
        (omdlAdvantage C (2 * qs + 1) (reductionLazy C nonceCoef N qs A (2 * (qh + qs) + 1)) +
          collisionAdvantage C nonceCoef N qs A)) + (qh + qs + 1 : ℕ) / n + qs / (n - 1 : ℝ)
```

### The challenge hash reduced modulo `n`

`Dahlias/Hashed.lean` and `Dahlias/BytesSecurity.lean`. The random oracle answers with hash outputs, which the adversary sees and the signer and the verifier reduce.

```lean
/-- The game's answers when the random oracle returns outputs in `H`. -/
def AdvRH (H : Type) {N : ℕ} : AdvQ n N E X M → Type
  | .hash _ => H
  | .openSession => Option (PubNonce E)
  | .close .. => Option (ZMod n)
  | .single _ => Option (X × ZMod n)
```

```lean
/-- An adversary that sees the outputs of the hash function. -/
abbrev AdversaryH (n N : ℕ) (E X M H Coins : Type) :=
  Coins → E → Alg (AdvQ n N E X M) (AdvRH H) (Forgery n X M)
```

```lean
/-- The game's answers for the table `Tab` of hash outputs: a hash query
returns the output, the signer reduces it with `red`. -/
def challengerH (x : ZMod n) (nonces : Fin qs → SecNonce n) (Tab : SigIn N X M → H) :
    (q : AdvQ n N E X M) → SignerState X M → AdvRH H q × SignerState X M
  | .hash z, st => (Tab z, st)
  | .openSession, st =>
    challenger C nonceCoef N qs x nonces (fun z => red (Tab z)) .openSession st
  | .close k τ m agg pm pubnonces, st =>
    challenger C nonceCoef N qs x nonces (fun z => red (Tab z)) (.close k τ m agg pm pubnonces) st
  | .single items, st =>
    challenger C nonceCoef N qs x nonces (fun z => red (Tab z)) (.single items) st
```

```lean
/-- The sample of the game: the secret key, the nonces, the adversary's coins
and the table of hash outputs. -/
abbrev ForgeSampleH (n N qs : ℕ) (X M H Coins : Type) :=
  (ZMod n)ˣ × (Fin qs → (ZMod n)ˣ × (ZMod n)ˣ) × Coins × (SigIn N X M → H)
```

```lean
/-- **The unforgeability game with hash outputs in `H`** on one sample. The
verifier reduces the outputs with `red` as the signer does. -/
def forgeExperimentH (A : AdversaryH n N E X M H Coins) (ω : ForgeSampleH n N qs X M H Coins) :
    Prop :=
  let x : ZMod n := ω.1
  let nonces : Fin qs → SecNonce n := fun k => ((ω.2.1 k).1, (ω.2.1 k).2)
  let Tab := ω.2.2.2
  let out := (A ω.2.2.1 (C.mulG x)).run (challengerH C nonceCoef N qs red x nonces Tab)
    ⟨0, [], []⟩
  Wins C nonceCoef N x (fun z => red (Tab z)) out.1 out.2
```

```lean
/-- The adversary's probability of forging in the game with hash outputs. -/
noncomputable def forgeAdvantageH [Fintype Coins] [Fintype (SigIn N X M)] [Fintype H]
    (A : AdversaryH n N E X M H Coins) : ℝ :=
  prob (forgeExperimentH C nonceCoef N qs red A)
```

```lean
/-- The adversary for the game with scalar answers: when the oracle answers
`c`, it continues with the output `g c`. -/
def liftHash (g : ZMod n → H) {α : Type} :
    Alg (AdvQ n N E X M) (AdvRH H) α → Alg (AdvQ n N E X M) AdvR α
  | .done a => .done a
  | .ask (.hash z) f => .ask (.hash z) fun c => liftHash g (f (g c))
  | .ask .openSession f => .ask .openSession fun r => liftHash g (f r)
  | .ask (.close k τ m agg pm pubnonces) f =>
    .ask (.close k τ m agg pm pubnonces) fun r => liftHash g (f r)
  | .ask (.single items) f => .ask (.single items) fun r => liftHash g (f r)
```

```lean
/-- `h mod n`. -/
def redFin (m : ℕ) (h : Fin m) : ZMod n := (h.val : ZMod n)
```

```lean
/-- The smallest output that reduces to `c`. -/
def liftFin {m : ℕ} (hm : n ≤ m) (c : ZMod n) : Fin m :=
  ⟨c.val, lt_of_lt_of_le (ZMod.val_lt c) hm⟩
```

```lean
/-- **BIP 459's challenge hash**: an `m`-valued random oracle reduced modulo
`n`, for `m = 2²⁵⁶`. The adversary's advantage is at most the bound of
`unforgeable_sqrt` plus `(qh + qs + N) ⋅ (m - n) / m`. -/
theorem unforgeable_sqrt_fin {m : ℕ} (hm : n ≤ m) (A : AdversaryH n N E X M (Fin m) Coins)
    (hN : N < n) (qh : ℕ) (hA : ∀ coins P, HashBound (A coins P) qh) :
    forgeAdvantageH C nonceCoef N qs (redFin m) A ≤
      Real.sqrt ((qh + qs + 1 : ℕ) *
          (omdlAdvantage C (2 * qs + 1)
              (reduction C nonceCoef N qs fun coins P => liftHash N (liftFin hm) (A coins P)) +
            collisionAdvantage C nonceCoef N qs
              fun coins P => liftHash N (liftFin hm) (A coins P))) +
        (qh + qs + 1 : ℕ) / n + qs / (n - 1 : ℝ) +
        (qh + qs + N : ℕ) * ((m - n : ℝ) / m)
```

```lean
/-- 32-byte arrays. -/
abbrev B32 := {b : Bytes // b.length = 32}
```

```lean
/-- **secp256k1 with x-coordinates as 32-byte arrays.** -/
def secp256k1X : Curve n Point B32 where
  G := secp256k1B.G
  G_ne_zero := secp256k1B.G_ne_zero
  order_G := secp256k1B.order_G
  x P := ⟨xbytes P, length_xbytes P⟩
  hasEvenY := hasEvenY
  liftX b := secp256k1B.liftX b.1
  x_neg P := Subtype.ext (secp256k1B.x_neg P)
  hasEvenY_neg := secp256k1B.hasEvenY_neg
  liftX_x P hP he := secp256k1B.liftX_x P hP he
  liftX_spec r P h :=
    ⟨(secp256k1B.liftX_spec r.1 P h).1, (secp256k1B.liftX_spec r.1 P h).2.1,
      Subtype.ext (secp256k1B.liftX_spec r.1 P h).2.2⟩
```

```lean
/-- `hash_BIP0459/noncecoef` on 32-byte public keys and messages. -/
def nonceCoef32 (R₁ R₂ : Point) (items : List (B32 × B32 × Point)) : ZMod n :=
  Bytes.hashes.nonceCoef R₁ R₂ (items.map fun t => (t.1.1, t.2.1.1, t.2.2))
```

```lean
/-- **BIP 459 with 32-byte keys and messages is unforgeable under AOMDL**, with
the challenge hash as a 256-bit random oracle reduced modulo `n` and the BIP's
nonce coefficient hash. -/
theorem bytes_unforgeable_256 {Coins : Type} [Fintype Coins] (N qs : ℕ)
    (A : AdversaryH n N Point B32 B32 (Fin (2 ^ 256)) Coins) (hN : N < n) (qh : ℕ)
    (hA : ∀ coins P, HashBound (A coins P) qh) :
    forgeAdvantageH secp256k1X nonceCoef32 N qs (redFin (2 ^ 256)) A ≤
      Real.sqrt ((qh + qs + 1 : ℕ) *
        (omdlAdvantage secp256k1X (2 * qs + 1)
            (reduction secp256k1X nonceCoef32 N qs
              fun coins P => liftHash N (liftFin n_lt.le) (A coins P)) +
          collisionAdvantage secp256k1X nonceCoef32 N qs
            fun coins P => liftHash N (liftFin n_lt.le) (A coins P))) +
        (qh + qs + 1 : ℕ) / n + qs / (n - 1 : ℝ) +
        (qh + qs + N : ℕ) * ((((2 ^ 256 : ℕ) : ℝ) - n) / ((2 ^ 256 : ℕ) : ℝ))
```

```lean
/-- The cost of reducing a 256-bit hash output modulo `n`, for every oracle
value the game reads, is at most `2^-127`. -/
theorem hash_gap : (((2 ^ 256 : ℕ) : ℝ) - n) / ((2 ^ 256 : ℕ) : ℝ) ≤ 1 / 2 ^ 127
```

### Nonces derived by `NonceGen`

`Dahlias/Second.lean`, `Dahlias/NonceGen.lean` and `Dahlias/NonceGenSk.lean`. The adversary may also query `hash_BIP0459/nonce` and `hash_BIP0459/aux` and set the `extra_in` of the next slot.

```lean
/-- The answers to the queries `Q` and to the queries of `G`. -/
def SumR (R : Q → Type) (W : Type) : Q ⊕ D → Type
  | .inl q => R q
  | .inr _ => W
```

```lean
/-- Answer the queries of `G` from a table. -/
def answerG (G : D → W) : Alg (Q ⊕ D) (SumR R W) α → Alg Q R α
  | .done a => .done a
  | .ask (.inl q) f => .ask q fun r => answerG G (f r)
  | .ask (.inr z) f => answerG G (f (G z))
```

```lean
/-- At most `q` queries to `G`, whatever the answers. -/
def NBound : Alg (Q ⊕ D) (SumR R W) α → ℕ → Prop
  | .done _, _ => True
  | .ask (.inl _) f, q => ∀ r, NBound (f r) q
  | .ask (.inr _) f, q => 0 < q ∧ ∀ r, NBound (f r) (q - 1)
```

```lean
/-- An adversary that may also set the `extra_in` of the next nonce slot and
query `hash_BIP0459/nonce`. -/
abbrev NAdversary (n N : ℕ) (E X M Rnd Ex W Coins : Type) :=
  Coins → E → Alg ((AdvQ n N E X M ⊕ Ex) ⊕ (Rnd × Ex × Bool)) (SumR (SumR AdvR Unit) W)
    (Forgery n X M)
```

```lean
/-- The adversary for the game with uniform nonces: it answers the queries to
`hash_BIP0459/nonce` from a table in its coins and drops the `extra_in`. -/
def withTable (A : NAdversary n N E X M Rnd Ex W Coins) :
    Adversary n N E X M (Coins × (Rnd × Ex × Bool → W)) :=
  fun c P => answerG (fun _ : Ex => ()) (answerG c.2 (A c.1 P))
```

```lean
/-- The game's answers when the nonces of a slot depend on its `extra_in`.
The state has the `extra_in` chosen for every slot. -/
def challengerE (nv : Fin qs → Ex → SecNonce n) (x : ZMod n) (T : SigIn N X M → ZMod n) :
    (q : AdvQ n N E X M ⊕ Ex) → SignerState X M × (ℕ → Ex) →
      SumR AdvR Unit q × (SignerState X M × (ℕ → Ex))
  | .inl q, s =>
    ((challenger C nonceCoef N qs x (fun k => nv k (s.2 k)) T q s.1).1,
      ((challenger C nonceCoef N qs x (fun k => nv k (s.2 k)) T q s.1).2, s.2))
  | .inr e, s => ((), (s.1, update s.2 s.1.opened e))
```

```lean
/-- The part of the sample that the nonces do not depend on: the secret key,
the adversary's coins and the challenge hash. -/
abbrev Rest (n N : ℕ) (X M Coins : Type) := (ZMod n)ˣ × Coins × (SigIn N X M → ZMod n)
```

```lean
/-- The nonces of a slot from the values of `hash_BIP0459/nonce`. -/
def nvOf (v : Fin qs × Ex × Bool → W) : Fin qs → Ex → SecNonce n :=
  fun k e => (ρ (v (k, e, false)), ρ (v (k, e, true)))
```

```lean
/-- The game for nonces that depend on the `extra_in`, with the table `G`. -/
def winE (θ : Rest n N X M Coins) (G : Rnd × Ex × Bool → W) (nv : Fin qs → Ex → SecNonce n) :
    Prop :=
  let out := (answerG G (A θ.2.1 (C.mulG (θ.1 : ZMod n)))).run
    (challengerE C nonceCoef N qs nv (θ.1 : ZMod n) θ.2.2) (⟨0, [], []⟩, fun _ => e₀)
  Wins C nonceCoef N (θ.1 : ZMod n) θ.2.2 out.1 out.2.1
```

```lean
/-- The input of `hash_BIP0459/nonce` for a slot, an `extra_in` and a nonce
index. -/
def noncePt (rands : Fin qs → Rnd) (i : Fin qs × Ex × Bool) : Rnd × Ex × Bool :=
  (rands i.1, i.2.1, i.2.2)
```

```lean
/-- **The unforgeability game with `NonceGen`** on one sample: the nonces of
slot `k` are `ρ (G (rand k, extra_in, i))`. -/
def nonceGenExperiment
    (ω : (Rest n N X M Coins × (Fin qs → Rnd)) × (Rnd × Ex × Bool → W)) : Prop :=
  winE C nonceCoef N qs A e₀ ω.1.1 ω.2 (nvOf qs ρ fun i => ω.2 (noncePt qs ω.1.2 i))
```

```lean
/-- The adversary's advantage in the game with `NonceGen`. -/
noncomputable def nonceGenAdvantage : ℝ := prob (nonceGenExperiment C nonceCoef N qs A ρ e₀)
```

```lean
/-- **Unforgeability with `NonceGen`**, under AOMDL with both
`hash_BIP0459/sig` and `hash_BIP0459/nonce` as random oracles. -/
theorem nonceGen_unforgeable (g : (ZMod n)ˣ → W) (hg : Injective g) (hρ : ∀ u, ρ (g u) = u)
    (hN : N < n) (qh qn : ℕ) (hA : ∀ c P, NBound (A c P) qn)
    (hH : ∀ c P G, HashBound (answerG (fun _ : Ex => ()) (answerG G (A c P))) qh) :
    nonceGenAdvantage C nonceCoef N qs A ρ e₀ ≤
      Real.sqrt ((qh + qs + 1 : ℕ) *
          (omdlAdvantage C (2 * qs + 1) (reduction C nonceCoef N qs (withTable N A)) +
            collisionAdvantage C nonceCoef N qs (withTable N A))) + (qh + qs + 1 : ℕ) / n +
        qs / (n - 1 : ℝ) +
        (qs : ℝ) ^ 2 / Fintype.card Rnd + qs * (qn / Fintype.card Rnd) +
        (2 * qs : ℕ) * ((Fintype.card W - Fintype.card (ZMod n)ˣ : ℝ) / Fintype.card W)
```

```lean
/-- An adversary that may also query `hash_BIP0459/aux`. -/
abbrev SkAdversary (n N : ℕ) (E X M Rnd Rp Ex W Coins : Type) :=
  Coins → E → Alg (((AdvQ n N E X M ⊕ Ex) ⊕ (Rnd × Ex × Bool)) ⊕ Rp)
    (SumR (SumR (SumR AdvR Unit) W) Rnd) (Forgery n X M)
```

```lean
/-- The adversary for the game of `Dahlias.NonceGen` that answers the queries
to `hash_BIP0459/aux` from a table in its coins. -/
def withAux (A : SkAdversary n N E X M Rnd Rp Ex W Coins) :
    NAdversary n N E X M Rnd Ex W (Coins × (Rp → Rnd)) :=
  fun c P => answerG c.2 (A c.1 P)
```

```lean
/-- The game with the `rand` of every slot given by `v`, masked with the
secret key, and the table `Aux` for the adversary's queries. -/
def winSk (θ : Rest n N X M Coins × (Rnd × Ex × Bool → W)) (Aux : Rp → Rnd)
    (v : Fin qs → Rnd) : Prop :=
  nonceGenExperiment C nonceCoef N qs (fun c P => answerG Aux (A c P)) ρ e₀
    ((θ.1, fun k => mask θ.1.1 (v k)), θ.2)
```

```lean
/-- **The unforgeability game with `NonceGen` and its `sk` argument** on one
sample: the `rand` of slot `k` is `mask x (Aux (rand' k))`. -/
def nonceGenSkExperiment
    (ω : ((Rest n N X M Coins × (Rnd × Ex × Bool → W)) × (Fin qs → Rp)) × (Rp → Rnd)) : Prop :=
  winSk C nonceCoef N qs A ρ e₀ mask ω.1.1 ω.2 fun k => ω.2 (ω.1.2 k)
```

```lean
/-- The adversary's advantage in the game with `NonceGen` and its `sk`
argument. -/
noncomputable def nonceGenSkAdvantage : ℝ :=
  prob (nonceGenSkExperiment C nonceCoef N qs A ρ e₀ mask)
```

```lean
/-- **`NonceGen` with its `sk` argument**, against the game with uniform
nonces: the error terms of the two random oracles and of the reduction modulo
the group order. -/
theorem nonceGenSk_advantage (g : (ZMod n)ˣ → W) (hg : Injective g) (hρ : ∀ u, ρ (g u) = u)
    (qn qa : ℕ) (hA : ∀ c P, NBound (A c P) qa)
    (hG : ∀ c P (Aux : Rp → Rnd), NBound (answerG Aux (A c P)) qn) :
    nonceGenSkAdvantage C nonceCoef N qs A ρ e₀ mask ≤
      forgeAdvantage C nonceCoef N qs (withTable N (withAux N A)) +
        (qs : ℝ) ^ 2 / Fintype.card Rnd + qs * (qn / Fintype.card Rnd) +
        (2 * qs : ℕ) * ((Fintype.card W - Fintype.card (ZMod n)ˣ : ℝ) / Fintype.card W) +
        (qs : ℝ) ^ 2 / Fintype.card Rp + qs * (qa / Fintype.card Rp)
```

### Binding

`Dahlias/Binding.lean`.

```lean
/-- A binding adversary with coins in `Coins`: it queries the challenge hash
and outputs two lists and a signature. -/
abbrev BindAdversary (n N : ℕ) (X M Coins : Type) :=
  Coins → QTree (SigIn N X M) (ZMod n) (List (X × M) × List (X × M) × (X × ZMod n))
```

```lean
/-- **The strong binding game** on one sample. -/
def bindExperiment {Coins : Type} (A : BindAdversary n N X M Coins)
    (ω : Coins × (SigIn N X M → ZMod n)) : Prop :=
  (eval ω.2 (A ω.1)).1 ≠ (eval ω.2 (A ω.1)).2.1 ∧
    (eval ω.2 (A ω.1)).1.length ≤ N ∧ (eval ω.2 (A ω.1)).2.1.length ≤ N ∧
    verify C.ops (hashesOf N nonceCoef ω.2) (eval ω.2 (A ω.1)).1 (eval ω.2 (A ω.1)).2.2 = true ∧
    verify C.ops (hashesOf N nonceCoef ω.2) (eval ω.2 (A ω.1)).2.1 (eval ω.2 (A ω.1)).2.2 = true
```

```lean
/-- **BIP 459 is strongly binding**: an adversary with at most `qh` different
random oracle queries finds a signature that is valid for two different lists
with probability at most `(qh + 2⋅N)² / n`. -/
theorem strongly_binding (hE : Curve.PrimeOrder n E) (hN : N < n) (qh : ℕ)
    (hA : ∀ coins T, (fresh T (A coins)).length ≤ qh) :
    prob (bindExperiment C nonceCoef N A) ≤ ((qh + 2 * N : ℕ) : ℝ) ^ 2 / n
```

### The bytes

`Dahlias/Bytes.lean` and `Dahlias/Encoding.lean`. `Sign` and `Verify` on bytes parse their inputs and call the model.

```lean
/-- The secp256k1 operations of BIP 459, on 32-byte x-coordinates. -/
def specOps : Ops n Point Bytes where
  mulG := secp256k1.mulG
  smul k P := k.val • P
  x := xbytes
  hasEvenY := hasEvenY
  liftX b := if b.length = 32 ∧ toNatBE b < p then liftX (toNatBE b : F) else none
```

```lean
/-- `cbytes(P)`. -/
def cbytes (P : Point) : Bytes := (if hasEvenY P then 2 else 3) :: xbytes P
```

```lean
/-- `cpoint(b)`. -/
def cpoint (O : Ops n Point Bytes) (b : Bytes) : Option Point :=
  match b with
  | 2 :: x => O.liftX x
  | 3 :: x => (O.liftX x).map (- ·)
  | _ => none
```

```lean
/-- A 66-byte public or aggregate nonce as two points, with `0` for a half
that `cpoint` rejects (see `Dahlias.Basic`). -/
def parseNonce (O : Ops n Point Bytes) (b : Bytes) : PubNonce Point :=
  if b.length = 66 then ((cpoint O (b.take 33)).getD 0, (cpoint O (b.drop 33)).getD 0) else (0, 0)
```

```lean
/-- `int(b)` for a 32-byte array, failing if the value is `≥ n`. -/
def scalar (b : Bytes) : Option (ZMod n) :=
  if b.length = 32 ∧ toNatBE b < n then some (toNatBE b : ZMod n) else none
```

```lean
/-- `int(b) mod n`. -/
def scalarWrap (b : Bytes) : ZMod n := (toNatBE b : ZMod n)
```

```lean
/-- The tagged hashes of the signing protocol. -/
def hashes : Hashes n Point Bytes Bytes where
  nonceCoef R₁ R₂ items := scalarWrap (taggedHash "BIP0459/noncecoef"
    (cbytes R₁ ++ cbytes R₂ ++ items.flatMap fun it => it.1 ++ it.2.1 ++ cbytes it.2.2))
  sig pm r pkm := scalarWrap (taggedHash "BIP0459/sig"
    (pm.flatMap (fun x => x.1 ++ x.2) ++ r ++ pkm.1 ++ pkm.2))
```

```lean
/-- The common input conditions: the arrays have the same nonzero length,
public keys and messages are 32 bytes. -/
def wellFormed (pks msgs : List Bytes) (u : ℕ) : Bool :=
  decide (0 < u) && pks.length == u && msgs.length == u && pks.all is32 && msgs.all is32
```

```lean
/-- `Sign`. -/
def sign (secnonce sk m aggnonce : Bytes) (pks msgs pubnonces : List Bytes) : Option Bytes :=
  if wellFormed pks msgs pubnonces.length && is32 m && secnonce.length == 64 then
    match scalar (secnonce.take 32), scalar (secnonce.drop 32), scalar sk with
    | some r₁, some r₂, some d =>
      (Dahlias.sign O hashes (r₁, r₂) d m (parseNonce O aggnonce) (pks.zip msgs)
        (pubnonces.map (parseNonce O))).map serScalar
    | _, _, _ => none
  else none
```

```lean
/-- `Verify`. -/
def verify (pks msgs : List Bytes) (sig : Bytes) : Bool :=
  wellFormed pks msgs pks.length && sig.length == 64 &&
    match scalar (sig.drop 32) with
    | some s => Dahlias.verify O hashes (pks.zip msgs) (sig.take 32, s)
    | none => false
```

```lean
theorem cpoint_eq_some_iff {b : Bytes} {P : Point} :
    cpoint specOps b = some P ↔ P ≠ 0 ∧ b = cbytes P
```

```lean
/-- **The index lookup of `Sign` on bytes is the model's.** For 66-byte public
nonces, the indices `j` with `pubnonce_j[33:66] = cbytes(R₂)` are the indices
whose parsed second half is `R₂`. -/
theorem matchIdxs_bytes (pubnonces : List Bytes) (hlen : ∀ b ∈ pubnonces, b.length = 66)
    {R : Point} (hR : R ≠ 0) :
    matchIdxs (pubnonces.map (parseNonce specOps)) R =
      (List.range pubnonces.length).filter fun j =>
        (pubnonces[j]?).map (·.drop 33) = some (cbytes R)
```

```lean
/-- The bytes that `hash_BIP0459/sig` hashes. -/
def sigInput (pm : List (Bytes × Bytes)) (r : Bytes) (pkm : Bytes × Bytes) : Bytes :=
  pm.flatMap (fun x => x.1 ++ x.2) ++ r ++ pkm.1 ++ pkm.2
```

```lean
/-- The bytes that `hash_BIP0459/noncecoef` hashes. -/
def nonceCoefInput (R₁ R₂ : Point) (items : List (Bytes × Bytes × Point)) : Bytes :=
  cbytes R₁ ++ cbytes R₂ ++ items.flatMap fun it => it.1 ++ it.2.1 ++ cbytes it.2.2
```

```lean
/-- All public keys and messages of a list are 32 bytes. -/
def Pairs32 (pm : List (Bytes × Bytes)) : Prop := ∀ e ∈ pm, e.1.length = 32 ∧ e.2.length = 32
```

```lean
/-- **The input of `hash_BIP0459/sig` determines `(L, r, pk, m)`**, for
32-byte public keys, messages and `r`. -/
theorem sigInput_injective {pm pm' : List (Bytes × Bytes)} {r r' : Bytes}
    {pkm pkm' : Bytes × Bytes} (h : Pairs32 pm) (h' : Pairs32 pm') (hr : r.length = 32)
    (hr' : r'.length = 32) (hk : pkm.1.length = 32) (hk' : pkm'.1.length = 32)
    (hm : pkm.2.length = 32) (hm' : pkm'.2.length = 32)
    (heq : sigInput pm r pkm = sigInput pm' r' pkm') : pm = pm' ∧ r = r' ∧ pkm = pkm'
```

```lean
/-- The items of a nonce coefficient input have 32-byte public keys and
messages and nonces other than the point at infinity. -/
def Items32 (items : List (Bytes × Bytes × Point)) : Prop :=
  ∀ it ∈ items, it.1.length = 32 ∧ it.2.1.length = 32 ∧ it.2.2 ≠ 0
```

```lean
/-- **The input of `hash_BIP0459/noncecoef` determines `(R₁, R₂)` and the
`(pkᵢ, mᵢ, R₂,ᵢ)`**, for 32-byte public keys and messages and points other
than the point at infinity. `GetSessionValues` hashes only such inputs. -/
theorem nonceCoefInput_injective {R₁ R₂ R₁' R₂' : Point}
    {items items' : List (Bytes × Bytes × Point)} (h1 : R₁ ≠ 0) (h2 : R₂ ≠ 0) (h1' : R₁' ≠ 0)
    (h2' : R₂' ≠ 0) (h : Items32 items) (h' : Items32 items')
    (heq : nonceCoefInput R₁ R₂ items = nonceCoefInput R₁' R₂' items') :
    R₁ = R₁' ∧ R₂ = R₂' ∧ items = items'
```

```lean
/-- **`Verify` on bytes is `Verify` of the instance**: for 32-byte public
keys, messages and `r`, and the encoding of the scalar `s`. -/
theorem verify_bytes {H : Hashes n Point B32 B32} (hH : Agree H hashes) (pm : List (B32 × B32))
    (r : B32) (s : ZMod n) :
    Bytes.verify specOps (pm.map fun e => e.1.1) (pm.map fun e => e.2.1) (r.1 ++ serScalar s) =
      verify secp256k1X.ops H pm (r, s)
```

```lean
/-- **`Sign` on bytes is `Sign` of the instance**: for the encodings of the
secret nonce and the secret key, a 32-byte message, 32-byte public keys and
messages, and any byte arrays for the aggregate nonce and the public nonces,
which are parsed. -/
theorem sign_bytes {H : Hashes n Point B32 B32} (hH : Agree H hashes) (r₁ r₂ d : ZMod n)
    (m : B32) (aggnonce : Bytes) (pm : List (B32 × B32)) (pubnonces : List Bytes) :
    Bytes.sign specOps (serScalar r₁ ++ serScalar r₂) (serScalar d) m.1 aggnonce
        (pm.map fun e => e.1.1) (pm.map fun e => e.2.1) pubnonces =
      (sign secp256k1X.ops H (r₁, r₂) d m (parseNonce specOps aggnonce) pm
        (pubnonces.map (parseNonce specOps))).map serScalar
```

<!-- statements:end -->
