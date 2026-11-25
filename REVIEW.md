# Reviewing dahlias-lean

Lean checks the proofs. A reviewer checks that the statements say what they should. Proofs can stay unread, because a wrong proof does not compile. A wrong definition does, and some definitions are under `Dahlias/Proofs/`: the reduction, the collision finder and what they call are part of what the main theorem says. [Every definition behind the results](#every-definition-behind-the-results) lists all definitions that a result depends on. The list is computed from the compiled project, and the build fails if it changes.

## What to read

The definitions and statements below decide whether the results mean anything. [The statements](#the-statements) at the end of this file prints the main ones on one page and lists the rest.

1. `Dahlias/Basic.lean`, all of it. Compare the algorithms with BIP 459. The header lists the modelling choices.
2. `Dahlias/Security.lean`, all of it: the unforgeability game, the AOMDL game, and the places where the game differs from the paper's.
3. `Dahlias/Alg.lean`, the definitions `Alg`, `bind` and `run`, and `Dahlias/Prob.lean`, the definition `prob`.
4. `Dahlias/Unforgeability.lean`, the statements of `unforgeable` and `unforgeable_sqrt` and the definitions `collisionAdvantage` and `NoSingle`.
5. `Dahlias/Hashed.lean`, the game in which the random oracle returns hash outputs, and the statement of `unforgeable_sqrt_fin`.
6. `Dahlias/NonceGen.lean` and `Dahlias/NonceGenSk.lean`, the games with nonces derived as in `NonceGen`, and the statements. Then `Dahlias/NonceGenHashed.lean`, the games that also have the hash outputs of step 5, the forgers `withStream` and `withAuxStream` in `Dahlias/NonceGenLazy.lean`, and the statements of `bytes_nonceGenSk_unforgeable_256` and `bytes_nonceGen_unforgeable_256` in `Dahlias/BytesSecurity.lean`.
7. `Dahlias/Binding.lean`, the header, `bindExperiment` and the statement of `strongly_binding`.
8. `Dahlias/Proofs/Reduction.lean`, all definitions: `reduction`, `collider` and what they call. The theorems measure these two algorithms, so their bodies are part of the statement. Then `reductionLazy` in `Dahlias/LazyReduction.lean` and `colliderLazy` in `Dahlias/LazyCollider.lean`. The theorems for `NonceGen` with a counter measure a third algorithm, `keyForger` in `Dahlias/NonceGenCounter.lean`.
9. `Dahlias/Bytes.lean` and the statements of `Dahlias/Encoding.lean`, for BIP 459's bytes. Then `Dahlias/BytesGame.lean`: `AdvQB`, `challengerB` and `WinsB`, the game in which the adversary sends byte arrays.

taproot-lean supplies the curve interface (`Taproot.Curve`), secp256k1 and SHA-256. A full review reads those definitions too. taproot-lean checks the order of secp256k1's generator with compiled code. `Dahlias/OrderG.lean` proves it from a certificate that the kernel checks, and the theorems here use that proof (`secp256k1F`), so only the test vector checks depend on compiled code.

The model was compared with BIP 459 at bitcoin/bips commit [`f3d1668`](https://github.com/bitcoin/bips/blob/f3d1668891fcdad99770245110bc6a22c87bce97/bip-0459.mediawiki). CI takes the test vectors and the Python reference from the same commit.

## Questions to ask

**Is the game the paper's?** `forgeExperiment` is the co-EUF-CMA-TK game of the DahLIAS paper (Fig. 5) with two changes and one addition. All three are described in the header of `Dahlias/Security.lean`.

- The game records the tweaked x-only public key of every signature, where the paper records the tweak. With x-only keys two different tweaks can give the same key without revealing anything: `(α, β)` and `(-α, -β)` always do. The paper's game would count a signature under one of them as a forgery under the other.
- A `Sign` call that fails leaves the session open. The paper closes it. The adversary here has more freedom.
- The adversary may also ask for single-party signatures: the honest signer signs a list of its own tweaked keys with one uniform nonce (`signSingle`, `challenger_single`). This is not in the paper. Sessions and single-party signatures share the `qs` nonce slots. `challengerG true` is a variant of the game that only the proof uses. The statements a reader has to trust are about `challenger`, which is `challengerG false`.

**Is the adversary restricted?** An `Adversary` is any function from coins of a finite type and the public key point to an oracle algorithm. It chooses all other public keys, all messages, all nonces of the other signers, the aggregate nonce and the tweaks, and it may leave sessions open and interleave them. It is not algebraic. The hypothesis `HashBound` bounds its random oracle queries, counting a single-party signing query once for every entry of its list. The game bounds the number of sessions and single-party signatures.

**Does the reduction cheat?** `reduction` has the type `OmdlAdversary`: it is an oracle algorithm for the AOMDL game and gets nothing else. It wins only if it makes fewer discrete logarithm queries than it received challenges, so the query count is part of the statement. The type does not rule out an algorithm that finds the logarithms by search without asking, and there is no cost model, so the body has to be read. `reduction` asks for its challenges and calls `reductionBody`. That runs the forger with `simChallenger` answering its queries, which asks at most one discrete logarithm query for a signing query (`simSign`). It takes the fork point from the forger's output, runs the forger a second time with the table changed at that point, asks at most two more queries for every session (`solveSessions`) and computes the secret key from the two forgeries with one division (`extractX`). Nothing in these definitions goes through scalars or points in search of one. `collider` is a function of a sample. It holds the secret key, runs the game twice (`gameRecs`) and goes through the pairs of session records of the two runs for a collision. It is marked noncomputable only because it decides classically whether two hash inputs are equal.

**What is random?** The secret key and the nonces are uniform nonzero scalars. In `unforgeable` and `unforgeable_sqrt` the challenge hash is a uniform table of scalars, on inputs with lists of at most `N` entries. `forgeAdvantage_eq_lazy` proves that the game has the same advantage when the oracle answers every new query with the next of `qh + qs + N` uniform scalars. The coins of `reduction` contain a whole table. `reductionLazy` takes `2·(qh + qs) + 1` scalars instead and wins the AOMDL game with the same probability (`omdlAdvantage_reduction_eq_lazy`). The sample of `collider` has a whole table as well, and `colliderLazy` finds a collision as often with `2·(qh + qs)` scalars (`collisionAdvantage_eq_lazy`). `unforgeable_sqrt_lazy_both` is the theorem with these two algorithms. In `nonceGen_unforgeable` the forger that the reduction runs has a whole table of `hash_BIP0459/nonce` in its coins (`withTable`). `nonceGen_unforgeable_lazy` and `nonceGenSk_unforgeable_lazy` are the statements for forgers that answer the queries to `hash_BIP0459/nonce` and `hash_BIP0459/aux` from `qn` and `qa` values in their coins, with `reductionLazy` and `colliderLazy`. The theorems for 32-byte values are stated this way. The framework has no cost model, so there is no statement about running time.

**How is the challenge hash reduced modulo `n`?** BIP 459 computes `c = int(hash(…)) mod n` from a 256-bit hash. In the game of `Dahlias/Hashed.lean` the oracle returns a uniform element of a type `H` of hash outputs. The adversary sees the outputs, and `Sign` and `Verify` turn them into scalars with `red`. `forgeAdvantageH_le` reduces this game to the one with scalar answers. The game reads at most `qh + qs + N` oracle values, and each is outside a fixed set of `n` outputs, one for every scalar, with probability `(|H| - n) / |H|`. For `H = {0, …, 2^256 - 1}` and `red h = h mod n` that is at most `2^-127` (`hash_gap`), and `bytes_unforgeable_256` is the theorem for secp256k1. `Dahlias/BindingHashed.lean` does the same for strong binding, where the game reads at most `qh + 2⋅N` oracle values (`strongly_binding_fin`, `bytes_strongly_binding_256`).

**What is the nonce coefficient hash?** A fixed function into the scalars, `nonceCoef`. The theorem holds for every such function and measures how often `collider` outputs a collision of it. This is the usual way to state collision resistance for an unkeyed hash function. BIP 459's `int(hash_BIP0459/noncecoef(…)) mod n` is such a function (`nonceCoef32`). `collision_bytes` proves that a collision of it is a pair of different byte strings whose tagged SHA-256 values are congruent modulo `n`, so equal or `n` apart. That includes the inputs with the point at infinity, which the game hashes for the nonce of a single-party signature: `cbytes` maps that point to `02 ‖ 0^32`, and no curve point has the x-coordinate `0` (`sq_ne_seven`).

**What does the single-party query add?** BIP 459 leaves open how a party that holds all keys of a list signs without running the protocol with itself, and says that the method sketched on the mailing list needs a security analysis. `signSingle` is that method: one nonce `r`, `R = r⋅G`, `s = ±r + Σ cᵢ⋅dᵢ`. The game offers it to the adversary next to the sessions, and `unforgeable_sqrt` covers it at the cost of `qs / (n - 1)`. The reduction cannot answer two such queries of one slot with the same nonce in its two runs, so it works with a variant in which the nonce is `r₁ + b⋅r₂` for a coefficient `b` derived from the list (`challengerG true`). `forgeAdvantage_le_derived` shows that the adversary cannot tell the variant from the game.

**Is the theorem vacuous?** `Dahlias/Examples.lean` has a forger that satisfies `HashBound` and wins with positive probability. `Dahlias/Secp256k1.lean` instantiates the theorem for secp256k1.

**Is the binding game the paper's?** `bindExperiment` is the game of Fig. 11 with the random oracle of the unforgeability game: the adversary outputs two lists and one signature and wins if the lists differ and the signature verifies for both. The theorem counts the adversary's own oracle queries. The `2N` in the bound are the verifier's queries. It holds for groups of prime order, and `secp256k1_primeOrder` proves that secp256k1 is one.

**Is the AOMDL game the usual one?** The game of `Dahlias/Security.lean` draws the discrete logarithms of its challenges from the nonzero scalars, because the challenges stand for the secret key and the nonces, which are nonzero. The usual game draws them from all scalars. `Dahlias/OmdlStd.lean` has that game. `omdlAdvantage_le_std` shows that an adversary's advantages in the two differ by at most `c / n` for `c` challenges, and `unforgeable_sqrt_std` is the main theorem with the usual game: the reduction's `2⋅qs + 1` challenges add `(2⋅qs + 1) / n` next to its advantage.

**What does the bound say?** With `q = qh + qs + 1`, `unforgeable` states `adv * (adv / q - 1 / n) ≤ omdl + coll` for adversaries that ask for no single-party signatures (`NoSingle`). This is the bound of the paper's Theorem 2 up to the count of queries. `unforgeable_sqrt` holds for all adversaries: `adv ≤ sqrt (q * (omdl + coll)) + q / n + qs / (n - 1)`. The square root is the loss of the forking lemma, and `qs / (n - 1)` pays for the single-party signatures.

**Is the bound tight?** Its additive term is. `grinder` makes `q` random oracle queries and no signing queries, and it computes no discrete logarithm. For each of `q` messages it asks for the challenge of the list `[(pk, m)]` with `R = pk`, and if a challenge is `-1` the signature `(pk, 0)` is valid. It forges with probability at least `1 - ((n - 1) / n)^q`, which is at least `q / (n + q)` (`grinder_advantage`, `grinder_advantage_ge`). `unforgeable_sqrt` bounds this forger by `sqrt (…) + (q + 1) / n`. No theorem here says that the square root or the term `qs / (n - 1)` is needed.

**What connects the theorems to BIP 459's bytes?** `Dahlias/Bytes.lean` defines the algorithms on bytes as parsing followed by the model's algorithms, and the 60 test vectors and the differential tests run them. `Dahlias/Encoding.lean` proves what the model takes for granted. The hash inputs are injective encodings of the structured inputs (`sigInput_injective`, `nonceCoefInput_injective`). `cpoint` accepts exactly the encodings `cbytes(P)`, so comparing nonces as bytes is comparing points (`cpoint_eq_some_iff`, `matchIdxs_bytes`). `sign_bytes` and `verify_bytes` say that `Sign` and `Verify` on bytes are `Sign` and `Verify` of the instance that `bytes_unforgeable` and `bytes_unforgeable_256` are about. A nonce that does not parse becomes the point `0` there, and the adversary of the game may send `0` as well. `nonceGen_eq` and `nonceGen_sk_eq` say that `NonceGen` on bytes derives the secret nonces as the games with `NonceGen` do: they are `hash_BIP0459/nonce(rand ‖ extra_in ‖ i)` as 256-bit values reduced modulo `n`, and with the `sk` argument `rand` is `maskXor x` of `hash_BIP0459/aux(rand')`. The bytes that the nonce hash gets determine `(rand, extra_in, i)` (`nonceInput_injective`). SHA-256 has 32 bytes of output (`length_sha256`), so the challenge hash is a 256-bit value reduced modulo `n` (`hashes_sig_eq_redFin`).

## BIP 459's claims

What BIP 459 says about correctness and security, and the theorem for it.

| BIP 459 | Lean |
|---|---|
| General Signing Flow: if all signers behaved honestly, the result passes `Verify`. | `verify_honest` in the model, `Bytes.verify_honest` on bytes. |
| General Signing Flow: if the aggregate signature is invalid, the coordinator can find the disruptive signer with `PartialSigVerify`. `PartialSigVerify`: if it succeeds for all signers, `SigAgg` with the aggregate nonce from `NonceAgg` gives a valid signature. | `verify_sigAgg_of_partialSigVerify`, and `exists_partialSigVerify_eq_false` for the contrapositive: an invalid aggregate has a partial signature that fails. `partialSigVerify_iff_eq_sign`: at an honest signer's index the partial signature that `Sign` returns passes and no other value does, so an honest signer is not blamed and nobody can pass in its place. `verify_eq_false_of_one_bad`: one bad partial signature among good ones makes the aggregate invalid. Two bad ones can cancel, and `PartialSigVerify` still fails for both. |
| General Signing Flow and Security: a `secnonce` must not be used twice. Three executions of `Sign` in different sessions reveal the secret key. Nonce Generation: the same holds for nonces derived deterministically. | `evenScalar_of_three_sessions`, if a determinant of public values is nonzero. `evenScalar_of_nonce_reuse` for two executions with the same session values and different challenges. |
| Nonce Generation: `NonceGen` with a uniform `rand'`. | `nonceGen_unforgeable`, with `hash_BIP0459/nonce` as a random oracle and an `extra_in` chosen by the adversary. `nonceGenSk_advantage` adds the optional `sk` argument. `bytes_nonceGenSk_unforgeable_256` and `bytes_nonceGen_unforgeable_256` are the statements for 32-byte values and 256-bit hashes. |
| Nonce Generation: the optional arguments may prevent key exposure if `rand'` is not uniform. | `bytes_nonceGenCtr_unforgeable_256` for one case: the `sk` argument is given and `rand'` is a public counter value that does not repeat, as in `secp256k1_fullagg_nonce_gen_counter`. No theorem for any other `rand'` that is not uniform, or for `extra_in`. |
| Role of the Coordinator and Security: a malicious coordinator colluding with all but one signer cannot forge. | `unforgeable_sqrt`. The adversary of the game is the coordinator and every other signer. |
| List Ordering: a signature valid for a list is not valid for a non-trivial permutation of it, except with negligible probability. `Sign`: the aggregate signature is valid for exactly this list. Security: the scheme is strongly binding. | `strongly_binding`, `secp256k1_strongly_binding`: a signature is valid for two different lists with probability at most `(qh + 2N)² / n`. `bytes_strongly_binding_256` is the statement for secp256k1 with 32-byte keys and messages and a 256-bit random oracle reduced modulo `n`, which adds `(qh + 2N) ⋅ (2^256 - n) / 2^256`. |
| Rationale: 32-byte messages keep the encoding of the list `L` unambiguous. | `sigInput_injective`, and `nonceCoefInput_injective` for the nonce coefficient. |
| Rationale: verifiers should hash the common prefix `L ‖ xbytes(R)` once. | No theorem. The model hashes every input from the start. libsecp256k1 hashes the prefix once, and the differential test compares the two. |
| Rationale: two nonces per signer prevent the ROS attack across concurrent sessions. | `unforgeable_sqrt`, for any number of concurrent sessions. No theorem about a scheme with one nonce per signer. |
| Rationale, Security and the footnote of `Sign`: the `R₂` uniqueness check and the message check are needed. Checking that the combination of public key, message and `R₂` is unique is not enough. | `ros_forgery`: with the weaker check, `ℓ ≥ log₂ n` concurrent sessions give a forgery. `msgSwap_wins`: without the message check a coordinator makes the signer sign any message. No theorem for the key extraction that the Security section mentions. |
| Rationale: key tweaking for BIP 32 and BIP 341. Key Tweaking: the signer uses `sk'`, the list has `xbytes(P')`. | `tweakPK_mulG`: `TweakSK` and `TweakPK` agree. `tweakSK_affine`: both kinds of tweak, and sequences of them, are tweaks of the game, so `unforgeable_sqrt` covers them. |
| Rationale: an optimized signing algorithm for a single party that knows all secret keys needs a security analysis before it can be specified. | `unforgeable_sqrt` covers the method `signSingle` (`challenger_single`), also when the party runs sessions with others at the same time. `verify_signSingle` and `sigAgg_eq_signSingle` show that it produces the signature of the protocol for the same `R`. |
| Security: a partial signature is not a signature. An adversary can produce one that verifies for any public key. | No theorem. |
| Security: proven under AOMDL in the concurrent setting with key tweaking, with `hash_BIP0459/sig` as a random oracle and a collision resistant `hash_BIP0459/noncecoef`. | `unforgeable`, `unforgeable_sqrt`. `bytes_unforgeable_256` is the statement for secp256k1 with 32-byte keys and messages, the BIP's nonce coefficient hash, and a 256-bit random oracle reduced modulo `n`. `bytes_nonceGenSk_unforgeable_256` is that statement with the nonces of `NonceGen`. |
| Security, footnote: strong binding needs public keys other than the point at infinity, which `lift_x` guarantees. | `verify` fails unless every key lifts, and `strongly_binding` uses that. |
| The pseudocode of `Sign`, `Verify` and the other algorithms. | `Dahlias/Basic.lean` and `Dahlias/Bytes.lean` are transcriptions. No theorem says they are BIP 459's algorithms. The 60 test vectors and the differential tests against `reference.py` and libsecp256k1 compare them. |

## What the theorems do not say

- No theorem bounds running time. `reduction` runs the forger twice, which is visible in its definition. `reductionLazy` and `colliderLazy` show that neither algorithm of the theorem needs a table of exponential size.
- The game is for lists of at most `N` entries, with `N < n`.
- The nonces of the game are uniform. `nonceGen_unforgeable` and `nonceGenSk_advantage` derive them as `NonceGen` does, from a uniform `rand'` and with the hash functions of `NonceGen` as random oracles. `nonceGenCtr_advantage` and `bytes_nonceGenCtr_unforgeable_256` are for a `rand'` that is a public counter value, with the `sk` argument. Its counter values are distinct. The key that `NonceGen` gets in a slot is the signer's key or a key tweaked from it. That tweak is fixed before the game: the adversary chooses the tweak of every signing query, but not the key of `NonceGen`. No theorem says anything about another `rand'` that is not uniform.
- BIP 459's `NonceGen` fails if a derived nonce is zero (`nonceGen_eq`). The signer of the games with `NonceGen` uses the slot all the same. The error term for the reduction modulo `n` bounds the probability of such a slot.
- In the games with the byte interface (`Dahlias/BytesGame.lean`) three things are not byte arrays. The tweak of a signing query and of a forgery is a pair of scalars, since `Sign` has no tweak argument. A hash query is a tuple of 32-byte arrays and not the byte string that BIP 459 hashes. A single-party signature has no algorithm on bytes in BIP 459, so that query takes 32-byte messages. No theorem has a random oracle on byte strings.
- `hash_BIP0459/sig` is a random oracle on structured inputs with lists of at most `N` entries. SHA-256 on the bytes is a function of those inputs (`sigInput_injective`), and modelling it as a random function is the assumption.
- A single-party signature of the game is for a list of keys that are all tweaks `α + β⋅x`, `β ≠ 0`, of the one honest key. The theorem does not cover a party that signs alone for several unrelated secret keys.

## Machine checks

- `lake build` compiles every proof. It fails if the axioms of a main result change (`Dahlias/Summary.lean`). The build sets `autoImplicit = false`, so a misspelled variable in a statement is an error and not a new implicit variable.
- `Dahlias/Summary.lean` also guards two inventories of the whole project, computed by the commands of `Dahlias/Audit.lean`. `#project_axioms` lists the axioms that the modules declare and that their declarations depend on, so an axiom that no main result uses fails the build too. `#surface` lists the definitions behind the results, which is the last section of this file.
- `scripts/check.sh` reads every Lean file of the repository for `sorry`, axioms, unsafe code and compiled evaluation outside the test vector checks. It checks that the root module has only imports and the generated summary only guarded commands. It checks that every code block under [The statements](#the-statements) is in the sources word for word, and that `Dahlias/Summary.lean` checks the axioms of every theorem printed there and of every result in the README's table. It finds a result by its full name, so a declaration with the same last name in another namespace does not count.
- `scripts/check_selftest.sh` changes a copy of the sources in ten ways, such as an axiom in the root module or in the summary, and checks that `scripts/check.sh` fails each time.
- `scripts/replay.sh` replays in the kernel with `leanchecker`, without the elaborator, every project module and every taproot-lean module that the project imports, one process per module.
- CI runs all of these. It also regenerates the summary and the test vector data, runs 300 cases of `scripts/fuzz.py` against the Python reference with a new seed for every run, and checks that the build fails when an unused axiom is added to a module.
- A second CI job builds libsecp256k1 with the `fullagg` module at the commit the README names. It runs the module's unit tests, 3,000 cases of `scripts/fuzz.py` against the Python reference with a new seed, and the exhaustive tests on the group of order 13.

### Mutants of the model

`scripts/mutate_model.py` changes one definition at a time in a copy of the project and builds it. A mutant that still built would show that no theorem depends on the detail it changes. All 18 fail. A second CI workflow runs it on every push. Lake does not build what depends on a module that failed, so the table names the declarations nearest to the changed definition, which are often lemmas and not main theorems.

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
| The game with hash outputs verifies a forgery with the challenges `0` | `forgeAdvantageH_le` |
| The nonce hash does not get the nonce index, so `r₁ = r₂` | `noncePt_injective` |
| The adversary can set the `extra_in` of a slot that is open | `sel_couple` |
| The game with `NonceGen` and hash outputs verifies a forgery with the challenges `0` | `nonceGenExperimentH_lift`, `nonceGenExperimentH_le` |
| A lazily sampled oracle answers a repeated query with a new value | `evalLazy_toTree` |
| `rand` is masked with the key `1` and not with the secret key in the game with a counter | `nonceGenCtr_advantage`, `nonceGenCtrAdvantageH_le` |
| The forger of the game with a counter does not check that its message is new | `forgeTail_wins`, `hashBound_forgeTail` |
| The game with the byte interface accepts a forgery without `Verify` | `wins_of_winsB` |

For two of BIP 459's checks there is more than a proof that fails. `msgSwap_wins` is an attack on `Sign` without the message check, and `ros_forgery` is one on `Sign` with the weaker uniqueness check.

### Tests of the implementations

`scripts/fuzz.py` compares the algorithms on bytes with BIP 459's `reference.py` and with libsecp256k1's `fullagg` module, on honest sessions and on malformed inputs. `scripts/mutate_secp256k1.py` measures what those cases, the module's unit tests and the exhaustive tests on a small group notice. Of 59 small changes to the C module they notice 58. The README has the details and the one exception.

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

`Dahlias/Security.lean`, with challenges that have nonzero discrete logarithms, and `Dahlias/OmdlStd.lean`, with uniform challenges.

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

```lean
/-- The discrete logarithms of the first `ℓ` challenges. -/
def chalLogsStd {c : ℕ} (xs : Fin c → ZMod n) (ℓ : ℕ) : List (ZMod n) :=
  (List.range ℓ).map fun i => if h : i < c then xs ⟨i, h⟩ else 0
```

```lean
/-- The game's answers, for challenges with the discrete logarithms `xs`. -/
def omdlChallengerStd {c : ℕ} (xs : Fin c → ZMod n) :
    (q : OmdlQ n) → ℕ × ℕ → OmdlR E q × (ℕ × ℕ)
  | .chal, (ℓ, d) =>
    if h : ℓ < c then (some (C.mulG (xs ⟨ℓ, h⟩)), (ℓ + 1, d)) else (none, (ℓ, d))
  | .dlog a bs, (ℓ, d) =>
    (a + (List.zipWith (· * ·) bs (chalLogsStd xs ℓ)).sum, (ℓ, d + 1))
```

```lean
/-- **The AOMDL game with uniform challenges** on one sample: at most `c`
challenges with the discrete logarithms `xs`, which may be zero. The adversary
wins if it outputs the discrete logarithms of all challenges it received and
made fewer discrete logarithm queries than it received challenges. -/
def omdlExperimentStd (c : ℕ) {Coins : Type} (B : OmdlAdversary n E Coins)
    (ω : (Fin c → ZMod n) × Coins) : Prop :=
  let out := (B ω.2).run (omdlChallengerStd C ω.1) (0, 0)
  out.1 = chalLogsStd ω.1 out.2.1 ∧ out.2.2 < out.2.1
```

```lean
/-- The adversary's probability of winning the AOMDL game with uniform
challenges. -/
noncomputable def omdlAdvantageStd (c : ℕ) {Coins : Type} [Fintype Coins]
    (B : OmdlAdversary n E Coins) : ℝ :=
  prob (omdlExperimentStd C c B)
```

```lean
/-- **Nonzero challenges cost at most `c / n`.** -/
theorem omdlAdvantage_le_std (c : ℕ) (B : OmdlAdversary n E Coins) :
    omdlAdvantage C c B ≤ omdlAdvantageStd C c B + c / n
```

### Unforgeability

`Dahlias/Unforgeability.lean`, `Dahlias/Proofs/Reduction.lean`, `Dahlias/LazyReduction.lean` and `Dahlias/LazyCollider.lean`. Of the reduction and the collision finder only the types are printed.

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
/-- **BIP 459 is unforgeable under AOMDL with uniform challenges.** This is
`unforgeable_sqrt` with the advantage of `reduction A` in the game whose
challenges have uniform discrete logarithms. The `2⋅qs + 1` challenges that
the reduction asks for add `(2⋅qs + 1) / n`. -/
theorem unforgeable_sqrt_std (hN : N < n) (qh : ℕ) (hA : ∀ coins P, HashBound (A coins P) qh) :
    forgeAdvantage C nonceCoef N qs A ≤
      Real.sqrt ((qh + qs + 1 : ℕ) *
        (omdlAdvantageStd C (2 * qs + 1) (reduction C nonceCoef N qs A) + (2 * qs + 1 : ℕ) / n +
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

```lean
/-- The sample of `colliderLazy`: the secret key, the nonces, the forger's
coins and `q` scalars for the answers of the oracle. -/
abbrev LazyColliderSample (n qs q : ℕ) (Coins : Type) :=
  (ZMod n)ˣ × (Fin qs → (ZMod n)ˣ × (ZMod n)ˣ) × Coins × (Fin q → ZMod n)
```

```lean
/-- **The collision finder with a lazily sampled random oracle.** It gets a
sample and the new value at the fork point. -/
noncomputable def colliderLazy (q : ℕ) (p : LazyColliderSample n qs q Coins × ZMod n) :
    (E × E × List (X × M × E)) × (E × E × List (X × M × E)) :=
  ((answerLazy (QTree.stream p.1.2.2.2) 0 []
    (colliderM C nonceCoef N qs A p.1.1 p.1.2.1 p.1.2.2.1 p.2)).run
      (noOmdl (n := n) (E := E)) ()).1
```

```lean
/-- The probability that `colliderLazy A` outputs a collision of the nonce
coefficient hash. -/
noncomputable def collisionAdvantageLazy (q : ℕ) : ℝ :=
  prob fun p : LazyColliderSample n qs q Coins × ZMod n =>
    IsCollision nonceCoef (colliderLazy C nonceCoef N qs A q p)
```

```lean
/-- **BIP 459 is unforgeable under AOMDL, with a reduction and a collision
finder that sample the random oracle lazily.** The statement of
`unforgeable_sqrt` for `reductionLazy` and `colliderLazy`. -/
theorem unforgeable_sqrt_lazy_both (hN : N < n) (qh : ℕ)
    (hA : ∀ coins P, HashBound (A coins P) qh) :
    forgeAdvantage C nonceCoef N qs A ≤
      Real.sqrt ((qh + qs + 1 : ℕ) *
        (omdlAdvantage C (2 * qs + 1) (reductionLazy C nonceCoef N qs A (2 * (qh + qs) + 1)) +
          collisionAdvantageLazy C nonceCoef N qs A (2 * (qh + qs)))) +
        (qh + qs + 1 : ℕ) / n + qs / (n - 1 : ℝ)
```

### The additive term of the bound

`Dahlias/Tightness.lean`. A forger that makes `q` random oracle queries, no signing queries and computes no discrete logarithm.

```lean
/-- The grinder's random oracle query for the message `m`: the challenge of
the list `[(pk, m)]` with `R = pk`. -/
def grindIn (hN : 1 ≤ N) (pk : X) (m : M) : SigIn N X M :=
  (⟨[(pk, m)], by simpa using hN⟩, pk, (pk, m))
```

```lean
/-- The grinder's forgery for the message `m`: the signature `(pk, 0)` for the
list `[(pk, m)]` and the untweaked key. -/
def grindOut (pk : X) (m : M) : Forgery n X M := ⟨[(pk, m)], (0, 1), (pk, 0)⟩
```

```lean
/-- Ask for the challenges of the messages one by one and stop at the first
that is `-1`. -/
def grindAlg (hN : 1 ≤ N) (pk : X) : List M → Alg (AdvQ n N E X M) AdvR (Forgery n X M)
  | [] => .done ⟨[], (0, 1), (pk, 0)⟩
  | m :: ms => .ask (.hash (grindIn N hN pk m)) fun (c : ZMod n) =>
      if c = -1 then .done (grindOut pk m) else grindAlg hN pk ms
```

```lean
/-- A forger that needs no signature and no discrete logarithm. -/
def grinder (ms : List M) : Adversary n N E X M Unit := fun _ P =>
  if hN : 1 ≤ N then grindAlg N hN (C.x P) ms else .done ⟨[], (0, 1), (C.x P, 0)⟩
```

```lean
/-- The grinder makes at most one random oracle query for every message. -/
theorem grinder_hashBound (ms : List M) (u : Unit) (P : E) :
    HashBound (grinder C N ms u P) ms.length
```

```lean
/-- **The additive term is needed.** With `q` different messages the grinder
makes at most `q` random oracle queries and no signing queries, and it forges
with probability at least `1 - ((n - 1) / n)^q`. -/
theorem grinder_advantage (hN : 1 ≤ N) (ms : List M) (hms : ms.Nodup) :
    1 - (((n : ℝ) - 1) / n) ^ ms.length ≤ forgeAdvantage C nonceCoef N qs (grinder C N ms)
```

```lean
/-- **The additive term is needed**, in closed form: the grinder forges with
probability at least `q / (n + q)`. -/
theorem grinder_advantage_ge (hN : 1 ≤ N) (ms : List M) (hms : ms.Nodup) :
    (ms.length : ℝ) / (n + ms.length) ≤ forgeAdvantage C nonceCoef N qs (grinder C N ms)
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
    ((θ.1, fun k => mask θ.1.1 k (v k)), θ.2)
```

```lean
/-- **The unforgeability game with `NonceGen` and its `sk` argument** on one
sample: the `rand` of slot `k` is `mask x k (Aux (rand' k))`. -/
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

### `NonceGen`, 256-bit hashes and 32-byte values together

`Dahlias/NonceGenHashed.lean`, `Dahlias/NonceGenLazy.lean` and `Dahlias/BytesSecurity.lean`. One game has the nonces of `NonceGen` and a challenge hash whose outputs the adversary sees and the signer and the verifier reduce. The forgers `withStream` and `withAuxStream` answer the queries to the hash functions of `NonceGen` from values in their coins.

```lean
/-- The algorithm that gets answers in `R'` and continues as `t` does on their
images under `f`. -/
def mapAns (f : (q : Q) → R' q → R q) : Alg Q R α → Alg Q R' α
  | .done a => .done a
  | .ask q k => .ask q fun r => mapAns f (k (f q r))
```

```lean
/-- `f` on the answers of the game, nothing on the answers of the table. -/
def sumAns (f : (q : Q) → R' q → R q) : (q : Q ⊕ D) → SumR R' W q → SumR R W q
  | .inl q, r => f q r
  | .inr _, w => w
```

```lean
/-- An adversary of the game with `NonceGen` that sees the outputs of the
challenge hash. -/
abbrev NAdversaryH (n N : ℕ) (E X M Rnd Ex W H Coins : Type) :=
  Coins → E → Alg ((AdvQ n N E X M ⊕ Ex) ⊕ (Rnd × Ex × Bool)) (SumR (SumR (AdvRH H) Unit) W)
    (Forgery n X M)
```

```lean
/-- An adversary of the game with `NonceGen` and its `sk` argument that sees
the outputs of the challenge hash. -/
abbrev SkAdversaryH (n N : ℕ) (E X M Rnd Rp Ex W H Coins : Type) :=
  Coins → E → Alg (((AdvQ n N E X M ⊕ Ex) ⊕ (Rnd × Ex × Bool)) ⊕ Rp)
    (SumR (SumR (SumR (AdvRH H) Unit) W) Rnd) (Forgery n X M)
```

```lean
/-- `challengerE` for a table `Tab` of hash outputs: a hash query returns the
output, the signer reduces it with `red`. -/
def challengerEH (nv : Fin qs → Ex → SecNonce n) (x : ZMod n) (Tab : SigIn N X M → H) :
    (q : AdvQ n N E X M ⊕ Ex) → SignerState X M × (ℕ → Ex) →
      SumR (AdvRH H) Unit q × (SignerState X M × (ℕ → Ex))
  | .inl q, s =>
    ((challengerH C nonceCoef N qs red x (fun k => nv k (s.2 k)) Tab q s.1).1,
      ((challengerH C nonceCoef N qs red x (fun k => nv k (s.2 k)) Tab q s.1).2, s.2))
  | .inr e, s => ((), (s.1, update s.2 s.1.opened e))
```

```lean
/-- The part of the sample that the nonces do not depend on: the secret key,
the adversary's coins and the table of hash outputs. -/
abbrev RestH (n N : ℕ) (X M H Coins : Type) := (ZMod n)ˣ × Coins × (SigIn N X M → H)
```

```lean
/-- **The unforgeability game with `NonceGen` and hash outputs in `H`** on one
sample: the nonces of slot `k` are `ρ (G (rand k, extra_in, i))`, and the
verifier reduces the outputs of the challenge hash with `red` as the signer
does. -/
def nonceGenExperimentH (A : NAdversaryH n N E X M Rnd Ex W H Coins) (ρ : W → ZMod n) (e₀ : Ex)
    (ω : (RestH n N X M H Coins × (Fin qs → Rnd)) × (Rnd × Ex × Bool → W)) : Prop :=
  let x : ZMod n := ω.1.1.1
  let Tab := ω.1.1.2.2
  let out := (answerG ω.2 (A ω.1.1.2.1 (C.mulG x))).run
    (challengerEH C nonceCoef N qs red (nvOf qs ρ fun i => ω.2 (noncePt qs ω.1.2 i)) x Tab)
    (⟨0, [], []⟩, fun _ => e₀)
  Wins C nonceCoef N x (fun z => red (Tab z)) out.1 out.2.1
```

```lean
/-- **The unforgeability game with `NonceGen`, its `sk` argument and hash
outputs in `H`** on one sample: the `rand` of slot `k` is
`mask x k (Aux (rand' k))`. -/
def nonceGenSkExperimentH (A : SkAdversaryH n N E X M Rnd Rp Ex W H Coins) (ρ : W → ZMod n)
    (e₀ : Ex) (mask : (ZMod n)ˣ → Fin qs → Rnd ≃ Rnd)
    (ω : ((RestH n N X M H Coins × (Rnd × Ex × Bool → W)) × (Fin qs → Rp)) × (Rp → Rnd)) :
    Prop :=
  nonceGenExperimentH C nonceCoef N qs red (fun c P => answerG ω.2 (A c P)) ρ e₀
    ((ω.1.1.1, fun k => mask ω.1.1.1.1 k (ω.2 (ω.1.2 k))), ω.1.1.2)
```

```lean
/-- The adversary's advantage in the game with `NonceGen` and hash outputs in
`H`. -/
noncomputable def nonceGenAdvantageH [Fintype Coins] [Fintype (SigIn N X M)] [Fintype H]
    [Fintype Rnd] [DecidableEq Rnd] [Fintype Ex] [DecidableEq Ex] [Fintype W]
    (A : NAdversaryH n N E X M Rnd Ex W H Coins) (ρ : W → ZMod n) (e₀ : Ex) : ℝ :=
  prob (nonceGenExperimentH C nonceCoef N qs red A ρ e₀)
```

```lean
/-- The adversary's advantage in the game with `NonceGen`, its `sk` argument
and hash outputs in `H`. -/
noncomputable def nonceGenSkAdvantageH [Fintype Coins] [Fintype (SigIn N X M)] [Fintype H]
    [Fintype Rnd] [Fintype Rp] [DecidableEq Rp] [Fintype Ex] [DecidableEq Ex] [DecidableEq Rnd]
    [Fintype W] (A : SkAdversaryH n N E X M Rnd Rp Ex W H Coins) (ρ : W → ZMod n) (e₀ : Ex)
    (mask : (ZMod n)ˣ → Fin qs → Rnd ≃ Rnd) : ℝ :=
  prob (nonceGenSkExperimentH C nonceCoef N qs red A ρ e₀ mask)
```

```lean
/-- The game's answers with the scalar answer of the challenge hash replaced
by the output `g c`. -/
def hashAns (g : ZMod n → H) : (q : AdvQ n N E X M) → AdvR q → AdvRH H q
  | .hash _, c => g c
  | .openSession, r => r
  | .close .., r => r
  | .single _, r => r
```

```lean
/-- The adversary for the game of `Dahlias.NonceGen`: when the challenge hash
answers `c`, it continues with the output `g c`. -/
def liftHashN (g : ZMod n → H) (A : NAdversaryH n N E X M Rnd Ex W H Coins) :
    NAdversary n N E X M Rnd Ex W Coins :=
  fun c P => mapAns (sumAns (sumAns (hashAns N g))) (A c P)
```

```lean
/-- The adversary for the game of `Dahlias.NonceGenSk`: when the challenge
hash answers `c`, it continues with the output `g c`. -/
def liftHashSk (g : ZMod n → H) (A : SkAdversaryH n N E X M Rnd Rp Ex W H Coins) :
    SkAdversary n N E X M Rnd Rp Ex W Coins :=
  fun c P => mapAns (sumAns (sumAns (sumAns (hashAns N g)))) (A c P)
```

```lean
/-- Answer the queries of `G` lazily from the stream `v`. -/
def answerLazy (v : ℕ → W) : ℕ → List (D × W) → Alg (Q ⊕ D) (SumR R W) α → Alg Q R α
  | _, _, .done a => .done a
  | k, μ, .ask (.inl q) f => .ask q fun r => answerLazy v k μ (f r)
  | k, μ, .ask (.inr z) f =>
    match memo μ z with
    | some s => answerLazy v k μ (f s)
    | none => answerLazy v (k + 1) (μ ++ [(z, v k)]) (f (v k))
```

```lean
/-- The adversary for the game with uniform nonces that answers the queries
to `hash_BIP0459/nonce` lazily, from `q` values in its coins, and drops the
`extra_in`. -/
def withStream [DecidableEq Rnd] [DecidableEq Ex] [Inhabited W] (q : ℕ)
    (A : NAdversary n N E X M Rnd Ex W Coins) : Adversary n N E X M (Coins × (Fin q → W)) :=
  fun c P => answerG (fun _ : Ex => ()) (answerLazy (stream c.2) 0 [] (A c.1 P))
```

```lean
/-- The adversary for the game of `Dahlias.NonceGen` that answers the queries
to `hash_BIP0459/aux` lazily, from `q` values in its coins. -/
def withAuxStream [DecidableEq Rp] [Inhabited Rnd] (q : ℕ)
    (A : SkAdversary n N E X M Rnd Rp Ex W Coins) :
    NAdversary n N E X M Rnd Ex W (Coins × (Fin q → Rnd)) :=
  fun c P => answerLazy (stream c.2) 0 [] (A c.1 P)
```

```lean
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
        (2 * qs : ℕ) * ((m - (n - 1) : ℝ) / m)
```

```lean
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
        (qs : ℝ) ^ 2 / Fintype.card Rp + qs * (qa / Fintype.card Rp)
```

```lean
/-- There are `2²⁵⁶` 32-byte arrays. -/
theorem card_B32 : Fintype.card B32 = 2 ^ 256
```

```lean
/-- **BIP 459 with 32-byte keys and messages, `NonceGen` and 256-bit hashes is
unforgeable under AOMDL.** The nonces come from `NonceGen` with its `sk`
argument, for 32-byte values `rand'` and `rand` and any family of bijections
`mask`, such as `maskXor d` for the secret key `d` that `NonceGen` gets in the
slot: the signer's key or a key tweaked from it by a tweak that is fixed
before the game. `hash_BIP0459/sig`, `hash_BIP0459/nonce` and
`hash_BIP0459/aux` are random oracles. The first two have 256-bit outputs
that are reduced modulo `n`. The nonce coefficient hash is the BIP's.

The adversary makes at most `qh`, `qn` and `qa` queries to the three oracles
and opens at most `qs` sessions. `extra_in` is a value of any finite type
`Ex`. The forger `withStream (withAuxStream …)`, the reduction and the
collision finder sample all random oracles lazily. -/
theorem bytes_nonceGenSk_unforgeable_256 {Coins Ex : Type} [Fintype Coins] [Fintype Ex]
    [DecidableEq Ex] (N qs : ℕ)
    (A : SkAdversaryH n N Point B32 B32 B32 B32 Ex (Fin (2 ^ 256)) (Fin (2 ^ 256)) Coins)
    (e₀ : Ex) (mask : (ZMod n)ˣ → Fin qs → B32 ≃ B32) (hN : N < n) (qh qn qa : ℕ)
    (hA : ∀ c P, NBound (A c P) qa)
    (hG : ∀ c P (Aux : B32 → B32), NBound (answerG Aux (A c P)) qn)
    (hH : ∀ c P G (Aux : B32 → B32),
      HashBound (answerG (fun _ : Ex => ()) (answerG G (answerG Aux (A c P)))) qh) :
    nonceGenSkAdvantageH secp256k1X nonceCoef32 N qs (redFin (2 ^ 256)) A (redFin (2 ^ 256)) e₀
        mask ≤
      Real.sqrt ((qh + qs + 1 : ℕ) *
        (omdlAdvantage secp256k1X (2 * qs + 1)
            (reductionLazy secp256k1X nonceCoef32 N qs
              (withStream N qn (withAuxStream N qa (liftHashSk N (liftFin n_lt.le) A)))
              (2 * (qh + qs) + 1)) +
          collisionAdvantageLazy secp256k1X nonceCoef32 N qs
            (withStream N qn (withAuxStream N qa (liftHashSk N (liftFin n_lt.le) A)))
            (2 * (qh + qs)))) +
        (qh + qs + 1 : ℕ) / n + qs / (n - 1 : ℝ) +
        (qh + qs + N : ℕ) * ((((2 ^ 256 : ℕ) : ℝ) - n) / ((2 ^ 256 : ℕ) : ℝ)) +
        (qs : ℝ) ^ 2 / ((2 ^ 256 : ℕ) : ℝ) + qs * (qn / ((2 ^ 256 : ℕ) : ℝ)) +
        (2 * qs : ℕ) * ((((2 ^ 256 : ℕ) : ℝ) - (n - 1)) / ((2 ^ 256 : ℕ) : ℝ)) +
        (qs : ℝ) ^ 2 / ((2 ^ 256 : ℕ) : ℝ) + qs * (qa / ((2 ^ 256 : ℕ) : ℝ))
```

```lean
/-- **BIP 459 with 32-byte keys and messages, `NonceGen` without its `sk`
argument and 256-bit hashes is unforgeable under AOMDL.** The `rand` of
`NonceGen` is a uniform 32-byte value. `hash_BIP0459/sig` and
`hash_BIP0459/nonce` are random oracles with 256-bit outputs that are reduced
modulo `n`. The nonce coefficient hash is the BIP's. The forger `withStream`,
the reduction and the collision finder sample the random oracles lazily. -/
theorem bytes_nonceGen_unforgeable_256 {Coins Ex : Type} [Fintype Coins] [Fintype Ex]
    [DecidableEq Ex] (N qs : ℕ)
    (A : NAdversaryH n N Point B32 B32 B32 Ex (Fin (2 ^ 256)) (Fin (2 ^ 256)) Coins) (e₀ : Ex)
    (hN : N < n) (qh qn : ℕ) (hA : ∀ c P, NBound (A c P) qn)
    (hH : ∀ c P G, HashBound (answerG (fun _ : Ex => ()) (answerG G (A c P))) qh) :
    nonceGenAdvantageH secp256k1X nonceCoef32 N qs (redFin (2 ^ 256)) A (redFin (2 ^ 256)) e₀ ≤
      Real.sqrt ((qh + qs + 1 : ℕ) *
        (omdlAdvantage secp256k1X (2 * qs + 1)
            (reductionLazy secp256k1X nonceCoef32 N qs
              (withStream N qn (liftHashN N (liftFin n_lt.le) A)) (2 * (qh + qs) + 1)) +
          collisionAdvantageLazy secp256k1X nonceCoef32 N qs
            (withStream N qn (liftHashN N (liftFin n_lt.le) A)) (2 * (qh + qs)))) +
        (qh + qs + 1 : ℕ) / n + qs / (n - 1 : ℝ) +
        (qh + qs + N : ℕ) * ((((2 ^ 256 : ℕ) : ℝ) - n) / ((2 ^ 256 : ℕ) : ℝ)) +
        (qs : ℝ) ^ 2 / ((2 ^ 256 : ℕ) : ℝ) + qs * (qn / ((2 ^ 256 : ℕ) : ℝ)) +
        (2 * qs : ℕ) * ((((2 ^ 256 : ℕ) : ℝ) - (n - 1)) / ((2 ^ 256 : ℕ) : ℝ))
```

### `NonceGen` with a counter in place of `rand'`

`Dahlias/NonceGenCounter.lean` and `Dahlias/BytesSecurity.lean`. The signer runs `NonceGen` with its secret key and a public counter value, and no random value. The bound is for two forgers: the adversary, and `keyForger`, which recovers the secret key when the adversary queries the nonce hash at a `rand`.

```lean
/-- An algorithm without table queries. -/
def liftQ : Alg Q R α → Alg (Q ⊕ D) (SumR R W) α
  | .done a => .done a
  | .ask q f => .ask (.inl q) fun r => liftQ (f r)
```

```lean
/-- The algorithm that also returns a tally of its queries and their
answers. -/
def tally (upd : (q : Q) → R q → σ → σ) : Alg Q R α → σ → Alg Q R (α × σ)
  | .done a, o => .done (a, o)
  | .ask q f, o => .ask q fun r => tally upd (f r) (upd q r o)
```

```lean
/-- A tally that leaves the queries of the table out. -/
def liftUpd (upd : (q : Q) → R q → σ → σ) : (q : Q ⊕ D) → SumR R W q → σ → σ
  | .inl q, r, o => upd q r o
  | .inr _, _, o => o
```

```lean
/-- Query the table at the points `pt k` for the `k` of a list, and return
every `k` with the answer. -/
def askList {ι : Type} (pt : ι → D) : List ι → Alg (Q ⊕ D) (SumR R W) (List (ι × W))
  | [] => .done []
  | k :: l => .ask (.inr (pt k)) fun a => askList pt l >>= fun as => .done ((k, a) :: as)
```

```lean
/-- What a successful signing query adds to the signer's record: the list of
a session, or the items of a single-party signature. -/
abbrev SignedQ (n : ℕ) (X M : Type) := List (X × M) ⊕ List (Tweak n × M)
```

```lean
/-- The successful signing queries, from a query and its answer. -/
def trackOf : (q : AdvQ n N E X M) → AdvR q → List (SignedQ n X M) → List (SignedQ n X M)
  | .hash _, _, tr => tr
  | .openSession, _, tr => tr
  | .close _ _ _ _ pm _, r, tr => if r.isSome then .inl pm :: tr else tr
  | .single items, r, tr => if r.isSome then .inr items :: tr else tr
```

```lean
/-- The list of public keys and messages of a successful signing query. -/
def signedList (x : ZMod n) : SignedQ n X M → List (X × M)
  | .inl pm => pm
  | .inr items => singleKeys C x items
```

```lean
/-- The tally of a forger: its queries to the nonce hash and its successful
signing queries. -/
def obsUpd {D₁ W₁ : Type} : (q : (AdvQ n N E X M ⊕ Ex) ⊕ D₁) → SumR (SumR AdvR Unit) W₁ q →
    List D₁ × List (SignedQ n X M) → List D₁ × List (SignedQ n X M)
  | .inl (.inl q), r, o => (o.1, trackOf N q r o.2)
  | .inl (.inr _), _, o => o
  | .inr z, _, o => (z :: o.1, o.2)
```

```lean
/-- The secret key, from the queries to the nonce hash and the values of the
aux hash at the counters: the first candidate that matches the public key. -/
def findKey (P : E) (log : List (Rnd × Ex × Bool)) (as : List (Fin qs × Rnd)) :
    Option (ZMod n)ˣ :=
  (log.product as).findSome? fun za =>
    (unmask za.2.1 za.1.1 za.2.2).filter fun x' : (ZMod n)ˣ => decide (C.mulG (x' : ZMod n) = P)
```

```lean
/-- A forgery by the holder of the secret key `x'`: a signature with the nonce
`1` for the key itself and the first of the messages `msgs` whose list the
signer has not signed. -/
def forgeTail (x' : ZMod n) (tr : List (SignedQ n X M)) (fallback : Forgery n X M) :
    Alg (AdvQ n N E X M) AdvR (Forgery n X M) :=
  match (List.finRange (qs + 1)).find? fun j =>
      decide ([(C.x (C.mulG x'), msgs j)] ∉ tr.map (signedList C x')) with
  | none => .done fallback
  | some j =>
    if hN : [(C.x (C.mulG x'), msgs j)].length ≤ N then
      .ask (.hash (⟨[(C.x (C.mulG x'), msgs j)], hN⟩, C.x (C.mulG 1),
        (C.x (C.mulG x'), msgs j))) fun (c : ZMod n) =>
          .done ⟨[(C.x (C.mulG x'), msgs j)], (0, 1), (C.x (C.mulG 1),
            (if C.hasEvenY (C.mulG 1) then 1 else -1) + (c * C.ops.evenScalar x' + 0))⟩
    else .done fallback
```

```lean
/-- **The forger from a query at a secret point.** It runs `A` and keeps a
tally of the queries to the nonce hash and of the successful signing queries.
Then it reads the aux hash at the counters and looks for the secret key among
the candidates that the queries to the nonce hash give. With the key it signs
a new message. -/
def keyForger (A : SkAdversary n N E X M Rnd Rp Ex W Coins) :
    SkAdversary n N E X M Rnd Rp Ex W Coins := fun c P =>
  tally (liftUpd (obsUpd N)) (A c P) ([], []) >>= fun out =>
    askList ctr (List.finRange qs) >>= fun as =>
      match findKey C qs unmask P out.2.1 as with
      | none => .done out.1
      | some x' => liftQ (liftQ (liftQ (forgeTail C N qs msgs (x' : ZMod n) out.2.2 out.1)))
```

```lean
/-- **The unforgeability game with `NonceGen`, its `sk` argument and a counter
in place of `rand'`** on one sample: the `rand` of slot `k` is
`mask x k (Aux (ctr k))`. The counter values `ctr k` are public. The game is the
one of `Dahlias.NonceGenSk` with them in place of the uniform values
`rand'`. -/
def nonceGenCtrExperiment
    (ω : (Rest n N X M Coins × (Rnd × Ex × Bool → W)) × (Rp → Rnd)) : Prop :=
  winSk C nonceCoef N qs A ρ e₀ mask ω.1 ω.2 fun k => ω.2 (ctr k)
```

```lean
/-- The adversary's advantage in the game with a counter. -/
noncomputable def nonceGenCtrAdvantage : ℝ :=
  prob (nonceGenCtrExperiment C nonceCoef N qs ctr mask e₀ A ρ)
```

```lean
/-- **`NonceGen` with a counter in place of `rand'`.** The counter values are
distinct, the secret key can be read off a `rand` and the value of the aux
hash (`unmask`), and there are `qs + 1` messages. Then an adversary wins the
game at most as often as it and the forger `keyForger A` together win the game
with uniform nonces, plus the terms for two equal values of the aux hash and
for the reduction modulo the group order.

The nonces are fresh values of the nonce hash unless the adversary queries it
at a `rand`, and a `rand` gives the secret key. -/
theorem nonceGenCtr_advantage (hctr : Injective ctr)
    (hunmask : ∀ x k a, unmask k (mask x k a) a = some x) (hmsgs : Injective msgs) (hN : 0 < N)
    (g : (ZMod n)ˣ → W) (hg : Injective g) (hρ : ∀ u, ρ (g u) = u) :
    nonceGenCtrAdvantage C nonceCoef N qs ctr mask e₀ A ρ ≤
      forgeAdvantage C nonceCoef N qs (withTable N (withAux N A)) +
        forgeAdvantage C nonceCoef N qs
          (withTable N (withAux N (keyForger C N qs unmask msgs ctr A))) +
        (qs : ℝ) ^ 2 / Fintype.card Rnd +
        2 * ((2 * qs : ℕ) * ((Fintype.card W - Fintype.card (ZMod n)ˣ : ℝ) / Fintype.card W))
```

```lean
/-- The bound of `unforgeable_sqrt_lazy_both` on the advantage of a forger
that makes at most `qh` hash queries: the term with `reductionLazy` and
`colliderLazy` and the two additive terms. -/
noncomputable def lazyBound {Coins' : Type} [Fintype Coins'] (qh : ℕ)
    (F : Adversary n N E X M Coins') : ℝ :=
  Real.sqrt ((qh + qs + 1 : ℕ) *
      (omdlAdvantage C (2 * qs + 1) (reductionLazy C nonceCoef N qs F (2 * (qh + qs) + 1)) +
        collisionAdvantageLazy C nonceCoef N qs F (2 * (qh + qs)))) +
    (qh + qs + 1 : ℕ) / n + qs / (n - 1 : ℝ)
```

```lean
/-- **The unforgeability game with `NonceGen`, its `sk` argument, a counter in
place of `rand'` and hash outputs in `H`** on one sample. -/
def nonceGenCtrExperimentH
    (ω : (RestH n N X M H Coins × (Rnd × Ex × Bool → W)) × (Rp → Rnd)) : Prop :=
  nonceGenExperimentH C nonceCoef N qs red (fun c P => answerG ω.2 (AH c P)) ρ e₀
    ((ω.1.1, fun k => mask ω.1.1.1 k (ω.2 (ctr k))), ω.1.2)
```

```lean
/-- The adversary's advantage in the game with a counter and hash outputs in
`H`. -/
noncomputable def nonceGenCtrAdvantageH : ℝ :=
  prob (nonceGenCtrExperimentH C nonceCoef N qs ctr mask e₀ ρ red AH)
```

```lean
/-- **BIP 459's `NonceGen` with its `sk` argument, a counter in place of
`rand'`, and the challenge hash**: `m`-valued random oracles reduced modulo
`n`, for `m = 2²⁵⁶`. -/
theorem nonceGenCtr_unforgeable_fin [Inhabited Rnd] {m : ℕ} [NeZero m] (hm : n ≤ m)
    (AH : SkAdversaryH n N E X M Rnd Rp Ex (Fin m) (Fin m) Coins) (hctr : Injective ctr)
    (hunmask : ∀ x k a, unmask k (mask x k a) a = some x) (hmsgs : Injective msgs) (hN0 : 0 < N)
    (hN : N < n) (qh qn qa : ℕ) (hA : ∀ c P, NBound (AH c P) qa)
    (hG : ∀ c P (Aux : Rp → Rnd), NBound (answerG Aux (AH c P)) qn)
    (hH : ∀ c P G (Aux : Rp → Rnd),
      HashBound (answerG (fun _ : Ex => ()) (answerG G (answerG Aux (AH c P)))) qh) :
    nonceGenCtrAdvantageH C nonceCoef N qs ctr mask e₀ (redFin m) (redFin m) AH ≤
      lazyBound C nonceCoef N qs qh
          (withStream N qn (withAuxStream N qa (liftHashSk N (liftFin hm) AH))) +
        lazyBound C nonceCoef N qs (qh + 1)
          (withStream N qn (withAuxStream N (qa + qs)
            (keyForger C N qs unmask msgs ctr (liftHashSk N (liftFin hm) AH)))) +
        (qh + qs + N : ℕ) * ((m - n : ℝ) / m) +
        (qs : ℝ) ^ 2 / Fintype.card Rnd +
        2 * ((2 * qs : ℕ) * ((m - (n - 1) : ℝ) / m))
```

```lean
/-- The byte-wise xor of two 32-byte arrays. -/
def xor32 (a b : B32) : B32 :=
  ⟨List.zipWith (· ^^^ ·) a.1 b.1, by rw [List.length_zipWith, a.2, b.2, min_self]⟩
```

```lean
/-- `bytes(x)` as a 32-byte array. -/
def ser32 (x : ZMod n) : B32 := ⟨serScalar x, length_bytes32 _⟩
```

```lean
/-- **The `rand` of `NonceGen` with the secret key `d` as its `sk` argument**:
`bytes(d) xor hash_BIP0459/aux(rand')`, as a bijection on the values of the
aux hash. -/
def maskXor (d : ZMod n) : B32 ≃ B32 where
  toFun a := xor32 (ser32 d) a
  invFun a := xor32 (ser32 d) a
  left_inv a := Subtype.ext (zipXor_cancel_left _ _ ((ser32 d).2.trans a.2.symm))
  right_inv a := Subtype.ext (zipXor_cancel_left _ _ ((ser32 d).2.trans a.2.symm))
```

```lean
/-- The signer's secret key from a `rand` and the value of the aux hash, when
`NonceGen` got the key with the tweak `τ`. -/
def unmaskXor (τ : Tweak n) (r a : B32) : Option (ZMod n)ˣ :=
  (scalar (xor32 r a).1).bind fun d =>
    if h : (d - τ.1) / τ.2 = 0 then none else some (Units.mk0 ((d - τ.1) / τ.2) h)
```

```lean
/-- A `rand` and the value of the aux hash give the secret key. -/
theorem unmaskXor_maskXor (τ : Tweak n) (hτ : τ.2 ≠ 0) (x : (ZMod n)ˣ) (a : B32) :
    unmaskXor τ (maskXor (τ.sk x) a) a = some x
```

```lean
/-- **BIP 459 with 32-byte keys and messages, 256-bit hashes and `NonceGen`
with a counter in place of `rand'` is unforgeable under AOMDL.** For slot `k`
the signer runs `NonceGen` with the secret key `d = (τ k).sk x` and the public
32-byte value `ctr k` in place of a random value, as
`secp256k1_fullagg_nonce_gen_counter` does. The values `ctr k` are distinct.
The tweaks `τ k` are fixed before the game and have a nonzero factor, as the
tweaks of BIP 459 have. With `τ k = (0, 1)` the key is the signer's key `x`.
`rand` is `bytes(d) xor hash_BIP0459/aux(ctr k)`. `hash_BIP0459/sig`,
`hash_BIP0459/nonce` and `hash_BIP0459/aux` are random oracles, the first two
with 256-bit outputs that are reduced modulo `n`. The nonce coefficient hash
is the BIP's.

The bound has the terms of `unforgeable_sqrt_lazy_both` twice: for the
adversary, and for the forger `keyForger`, which finds the secret key when the
adversary queries the nonce hash at a `rand`. `msgs` are any `qs + 1` distinct
messages. -/
theorem bytes_nonceGenCtr_unforgeable_256 {Coins Ex : Type} [Fintype Coins] [Fintype Ex]
    [DecidableEq Ex] (N qs : ℕ)
    (A : SkAdversaryH n N Point B32 B32 B32 B32 Ex (Fin (2 ^ 256)) (Fin (2 ^ 256)) Coins)
    (e₀ : Ex) (ctr : Fin qs → B32) (hctr : Function.Injective ctr) (τ : Fin qs → Tweak n)
    (hτ : ∀ k, (τ k).2 ≠ 0) (msgs : Fin (qs + 1) → B32) (hmsgs : Function.Injective msgs)
    (hN0 : 0 < N) (hN : N < n) (qh qn qa : ℕ)
    (hA : ∀ c P, NBound (A c P) qa)
    (hG : ∀ c P (Aux : B32 → B32), NBound (answerG Aux (A c P)) qn)
    (hH : ∀ c P G (Aux : B32 → B32),
      HashBound (answerG (fun _ : Ex => ()) (answerG G (answerG Aux (A c P)))) qh) :
    nonceGenCtrAdvantageH secp256k1X nonceCoef32 N qs ctr (fun x k => maskXor ((τ k).sk x)) e₀
        (redFin (2 ^ 256)) (redFin (2 ^ 256)) A ≤
      lazyBound secp256k1X nonceCoef32 N qs qh
          (withStream N qn (withAuxStream N qa (liftHashSk N (liftFin n_lt.le) A))) +
        lazyBound secp256k1X nonceCoef32 N qs (qh + 1)
          (withStream N qn (withAuxStream N (qa + qs)
            (keyForger secp256k1X N qs (fun k => unmaskXor (τ k)) msgs ctr
              (liftHashSk N (liftFin n_lt.le) A)))) +
        (qh + qs + N : ℕ) * ((((2 ^ 256 : ℕ) : ℝ) - n) / ((2 ^ 256 : ℕ) : ℝ)) +
        (qs : ℝ) ^ 2 / ((2 ^ 256 : ℕ) : ℝ) +
        2 * ((2 * qs : ℕ) * ((((2 ^ 256 : ℕ) : ℝ) - (n - 1)) / ((2 ^ 256 : ℕ) : ℝ)))
```

### Binding

`Dahlias/Binding.lean`, and `Dahlias/BindingHashed.lean` for the oracle with hash outputs.

```lean
/-- A deterministic algorithm with adaptive queries to a function `D → S`. -/
abbrev QTree (D S α : Type) := Alg D (fun _ => S) α
```

```lean
/-- The output on the function `T`. -/
def eval (T : D → S) : QTree D S α → α
  | .done a => a
  | .ask d f => eval T (f (T d))
```

```lean
/-- The fresh queries on the function `T`, appended to the points `l` that
count as queried already. -/
def flog (T : D → S) : List D → QTree D S α → List D
  | l, .done _ => l
  | l, .ask d f => flog T (if d ∈ l then l else l ++ [d]) (f (T d))
```

```lean
/-- The points queried on the function `T`, in order, each once. -/
def fresh (T : D → S) (t : QTree D S α) : List D := flog T [] t
```

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

```lean
/-- A binding adversary whose oracle answers with hash outputs in `H`. -/
abbrev BindAdversaryH (n N : ℕ) (X M H Coins : Type) :=
  Coins → QTree (SigIn N X M) H (List (X × M) × List (X × M) × (X × ZMod n))
```

```lean
/-- **The strong binding game with hash outputs** on one sample. The oracle is
a table of hash outputs, which the adversary sees, and `Verify` reduces them
to scalars with `red`. -/
def bindExperimentH {Coins : Type} (A : BindAdversaryH n N X M H Coins)
    (ω : Coins × (SigIn N X M → H)) : Prop :=
  (eval ω.2 (A ω.1)).1 ≠ (eval ω.2 (A ω.1)).2.1 ∧
    (eval ω.2 (A ω.1)).1.length ≤ N ∧ (eval ω.2 (A ω.1)).2.1.length ≤ N ∧
    verify C.ops (hashesOf N nonceCoef fun z => red (ω.2 z)) (eval ω.2 (A ω.1)).1
      (eval ω.2 (A ω.1)).2.2 = true ∧
    verify C.ops (hashesOf N nonceCoef fun z => red (ω.2 z)) (eval ω.2 (A ω.1)).2.1
      (eval ω.2 (A ω.1)).2.2 = true
```

```lean
/-- **Strong binding with BIP 459's challenge hash**: an `m`-valued random
oracle reduced modulo `n`, for `m = 2²⁵⁶`. A signature is valid for two
different lists with probability at most the bound of `strongly_binding` plus
`(qh + 2⋅N) ⋅ (m - n) / m`. -/
theorem strongly_binding_fin {m : ℕ} (hm : n ≤ m) (A : BindAdversaryH n N X M (Fin m) Coins)
    (hE : Curve.PrimeOrder n E) (hN : N < n) (qh : ℕ)
    (hA : ∀ coins (Tab : SigIn N X M → Fin m), (fresh Tab (A coins)).length ≤ qh) :
    prob (bindExperimentH C nonceCoef N (redFin m) A) ≤
      ((qh + 2 * N : ℕ) : ℝ) ^ 2 / n + (qh + 2 * N : ℕ) * ((m - n : ℝ) / m)
```

```lean
/-- **BIP 459 with 32-byte keys and messages is strongly binding**, with the
challenge hash as a 256-bit random oracle reduced modulo `n`. -/
theorem bytes_strongly_binding_256 {Coins : Type} [Fintype Coins] (N : ℕ)
    (A : BindAdversaryH n N B32 B32 (Fin (2 ^ 256)) Coins) (hN : N < n) (qh : ℕ)
    (hA : ∀ coins Tab, (QTree.fresh Tab (A coins)).length ≤ qh) :
    prob (bindExperimentH secp256k1X nonceCoef32 N (redFin (2 ^ 256)) A) ≤
      ((qh + 2 * N : ℕ) : ℝ) ^ 2 / n +
        (qh + 2 * N : ℕ) * ((((2 ^ 256 : ℕ) : ℝ) - n) / ((2 ^ 256 : ℕ) : ℝ))
```

### Finding a disruptive signer

`Dahlias/Correctness.lean` and `Dahlias/Blame.lean`. The statements hold for every choice of the hash functions.

```lean
/-- **A partial signature made by `Sign` passes `PartialSigVerify`**, at the
index `j` that holds the signer's public nonce, when the aggregate nonce is
the one `NonceAgg` computes. -/
theorem partialSigVerify_sign {r₁ r₂ sk : ZMod n} {m : M} {agg : PubNonce E}
    {pm : List (X × M)} {pubnonces : List (PubNonce E)} {s : ZMod n} {j : ℕ}
    (hagg : nonceAgg pubnonces = some agg)
    (hj : pubnonces[j]? = some (C.mulG r₁, C.mulG r₂))
    (hs : sign C.ops H (r₁, r₂) sk m agg pm pubnonces = some s) :
    partialSigVerify C.ops H s pm pubnonces j = true
```

```lean
/-- **Partial signatures that verify aggregate to a valid signature.** If
`PartialSigVerify` accepts the partial signature of every signer, then
`SigAgg`, called with the aggregate nonce from `NonceAgg`, returns a signature
that `Verify` accepts. -/
theorem verify_sigAgg_of_partialSigVerify {pm : List (X × M)} {pubnonces : List (PubNonce E)}
    {psigs : List (ZMod n)} {agg : PubNonce E} {sig : X × ZMod n}
    (hagg : nonceAgg pubnonces = some agg)
    (hsig : sigAgg C.ops H agg pm pubnonces psigs = some sig)
    (hpart : ∀ (i : ℕ) (hi : i < psigs.length),
      partialSigVerify C.ops H psigs[i] pm pubnonces i = true) :
    verify C.ops H pm sig = true
```

```lean
/-- **The honest partial signature is the only one that passes.** At the
index that holds an honest signer's public nonce, `PartialSigVerify` accepts
`s'` iff `s'` is the partial signature that `Sign` returns. -/
theorem partialSigVerify_iff_eq_sign {r₁ r₂ sk : ZMod n} {m : M} {agg : PubNonce E}
    {pm : List (X × M)} {pubnonces : List (PubNonce E)} {s : ZMod n} {j : ℕ}
    (hagg : nonceAgg pubnonces = some agg)
    (hj : pubnonces[j]? = some (C.mulG r₁, C.mulG r₂))
    (hs : sign C.ops H (r₁, r₂) sk m agg pm pubnonces = some s) (s' : ZMod n) :
    partialSigVerify C.ops H s' pm pubnonces j = true ↔ s' = s
```

```lean
/-- **An invalid aggregate signature has a partial signature that fails.** If
the signature that `SigAgg` returns, called with the aggregate nonce from
`NonceAgg`, does not pass `Verify`, then `PartialSigVerify` rejects the
partial signature of at least one signer. -/
theorem exists_partialSigVerify_eq_false {pm : List (X × M)} {pubnonces : List (PubNonce E)}
    {psigs : List (ZMod n)} {agg : PubNonce E} {sig : X × ZMod n}
    (hagg : nonceAgg pubnonces = some agg)
    (hsig : sigAgg C.ops H agg pm pubnonces psigs = some sig)
    (hver : verify C.ops H pm sig = false) :
    ∃ (i : ℕ) (hi : i < psigs.length),
      partialSigVerify C.ops H psigs[i] pm pubnonces i = false
```

```lean
/-- **One bad partial signature among good ones makes the aggregate signature
invalid.** If `PartialSigVerify` rejects the partial signature of signer `i`
and accepts those of all other signers, the signature from `SigAgg` does not
pass `Verify`. -/
theorem verify_eq_false_of_one_bad {pm : List (X × M)} {pubnonces : List (PubNonce E)}
    {psigs : List (ZMod n)} {agg : PubNonce E} {sig : X × ZMod n} {i : ℕ}
    (hagg : nonceAgg pubnonces = some agg)
    (hsig : sigAgg C.ops H agg pm pubnonces psigs = some sig) (hi : i < psigs.length)
    (hbad : partialSigVerify C.ops H psigs[i] pm pubnonces i = false)
    (hothers : ∀ (k : ℕ) (hk : k < psigs.length), k ≠ i →
      partialSigVerify C.ops H psigs[k] pm pubnonces k = true) :
    verify C.ops H pm sig = false
```

### The bytes

`Dahlias/Bytes.lean` and `Dahlias/Encoding.lean`. `Sign` and `Verify` on bytes parse their inputs and call the model. `NonceGen` on bytes derives the nonces as the games do.

```lean
/-- The secp256k1 operations of BIP 459, on 32-byte x-coordinates. -/
def specOps : Ops n Point Bytes where
  mulG := secp256k1F.mulG
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
/-- `NonceGen` with the random value `rand'` as an argument, returning
`(secnonce, pubnonce)`. It fails unless `rand'` and `sk`, if present, are 32
bytes. -/
def nonceGen (rand' : Bytes) (sk : Option Bytes) (extraIn : Bytes) : Option (Bytes × Bytes) :=
  if is32 rand' && sk.all is32 then
    let rand := match sk with
      | some sk => List.zipWith (· ^^^ ·) sk (taggedHash "BIP0459/aux" rand')
      | none => rand'
    let r (i : UInt8) := scalarWrap (taggedHash "BIP0459/nonce" (rand ++ extraIn ++ [i]))
    (Dahlias.nonceGen O (r 0) (r 1)).map fun (sec, pub) =>
      (serScalar sec.1 ++ serScalar sec.2, serNonce pub)
  else none
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
/-- A list of 32-byte pairs as a list of byte array pairs. -/
def vals (L : List (B32 × B32)) : List (Bytes × Bytes) := L.map fun e => (e.1.1, e.2.1)
```

```lean
/-- Hash functions on 32-byte arrays that agree with hash functions on byte
arrays. -/
def Agree (H : Hashes n Point B32 B32) (Hb : Hashes n Point Bytes Bytes) : Prop :=
  (∀ R₁ R₂ items, H.nonceCoef R₁ R₂ items =
      Hb.nonceCoef R₁ R₂ (items.map fun t => (t.1.1, t.2.1.1, t.2.2))) ∧
    ∀ L r e, H.sig L r e = Hb.sig (vals L) r.1 (e.1.1, e.2.1)
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
messages. -/
def Items32 (items : List (Bytes × Bytes × Point)) : Prop :=
  ∀ it ∈ items, it.1.length = 32 ∧ it.2.1.length = 32
```

```lean
/-- **The input of `hash_BIP0459/noncecoef` determines `(R₁, R₂)` and the
`(pkᵢ, mᵢ, R₂,ᵢ)`**, for 32-byte public keys and messages. The points may be
the point at infinity: `GetSessionValues` hashes no such input, but the game
does for the nonce of a single-party signature. -/
theorem nonceCoefInput_injective {R₁ R₂ R₁' R₂' : Point}
    {items items' : List (Bytes × Bytes × Point)} (h : Items32 items) (h' : Items32 items')
    (heq : nonceCoefInput R₁ R₂ items = nonceCoefInput R₁' R₂' items') :
    R₁ = R₁' ∧ R₂ = R₂' ∧ items = items'
```

```lean
/-- The bytes that `hash_BIP0459/noncecoef` hashes for an input of
`nonceCoef32`. -/
def nonceCoefBytes (z : Point × Point × List (B32 × B32 × Point)) : Bytes :=
  nonceCoefInput z.1 z.2.1 (z.2.2.map fun t => (t.1.1, t.2.1.1, t.2.2))
```

```lean
/-- **A collision of the nonce coefficient hash is a collision of SHA-256
modulo `n`.** The two inputs are hashed as two different byte strings, and
the tagged hashes of the two strings, read as numbers, are congruent modulo
`n`. So `collisionAdvantage` for `nonceCoef32` is the probability that
`collider` finds such a pair of strings. -/
theorem collision_bytes
    {p : (Point × Point × List (B32 × B32 × Point)) × (Point × Point × List (B32 × B32 × Point))}
    (h : IsCollision nonceCoef32 p) :
    nonceCoefBytes p.1 ≠ nonceCoefBytes p.2 ∧
      toNatBE (taggedHash "BIP0459/noncecoef" (nonceCoefBytes p.1)) % n =
        toNatBE (taggedHash "BIP0459/noncecoef" (nonceCoefBytes p.2)) % n
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

```lean
/-- **SHA-256 has 32 bytes of output.** -/
theorem length_sha256 (msg : Bytes) : (sha256 msg).length = 32
```

```lean
/-- A 32-byte array as a 256-bit value. -/
def int256 (b : Bytes) (h : b.length = 32) : Fin (2 ^ 256) :=
  ⟨toNatBE b, by
    have := toNatBE_lt b
    rw [h] at this
    exact lt_of_lt_of_eq this (by norm_num)⟩
```

```lean
/-- `hash_BIP0459/sig` with its 256-bit output. -/
def sigHash256 (pm : List (Bytes × Bytes)) (r : Bytes) (pkm : Bytes × Bytes) : Fin (2 ^ 256) :=
  int256 (taggedHash "BIP0459/sig" (sigInput pm r pkm)) (length_taggedHash _ _)
```

```lean
/-- **The challenge hash of BIP 459 is a 256-bit hash output reduced modulo
`n`**: the form `red ∘ Tab` that the games with hash outputs have, with
`red = redFin (2^256)`. -/
theorem hashes_sig_eq_redFin (pm : List (Bytes × Bytes)) (r : Bytes) (pkm : Bytes × Bytes) :
    Bytes.hashes.sig pm r pkm = redFin (2 ^ 256) (sigHash256 pm r pkm)
```

```lean
/-- `hash_BIP0459/aux` on 32-byte arrays. -/
def auxHash (r : B32) : B32 := ⟨taggedHash "BIP0459/aux" r.1, length_taggedHash _ _⟩
```

```lean
/-- The bytes that `hash_BIP0459/nonce` hashes: `rand ‖ extra_in ‖ i`. -/
def nonceInput (rand : B32) (extraIn : Bytes) (i : Bool) : Bytes :=
  rand.1 ++ extraIn ++ [if i then 1 else 0]
```

```lean
/-- `hash_BIP0459/nonce` with its 256-bit output, as a function of
`(rand, extra_in, i)`. -/
def nonceHash256 (z : B32 × Bytes × Bool) : Fin (2 ^ 256) :=
  int256 (taggedHash "BIP0459/nonce" (nonceInput z.1 z.2.1 z.2.2)) (length_taggedHash _ _)
```

```lean
/-- **The input of `hash_BIP0459/nonce` determines `(rand, extra_in, i)`**,
for a 32-byte `rand` and an `extra_in` of any length. So a hash of the bytes
is a function of the triple, which is what the games query. -/
theorem nonceInput_injective {rand rand' : B32} {e e' : Bytes} {i i' : Bool}
    (h : nonceInput rand e i = nonceInput rand' e' i') : rand = rand' ∧ e = e' ∧ i = i'
```

```lean
/-- **`NonceGen` without the `sk` argument, on bytes, derives the nonces as the
games do**: the secret nonces are `ρ (G (rand, extra_in, i))` for
`G = nonceHash256` and `ρ = redFin (2^256)`. It fails if one of them is
zero. -/
theorem nonceGen_eq (O : Ops n Point Bytes) (rand : B32) (extraIn : Bytes) :
    Bytes.nonceGen O rand.1 none extraIn =
      (Dahlias.nonceGen O (redFin (2 ^ 256) (nonceHash256 (rand, extraIn, false)))
        (redFin (2 ^ 256) (nonceHash256 (rand, extraIn, true)))).map
          fun (sec, pub) => (serScalar sec.1 ++ serScalar sec.2, serNonce pub)
```

```lean
/-- **`NonceGen` with the `sk` argument, on bytes, derives the nonces as the
games do**, for the secret key `d` as the argument: the secret nonces are
`ρ (G (rand, extra_in, i))` with `rand = maskXor d (Aux rand')`, for
`G = nonceHash256`, `Aux = auxHash` and `ρ = redFin (2^256)`. So `maskXor` is
the xor of BIP 459's `NonceGen`. -/
theorem nonceGen_sk_eq (O : Ops n Point Bytes) (d : ZMod n) (rand' : B32) (extraIn : Bytes) :
    Bytes.nonceGen O rand'.1 (some (serScalar d)) extraIn =
      (Dahlias.nonceGen O
        (redFin (2 ^ 256) (nonceHash256 (maskXor d (auxHash rand'), extraIn, false)))
        (redFin (2 ^ 256) (nonceHash256 (maskXor d (auxHash rand'), extraIn, true)))).map
          fun (sec, pub) => (serScalar sec.1 ++ serScalar sec.2, serNonce pub)
```

### The byte interface

`Dahlias/BytesGame.lean`. The adversary sends the arguments of `Sign` and its forgery as byte arrays. The signer runs `Sign` on bytes and the game `Verify` on bytes, with the challenge hash as an oracle. The bounds are for the adversaries that parse.

```lean
/-- `Sign` with the hash functions `H` in place of the tagged hashes of
BIP 459. The games with the byte interface use it with the challenge hash as
a random oracle. -/
def signWith (H : Hashes n Point Bytes Bytes) (secnonce sk m aggnonce : Bytes)
    (pks msgs pubnonces : List Bytes) : Option Bytes :=
  if wellFormed pks msgs pubnonces.length && is32 m && secnonce.length == 64 then
    match scalar (secnonce.take 32), scalar (secnonce.drop 32), scalar sk with
    | some r₁, some r₂, some d =>
      (Dahlias.sign O H (r₁, r₂) d m (parseNonce O aggnonce) (pks.zip msgs)
        (pubnonces.map (parseNonce O))).map serScalar
    | _, _, _ => none
  else none
```

```lean
/-- `Verify` with the hash functions `H` in place of the tagged hashes of
BIP 459. -/
def verifyWith (H : Hashes n Point Bytes Bytes) (pks msgs : List Bytes) (sig : Bytes) : Bool :=
  wellFormed pks msgs pks.length && sig.length == 64 &&
    match scalar (sig.drop 32) with
    | some s => Dahlias.verify O H (pks.zip msgs) (sig.take 32, s)
    | none => false
```

```lean
/-- The algorithm that runs `f q` in place of every query `q`. -/
def transl (f : (q : Q) → Alg Q' R' (R q)) : Alg Q R α → Alg Q' R' α
  | .done a => .done a
  | .ask q k => f q >>= fun r => transl f (k r)
```

```lean
/-- The translation of the game's queries, with the queries of the table
passed on. -/
def sumTr (f : (q : Q) → Alg Q' R' (R q)) :
    (q : Q ⊕ D) → Alg (Q' ⊕ D) (SumR R' W) (SumR R W q)
  | .inl q => liftQ (f q)
  | .inr d => .ask (.inr d) .done
```

```lean
/-- A byte array as a 32-byte array: itself if it has 32 bytes. -/
def to32 (b : Bytes) : B32 := if h : b.length = 32 then ⟨b, h⟩ else default
```

```lean
/-- Lists of public keys and messages as a list of pairs of 32-byte arrays. -/
def pairs32 (pks msgs : List Bytes) : List (B32 × B32) :=
  (pks.zip msgs).map fun e => (to32 e.1, to32 e.2)
```

```lean
/-- The hash functions on byte arrays for the table `Tab` of hash outputs: the
nonce coefficient hash of BIP 459, and for 32-byte public keys, messages and
`r` the reduced table value as the challenge hash. `Sign` and `Verify` hash
no other arrays. -/
def hashesB (Tab : SigIn N B32 B32 → H) : Hashes n Point Bytes Bytes where
  nonceCoef := Bytes.hashes.nonceCoef
  sig pm r pkm := (hashesOf N nonceCoef32 fun z => red (Tab z)).sig
    (pm.map fun e => (to32 e.1, to32 e.2)) (to32 r) (to32 pkm.1, to32 pkm.2)
```

```lean
/-- **The adversary's queries with byte arrays.** A signing query has the
arguments of `Sign` that the other parties choose: the message, the aggregate
nonce, the public keys, the messages and the public nonces, as byte arrays of
any length. The tweak of the signer's key stays a pair of scalars, and a hash
query has 32-byte arrays. -/
inductive AdvQB (N : ℕ) where
  /-- A random oracle query. -/
  | hash (z : SigIn N B32 B32)
  /-- Open a signing session. -/
  | openSession
  /-- Close session `k`: the honest signer's `Sign` with the tweak `τ`. -/
  | close (k : ℕ) (τ : Tweak n) (m aggnonce : Bytes) (pks msgs pubnonces : List Bytes)
  /-- Sign alone for a list of the honest signer's own tweaked keys and
  messages, with one nonce. -/
  | single (items : List (Tweak n × Bytes))
```

```lean
/-- The answers in bytes: a hash output, the 66-byte public nonce, the 32-byte
partial signature, the 64-byte signature. -/
def AdvRB (H : Type) {N : ℕ} : AdvQB N → Type
  | .hash _ => H
  | .openSession => Option Bytes
  | .close .. => Option Bytes
  | .single _ => Option Bytes
```

```lean
/-- A forgery in bytes: the public keys, the messages, the tweak of the honest
signer's key and the 64-byte signature. -/
structure ForgeryB where
  pks : List Bytes
  msgs : List Bytes
  τ : Tweak n
  sig : Bytes
```

```lean
/-- The forgery on parsed values. -/
def toForgery (f : ForgeryB) : Forgery n B32 B32 :=
  ⟨pairs32 f.pks f.msgs, f.τ, (to32 (f.sig.take 32), (scalar (f.sig.drop 32)).getD 0)⟩
```

```lean
/-- A byte query as a query of the game on parsed values. A signing query
whose public keys and messages are not 32-byte arrays of the same number is
answered with a failure, as `Sign` answers it. -/
def trB {N : ℕ} : (q : AdvQB N) → Alg (AdvQ n N Point B32 B32) (AdvRH H) (AdvRB H q)
  | .hash z => .ask (.hash z) fun c => .done c
  | .openSession => .ask .openSession fun r => .done (r.map serNonce)
  | .close k τ m aggnonce pks msgs pubnonces =>
    if pks.length = msgs.length ∧ pks.all is32 = true ∧ msgs.all is32 = true ∧ is32 m = true then
      .ask (.close k τ (to32 m) (parseNonce specOps aggnonce) (pairs32 pks msgs)
        (pubnonces.map (parseNonce specOps))) fun r => .done (r.map serScalar)
    else .done none
  | .single items =>
    if items.all (fun i => is32 i.2) = true then
      .ask (.single (items.map fun i => (i.1, to32 i.2))) fun r =>
        .done (r.map fun s => s.1.1 ++ serScalar s.2)
    else .done none
```

```lean
/-- **The game's answers to the queries in bytes**, for the table `Tab` of
hash outputs. A session is closed with `Sign` on bytes (`Bytes.signWith`),
with the challenge hash answered from the table. The public nonce of a new
session and a single-party signature are the game's, serialized. -/
def challengerB (x : ZMod n) (nonces : Fin qs → SecNonce n) (Tab : SigIn N B32 B32 → H) :
    (q : AdvQB N) → SignerState B32 B32 → AdvRB H q × SignerState B32 B32
  | .hash z, st => (Tab z, st)
  | .openSession, st =>
    (((challenger secp256k1X nonceCoef32 N qs x nonces (fun z => red (Tab z))
        .openSession st).1).map serNonce,
      (challenger secp256k1X nonceCoef32 N qs x nonces (fun z => red (Tab z)) .openSession st).2)
  | .close k τ m aggnonce pks msgs pubnonces, st =>
    if h : k < qs ∧ k < st.opened ∧ k ∉ st.closed ∧ τ.2 ≠ 0 ∧ pks.length ≤ N then
      match Bytes.signWith specOps (hashesB N red Tab)
          (serScalar (nonces ⟨k, h.1⟩).1 ++ serScalar (nonces ⟨k, h.1⟩).2) (serScalar (τ.sk x))
          m aggnonce pks msgs pubnonces with
      | some psig =>
        (some psig, { st with closed := k :: st.closed
                              signed := (pairs32 pks msgs,
                                secp256k1X.x (secp256k1X.mulG (τ.sk x)), to32 m) :: st.signed })
      | none => (none, st)
    else (none, st)
  | .single items, st =>
    if items.all (fun i => is32 i.2) = true then
      (((challenger secp256k1X nonceCoef32 N qs x nonces (fun z => red (Tab z))
          (.single (items.map fun i => (i.1, to32 i.2))) st).1).map fun s =>
            s.1.1 ++ serScalar s.2,
        (challenger secp256k1X nonceCoef32 N qs x nonces (fun z => red (Tab z))
          (.single (items.map fun i => (i.1, to32 i.2))) st).2)
    else (none, st)
```

```lean
/-- **The winning condition on a forgery in bytes**: `Verify` on bytes
(`Bytes.verifyWith`) accepts, with the challenge hash answered from the
table, and the list has the honest signer's tweaked key with a message that
the signer did not sign in that list. -/
def WinsB (x : ZMod n) (Tab : SigIn N B32 B32 → H) (f : ForgeryB) (st : SignerState B32 B32) :
    Prop :=
  f.τ.2 ≠ 0 ∧ f.τ.sk x ≠ 0 ∧ f.pks.length ≤ N ∧
    (∃ m, (secp256k1X.x (secp256k1X.mulG (f.τ.sk x)), m) ∈ pairs32 f.pks f.msgs ∧
      (pairs32 f.pks f.msgs, secp256k1X.x (secp256k1X.mulG (f.τ.sk x)), m) ∉ st.signed) ∧
    Bytes.verifyWith specOps (hashesB N red Tab) f.pks f.msgs f.sig = true
```

```lean
/-- The cost of a query in bytes in random oracle queries. -/
def hashCostB {N : ℕ} : AdvQB N → ℕ
  | .hash _ => 1
  | .single items => items.length
  | _ => 0
```

```lean
/-- At most `qh` random oracle queries, whatever the answers: `HashBound` for
the queries in bytes. -/
def HashBoundB {N : ℕ} {α : Type} : Alg (AdvQB N) (AdvRB H) α → ℕ → Prop
  | .done _, _ => True
  | .ask q f, qh => hashCostB q ≤ qh ∧ ∀ r, HashBoundB (f r) (qh - hashCostB q)
```

```lean
/-- An adversary with the byte interface. -/
abbrev AdversaryB (N : ℕ) (H Coins : Type) := Coins → Point → Alg (AdvQB N) (AdvRB H) ForgeryB
```

```lean
/-- **The unforgeability game with the byte interface** on one sample, with
hash outputs in `H`. -/
def forgeExperimentB (A : AdversaryB N H Coins) (ω : ForgeSampleH n N qs B32 B32 H Coins) :
    Prop :=
  let x : ZMod n := ω.1
  let nonces : Fin qs → SecNonce n := fun k => ((ω.2.1 k).1, (ω.2.1 k).2)
  let Tab := ω.2.2.2
  let out := (A ω.2.2.1 (secp256k1X.mulG x)).run (challengerB N qs red x nonces Tab) ⟨0, [], []⟩
  WinsB N red x Tab out.1 out.2
```

```lean
/-- The adversary on parsed values: it parses the queries of `A` and its
forgery. -/
def toStruct (A : AdversaryB N H Coins) : AdversaryH n N Point B32 B32 H Coins :=
  fun c P => transl trB (A c P) >>= fun f => .done (toForgery f)
```

```lean
/-- The game's answers in bytes when the nonces of a slot depend on its
`extra_in`: `challengerEH` with the byte interface. -/
def challengerEB (nv : Fin qs → Ex → SecNonce n) (x : ZMod n) (Tab : SigIn N B32 B32 → H) :
    (q : AdvQB N ⊕ Ex) → SignerState B32 B32 × (ℕ → Ex) →
      SumR (AdvRB H) Unit q × (SignerState B32 B32 × (ℕ → Ex))
  | .inl q, s =>
    ((challengerB N qs red x (fun k => nv k (s.2 k)) Tab q s.1).1,
      ((challengerB N qs red x (fun k => nv k (s.2 k)) Tab q s.1).2, s.2))
  | .inr e, s => ((), (s.1, update s.2 s.1.opened e))
```

```lean
/-- An adversary of the game with `NonceGen`, with the byte interface. -/
abbrev NAdversaryB (N : ℕ) (Rnd Ex W H Coins : Type) :=
  Coins → Point → Alg ((AdvQB N ⊕ Ex) ⊕ (Rnd × Ex × Bool)) (SumR (SumR (AdvRB H) Unit) W) ForgeryB
```

```lean
/-- An adversary of the game with `NonceGen` and its `sk` argument, with the
byte interface. -/
abbrev SkAdversaryB (N : ℕ) (Rnd Rp Ex W H Coins : Type) :=
  Coins → Point → Alg (((AdvQB N ⊕ Ex) ⊕ (Rnd × Ex × Bool)) ⊕ Rp)
    (SumR (SumR (SumR (AdvRB H) Unit) W) Rnd) ForgeryB
```

```lean
/-- **The unforgeability game with `NonceGen`, hash outputs in `H` and the
byte interface** on one sample: `nonceGenExperimentH` with `Sign` and `Verify`
on bytes. -/
def nonceGenExperimentB (A : NAdversaryB N Rnd Ex W H Coins) (ρ : W → ZMod n) (e₀ : Ex)
    (ω : (RestH n N B32 B32 H Coins × (Fin qs → Rnd)) × (Rnd × Ex × Bool → W)) : Prop :=
  let x : ZMod n := ω.1.1.1
  let Tab := ω.1.1.2.2
  let out := (answerG ω.2 (A ω.1.1.2.1 (secp256k1X.mulG x))).run
    (challengerEB N qs red (nvOf qs ρ fun i => ω.2 (noncePt qs ω.1.2 i)) x Tab)
    (⟨0, [], []⟩, fun _ => e₀)
  WinsB N red x Tab out.1 out.2.1
```

```lean
/-- **The game with `NonceGen`, its `sk` argument and the byte interface** on
one sample: the `rand` of slot `k` is `mask x k (Aux (rand' k))`. -/
def nonceGenSkExperimentB (A : SkAdversaryB N Rnd Rp Ex W H Coins) (ρ : W → ZMod n) (e₀ : Ex)
    (mask : (ZMod n)ˣ → Fin qs → Rnd ≃ Rnd)
    (ω : ((RestH n N B32 B32 H Coins × (Rnd × Ex × Bool → W)) × (Fin qs → Rp)) × (Rp → Rnd)) :
    Prop :=
  nonceGenExperimentB N qs red (fun c P => answerG ω.2 (A c P)) ρ e₀
    ((ω.1.1.1, fun k => mask ω.1.1.1.1 k (ω.2 (ω.1.2 k))), ω.1.1.2)
```

```lean
/-- **The game with `NonceGen`, its `sk` argument, a counter in place of
`rand'` and the byte interface** on one sample: the `rand` of slot `k` is
`mask x k (Aux (ctr k))`. -/
def nonceGenCtrExperimentB (A : SkAdversaryB N Rnd Rp Ex W H Coins) (ρ : W → ZMod n) (e₀ : Ex)
    (mask : (ZMod n)ˣ → Fin qs → Rnd ≃ Rnd) (ctr : Fin qs → Rp)
    (ω : (RestH n N B32 B32 H Coins × (Rnd × Ex × Bool → W)) × (Rp → Rnd)) : Prop :=
  nonceGenExperimentB N qs red (fun c P => answerG ω.2 (A c P)) ρ e₀
    ((ω.1.1, fun k => mask ω.1.1.1 k (ω.2 (ctr k))), ω.1.2)
```

```lean
/-- The adversary of the game with `NonceGen` on parsed values. -/
def toStructN (A : NAdversaryB N Rnd Ex W H Coins) :
    NAdversaryH n N Point B32 B32 Rnd Ex W H Coins :=
  fun c P => transl (sumTr (sumTr trB)) (A c P) >>= fun f => .done (toForgery f)
```

```lean
/-- The adversary of the game with `NonceGen` and its `sk` argument on parsed
values. -/
def toStructSk (A : SkAdversaryB N Rnd Rp Ex W H Coins) :
    SkAdversaryH n N Point B32 B32 Rnd Rp Ex W H Coins :=
  fun c P => transl (sumTr (sumTr (sumTr trB))) (A c P) >>= fun f => .done (toForgery f)
```

```lean
/-- **BIP 459 is unforgeable under AOMDL with the byte interface.** The
adversary sends the message, the aggregate nonce, the public keys, the
messages and the public nonces of a signing query as byte arrays of any
length, and its forgery as byte arrays. The signer runs `Sign` on bytes and
the game runs `Verify` on bytes, with the challenge hash as a 256-bit random
oracle reduced modulo `n` and the BIP's nonce coefficient hash. The bound is
the one of `bytes_unforgeable_256` for the adversary `toStruct A`, which
parses. -/
theorem bytesGame_unforgeable_256 {Coins : Type} [Fintype Coins] (N qs : ℕ)
    (A : AdversaryB N (Fin (2 ^ 256)) Coins) (hN : N < n) (qh : ℕ)
    (hA : ∀ c P, HashBoundB (A c P) qh) :
    prob (forgeExperimentB N qs (redFin (2 ^ 256)) A) ≤
      Real.sqrt ((qh + qs + 1 : ℕ) *
        (omdlAdvantage secp256k1X (2 * qs + 1)
            (reduction secp256k1X nonceCoef32 N qs
              fun coins P => liftHash N (liftFin n_lt.le) (toStruct N A coins P)) +
          collisionAdvantage secp256k1X nonceCoef32 N qs
            fun coins P => liftHash N (liftFin n_lt.le) (toStruct N A coins P))) +
        (qh + qs + 1 : ℕ) / n + qs / (n - 1 : ℝ) +
        (qh + qs + N : ℕ) * ((((2 ^ 256 : ℕ) : ℝ) - n) / ((2 ^ 256 : ℕ) : ℝ))
```

```lean
/-- **BIP 459 with `NonceGen` and 256-bit hashes is unforgeable under AOMDL
with the byte interface**, for `NonceGen` without its `sk` argument. The game
is the one of `bytes_nonceGen_unforgeable_256` with `Sign` and `Verify` on
bytes, and the bound is the one for the adversary `toStructN A`, which
parses. -/
theorem bytesGame_nonceGen_unforgeable_256 {Coins Ex : Type} [Fintype Coins] [Fintype Ex]
    [DecidableEq Ex] (N qs : ℕ)
    (A : NAdversaryB N B32 Ex (Fin (2 ^ 256)) (Fin (2 ^ 256)) Coins) (e₀ : Ex) (hN : N < n)
    (qh qn : ℕ) (hA : ∀ c P, NBound (A c P) qn)
    (hH : ∀ c P G, HashBoundB (answerG (fun _ : Ex => ()) (answerG G (A c P))) qh) :
    prob (nonceGenExperimentB N qs (redFin (2 ^ 256)) A (redFin (2 ^ 256)) e₀) ≤
      lazyBound secp256k1X nonceCoef32 N qs qh
          (withStream N qn (liftHashN N (liftFin n_lt.le) (toStructN N A))) +
        (qh + qs + N : ℕ) * ((((2 ^ 256 : ℕ) : ℝ) - n) / ((2 ^ 256 : ℕ) : ℝ)) +
        (qs : ℝ) ^ 2 / ((2 ^ 256 : ℕ) : ℝ) + qs * (qn / ((2 ^ 256 : ℕ) : ℝ)) +
        (2 * qs : ℕ) * ((((2 ^ 256 : ℕ) : ℝ) - (n - 1)) / ((2 ^ 256 : ℕ) : ℝ))
```

```lean
/-- **BIP 459 with `NonceGen`, its `sk` argument and 256-bit hashes is
unforgeable under AOMDL with the byte interface.** The game is the one of
`bytes_nonceGenSk_unforgeable_256` with `Sign` and `Verify` on bytes: the
adversary sends byte arrays of any length, gets the public nonces and the
partial signatures as byte arrays, and sees the 256-bit outputs of the
challenge hash. The bound is the one for the adversary `toStructSk A`, which
parses. -/
theorem bytesGame_nonceGenSk_unforgeable_256 {Coins Ex : Type} [Fintype Coins] [Fintype Ex]
    [DecidableEq Ex] (N qs : ℕ)
    (A : SkAdversaryB N B32 B32 Ex (Fin (2 ^ 256)) (Fin (2 ^ 256)) Coins) (e₀ : Ex)
    (mask : (ZMod n)ˣ → Fin qs → B32 ≃ B32) (hN : N < n) (qh qn qa : ℕ)
    (hA : ∀ c P, NBound (A c P) qa)
    (hG : ∀ c P (Aux : B32 → B32), NBound (answerG Aux (A c P)) qn)
    (hH : ∀ c P G (Aux : B32 → B32),
      HashBoundB (answerG (fun _ : Ex => ()) (answerG G (answerG Aux (A c P)))) qh) :
    prob (nonceGenSkExperimentB N qs (redFin (2 ^ 256)) A (redFin (2 ^ 256)) e₀ mask) ≤
      lazyBound secp256k1X nonceCoef32 N qs qh
          (withStream N qn (withAuxStream N qa
            (liftHashSk N (liftFin n_lt.le) (toStructSk N A)))) +
        (qh + qs + N : ℕ) * ((((2 ^ 256 : ℕ) : ℝ) - n) / ((2 ^ 256 : ℕ) : ℝ)) +
        (qs : ℝ) ^ 2 / ((2 ^ 256 : ℕ) : ℝ) + qs * (qn / ((2 ^ 256 : ℕ) : ℝ)) +
        (2 * qs : ℕ) * ((((2 ^ 256 : ℕ) : ℝ) - (n - 1)) / ((2 ^ 256 : ℕ) : ℝ)) +
        (qs : ℝ) ^ 2 / ((2 ^ 256 : ℕ) : ℝ) + qs * (qa / ((2 ^ 256 : ℕ) : ℝ))
```

```lean
/-- **BIP 459 with `NonceGen` with a counter in place of `rand'` and 256-bit
hashes is unforgeable under AOMDL with the byte interface.** The game is the
one of `bytes_nonceGenCtr_unforgeable_256` with `Sign` and `Verify` on bytes,
and the bound is the one for the adversary `toStructSk A`, which parses. -/
theorem bytesGame_nonceGenCtr_unforgeable_256 {Coins Ex : Type} [Fintype Coins] [Fintype Ex]
    [DecidableEq Ex] (N qs : ℕ)
    (A : SkAdversaryB N B32 B32 Ex (Fin (2 ^ 256)) (Fin (2 ^ 256)) Coins) (e₀ : Ex)
    (ctr : Fin qs → B32) (hctr : Injective ctr) (τ : Fin qs → Tweak n) (hτ : ∀ k, (τ k).2 ≠ 0)
    (msgs : Fin (qs + 1) → B32) (hmsgs : Injective msgs) (hN0 : 0 < N) (hN : N < n)
    (qh qn qa : ℕ) (hA : ∀ c P, NBound (A c P) qa)
    (hG : ∀ c P (Aux : B32 → B32), NBound (answerG Aux (A c P)) qn)
    (hH : ∀ c P G (Aux : B32 → B32),
      HashBoundB (answerG (fun _ : Ex => ()) (answerG G (answerG Aux (A c P)))) qh) :
    prob (nonceGenCtrExperimentB N qs (redFin (2 ^ 256)) A (redFin (2 ^ 256)) e₀
        (fun x k => maskXor ((τ k).sk x)) ctr) ≤
      lazyBound secp256k1X nonceCoef32 N qs qh
          (withStream N qn (withAuxStream N qa
            (liftHashSk N (liftFin n_lt.le) (toStructSk N A)))) +
        lazyBound secp256k1X nonceCoef32 N qs (qh + 1)
          (withStream N qn (withAuxStream N (qa + qs)
            (keyForger secp256k1X N qs (fun k => unmaskXor (τ k)) msgs ctr
              (liftHashSk N (liftFin n_lt.le) (toStructSk N A))))) +
        (qh + qs + N : ℕ) * ((((2 ^ 256 : ℕ) : ℝ) - n) / ((2 ^ 256 : ℕ) : ℝ)) +
        (qs : ℝ) ^ 2 / ((2 ^ 256 : ℕ) : ℝ) +
        2 * ((2 * qs : ℕ) * ((((2 ^ 256 : ℕ) : ℝ) - (n - 1)) / ((2 ^ 256 : ℕ) : ℝ)))
```

### Every definition behind the results

The definitions of the project that the statements of the results in `Dahlias/Summary.lean` depend on, directly or through other definitions. `#surface` in `Dahlias/Audit.lean` computes the list from the compiled project, `Dahlias/Summary.lean` guards it, and the build fails if it changes. Proofs are not followed, since what a proof uses does not change what a statement says. Whoever agrees with these definitions knows what the results say. The ones that are not printed above have to be read in the sources.

- `Dahlias/Alg.lean`: `Alg`, `Alg.bind`, `Alg.instMonad`, `Alg.interp`, `Alg.run`
- `Dahlias/Attacks.lean`: `Security.challengerWith`, `Security.msgSwap`, `Security.sgn`, `Security.signNoMsgCheck`
- `Dahlias/Basic.lean`: `Hashes`, `Ops`, `PubNonce`, `SecNonce`, `coefItems`, `getSessionValues`, `keySum`, `matchIdxs`, `nonceAgg`, `nonceGen`, `partialSigVerify`, `sigAgg`, `sign`, `tweakPK`, `tweakSK`, `verify`, `Ops.evenScalar`, `Ops.signOf`, `Taproot.Curve.ops`
- `Dahlias/Binding.lean`: `Security.BindAdversary`, `Security.bindExperiment`
- `Dahlias/BindingHashed.lean`: `Security.BindAdversaryH`, `Security.bindExperimentH`, `Security.liftBind`
- `Dahlias/Bytes.lean`: `Bytes.cbytes`, `Bytes.cpoint`, `Bytes.hashes`, `Bytes.is32`, `Bytes.nonceAgg`, `Bytes.nonceGen`, `Bytes.parseNonce`, `Bytes.partialSigVerify`, `Bytes.scalar`, `Bytes.scalarWrap`, `Bytes.serNonce`, `Bytes.serScalar`, `Bytes.sigAgg`, `Bytes.sign`, `Bytes.signWith`, `Bytes.specOps`, `Bytes.tweakPKOfSK`, `Bytes.tweakSK`, `Bytes.verify`, `Bytes.verifyWith`, `Bytes.wellFormed`, `Bytes.xbytes`
- `Dahlias/BytesCorrectness.lean`: `Bytes.pkOf`, `Bytes.pubnonceOf`, `Bytes.secnonceOf`, `Bytes.skOf`
- `Dahlias/BytesCurve.lean`: `Bytes.secp256k1B`
- `Dahlias/BytesGame.lean`: `Security.AdvQB`, `Security.AdvRB`, `Security.AdversaryB`, `Security.ForgeryB`, `Security.HashBoundB`, `Security.NAdversaryB`, `Security.SkAdversaryB`, `Security.WinsB`, `Security.challengerB`, `Security.challengerEB`, `Security.forgeExperimentB`, `Security.hashCostB`, `Security.hashesB`, `Security.nonceGenCtrExperimentB`, `Security.nonceGenExperimentB`, `Security.nonceGenSkExperimentB`, `Security.pairs32`, `Security.sumTr`, `Security.to32`, `Security.toForgery`, `Security.toStruct`, `Security.toStructN`, `Security.toStructSk`, `Security.trB`, `Security.transl`
- `Dahlias/BytesSecurity.lean`: `Security.Agree`, `Security.B32`, `Security.instDecidableEqB32`, `Security.instFintypeB32`, `Security.instInhabitedB32`, `Security.maskXor`, `Security.nonceCoef32`, `Security.secp256k1X`, `Security.ser32`, `Security.unmaskXor`, `Security.vals`, `Security.xor32`
- `Dahlias/Correctness.lean`: `Signer`, `Signer.pkm`, `Signer.pubnonce`
- `Dahlias/Encoding.lean`: `Bytes.Items32`, `Bytes.Pairs32`, `Bytes.nonceCoefInput`, `Bytes.sigInput`, `Security.auxHash`, `Security.int256`, `Security.nonceCoefBytes`, `Security.nonceGen_eq`, `Security.nonceHash256`, `Security.nonceInput`, `Security.sigHash256`
- `Dahlias/Examples.lean`: `Security.guesser`
- `Dahlias/Fork.lean`: `QTree.Accepts`, `QTree.Forks`
- `Dahlias/Hashed.lean`: `Security.AdvRH`, `Security.AdversaryH`, `Security.ForgeSampleH`, `Security.challengerH`, `Security.forgeAdvantageH`, `Security.forgeExperimentH`, `Security.liftFin`, `Security.liftHash`, `Security.redFin`
- `Dahlias/Lazy.lean`: `QTree.Ext`, `QTree.evalLazy`, `QTree.mapTree`, `QTree.memo`, `QTree.stream`
- `Dahlias/LazyCollider.lean`: `Security.LazyColliderSample`, `Security.colliderLazy`, `Security.colliderM`, `Security.collisionAdvantageLazy`, `Security.gameRecsM`, `Security.logChallengerM`, `Security.noOmdl`
- `Dahlias/LazyGame.lean`: `Security.LazySample`, `Security.lazyExperiment`, `Security.verifyWith`, `Security.winTail`, `Security.winTree`
- `Dahlias/LazyReduction.lean`: `Security.RM`, `Security.rdFork`, `Security.rdTable`, `Security.readAll`, `Security.reductionBodyM`, `Security.reductionLazy`, `Security.reductionM`, `Security.simChallengerM`
- `Dahlias/LocalFork.lean`: `LocalFork.accCount`, `LocalFork.forkCount`
- `Dahlias/NonceGen.lean`: `Security.NAdversary`, `Security.Rest`, `Security.challengerE`, `Security.nonceGenAdvantage`, `Security.nonceGenExperiment`, `Security.noncePt`, `Security.nvOf`, `Security.winE`, `Security.withTable`
- `Dahlias/NonceGenCounter.lean`: `Security.SignedQ`, `Security.askList`, `Security.findKey`, `Security.forgeTail`, `Security.keyForger`, `Security.lazyBound`, `Security.liftUpd`, `Security.nonceGenCtrAdvantage`, `Security.nonceGenCtrAdvantageH`, `Security.nonceGenCtrExperiment`, `Security.nonceGenCtrExperimentH`, `Security.obsUpd`, `Security.signedList`, `Security.tally`, `Security.trackOf`
- `Dahlias/NonceGenHashed.lean`: `Security.NAdversaryH`, `Security.RestH`, `Security.SkAdversaryH`, `Security.challengerEH`, `Security.hashAns`, `Security.liftHashN`, `Security.liftHashSk`, `Security.mapAns`, `Security.nonceGenAdvantageH`, `Security.nonceGenExperimentH`, `Security.nonceGenSkAdvantageH`, `Security.nonceGenSkExperimentH`, `Security.sumAns`
- `Dahlias/NonceGenLazy.lean`: `Security.withAuxStream`, `Security.withStream`
- `Dahlias/NonceGenSk.lean`: `Security.SkAdversary`, `Security.nonceGenSkAdvantage`, `Security.nonceGenSkExperiment`, `Security.winSk`, `Security.withAux`
- `Dahlias/OmdlStd.lean`: `Security.chalLogsStd`, `Security.omdlAdvantageStd`, `Security.omdlChallengerStd`, `Security.omdlExperimentStd`
- `Dahlias/OrderG.lean`: `secp256k1F`
- `Dahlias/Prob.lean`: `prob`
- `Dahlias/QueryRun.lean`: `QTree`, `QTree.askAll`, `QTree.eval`, `QTree.flog`, `QTree.fresh`, `QTree.queryAll`
- `Dahlias/Ros.lean`: `Security.effNonce`, `Security.rosBit`, `Security.rosCoef`, `Security.rosConst`, `Security.signTupleCheck`
- `Dahlias/Second.lean`: `Security.NBound`, `Security.SumR`, `Security.answerG`, `Security.answerLazy`, `Security.gLog`, `Security.liftQ`
- `Dahlias/Secp256k1.lean`: `Security.instFintypeBList`, `Security.instFintypeSigIn`
- `Dahlias/Security.lean`: `Security.AdvQ`, `Security.AdvR`, `Security.Adversary`, `Security.BList`, `Security.ForgeSample`, `Security.Forgery`, `Security.HashBound`, `Security.OmdlAdversary`, `Security.OmdlQ`, `Security.OmdlR`, `Security.SigIn`, `Security.SignerState`, `Security.Tweak`, `Security.Wins`, `Security.chalLogs`, `Security.challenger`, `Security.challengerG`, `Security.forgeAdvantage`, `Security.forgeAdvantageG`, `Security.forgeExperimentG`, `Security.hashesOf`, `Security.omdlAdvantage`, `Security.omdlChallenger`, `Security.omdlExperiment`, `Security.singleKeys`, `Security.singleNcIn`, `Security.singleNonce`, `Security.singleS`, `Security.Tweak.sk`
- `Dahlias/Single.lean`: `signSingle`, `singleList`
- `Dahlias/Tightness.lean`: `Security.grindAlg`, `Security.grindIn`, `Security.grindOut`, `Security.grinder`
- `Dahlias/Tweaks.lean`: `Security.bipTweakSign`
- `Dahlias/Unforgeability.lean`: `Security.NoSingle`, `Security.collisionAdvantage`, `Security.instFintypeProdForallSigInZMod`
- `Dahlias/VectorData.lean`: `Vectors.nonceAggRows`, `Vectors.nonceGenRows`, `Vectors.partialSigVerifyRows`, `Vectors.signErrorRows`, `Vectors.signRows`, `Vectors.tweakRows`, `Vectors.verifyRows`
- `Dahlias/Vectors.lean`: `Vectors.checkNonceAgg`, `Vectors.checkNonceGen`, `Vectors.checkPartialSigVerify`, `Vectors.checkSign`, `Vectors.checkSignError`, `Vectors.checkTweak`, `Vectors.checkVerify`, `Vectors.hexList`, `Vectors.optHex`
- `Dahlias/Proofs/ForkGame.lean`: `Security.instFintypeProdForgeSampleZMod`, `Security.noncesOf`
- `Dahlias/Proofs/Game.lean`: `Security.H₀`, `Security.forkPoint`, `Security.signPost`, `Security.signPre`, `Security.treeChallenger`
- `Dahlias/Proofs/Reduction.lean`: `Security.CloseRec`, `Security.IsCollision`, `Security.KeyTerm`, `Security.SimState`, `Security.coefVec`, `Security.collider`, `Security.dlogPoint`, `Security.dlogRep`, `Security.evenLift`, `Security.extractX`, `Security.forkPointPub`, `Security.gameRecs`, `Security.getChals`, `Security.keyPoint`, `Security.keySign`, `Security.logChallenger`, `Security.ncHash`, `Security.reduction`, `Security.reductionBody`, `Security.signPrePub`, `Security.simChallenger`, `Security.simSign`, `Security.singleKeysPub`, `Security.singleTerms`, `Security.solveSession`, `Security.solveSessions`, `Security.CloseRec.ncIn`, `Security.CloseRec.point`, `Security.CloseRec.w`, `Security.Tweak.pk`

<!-- statements:end -->
