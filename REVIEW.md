# Reviewing dahlias-lean

Lean checks the proofs. A reviewer checks that the statements say what they should. Proofs can stay unread, because a wrong proof does not compile. A wrong definition does, and some definitions are under `Dahlias/Proofs/`: the reduction, the collision finder and what they call are part of what the unforgeability theorem says. [The main results](#the-main-results) names one result for every property and lists, for each, the definitions that decide what it says. [Every definition behind the results](#every-definition-behind-the-results) is that list for all results. Both are computed from the compiled project, and the build fails if they change.

## The main results

There is one main result for every property. It is stated for any curve that satisfies taproot-lean's interface and for any type of x-only encodings and of messages. Every other result is one of these in another form, for another model of the challenge hash or of the nonces, for secp256k1 or for bytes, or it is a fact that supports one. The [README](README.md#results) lists them.

A reader of a main result has to agree with its statement and with the definitions behind the statement. The table counts those definitions of the project and their source lines, comments included. `#reading` in `Dahlias/Audit.lean` computes the numbers and the lists, and `Dahlias/Summary.lean` guards them. taproot-lean's curve interface is not counted.

<!-- main:begin -->

| Main result | Theorem | Definitions | Lines |
|---|---|---|---|
| Correctness | `verify_honest` | 17 | 96 |
| Unforgeability | `unforgeable_sqrt`, `unforgeable` | 86 | 570 |
| Strong binding | `strongly_binding` | 16 | 79 |
| Finding a disruptive signer | `partialSigVerify_iff_eq_sign`, `exists_partialSigVerify_eq_false`, `verify_eq_false_of_one_bad` | 16 | 100 |
| All of them |  | 98 | 628 |

The definitions of the project behind each main result, by file:

**Correctness**

- `Dahlias/Basic.lean`: `Hashes`, `Ops`, `PubNonce`, `SecNonce`, `coefItems`, `getSessionValues`, `keySum`, `matchIdxs`, `nonceAgg`, `sigAgg`, `sign`, `verify`, `Ops.evenScalar`, `Taproot.Curve.ops`
- `Dahlias/Correctness.lean`: `Signer`, `Signer.pkm`, `Signer.pubnonce`

**Unforgeability**

- `Dahlias/Alg.lean`: `Alg`, `Alg.bind`, `Alg.instMonad`, `Alg.interp`, `Alg.run`
- `Dahlias/Basic.lean`: `Hashes`, `Ops`, `PubNonce`, `SecNonce`, `coefItems`, `getSessionValues`, `keySum`, `matchIdxs`, `sign`, `verify`, `Ops.evenScalar`, `Ops.signOf`, `Taproot.Curve.ops`
- `Dahlias/Prob.lean`: `prob`
- `Dahlias/Security.lean`: `Security.AdvQ`, `Security.AdvR`, `Security.Adversary`, `Security.BList`, `Security.ForgeSample`, `Security.Forgery`, `Security.HashBound`, `Security.OmdlAdversary`, `Security.OmdlQ`, `Security.OmdlR`, `Security.SigIn`, `Security.SignerState`, `Security.Tweak`, `Security.Wins`, `Security.chalLogs`, `Security.challengerG`, `Security.forgeAdvantage`, `Security.forgeAdvantageG`, `Security.forgeExperimentG`, `Security.hashesOf`, `Security.omdlAdvantage`, `Security.omdlChallenger`, `Security.omdlExperiment`, `Security.singleKeys`, `Security.singleNcIn`, `Security.singleNonce`, `Security.singleS`, `Security.Tweak.sk`
- `Dahlias/Unforgeability.lean`: `Security.NoSingle`, `Security.collisionAdvantage`, `Security.instFintypeProdForallSigInZMod`
- `Dahlias/Proofs/ForkGame.lean`: `Security.instFintypeProdForgeSampleZMod`, `Security.noncesOf`
- `Dahlias/Proofs/Game.lean`: `Security.H₀`, `Security.forkPoint`, `Security.signPost`, `Security.signPre`
- `Dahlias/Proofs/Reduction.lean`: `Security.CloseRec`, `Security.IsCollision`, `Security.KeyTerm`, `Security.SimState`, `Security.coefVec`, `Security.collider`, `Security.dlogPoint`, `Security.dlogRep`, `Security.evenLift`, `Security.extractX`, `Security.forkPointPub`, `Security.gameRecs`, `Security.getChals`, `Security.keyPoint`, `Security.keySign`, `Security.logChallenger`, `Security.ncHash`, `Security.reduction`, `Security.reductionBody`, `Security.signPrePub`, `Security.simChallenger`, `Security.simSign`, `Security.singleKeysPub`, `Security.singleTerms`, `Security.solveSession`, `Security.solveSessions`, `Security.CloseRec.ncIn`, `Security.CloseRec.point`, `Security.CloseRec.w`, `Security.Tweak.pk`

**Strong binding**

- `Dahlias/Alg.lean`: `Alg`
- `Dahlias/Basic.lean`: `Hashes`, `Ops`, `keySum`, `verify`, `Taproot.Curve.ops`
- `Dahlias/Binding.lean`: `Security.BindAdversary`, `Security.bindExperiment`
- `Dahlias/Prob.lean`: `prob`
- `Dahlias/QueryRun.lean`: `QTree`, `QTree.eval`, `QTree.flog`, `QTree.fresh`
- `Dahlias/Security.lean`: `Security.BList`, `Security.SigIn`, `Security.hashesOf`

**Finding a disruptive signer**

- `Dahlias/Basic.lean`: `Hashes`, `Ops`, `PubNonce`, `SecNonce`, `coefItems`, `getSessionValues`, `keySum`, `matchIdxs`, `nonceAgg`, `partialSigVerify`, `sigAgg`, `sign`, `verify`, `Ops.evenScalar`, `Ops.signOf`, `Taproot.Curve.ops`

<!-- main:end -->

## What to read

For a main result, read the definitions on its list and then its statement. [The statements](#the-statements) prints the statements and most of the definitions on one page, in this order.

1. `Dahlias/Basic.lean`, all of it. Compare the algorithms with BIP 459. The header lists the modelling choices. Then the statement of `verify_honest` in `Dahlias/Correctness.lean`.
2. `Dahlias/Alg.lean`, the definitions `Alg`, `bind` and `run`, and `Dahlias/Prob.lean`, the definition `prob`.
3. `Dahlias/Security.lean`, all of it: the unforgeability game, the AOMDL game, and the places where the game differs from the paper's.
4. `Dahlias/Proofs/Reduction.lean`, all definitions: `reduction`, `collider` and what they call. The theorems measure these two algorithms, so their bodies are part of the statement. Then `Dahlias/Unforgeability.lean`, the statements of `unforgeable_sqrt` and `unforgeable` and the definitions `collisionAdvantage` and `NoSingle`.
5. `Dahlias/Binding.lean`, the header, `bindExperiment` and the statement of `strongly_binding`.
6. `Dahlias/Blame.lean`, the statements of `partialSigVerify_iff_eq_sign`, `exists_partialSigVerify_eq_false` and `verify_eq_false_of_one_bad`.

The other forms have games of their own: the random oracle with hash outputs (`Dahlias/Hashed.lean`), the nonces of `NonceGen` (`Dahlias/NonceGen.lean`, `Dahlias/NonceGenSk.lean`, `Dahlias/NonceGenHashed.lean`, `Dahlias/NonceGenCounter.lean`) and the byte interface (`Dahlias/Bytes.lean`, `Dahlias/BytesGame.lean`). They measure three more algorithms, whose bodies are part of their statements: `reductionLazy` in `Dahlias/LazyReduction.lean`, `colliderLazy` in `Dahlias/LazyCollider.lean` and `keyForger` in `Dahlias/NonceGenCounter.lean`.

taproot-lean supplies the curve interface (`Taproot.Curve`), secp256k1 and SHA-256. A full review reads those definitions too. taproot-lean checks the order of secp256k1's generator with compiled code. `Dahlias/OrderG.lean` proves it from a certificate that the kernel checks, and the theorems here use that proof (`secp256k1F`), so only the test vector checks depend on compiled code.

The model was compared with BIP 459 at bitcoin/bips commit [`f3d1668`](https://github.com/bitcoin/bips/blob/f3d1668891fcdad99770245110bc6a22c87bce97/bip-0459.mediawiki). CI takes the test vectors and the Python reference from the same commit.

## Questions to ask

**Is the game the paper's?** `forgeExperiment` is the co-EUF-CMA-TK game of the DahLIAS paper with two changes and one addition. All three are described in the header of `Dahlias/Security.lean`, and [The paper's statements](#the-papers-statements) has them next to the paper's definitions.

- The game records the tweaked x-only public key of every signature, where the paper records the tweak. With x-only keys two different tweaks can give the same key without revealing anything: `(α, β)` and `(-α, -β)` always do (`Tweak.xonly_neg`). The signer answers a query with one as it answers the query with the other (`challengerG_close_neg`), so the paper's game would count a signature under one of them as a forgery under the other. The paper's proof needs that two such tweaks reveal the secret key, which cannot hold here (`not_collisionExtractable`).
- A `Sign` call that fails leaves the session open. The paper closes it. The adversary here has more freedom.
- The adversary may also ask for single-party signatures: the honest signer signs a list of its own tweaked keys with one uniform nonce (`signSingle`, `challenger_single`). This is not in the paper. Sessions and single-party signatures share the `qs` nonce slots. `challengerG true` is a variant of the game that only the proof uses. The statements a reader has to trust are about `challenger`, which is `challengerG false`.

**Is the adversary restricted?** An `Adversary` is any function from coins of a finite type and the public key point to an oracle algorithm. It chooses all other public keys, all messages, all nonces of the other signers, the aggregate nonce and the tweaks, and it may leave sessions open and interleave them. It is not algebraic. The hypothesis `HashBound` bounds its random oracle queries, counting a single-party signing query once for every entry of its list. The game bounds the number of sessions and single-party signatures.

**Does the reduction cheat?** `reduction` has the type `OmdlAdversary`: it is an oracle algorithm for the AOMDL game and gets nothing else. It wins only if it makes fewer discrete logarithm queries than it received challenges, so the query count is part of the statement. The type does not rule out an algorithm that finds the logarithms by search without asking, and there is no cost model, so the body has to be read. `reduction` asks for its challenges and calls `reductionBody`. That runs the forger with `simChallenger` answering its queries, which asks at most one discrete logarithm query for a signing query (`simSign`). It takes the fork point from the forger's output, runs the forger a second time with the table changed at that point, asks at most two more queries for every session (`solveSessions`) and computes the secret key from the two forgeries with one division (`extractX`). Nothing in these definitions goes through scalars or points in search of one. `collider` is a function of a sample. It holds the secret key, runs the game twice (`gameRecs`) and goes through the pairs of session records of the two runs for a collision. It is marked noncomputable only because it decides classically whether two hash inputs are equal.

**What is random?** The secret key and the nonces are uniform nonzero scalars. In `unforgeable` and `unforgeable_sqrt` the challenge hash is a uniform table of scalars, on inputs with lists of at most `N` entries. `forgeAdvantage_eq_lazy` proves that the game has the same advantage when the oracle answers every new query with the next of `qh + qs + N` uniform scalars. The coins of `reduction` contain a whole table. `reductionLazy` takes `2·(qh + qs) + 1` scalars instead and wins the AOMDL game with the same probability (`omdlAdvantage_reduction_eq_lazy`). The sample of `collider` has a whole table as well, and `colliderLazy` finds a collision as often with `2·(qh + qs)` scalars (`collisionAdvantage_eq_lazy`). `unforgeable_sqrt_lazy_both` is the theorem with these two algorithms. In `nonceGen_unforgeable` the forger that the reduction runs has a whole table of `hash_BIP0459/nonce` in its coins (`withTable`). `nonceGen_unforgeable_lazy` and `nonceGenSk_unforgeable_lazy` are the statements for forgers that answer the queries to `hash_BIP0459/nonce` and `hash_BIP0459/aux` from `qn` and `qa` values in their coins, with `reductionLazy` and `colliderLazy`. The theorems for 32-byte values are stated this way. The framework has no cost model, so there is no statement about running time.

**How is the challenge hash reduced modulo `n`?** BIP 459 computes `c = int(hash(…)) mod n` from a 256-bit hash. In the game of `Dahlias/Hashed.lean` the oracle returns a uniform element of a type `H` of hash outputs. The adversary sees the outputs, and `Sign` and `Verify` turn them into scalars with `red`. `forgeAdvantageH_le` reduces this game to the one with scalar answers. The game reads at most `qh + qs + N` oracle values, and each is outside a fixed set of `n` outputs, one for every scalar, with probability `(|H| - n) / |H|`. For `H = {0, …, 2^256 - 1}` and `red h = h mod n` that is at most `2^-127` (`hash_gap`), and `bytes_unforgeable_256` is the theorem for secp256k1. `Dahlias/BindingHashed.lean` does the same for strong binding, where the game reads at most `qh + 2⋅N` oracle values (`strongly_binding_fin`, `bytes_strongly_binding_256`).

**What is the nonce coefficient hash?** A fixed function into the scalars, `nonceCoef`. The theorem holds for every such function and measures how often `collider` outputs a collision of it. This is the usual way to state collision resistance for an unkeyed hash function. BIP 459's `int(hash_BIP0459/noncecoef(…)) mod n` is such a function (`nonceCoef32`). `collision_bytes` proves that a collision of it is a pair of different byte strings whose tagged SHA-256 values are congruent modulo `n`, so equal or `n` apart. That includes the inputs with the point at infinity, which the game hashes for the nonce of a single-party signature: `cbytes` maps that point to `02 ‖ 0^32`, and no curve point has the x-coordinate `0` (`sq_ne_seven`).

**What does the single-party query add?** BIP 459 leaves open how a party that holds all keys of a list signs without running the protocol with itself, and says that the method sketched on the mailing list needs a security analysis. `signSingle` is that method: one nonce `r`, `R = r⋅G`, `s = ±r + Σ cᵢ⋅dᵢ`. The game offers it to the adversary next to the sessions, and `unforgeable_sqrt` covers it at the cost of `qs / (n - 1)`. The reduction cannot answer two such queries of one slot with the same nonce in its two runs, so it works with a variant in which the nonce is `r₁ + b⋅r₂` for a coefficient `b` derived from the list (`challengerG true`). `forgeAdvantage_le_derived` shows that the adversary cannot tell the variant from the game.

**Is the theorem vacuous?** `Dahlias/Examples.lean` has a forger that satisfies `HashBound` and wins with positive probability. `Dahlias/Secp256k1.lean` instantiates the theorem for secp256k1.

**Is the binding game the paper's?** `bindExperiment` is the paper's game SB with the random oracle of the unforgeability game: the adversary outputs two lists and one signature and wins if the lists differ and the signature verifies for both. The theorem counts the adversary's own oracle queries. The `2N` in the bound are the verifier's queries. It holds for groups of prime order, and `secp256k1_primeOrder` proves that secp256k1 is one.

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

## The paper's statements

The definitions and theorems of the DahLIAS paper next to the Lean ones. Page and figure numbers are those of the ePrint revision of 2026-05-09 ([2025/692](https://eprint.iacr.org/2025/692)). The revision of 2025-04-16 has the same statements and numbers the figures after the first one lower.

| Paper | Lean | Difference |
|---|---|---|
| The scheme, Fig. 7 (p. 20). Public keys and the nonce `R` are group elements. | `Dahlias/Basic.lean`, the algorithms of BIP 459 | Public keys and `R` are x-only, so `Sign` and `Verify` normalize to even y-coordinates. The paper draws the nonces from all scalars, and BIP 459's `Sign` fails on a zero nonce. |
| Correctness, Section 4.1 (p. 19): the scheme is `N²/2^λ`-correct. | `verify_honest` | Covered in part. If no signer's `Sign` fails, the signature verifies. No theorem bounds the probability that an honest `Sign` fails. |
| AOMDL game, Fig. 1 (p. 11). The challenges have nonzero discrete logarithms, and the adversary wins with fewer `ADLog` queries than challenges. | `omdlExperiment` | The same game, with at most `c` challenges. `unforgeable_sqrt_std` is the theorem for challenges with uniform discrete logarithms. |
| Collision resistance of `H_non`, Definition 2 and Fig. 2 (pp. 11 and 12), for a keyed family. | `collisionAdvantage` with `collider` | `nonceCoef` is one fixed function. The theorem measures how often an explicit algorithm finds a collision of it. |
| Tweaking schemes, Definition 5 and Lemma 1 (p. 22). A tweak is `(α, β)` with `β ≠ 0`, and `TweakPK(X, (α, β)) = g^α⋅X^β`. | `Tweak`, `Tweak.sk`, `tweakSK_affine` | The same tweaks, with x-only tweaked keys. Property P-3 of Definition 5, that two different tweaks with the same tweaked key reveal the secret key, does not hold for them (`not_collisionExtractable`). |
| Game co-EUF-CMA-TK, Fig. 5 (p. 17). | `forgeExperiment` | The game records `(L, pk̃, m)` with the tweaked x-only key, where the paper records `(L, τ, m)`. The signer cannot tell `τ` from `τ.neg` (`challengerG_close_neg`), so in the paper's game a signature under one would be a forgery under the other. A `Sign` call that fails leaves the session open and records nothing, where the paper closes the session and records the query. The adversary may also ask for single-party signatures (`challenger_single`). The game bounds the lists by `N`, which the paper does in the theorem. |
| Random oracle `H_sig`. | A uniform table of scalars on the inputs with lists of at most `N` entries | `forgeAdvantage_eq_lazy` is the lazily sampled form, and `unforgeable_sqrt_fin` has hash outputs that are reduced modulo `n`. |
| Local forking lemma, Lemma 2 (p. 24): `fork ≥ acc⋅(acc/q − 1/s)` for an oracle with at least `s` values. | `localFork_prob` | The same bound, for deterministic query algorithms and a uniform table. |
| Theorem 2 (p. 22). Its proof ends with `aomdl ≥ adv⋅(adv/q − 1/2^(λ−1)) − coll` (p. 34). | `unforgeable` | The same inequality with `1/n` for `1/2^(λ−1)`, for adversaries without single-party queries. Here `q = qh + qs + 1`. The paper's `q` counts the hash queries of its wrapped adversary, at most `qh + qs + N`. |
| Theorem 2, the bound: `adv ≤ sqrt(q⋅(aomdl + coll + 1/2^(λ−1)))`. | `unforgeable_sqrt`: `adv ≤ sqrt(q⋅(omdl + coll)) + q/n + qs/(n − 1)` | Both follow from the inequality above. The term `qs/(n − 1)` pays for the single-party signatures. |
| Theorem 2, the resources. `C` makes at most `2qs` `ADLog` queries and runs in time `2t_A + (6qs + 2N + 2)⋅t_exp`. `D` runs in time `2t_A + (8qs + 2N + 3)⋅t_exp`. | `reduction`, `collider` | The query count is covered: `reduction` gets `2qs + 1` challenges and wins only with fewer queries. Running time is not covered. `reductionLazy` and `colliderLazy` show that neither algorithm needs a table of exponential size. |
| The insecure variant of the check in `Sign'`, Section 4.2 (p. 21) and Appendix C (p. 44). | `ros_forgery` | The attack for `ℓ ≥ log₂ n` sessions, at the level of the signer's answers. |
| Game SB, Fig. 11, and Theorem 3 (p. 35): `adv ≤ qh²/2^λ`. | `bindExperiment`, `strongly_binding`: `adv ≤ (qh + 2N)²/n` | The Lean bound counts the `2N` oracle values that the verifier reads. |

## What the theorems do not say

- No theorem bounds running time. `reduction` runs the forger twice, which is visible in its definition. `reductionLazy` and `colliderLazy` show that neither algorithm of the theorem needs a table of exponential size.
- The game is for lists of at most `N` entries, with `N < n`.
- The nonces of the game are uniform. `nonceGen_unforgeable` and `nonceGenSk_advantage` derive them as `NonceGen` does, from a uniform `rand'` and with the hash functions of `NonceGen` as random oracles. `nonceGenCtr_advantage` and `bytes_nonceGenCtr_unforgeable_256` are for a `rand'` that is a public counter value, with the `sk` argument. Its counter values are distinct. The key that `NonceGen` gets in a slot is the signer's key or a key tweaked from it. That tweak is fixed before the game: the adversary chooses the tweak of every signing query, but not the key of `NonceGen`. No theorem says anything about another `rand'` that is not uniform.
- BIP 459's `NonceGen` fails if a derived nonce is zero (`nonceGen_eq`). The signer of the games with `NonceGen` uses the slot all the same. The error term for the reduction modulo `n` bounds the probability of such a slot.
- In the games with the byte interface (`Dahlias/BytesGame.lean`) three things are not byte arrays. The tweak of a signing query and of a forgery is a pair of scalars, since `Sign` has no tweak argument. A hash query is a tuple of 32-byte arrays and not the byte string that BIP 459 hashes. A single-party signature has no algorithm on bytes in BIP 459, so that query takes 32-byte messages. No theorem has a random oracle on byte strings.
- `hash_BIP0459/sig` is a random oracle on structured inputs with lists of at most `N` entries. SHA-256 on the bytes is a function of those inputs (`sigInput_injective`), and modelling it as a random function is the assumption.
- A single-party signature of the game is for a list of keys that are all tweaks `α + β⋅x`, `β ≠ 0`, of the one honest key. The theorem does not cover a party that signs alone for several unrelated secret keys.

## Machine checks

- `lake build` compiles every proof. It fails if the axioms of a result change (`Dahlias/Summary.lean`). The build sets `autoImplicit = false`, so a misspelled variable in a statement is an error and not a new implicit variable.
- `Dahlias/Summary.lean` also guards two inventories of the whole project, computed by the commands of `Dahlias/Audit.lean`. `#project_axioms` lists the axioms that the modules declare and that their declarations depend on, so an axiom that no result uses fails the build too. `#surface` lists the definitions behind the results, which is the last section of this file. The summary also guards the output of `#reading` for every main result, which is the table and the lists under [The main results](#the-main-results).
- `scripts/check.sh` reads every Lean file of the repository for `sorry`, axioms, unsafe code and compiled evaluation outside the test vector checks. It checks that the root module has only imports and the generated summary only guarded commands. It checks that every code block under [The statements](#the-statements) is in the sources word for word, and that `Dahlias/Summary.lean` checks the axioms of every theorem printed there and of every result in the README's tables. It finds a result by its full name, so a declaration with the same last name in another namespace does not count. It checks that the generated parts of this file are the ones `scripts/gen_review.py` prints, and that this file prints the statement of every main result.
- `scripts/check_selftest.sh` changes a copy of the sources in twelve ways, such as an axiom in the root module or in the summary, and checks that `scripts/check.sh` fails each time.
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

The statements of the main results and the definitions behind them, copied from the sources with their comments by `scripts/gen_review.py`. Proofs are left out.

Throughout, `n` is a prime, `E` is the group of curve points, `X` is the type of x-only encodings and `M` is the message type. `C : Curve n E X` is taproot-lean's curve interface, `nonceCoef` is the nonce coefficient hash, `N` bounds the length of a list and `qs` is the number of nonce slots.

Not printed here: the bodies of `reduction` and `collider` and what they call (`Dahlias/Proofs/Reduction.lean`, `Dahlias/Proofs/Game.lean`), and the definitions of taproot-lean at the commit pinned in `lakefile.toml`. The lists under [The main results](#the-main-results) name every definition of the project that a main result needs.

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

### Correctness

`Dahlias/Correctness.lean`. The statement holds for every choice of the hash functions.

```lean
/-- One signer of an honest session: secret key, message and secret nonce. -/
structure Signer (n : ℕ) (M : Type*) where
  sk : ZMod n
  m : M
  r₁ : ZMod n
  r₂ : ZMod n
```

```lean
/-- The signer's entry `(pk, m)` of the list `L`. -/
def Signer.pkm (C : Curve n E X) (σ : Signer n M) : X × M := (C.x (C.mulG σ.sk), σ.m)
```

```lean
/-- The signer's public nonce. -/
def Signer.pubnonce (C : Curve n E X) (σ : Signer n M) : PubNonce E :=
  (C.mulG σ.r₁, C.mulG σ.r₂)
```

```lean
/-- **An honest session produces a valid signature.** If every signer's
`Sign` succeeds on the list, the public nonces and the aggregate nonce from
`NonceAgg`, then the output of `SigAgg` passes `Verify`.

`Sign` fails for some signer exactly when a scalar is zero, two signers have
the same `R₂`, or a nonce sum is the point at infinity; for nonces drawn at
random this has negligible probability. -/
theorem verify_honest {signers : List (Signer n M)} {agg : PubNonce E} {psigs : List (ZMod n)}
    {sig : X × ZMod n}
    (hagg : nonceAgg (signers.map (Signer.pubnonce C)) = some agg)
    (hlen : psigs.length = signers.length)
    (hsign : ∀ (i : ℕ) (hi : i < signers.length),
      sign C.ops H (signers[i].r₁, signers[i].r₂) signers[i].sk signers[i].m agg
        (signers.map (Signer.pkm C)) (signers.map (Signer.pubnonce C)) = some (psigs[i]'(by omega)))
    (hsig : sigAgg C.ops H agg (signers.map (Signer.pkm C)) (signers.map (Signer.pubnonce C))
      psigs = some sig) :
    verify C.ops H (signers.map (Signer.pkm C)) sig = true
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

### The AOMDL game

`Dahlias/Security.lean`. The challenges have nonzero discrete logarithms.

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

`Dahlias/Unforgeability.lean` and `Dahlias/Proofs/Reduction.lean`. Of the reduction and the collision finder only the types are printed.

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

### Binding

`Dahlias/Binding.lean`, with the deterministic query algorithms of `Dahlias/QueryRun.lean`.

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

### Finding a disruptive signer

`Dahlias/Blame.lean`. The statements hold for every choice of the hash functions.

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

<!-- statements:end -->

<!-- definitions:begin -->

## Every definition behind the results

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
- `Dahlias/Tweaks.lean`: `Security.bipTweakSign`, `Security.Tweak.comp`, `Security.Tweak.neg`
- `Dahlias/Unforgeability.lean`: `Security.NoSingle`, `Security.collisionAdvantage`, `Security.instFintypeProdForallSigInZMod`
- `Dahlias/VectorData.lean`: `Vectors.nonceAggRows`, `Vectors.nonceGenRows`, `Vectors.partialSigVerifyRows`, `Vectors.signErrorRows`, `Vectors.signRows`, `Vectors.tweakRows`, `Vectors.verifyRows`
- `Dahlias/Vectors.lean`: `Vectors.checkNonceAgg`, `Vectors.checkNonceGen`, `Vectors.checkPartialSigVerify`, `Vectors.checkSign`, `Vectors.checkSignError`, `Vectors.checkTweak`, `Vectors.checkVerify`, `Vectors.hexList`, `Vectors.optHex`
- `Dahlias/Proofs/ForkGame.lean`: `Security.instFintypeProdForgeSampleZMod`, `Security.noncesOf`
- `Dahlias/Proofs/Game.lean`: `Security.H₀`, `Security.forkPoint`, `Security.signPost`, `Security.signPre`, `Security.treeChallenger`
- `Dahlias/Proofs/Reduction.lean`: `Security.CloseRec`, `Security.IsCollision`, `Security.KeyTerm`, `Security.SimState`, `Security.coefVec`, `Security.collider`, `Security.dlogPoint`, `Security.dlogRep`, `Security.evenLift`, `Security.extractX`, `Security.forkPointPub`, `Security.gameRecs`, `Security.getChals`, `Security.keyPoint`, `Security.keySign`, `Security.logChallenger`, `Security.ncHash`, `Security.reduction`, `Security.reductionBody`, `Security.signPrePub`, `Security.simChallenger`, `Security.simSign`, `Security.singleKeysPub`, `Security.singleTerms`, `Security.solveSession`, `Security.solveSessions`, `Security.CloseRec.ncIn`, `Security.CloseRec.point`, `Security.CloseRec.w`, `Security.Tweak.pk`

<!-- definitions:end -->
