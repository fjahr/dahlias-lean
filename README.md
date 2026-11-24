# dahlias-lean

Lean 4 proofs about [BIP 459](https://github.com/bitcoin/bips/blob/master/bip-0459.mediawiki), DahLIAS fully aggregated signatures for secp256k1.

The main result is a machine-checked version of Theorem 2 of the [DahLIAS paper](https://eprint.iacr.org/2025/692) for the algorithms of BIP 459: the scheme is unforgeable in the concurrent setting with key tweaking, under the algebraic one-more discrete logarithm assumption (AOMDL), with the challenge hash as a random oracle and a collision resistant nonce coefficient hash. Theorem 3 of the paper, strong binding, is proven as well.

`REVIEW.md` says what to read to check that the statements mean what they should.

## Results

| Theorem | File | Statement |
| --- | --- | --- |
| `unforgeable`, `unforgeable_sqrt`, `secp256k1_unforgeable` | `Dahlias/Unforgeability.lean`, `Dahlias/Secp256k1.lean` | A forger with success probability `adv`, at most `qh` random oracle queries and `qs` signing sessions gives an AOMDL adversary and a collision finder with `adv * (adv / q - 1 / n) ≤ omdl + coll` for `q = qh + qs + 1`. If the forger may also ask the signer for single-party signatures, `adv ≤ sqrt (q * (omdl + coll)) + q / n + qs / (n - 1)`. |
| `omdlAdvantage_le_std`, `unforgeable_sqrt_std` | `Dahlias/OmdlStd.lean` | The main theorem under the usual AOMDL assumption, whose challenges have uniform discrete logarithms. The game here draws them from the nonzero scalars, which costs at most `c / n` for `c` challenges. |
| `strongly_binding`, `secp256k1_strongly_binding` | `Dahlias/Binding.lean`, `Dahlias/Secp256k1.lean` | An adversary with at most `qh` random oracle queries finds a signature that is valid for two different lists of at most `N` entries with probability at most `(qh + 2N)² / n`. |
| `bytes_unforgeable`, `bytes_strongly_binding` | `Dahlias/BytesSecurity.lean` | Both security theorems for secp256k1 with 32-byte public keys and messages and the BIP's nonce coefficient hash. `sign_val` and `verify_val` say that this instance runs the byte-level `Sign` and `Verify`. |
| `strongly_binding_fin`, `bytes_strongly_binding_256` | `Dahlias/BindingHashed.lean`, `Dahlias/BytesSecurity.lean` | Strong binding with the challenge hash as BIP 459 computes it. The 256-bit oracle costs at most `(qh + 2N) / 2^127` on top of the bound. |
| `unforgeable_sqrt_fin`, `bytes_unforgeable_256`, `hash_gap` | `Dahlias/Hashed.lean`, `Dahlias/BytesSecurity.lean` | The same with the challenge hash as BIP 459 computes it. The random oracle has 256-bit outputs, which the adversary sees and `Sign` and `Verify` reduce modulo `n`. This costs at most `(qh + qs + N) / 2^127`. |
| `sigInput_injective`, `nonceCoefInput_injective`, `collision_bytes`, `cpoint_eq_some_iff`, `matchIdxs_bytes`, `sign_bytes`, `verify_bytes`, `nonceGen_eq`, `nonceGen_sk_eq`, `nonceInput_injective`, `hashes_sig_eq_redFin` | `Dahlias/Encoding.lean` | The byte encodings lose nothing. The hash inputs determine the structured inputs, so a collision of the nonce coefficient hash is a pair of different byte strings with tagged SHA-256 hashes that are congruent modulo `n`. No point has two encodings, and `Sign` and `Verify` on bytes are those of the instance of `bytes_unforgeable`. `NonceGen` on bytes derives the secret nonces as the games with `NonceGen` do, with the tagged hashes as the oracles and the byte-wise xor as the mask. SHA-256 has 32 bytes of output, so the challenge hash is a 256-bit value reduced modulo `n`. |
| `n_smul_G`, `secp256k1F` | `Dahlias/OrderG.lean`, `Dahlias/OrderCert.lean` | The generator of secp256k1 has order `n`. The kernel checks a certificate, a double-and-add chain with every slope and intermediate point written out, so no theorem depends on compiled code. `secp256k1F` is secp256k1 as the curve interface with this proof. |
| `secp256k1_primeOrder` | `Dahlias/PrimeOrder.lean` | secp256k1 has exactly `n` points. |
| `localFork_prob` | `Dahlias/LocalFork.lean`, `Dahlias/Fork.lean` | The local forking lemma of Bellare, Dai and Li. |
| `verify_honest` | `Dahlias/Correctness.lean`, `Dahlias/BytesCorrectness.lean` | An honest session produces a signature that verifies, for the model and for the byte-level algorithms. |
| `partialSigVerify_iff_eq_sign`, `exists_partialSigVerify_eq_false`, `verify_eq_false_of_one_bad` | `Dahlias/Blame.lean` | `PartialSigVerify` finds a disruptive signer. At an honest signer's index only the partial signature that `Sign` returns passes. An invalid aggregate signature has a partial signature that fails, and one bad partial signature among good ones makes the aggregate signature invalid. |
| `verify_sigAgg_of_partialSigVerify` | `Dahlias/Correctness.lean` | Partial signatures that pass `PartialSigVerify` aggregate to a valid signature. |
| `grinder_advantage`, `grinder_advantage_ge` | `Dahlias/Tightness.lean` | The additive term of the bound is needed. A forger with `q` random oracle queries and no signing queries wins with probability at least `1 - ((n - 1) / n)^q`, which is at least `q / (n + q)`. |
| `prob_eval_eq_lazy`, `forgeAdvantage_eq_lazy`, `omdlAdvantage_reduction_eq_lazy`, `collisionAdvantage_eq_lazy`, `unforgeable_sqrt_lazy_both` | `Dahlias/Lazy.lean`, `Dahlias/LazyGame.lean`, `Dahlias/LazyReduction.lean`, `Dahlias/LazyCollider.lean` | A uniform table is a lazily sampled oracle. The unforgeability game has the same advantage when every new challenge hash query gets the next of `qh + qs + N` uniform scalars. The reduction has the same advantage when it answers the forger's queries from `2·(qh + qs) + 1` uniform scalars instead of a table, and the collision finder with `2·(qh + qs)`. |
| `nonceGen_advantage`, `nonceGen_unforgeable`, `nonceGenSk_advantage` | `Dahlias/NonceGen.lean`, `Dahlias/NonceGenSk.lean` | The game in which the signer derives its nonces as in `NonceGen`, with `hash_BIP0459/nonce` as a second random oracle and an `extra_in` that the adversary chooses. The adversary gains at most `qs²/|Rnd| + qs·qn/|Rnd| + 2·qs·(|W| - (n - 1))/|W|` over the game with uniform nonces. With the optional `sk` argument and `hash_BIP0459/aux` as a third random oracle it gains at most `qs²/|Rp| + qs·qa/|Rp|` more, for the signer's key or a tweaked key of the slot as `sk`. |
| `nonceGenSk_unforgeable_fin`, `nonceGen_unforgeable_fin`, `bytes_nonceGenSk_unforgeable_256`, `bytes_nonceGen_unforgeable_256` | `Dahlias/NonceGenHashed.lean`, `Dahlias/NonceGenLazy.lean`, `Dahlias/BytesSecurity.lean` | One game with all of it. The signer derives its nonces as in `NonceGen`, with or without the `sk` argument, and the challenge hash has 256-bit outputs that the adversary sees and `Sign` and `Verify` reduce modulo `n`. The bound is the one of `unforgeable_sqrt` plus the error terms of the oracles, and the forger, the reduction and the collision finder in it sample all random oracles lazily. The last two theorems state it for secp256k1 with 32-byte keys, messages, `rand'` and `rand` and the BIP's nonce coefficient hash. |
| `nonceGenCtr_advantage`, `nonceGenCtr_unforgeable_fin`, `bytes_nonceGenCtr_unforgeable_256` | `Dahlias/NonceGenCounter.lean`, `Dahlias/BytesSecurity.lean` | `NonceGen` with the secret key and a counter in place of the random value `rand'`, as `secp256k1_fullagg_nonce_gen_counter` runs it. The counter values are public and distinct, so only the secret key hides `rand`. The nonces are still fresh unless the adversary queries the nonce hash at a `rand`, and a `rand` gives the secret key. So the adversary wins at most as often as it and a forger that recovers the key (`keyForger`) together win the game with uniform nonces, plus `qs²/2^256` and the terms for the reduction modulo `n`. The last theorem states it for 32-byte values, 256-bit hashes and `rand = bytes(d) xor hash_BIP0459/aux(counter)`, where `d` is the key that `NonceGen` gets in the slot: the signer's key or a key tweaked from it by a tweak that is fixed before the game. |
| `verify_signSingle`, `sigAgg_eq_signSingle`, `challenger_single`, `forgeAdvantage_le_derived` | `Dahlias/Single.lean`, `Dahlias/SingleGame.lean`, `Dahlias/Derived.lean` | Signing by a single party that holds all keys, with one nonce: the output verifies and equals the protocol's signature for the same nonce `R`. The unforgeability game offers these signatures to the adversary, and `unforgeable_sqrt` covers them. |
| `tweakPK_mulG`, `tweakSK_affine` | `Dahlias/Correctness.lean`, `Dahlias/Tweaks.lean` | `TweakSK` and `TweakPK` agree, and BIP 459's tweaks are tweaks of the security game. |
| `evenScalar_of_nonce_reuse`, `evenScalar_of_three_sessions`, `msgSwap_wins` | `Dahlias/Attacks.lean` | Reusing a secret nonce reveals the secret key, and without the message check in `Sign` a coordinator can make the signer sign any message. |
| `ros_bits`, `ros_forgery` | `Dahlias/Ros.lean` | The ROS attack: if `Sign` only checked that the combination of public key, message and `R2` is unique, `ℓ ≥ log₂ n` concurrent sessions would give a forgery. |
| test vectors | `Dahlias/Vectors.lean` | All 60 rows of the seven vector files of `bip-0459/vectors`. |

`Dahlias/Summary.lean` prints the axioms of every result. The theorems, including those about secp256k1, use Lean's three standard axioms. Only the test vector checks also use compiled evaluation (`native_decide`).

## Layout

- `Dahlias/Basic.lean`: the algorithms of BIP 459.
- `Dahlias/Bytes.lean`: the algorithms on byte arrays, with the BIP's encodings, range checks and SHA-256 tagged hashes. `Dahlias/Encoding.lean`: what the encodings preserve.
- `Dahlias/OrderG.lean`, `Dahlias/OrderCert.lean`: the order of secp256k1's generator, from a certificate that the kernel checks.
- `Dahlias/Security.lean`: the unforgeability game and the AOMDL game.
- `Dahlias/Alg.lean`, `Dahlias/QueryRun.lean`, `Dahlias/Prob.lean`: deterministic oracle algorithms and probabilities on finite sample spaces.
- `Dahlias/Proofs/`: the reduction to AOMDL, for the game in which a single-party signature uses a derived nonce.
- `Dahlias/Derived.lean`: from that game to the game with a uniform nonce.
- `Dahlias/OmdlStd.lean`: the AOMDL game with uniform challenges.
- `Dahlias/Lazy.lean`, `Dahlias/Second.lean`, `Dahlias/NonceProb.lean`: lazily sampled oracles, algorithms with a second oracle, and the counting lemmas for oracle values at secret points.
- `Dahlias/NonceGen.lean`, `Dahlias/NonceGenSk.lean`: the game with nonces derived as in `NonceGen`.
- `Dahlias/NonceGenHashed.lean`: that game with a challenge hash that returns hash outputs.
- `Dahlias/NonceGenLazy.lean`: its security theorems with lazily sampled random oracles.
- `Dahlias/NonceGenCounter.lean`: `NonceGen` with the secret key and a counter in place of the random value.
- `Dahlias/LazyReduction.lean`, `Dahlias/LazyCollider.lean`: the reduction and the collision finder with a lazily sampled random oracle.
- `Dahlias/Hashed.lean`, `Dahlias/BindingHashed.lean`: the games with hash outputs that are reduced modulo `n`.
- `Dahlias/Examples.lean`: a forger that wins the game by guessing the key, as a check that the definitions are not vacuous.
- `Dahlias/Tightness.lean`: a forger that shows the additive term of the bound is needed.
- `Dahlias/Blame.lean`: `PartialSigVerify` finds a disruptive signer.

The curve, SHA-256 and BIP 340 come from [taproot-lean](https://github.com/dni/taproot-lean). The security proof depends only on Mathlib and on taproot-lean's curve interface.

## Build

```sh
lake exe cache get
lake build
scripts/check.sh
scripts/replay.sh
```

The toolchain is Lean v4.34.1 with Mathlib v4.34.1. The first build compiles the dependencies that have no cache and takes a while.

`Dahlias/VectorData.lean`, `Dahlias/OrderCert.lean` and the last section of `REVIEW.md` are generated:

```sh
python3 scripts/gen_vectors.py path/to/bips/bip-0459/vectors > Dahlias/VectorData.lean
python3 scripts/gen_order_cert.py > Dahlias/OrderCert.lean
python3 scripts/gen_review.py
```

## Differential testing

`scripts/fuzz.py` generates honest signing sessions and malformed variants of every input, takes BIP 459's `reference.py` as the reference, and runs the same inputs through the Lean model (`scripts/Fuzz.lean`) and optionally through libsecp256k1's `fullagg` module (`scripts/fuzz_secp256k1.c`).

```sh
python3 scripts/fuzz.py path/to/bips/bip-0459 --cases 5000 --seed 1
```

For libsecp256k1, build the library with the module and compile the driver. The results in this file are for commit [`5f0e6926`](https://github.com/bitcoin-core/secp256k1/pull/1754/commits/5f0e692687181510d244ef8b561a144338f2cda1), the head of [bitcoin-core/secp256k1#1754](https://github.com/bitcoin-core/secp256k1/pull/1754) on 2026-11-20:

```sh
cmake -S path/to/secp256k1 -B build -DBUILD_SHARED_LIBS=OFF \
  -DSECP256K1_EXPERIMENTAL=ON -DSECP256K1_ENABLE_MODULE_FULLAGG=ON
cmake --build build
cc -O2 -Ipath/to/secp256k1/include scripts/fuzz_secp256k1.c build/lib/libsecp256k1.a -o fuzz_secp256k1
python3 scripts/fuzz.py path/to/bips/bip-0459 --no-lean --secp256k1 ./fuzz_secp256k1 --cases 12000
```

The C API cannot express fields of the wrong length. The driver skips those cases, about one in eight.

With `--secp256k1` the script also tests the state that only the C API keeps. It signs twice with the same `secnonce` object and expects the second call to fail. It signs with a `secnonce` object made for another public key, which must fail. And it signs with lists that differ from the ones the session was initialized with, which must fail unless both sets of lists give the same nonce coefficient input.

Runs so far found no mismatch. The latest were 6,600 cases with seed 31 against libsecp256k1, of which the script compared 5,901, and 3,000 cases with seed 20261120 against the Lean model. CI runs 300 cases against the Lean model and 3,000 against libsecp256k1 on every push, with a new seed each time.

The three implementations treat a few malformed inputs differently. The script counts these cases separately and lists them at the end of a run:

- `Sign`, `SigAgg` and `GetSessionValues` as specified never decode the other signers' public keys or the first halves of their public nonces. `reference.py` and the C API take parsed objects, so they reject such inputs earlier. The Lean model follows the specification text.
- `NonceAgg` of an empty array fails in the specification and raises `IndexError` in `reference.py`.
- `Sign` as specified fails if a secret nonce scalar is zero or not below `n`. The C `secnonce` object is opaque, and `partial_sign` rejects only the all-zero nonce.
- `NonceGen` as specified xors any 32 bytes given as `sk`. `reference.py` takes a scalar, and the C API rejects a secret key that is zero or not below `n`.

## Exhaustive test for the C module

`patches/secp256k1-fullagg-exhaustive-tests.patch` adds a test of the `fullagg` module to libsecp256k1's exhaustive tests, which run the library on a group of order 13 or 199. It applies to the commit named above.

The test runs signing sessions of one, two and three signers and compares every step with the value computed on discrete logarithms:

- `NonceAgg` fails exactly if an aggregate nonce is the point at infinity.
- `GetSessionValues` fails exactly if `R = R1 + b⋅R2` is the point at infinity.
- In both cases `PartialSigVerify` rejects every partial signature.
- `Sign` fails exactly if another signer has the same `R2`. A signer with the negation of that `R2` does not make it fail, which takes three signers to test, because two such nonces cancel in `NonceAgg`.
- Otherwise the partial signature is `e⋅(r1 + b⋅r2) + c⋅d'`, it is the only value `PartialSigVerify` accepts, and the sum of the partial signatures is the only `s` for which `Verify` accepts `(x(R), s)`.

These are the failure conditions of the Lean model (`Dahlias/Basic.lean`) and the statements of `Dahlias/Correctness.lean`. In a group of order 13 the failure cases, which never occur by chance on secp256k1, happen in more than a quarter of the two-signer sessions.

```sh
git -C path/to/secp256k1 apply path/to/dahlias-lean/patches/secp256k1-fullagg-exhaustive-tests.patch
cmake -S path/to/secp256k1 -B build -DSECP256K1_EXPERIMENTAL=ON \
  -DSECP256K1_ENABLE_MODULE_FULLAGG=ON -DSECP256K1_BUILD_EXHAUSTIVE_TESTS=ON
cmake --build build
build/bin/exhaustive_tests
```

The test passes on the groups of order 13 and 199. On order 13 the whole exhaustive suite takes about 15 seconds with it. On order 199 the new test alone takes about 26 seconds. There it tries all secret nonces of one signer, and all pairs of second nonces of two signers and of the first two of three signers, with the other values random. The order is a compile-time constant of `src/tests_exhaustive.c` (`-DEXHAUSTIVE_TEST_ORDER=199` for that file only), and the rest of the suite is slow on that group.

Of the 57 mutants of the C module in the next section, the exhaustive tests notice 26.

## Mutation test of the C module

`scripts/mutate_secp256k1.py` makes 57 small changes to `src/modules/fullagg/main_impl.h`, one at a time: a check dropped, a hash input left out or swapped, a sign wrong. For each mutant it asks three sets of tests whether they notice:

- the module's 12 unit tests, which include BIP 459's test vectors,
- the cases of `scripts/fuzz.py`, where it compares the mutant's output with the unmutated library's,
- the exhaustive tests on the group of order 13, with the patch above.

```sh
python3 scripts/mutate_secp256k1.py path/to/secp256k1 path/to/bips/bip-0459
```

The script works on an export of the checkout's `HEAD` in a temporary directory and takes about 25 minutes.

At the commit named above, with 3,300 cases (seed 7), the three sets together notice 56 of the 57 mutants. The survivor is `verify` reducing an `r ≥ p` modulo `p` where it should reject. A test for it needs a valid signature whose `R` has an x-coordinate below `2^256 - p`.

Only the exhaustive tests notice three mutants: `session_init` or `partial_sig_verify` accepting an `R` at infinity, and `verify` reducing an `s ≥ n` modulo `n`. On secp256k1 a test would need one particular hash output, or a valid signature with `s < 2^256 - n`.

The unit tests alone miss 12 mutants: those four and the following eight.

| Mutant | Why the unit tests pass |
|---|---|
| `nonce_gen` accepts a secret key that is zero or not below `n` | No test calls it with such a key. |
| `partial_sign` accepts a `secnonce` made for another public key | No test tries. |
| `partial_sign` accepts lists in which the signer's `R2` appears twice | The vector "Signer's R2 appears at two indices" is run with the signer at index 0. The code remembers the last index with that `R2` and also compares it with the signer's, so the second check fails for this vector. |
| `partial_sign` accepts the signer's `R2` at another index than the signer's | No test has it only there. |
| `partial_sign` compares `R2` by x-coordinate only | No test has another signer with the negation of the signer's `R2`. With two signers `NonceAgg` fails on such nonces, so the case needs three. |
| `partial_sig_agg` accepts a number of partial signatures other than the session's | No test tries. BIP 459 has no test vectors for `SigAgg`. |
| `partial_sig_parse` accepts a value not below `n` | No test tries. |
| `verify` accepts an empty list | The signature of the vector "Empty signer list" does not satisfy `s⋅G = R`, so `verify` rejects it with or without the check. |

The cases of `scripts/fuzz.py` notice all eight. Four mutants are noticed by the unit tests only, in `api_tests`: `nonce_gen` accepting an all-zero `rand'` or not clearing it, `session_init` accepting empty lists, and `partial_sign` not comparing the number of signers with the session. The driver never makes those calls.

## License

MIT, see `LICENSE`.
