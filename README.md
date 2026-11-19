# dahlias-lean

Lean 4 proofs about [BIP 459](https://github.com/bitcoin/bips/blob/master/bip-0459.mediawiki), DahLIAS fully aggregated signatures for secp256k1.

The main result is a machine-checked version of Theorem 2 of the [DahLIAS paper](https://eprint.iacr.org/2025/692) for the algorithms of BIP 459: the scheme is unforgeable in the concurrent setting with key tweaking, under the algebraic one-more discrete logarithm assumption (AOMDL), with the challenge hash as a random oracle and a collision resistant nonce coefficient hash. Theorem 3 of the paper, strong binding, is proven as well.

`REVIEW.md` says what to read to check that the statements mean what they should.

## Results

| Theorem | File | Statement |
| --- | --- | --- |
| `unforgeable`, `unforgeable_sqrt`, `secp256k1_unforgeable` | `Dahlias/Unforgeability.lean`, `Dahlias/Secp256k1.lean` | A forger with success probability `adv`, at most `qh` random oracle queries and `qs` signing sessions gives an AOMDL adversary and a collision finder with `adv * (adv / q - 1 / n) ≤ omdl + coll` for `q = qh + qs + 1`, and so `adv ≤ sqrt (q * (omdl + coll)) + q / n`. |
| `strongly_binding`, `secp256k1_strongly_binding` | `Dahlias/Binding.lean`, `Dahlias/Secp256k1.lean` | An adversary with at most `qh` random oracle queries finds a signature that is valid for two different lists of at most `N` entries with probability at most `(qh + 2N)² / n`. |
| `bytes_unforgeable`, `bytes_strongly_binding` | `Dahlias/BytesSecurity.lean` | Both security theorems for secp256k1 with 32-byte public keys and messages and the BIP's nonce coefficient hash. `sign_val` and `verify_val` say that this instance runs the byte-level `Sign` and `Verify`. |
| `secp256k1_primeOrder` | `Dahlias/PrimeOrder.lean` | secp256k1 has exactly `n` points. |
| `localFork_prob` | `Dahlias/LocalFork.lean`, `Dahlias/Fork.lean` | The local forking lemma of Bellare, Dai and Li. |
| `verify_honest` | `Dahlias/Correctness.lean`, `Dahlias/BytesCorrectness.lean` | An honest session produces a signature that verifies, for the model and for the byte-level algorithms. |
| `verify_sigAgg_of_partialSigVerify` | `Dahlias/Correctness.lean` | Partial signatures that pass `PartialSigVerify` aggregate to a valid signature. |
| `prob_eval_eq_lazy`, `forgeAdvantage_eq_lazy` | `Dahlias/Lazy.lean`, `Dahlias/LazyGame.lean` | A uniform table is a lazily sampled oracle. The unforgeability game has the same advantage when every new challenge hash query gets the next of `qh + qs + N` uniform scalars. |
| `nonceGen_advantage`, `nonceGen_unforgeable` | `Dahlias/NonceGen.lean` | The game in which the signer derives its nonces as in `NonceGen`, with `hash_BIP0459/nonce` as a second random oracle. The adversary gains at most `qs²/|Rnd| + qs·qn/|Rnd| + 2·qs·(|W| - (n - 1))/|W|` over the game with uniform nonces. |
| `verify_signSingle`, `sigAgg_eq_signSingle` | `Dahlias/Single.lean` | Signing by a single party that holds all keys, with one nonce: the output verifies and equals the protocol's signature for the same nonce `R`. |
| `tweakPK_mulG`, `tweakSK_affine` | `Dahlias/Correctness.lean`, `Dahlias/Tweaks.lean` | `TweakSK` and `TweakPK` agree, and BIP 459's tweaks are tweaks of the security game. |
| `evenScalar_of_nonce_reuse`, `evenScalar_of_three_sessions`, `msgSwap_wins` | `Dahlias/Attacks.lean` | Reusing a secret nonce reveals the secret key, and without the message check in `Sign` a coordinator can make the signer sign any message. |
| `ros_bits`, `ros_forgery` | `Dahlias/Ros.lean` | The ROS attack: if `Sign` only checked that the combination of public key, message and `R2` is unique, `ℓ ≥ log₂ n` concurrent sessions would give a forgery. |
| test vectors | `Dahlias/Vectors.lean` | All 60 rows of the seven vector files of `bip-0459/vectors`. |

`Dahlias/Summary.lean` prints the axioms of every result. The theorems use Lean's three standard axioms. The test vectors and the statements about secp256k1 also use compiled evaluation (`native_decide`).

## Layout

- `Dahlias/Basic.lean`: the algorithms of BIP 459.
- `Dahlias/Bytes.lean`: the algorithms on byte arrays, with the BIP's encodings, range checks and SHA-256 tagged hashes.
- `Dahlias/Security.lean`: the unforgeability game and the AOMDL game.
- `Dahlias/Alg.lean`, `Dahlias/QueryRun.lean`, `Dahlias/Prob.lean`: deterministic oracle algorithms and probabilities on finite sample spaces.
- `Dahlias/Proofs/`: the proof of `unforgeable`.
- `Dahlias/Examples.lean`: a forger that wins the game by guessing the key, as a check that the definitions are not vacuous.

The curve, SHA-256 and BIP 340 come from [taproot-lean](https://github.com/dni/taproot-lean). The security proof depends only on Mathlib and on taproot-lean's curve interface.

## Build

```sh
lake exe cache get
lake build
scripts/check.sh
lake env leanchecker Dahlias
```

The toolchain is Lean v4.34.1 with Mathlib v4.34.1. The first build compiles the dependencies that have no cache and takes a while.

`Dahlias/VectorData.lean` is generated:

```sh
python3 scripts/gen_vectors.py path/to/bips/bip-0459/vectors > Dahlias/VectorData.lean
```

## Differential testing

`scripts/fuzz.py` generates honest signing sessions and malformed variants of every input, takes BIP 459's `reference.py` as the reference, and runs the same inputs through the Lean model (`scripts/Fuzz.lean`) and optionally through libsecp256k1's `fullagg` module (`scripts/fuzz_secp256k1.c`).

```sh
python3 scripts/fuzz.py path/to/bips/bip-0459 --cases 5000 --seed 1
```

For libsecp256k1, build the library with the module and compile the driver:

```sh
cmake -S path/to/secp256k1 -B build -DBUILD_SHARED_LIBS=OFF \
  -DSECP256K1_EXPERIMENTAL=ON -DSECP256K1_ENABLE_MODULE_FULLAGG=ON
cmake --build build
cc -O2 -Ipath/to/secp256k1/include scripts/fuzz_secp256k1.c build/lib/libsecp256k1.a -o fuzz_secp256k1
python3 scripts/fuzz.py path/to/bips/bip-0459 --no-lean --secp256k1 ./fuzz_secp256k1 --cases 12000
```

The C API cannot express fields of the wrong length. The driver skips those cases, about one in eight.

With `--secp256k1` the script also tests the state that only the C API keeps. It signs twice with the same `secnonce` object and expects the second call to fail, and it signs with lists that differ from the ones the session was initialized with, which must fail unless both sets of lists give the same nonce coefficient input.

Runs so far found no mismatch: 5,000 cases against the Lean model (seed 1) and about 23,400 compared cases against libsecp256k1 (seeds 21 to 23).

The three implementations treat a few malformed inputs differently. The script counts these cases separately and lists them at the end of a run:

- `Sign`, `SigAgg` and `GetSessionValues` as specified never decode the other signers' public keys or the first halves of their public nonces. `reference.py` and the C API take parsed objects, so they reject such inputs earlier. The Lean model follows the specification text.
- `NonceAgg` of an empty array fails in the specification and raises `IndexError` in `reference.py`.
- `Sign` as specified fails if a secret nonce scalar is zero or not below `n`. The C `secnonce` object is opaque, and `partial_sign` rejects only the all-zero nonce.

## Exhaustive test for the C module

`patches/secp256k1-fullagg-exhaustive-tests.patch` adds a test of the `fullagg` module to libsecp256k1's exhaustive tests, which run the library on a group of order 13 or 199. It applies to the fork's branch `2026-11-half-full-agg` at commit `1f06bdf1`.

The test runs signing sessions of one and two signers for all secret nonces and compares every step with the value computed on discrete logarithms:

- `NonceAgg` fails exactly if an aggregate nonce is the point at infinity.
- `GetSessionValues` fails exactly if `R = R1 + b⋅R2` is the point at infinity.
- `Sign` fails exactly if another signer has the same `R2`.
- Otherwise the partial signature is `e⋅(r1 + b⋅r2) + c⋅d'`, it is the only value `PartialSigVerify` accepts, and the sum of the partial signatures is the only `s` for which `Verify` accepts `(x(R), s)`.

These are the failure conditions of the Lean model (`Dahlias/Basic.lean`) and the statements of `Dahlias/Correctness.lean`. In a group of order 13 the failure cases, which never occur by chance on secp256k1, happen in more than a quarter of the two-signer sessions.

```sh
git -C path/to/secp256k1 apply path/to/dahlias-lean/patches/secp256k1-fullagg-exhaustive-tests.patch
cmake -S path/to/secp256k1 -B build -DSECP256K1_EXPERIMENTAL=ON \
  -DSECP256K1_ENABLE_MODULE_FULLAGG=ON -DSECP256K1_BUILD_EXHAUSTIVE_TESTS=ON
cmake --build build
build/bin/exhaustive_tests
```

The test passes on the groups of order 13 and 199. On order 13 the whole exhaustive suite takes about 13 seconds with it. On order 199 the new test alone takes about 8 seconds; there it tries all secret nonces of one signer and all pairs of second nonces of two signers, with random keys and first nonces. The order is a compile-time constant of `src/tests_exhaustive.c` (`-DEXHAUSTIVE_TEST_ORDER=199` for that file only), and the rest of the suite is slow on that group.

Five mutations of the expected values (ignoring a duplicate `R2`, an infinite aggregate nonce or an infinite `R`, the sign of `R`, and accepting a second `s`) each make the test fail.

## License

MIT, see `LICENSE`.
