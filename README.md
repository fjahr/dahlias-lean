# dahlias-lean

Lean 4 proofs about [BIP 459](https://github.com/bitcoin/bips/blob/master/bip-0459.mediawiki), DahLIAS fully aggregated signatures for secp256k1.

The main result is a machine-checked version of Theorem 2 of the [DahLIAS paper](https://eprint.iacr.org/2025/692) for the algorithms of BIP 459: the scheme is unforgeable in the concurrent setting with key tweaking, under the algebraic one-more discrete logarithm assumption (AOMDL), with the challenge hash as a random oracle and a collision resistant nonce coefficient hash.

`REVIEW.md` says what to read to check that the statements mean what they should.

## Results

| Theorem | File | Statement |
| --- | --- | --- |
| `unforgeable`, `secp256k1_unforgeable` | `Dahlias/Unforgeability.lean`, `Dahlias/Secp256k1.lean` | A forger with success probability `adv`, at most `qh` random oracle queries and `qs` signing sessions gives an AOMDL adversary and a collision finder with `adv * (adv / (qh + qs + 1) - 1 / n) ≤ omdl + coll`. |
| `localFork_prob` | `Dahlias/LocalFork.lean`, `Dahlias/Fork.lean` | The local forking lemma of Bellare, Dai and Li. |
| `verify_honest` | `Dahlias/Correctness.lean`, `Dahlias/BytesCorrectness.lean` | An honest session produces a signature that verifies, for the model and for the byte-level algorithms. |
| `verify_sigAgg_of_partialSigVerify` | `Dahlias/Correctness.lean` | Partial signatures that pass `PartialSigVerify` aggregate to a valid signature. |
| `tweakPK_mulG`, `tweakSK_affine` | `Dahlias/Correctness.lean`, `Dahlias/Tweaks.lean` | `TweakSK` and `TweakPK` agree, and BIP 459's tweaks are tweaks of the security game. |
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

Runs so far found no mismatch: 5,000 cases against the Lean model (seed 1) and about 23,400 compared cases against libsecp256k1 (seeds 21 to 23).

The three implementations treat a few malformed inputs differently. The script counts these cases separately and lists them at the end of a run:

- `Sign`, `SigAgg` and `GetSessionValues` as specified never decode the other signers' public keys or the first halves of their public nonces. `reference.py` and the C API take parsed objects, so they reject such inputs earlier. The Lean model follows the specification text.
- `NonceAgg` of an empty array fails in the specification and raises `IndexError` in `reference.py`.
- `Sign` as specified fails if a secret nonce scalar is zero or not below `n`. The C `secnonce` object is opaque, and `partial_sign` rejects only the all-zero nonce.

## License

MIT, see `LICENSE`.
