# Reviewing dahlias-lean

Lean checks the proofs. A reviewer checks that the statements say what they should. Everything under `Dahlias/Proofs/` can stay unread, because a wrong proof does not compile. A wrong definition does.

## What to read

About 600 lines decide whether the results mean anything.

1. `Dahlias/Basic.lean`, all of it. Compare the algorithms with BIP 459. The header lists the modelling choices.
2. `Dahlias/Security.lean`, all of it: the unforgeability game, the AOMDL game, and the two places where the game differs from the paper's.
3. `Dahlias/Alg.lean`, the definitions `Alg`, `bind` and `run`, and `Dahlias/Prob.lean`, the definition `prob`.
4. `Dahlias/Unforgeability.lean`, the statement of `unforgeable` and the definition `collisionAdvantage`.
5. `Dahlias/Binding.lean`, the header, `bindExperiment` and the statement of `strongly_binding`.
6. `Dahlias/Proofs/Reduction.lean`, the types of `reduction` and `collider`.

taproot-lean supplies the curve interface (`Taproot.Curve`) and secp256k1. A full review reads those definitions too.

## Questions to ask

**Is the game the paper's?** `forgeExperiment` is the co-EUF-CMA-TK game of the DahLIAS paper (Fig. 5) with two changes and one addition. All three are described in the header of `Dahlias/Security.lean`.

- The game records the tweaked x-only public key of every signature, where the paper records the tweak. With x-only keys two different tweaks can give the same key without revealing anything: `(α, β)` and `(-α, -β)` always do. The paper's game would count a signature under one of them as a forgery under the other.
- A `Sign` call that fails leaves the session open. The paper closes it. The adversary here has more freedom.
- The adversary may also ask for single-party signatures: the honest signer signs a list of its own tweaked keys with one uniform nonce (`signSingle`, `challenger_single`). This is not in the paper. Sessions and single-party signatures share the `qs` nonce slots. `challengerG true` is a variant of the game that only the proof uses; the statements a reader has to trust are about `challenger`, which is `challengerG false`.

**Is the adversary restricted?** An `Adversary` is any function from coins of a finite type and the public key point to an oracle algorithm. It chooses all other public keys, all messages, all nonces of the other signers, the aggregate nonce and the tweaks, and it may leave sessions open and interleave them. It is not algebraic. The hypothesis `HashBound` bounds its random oracle queries, counting a single-party signing query once for every entry of its list; the number of sessions and single-party signatures is bounded by the game.

**Does the reduction cheat?** `reduction` has the type `OmdlAdversary`: it is an oracle algorithm for the AOMDL game and gets nothing else. It wins only if it makes fewer discrete logarithm queries than it received challenges, so the query count is part of the statement. `collider` is a function of a sample; it holds the secret key and runs the game by itself, which a collision finder may do.

**What is random?** The secret key and the session nonces are uniform nonzero scalars. The challenge hash is a uniform table on inputs with lists of at most `N` entries. `forgeAdvantage_eq_lazy` proves that the game has the same advantage when the oracle answers every new query with the next of `qh + qs + N` uniform scalars. The reduction's coins still contain a whole table. A reduction that samples lazily behaves the same by the same argument, but that is not proven for it, and the theorem has no notion of running time.

**What is the nonce coefficient hash?** A fixed function, `nonceCoef`. The theorem holds for every such function and measures how often `collider` outputs a collision of it. This is the usual way to state collision resistance for an unkeyed hash function.

**Is the theorem vacuous?** `Dahlias/Examples.lean` has a forger that satisfies `HashBound` and wins with positive probability. `Dahlias/Secp256k1.lean` instantiates the theorem for secp256k1.

**Is the binding game the paper's?** `bindExperiment` is the game of Fig. 11 with the random oracle of the unforgeability game: the adversary outputs two lists and one signature and wins if the lists differ and the signature verifies for both. The theorem counts the adversary's own oracle queries; the `2N` in the bound are the verifier's queries. It holds for groups of prime order.

**What does the bound say?** With `q = qh + qs + 1`, `unforgeable` states `adv * (adv / q - 1 / n) ≤ omdl + coll` for adversaries that ask for no single-party signatures (`NoSingle`). This is the bound of the paper's Theorem 2 up to the count of queries. `unforgeable_sqrt` holds for all adversaries: `adv ≤ sqrt (q * (omdl + coll)) + q / n + qs / (n - 1)`. The square root is the loss of the forking lemma, and `qs / (n - 1)` pays for the single-party signatures.

## What the theorem does not say

- No theorem bounds running time. `reduction` runs the forger twice; that is visible in its definition.
- The game is for lists of at most `N` entries, with `N < n`.
- In `bytes_unforgeable` public keys and messages are 32-byte arrays and the nonce coefficient hash is the BIP's. The public nonces stay curve points: the encoding of nonces as 66 bytes, the range checks on scalars and the length checks are outside the security statement. `Dahlias/Vectors.lean` runs the test vectors against the byte-level algorithms, `Dahlias/BytesCorrectness.lean` proves their correctness, and `scripts/fuzz.py` compares them with the Python reference and with libsecp256k1.
- In `unforgeable` nonces are uniform. `nonceGen_unforgeable` covers `NonceGen` without the optional `sk` argument: `rand` is uniform, the adversary chooses `extra_in`, and `hash_BIP0459/nonce` is a random oracle that the adversary can query. `nonceGenSk_advantage` adds the `sk` argument, `rand = sk xor hash_BIP0459/aux(rand')`, with `hash_BIP0459/aux` as a random oracle and `rand'` uniform. Both theorems assume uniform randomness. They say nothing about a `rand'` that is not uniform, which is the case the optional arguments exist for.

## Machine checks

- `lake build` compiles every proof and fails if the axioms of a main result change (`Dahlias/Summary.lean`).
- `scripts/check.sh` searches the sources for `sorry`, new axioms, unsafe code and stray `native_decide`.
- `lake env leanchecker Dahlias` replays every project module in the kernel, without the elaborator.
