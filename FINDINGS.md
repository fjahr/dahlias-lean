# What the work found

Writing the Lean model of BIP 459, proving the theorems and testing the reference code and the C module against the model turned up the points below. Each one names its evidence and a change that would settle it. None of them is a way to forge a signature or to learn a key.

The BIP text, the test vectors and `reference.py` are those of bitcoin/bips at commit [`f3d1668`](https://github.com/bitcoin/bips/tree/f3d1668891fcdad99770245110bc6a22c87bce97/bip-0459), which is the state of its master branch on 2026-11-26. The C module is [bitcoin-core/secp256k1#1754](https://github.com/bitcoin-core/secp256k1/pull/1754) at commit [`5f0e6926`](https://github.com/bitcoin-core/secp256k1/pull/1754/commits/5f0e692687181510d244ef8b561a144338f2cda1). The paper is the ePrint revision of 2026-05-09 of [2025/692](https://eprint.iacr.org/2025/692). On 2026-11-26 none of the proposed changes had been submitted.

## The security claim

| | Finding | Evidence | Proposed change |
|---|---|---|---|
| 1 | The paper's proof is for public keys that are group elements, and BIP 459's are x-only. BIP 459 says the scheme is proven secure "including when signers use key tweaking". The paper proves that for tweaking schemes in which two different tweaks with the same tweaked public key reveal the secret key (Definition 5, property P-3, used in the proof of Theorem 2 on p. 30). With x-only keys the tweaks `(α, β)` and `(-α, -β)` give the same public key and the same partial signatures for every secret key, so no such extraction exists. The paper's game records tweaks and would count a signature under one of the two as a forgery under the other. | `Tweak.xonly_neg`, `sign_neg`, `challengerG_close_neg`, `not_collisionExtractable`. The game of the Lean theorems records the tweaked x-only key, and `unforgeable_sqrt` is proven for it. | None to the algorithms. The Security section can say that the claim for x-only keys is about the game that records tweaked keys. |
| 2 | Signing alone with all keys has a security analysis. BIP 459 leaves out an optimized algorithm for a single party that knows all secret keys, because the method outlined on the mailing list "requires additional security analysis before it can be specified". | `signSingle` is that method. The unforgeability game offers it to the adversary next to the sessions, and `unforgeable_sqrt` covers it at the cost of `qs/(n − 1)` (`challenger_single`, `forgeAdvantage_le_derived`). It gives the protocol's signature for the same `R` (`sigAgg_eq_signSingle`). The analysis is for lists in which every key is a tweak of the one honest key. | The remark in the Rationale can cite the analysis. Whether to specify the algorithm is a separate decision. |

## The specification and `reference.py`

| | Finding | Evidence | Proposed change |
|---|---|---|---|
| 3 | `NonceAgg` of an empty array fails in the specification, where both sums are the point at infinity. `reference.py` raises `IndexError` at `pubnonces[0]`. | `scripts/fuzz.py`, the cases counted as `empty-nonceagg`. | Fail as the other cases do, and add a test vector. |
| 4 | `GetSessionValues` with `R` at infinity. The specification says "Fail if is_infinite(R)". `reference.py` has `assert not R.infinity`, which raises another error than the other failures and none under `python -O`. No input reaches it by chance on secp256k1. | The line in `reference.py`. The exhaustive tests reach the case in the C module on a group of order 13. | Raise the error of the other failures. |
| 5 | `Sign`, `SigAgg` and `GetSessionValues` as specified never decode the other signers' public keys or the first halves of their public nonces. `reference.py` and the C API take parsed objects and reject such inputs earlier. | `scripts/fuzz.py`, the cases counted as `lazy-pk` and `lazy-r1`. The Lean model follows the specification text. | Decide which behaviour is meant and state it in the specification. |
| 6 | `NonceGen` as specified xors any 32 bytes given as `sk`. `reference.py` takes a scalar, and the C API rejects a secret key that is zero or not below `n`. | `scripts/fuzz.py`, the cases counted as `noncegen-sk`. | State the range of `sk` in the specification. |

## The test vectors

| | Finding | Evidence | Proposed change |
|---|---|---|---|
| 7 | There are no test vectors for `SigAgg`. | The C mutant in which `partial_sig_agg` accepts a wrong number of partial signatures passes the module's unit tests. | A vector file for `SigAgg`. |
| 8 | The `Verify` vector "Empty signer list" does not need the check it is there for. Its signature does not satisfy `s⋅G = R`, so a verifier without the check rejects it as well. | The C mutant in which `verify` accepts an empty list passes the unit tests. | A signature with `s⋅G = R` in that vector. |
| 9 | No vector has another signer whose `R₂` is the negation of the signer's `R₂`. `Sign` compares the 33-byte encodings and must succeed. The case needs three signers, because with two `NonceAgg` fails on such nonces. | The C mutant that compares `R₂` by x-coordinate only passes the unit tests. | A `Sign` vector with three signers and a negated `R₂`. |
| 10 | The `Sign` error vector "Signer's R2 appears at two indices" has the signer's own entry first. Code that keeps the last index with that `R₂` and compares it with the signer's passes it without counting. | The C mutant without the count passes the unit tests for this reason. | A second vector with the signer's own entry last. |

## The C module

| | Finding | Evidence | Proposed change |
|---|---|---|---|
| 11 | The unit tests pass for ten changes to the module that a test on secp256k1 can notice. Two of them are `nonce_gen_counter` without the counter and without the secret key, and either would give away the secret key. `fullagg_nonce_gen_counter_test` checks that a signature verifies and does not compare nonces. | `scripts/mutate_secp256k1.py`. The [README](README.md#mutation-test-of-the-c-module) lists the ten with the reason for each. The cases of `scripts/fuzz.py` notice all of them. | A test for each. The vectors of 7 to 10 cover four. For `nonce_gen_counter`, compare the nonces of two counters and of two keys. |
| 12 | The module has no exhaustive test. Three changes can only be noticed on a small group: `session_init` and `partial_sig_verify` accepting an `R` at infinity, and `verify` reducing an `s ≥ n`. | `scripts/mutate_secp256k1.py` with the exhaustive tests as a third set. | `patches/secp256k1-fullagg-exhaustive-tests.patch` adds the test. It passes on the groups of order 13 and 199. |
