import Dahlias.Basic
import Dahlias.Correctness
import Dahlias.Bytes
import Dahlias.BytesCurve
import Dahlias.BytesCorrectness
import Dahlias.Vectors
import Dahlias.Prob
import Dahlias.LocalFork
import Dahlias.Alg
import Dahlias.QueryRun
import Dahlias.Fork
import Dahlias.Security
import Dahlias.Unforgeability
import Dahlias.Tweaks
import Dahlias.Secp256k1
import Dahlias.Examples

/-!
# Main results and their axioms

Each check below fails the build if the axioms of a main result change. The
theorems must depend only on Lean's standard axioms (`propext`,
`Classical.choice`, `Quot.sound`); a `sorry` would show up as `sorryAx`. The
test vector checks also depend on one `native_decide` axiom each (compiled
evaluation), and the results that mention secp256k1 inherit taproot-lean's
`native_decide` computation of `n·G = 0`.
-/

set_option linter.style.longLine false

/-! ## Correctness, for every choice of the hash functions -/

/-- info: 'Dahlias.verify_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Dahlias.verify_honest

/-- info: 'Dahlias.verify_sigAgg_of_partialSigVerify' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Dahlias.verify_sigAgg_of_partialSigVerify

/-- info: 'Dahlias.partialSigVerify_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Dahlias.partialSigVerify_sign

/-- info: 'Dahlias.tweakPK_mulG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Dahlias.tweakPK_mulG

/-! ## Correctness on bytes (inherits taproot-lean's `native_decide` computation of `n·G = 0`) -/

/--
info: 'Dahlias.Bytes.verify_honest' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Taproot.Secp256k1.n_smul_G._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms Dahlias.Bytes.verify_honest

/-! ## Test vectors (compiled evaluation) -/

/--
info: 'Dahlias.Vectors.nonceGen_vectors' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Dahlias.Vectors.nonceGen_vectors._native.native_decide.ax_1_1,
 Taproot.Secp256k1.n_smul_G._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms Dahlias.Vectors.nonceGen_vectors

/--
info: 'Dahlias.Vectors.nonceAgg_vectors' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Dahlias.Vectors.nonceAgg_vectors._native.native_decide.ax_1_1,
 Taproot.Secp256k1.n_smul_G._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms Dahlias.Vectors.nonceAgg_vectors

/--
info: 'Dahlias.Vectors.sign_vectors' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Dahlias.Vectors.sign_vectors._native.native_decide.ax_1_1,
 Taproot.Secp256k1.n_smul_G._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms Dahlias.Vectors.sign_vectors

/--
info: 'Dahlias.Vectors.signError_vectors' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Dahlias.Vectors.signError_vectors._native.native_decide.ax_1_1,
 Taproot.Secp256k1.n_smul_G._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms Dahlias.Vectors.signError_vectors

/--
info: 'Dahlias.Vectors.partialSigVerify_vectors' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Dahlias.Vectors.partialSigVerify_vectors._native.native_decide.ax_1_1,
 Taproot.Secp256k1.n_smul_G._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms Dahlias.Vectors.partialSigVerify_vectors

/--
info: 'Dahlias.Vectors.verify_vectors' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Dahlias.Vectors.verify_vectors._native.native_decide.ax_1_1,
 Taproot.Secp256k1.n_smul_G._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms Dahlias.Vectors.verify_vectors

/--
info: 'Dahlias.Vectors.tweak_vectors' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Dahlias.Vectors.tweak_vectors._native.native_decide.ax_1_1,
 Taproot.Secp256k1.n_smul_G._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms Dahlias.Vectors.tweak_vectors

/-! ## The local forking lemma -/

/-- info: 'Dahlias.LocalFork.localFork_prob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Dahlias.LocalFork.localFork_prob

/-- info: 'Dahlias.QTree.localFork_prob' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Dahlias.QTree.localFork_prob

/-! ## Unforgeability -/

/-- info: 'Dahlias.Security.unforgeable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Dahlias.Security.unforgeable

/--
info: 'Dahlias.Security.secp256k1_unforgeable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Taproot.Secp256k1.n_smul_G._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms Dahlias.Security.secp256k1_unforgeable

/-- info: 'Dahlias.Security.tweakSK_affine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Dahlias.Security.tweakSK_affine

/-- info: 'Dahlias.Security.guesser_advantage_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Dahlias.Security.guesser_advantage_pos
