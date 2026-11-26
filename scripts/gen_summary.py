#!/usr/bin/env python3
"""Generate Dahlias/Summary.lean from the axioms Lean reports for the results.

Usage: python3 scripts/gen_summary.py > Dahlias/Summary.lean  (after `lake build`)

Run it when a result is added or a definition behind a result changes. The
generated file then fails the build if the axioms of a result, the axioms of
the project, the list of definitions behind the results or the reading list of
a main result change.
"""

import os
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

SECTIONS = [
    ("Correctness, for every choice of the hash functions",
     ["Dahlias.verify_honest", "Dahlias.verify_sigAgg_of_partialSigVerify",
      "Dahlias.partialSigVerify_sign", "Dahlias.tweakPK_mulG"]),
    ("Finding a disruptive signer",
     ["Dahlias.partialSigVerify_iff", "Dahlias.partialSigVerify_unique",
      "Dahlias.partialSigVerify_iff_eq_sign", "Dahlias.exists_partialSigVerify_eq_false",
      "Dahlias.partialSigVerify_of_verify", "Dahlias.verify_eq_false_of_one_bad"]),
    ("Signing by a single party that holds all keys",
     ["Dahlias.verify_signSingle", "Dahlias.verify_unique", "Dahlias.sigAgg_eq_signSingle",
      "Dahlias.Security.challenger_single", "Dahlias.Security.forgeAdvantage_le_derived"]),
    ("The order of the generator of secp256k1, checked by the kernel",
     ["Dahlias.OrderG.n_smul_G", "Dahlias.secp256k1F"]),
    ("Correctness on bytes",
     ["Dahlias.Bytes.verify_honest"]),
    ("Test vectors (compiled evaluation)",
     ["Dahlias.Vectors.nonceGen_vectors", "Dahlias.Vectors.nonceAgg_vectors",
      "Dahlias.Vectors.sign_vectors", "Dahlias.Vectors.signError_vectors",
      "Dahlias.Vectors.partialSigVerify_vectors", "Dahlias.Vectors.verify_vectors",
      "Dahlias.Vectors.tweak_vectors"]),
    ("The local forking lemma",
     ["Dahlias.LocalFork.localFork_prob", "Dahlias.QTree.localFork_prob"]),
    ("Unforgeability",
     ["Dahlias.Security.unforgeable", "Dahlias.Security.unforgeable_sqrt",
      "Dahlias.Security.secp256k1_unforgeable",
      "Dahlias.Security.tweakSK_affine", "Dahlias.Security.bipTweakSign_ne_zero",
      "Dahlias.Security.Tweak.sk_comp", "Dahlias.Security.Tweak.comp_snd_ne_zero",
      "Dahlias.Security.guesser_hashBound", "Dahlias.Security.guesser_advantage_pos"]),
    ("The AOMDL game with uniform challenges",
     ["Dahlias.Security.omdlAdvantage_mul_le_std", "Dahlias.Security.omdlAdvantage_le_std",
      "Dahlias.Security.unforgeable_sqrt_std"]),
    ("The additive term of the bound is needed",
     ["Dahlias.Security.grinder_hashBound", "Dahlias.Security.grinder_advantage",
      "Dahlias.Security.grinder_advantage_ge"]),
    ("Lazy sampling of the random oracle",
     ["Dahlias.QTree.prob_eval_eq_lazy", "Dahlias.Security.forgeAdvantage_eq_lazy",
      "Dahlias.Security.omdlAdvantage_reduction_eq_lazy",
      "Dahlias.Security.unforgeable_sqrt_lazy", "Dahlias.Security.collisionAdvantage_eq_lazy",
      "Dahlias.Security.unforgeable_sqrt_lazy_both"]),
    ("The challenge hash as an output reduced modulo `n`",
     ["Dahlias.Security.forgeAdvantageH_le", "Dahlias.Security.unforgeable_sqrt_hashed",
      "Dahlias.Security.unforgeable_sqrt_fin"]),
    ("Nonces derived by `NonceGen`",
     ["Dahlias.Security.prob_winE_le", "Dahlias.Security.nonceGen_advantage",
      "Dahlias.Security.nonceGen_unforgeable",
      "Dahlias.Security.nonceGen_advantage_fin", "Dahlias.Security.nonceGenSk_le",
      "Dahlias.Security.nonceGenSk_advantage"]),
    ("`NonceGen` and the challenge hash reduced modulo `n`, together",
     ["Dahlias.Security.nonceGenAdvantageH_le", "Dahlias.Security.nonceGen_unforgeable_hashed",
      "Dahlias.Security.nonceGen_unforgeable_fin", "Dahlias.Security.nonceGenSkAdvantageH_le",
      "Dahlias.Security.nonceGenSk_unforgeable_hashed", "Dahlias.Security.lazy_of_tables",
      "Dahlias.Security.forgeAdvantage_withTable_eq_lazy",
      "Dahlias.Security.forgeAdvantage_withAux_eq_lazy",
      "Dahlias.Security.nonceGen_unforgeable_lazy",
      "Dahlias.Security.nonceGenSk_unforgeable_lazy",
      "Dahlias.Security.nonceGenSk_unforgeable_fin"]),
    ("`NonceGen` with a counter in place of `rand'`",
     ["Dahlias.Security.fresh_values_or_hit", "Dahlias.Security.prob_comp_injective",
      "Dahlias.Security.forgeTail_wins", "Dahlias.Security.winE_keyForger",
      "Dahlias.Security.nonceGenCtr_advantage", "Dahlias.Security.nonceGenCtr_unforgeable",
      "Dahlias.Security.nonceGenCtrAdvantageH_le",
      "Dahlias.Security.nonceGenCtr_unforgeable_hashed",
      "Dahlias.Security.nonceGenCtr_unforgeable_fin"]),
    ("Strong binding",
     ["Dahlias.Security.strongly_binding", "Dahlias.Security.secp256k1_strongly_binding",
      "Dahlias.Security.bindAdvantageH_le", "Dahlias.Security.strongly_binding_fin",
      "Dahlias.secp256k1_primeOrder"]),
    ("Security for 32-byte keys and messages",
     ["Dahlias.Security.bytes_unforgeable", "Dahlias.Security.bytes_unforgeable_256",
      "Dahlias.Security.hash_gap", "Dahlias.Security.bytes_strongly_binding",
      "Dahlias.Security.bytes_strongly_binding_256", "Dahlias.Security.card_B32",
      "Dahlias.Security.bytes_nonceGenSk_unforgeable_256",
      "Dahlias.Security.bytes_nonceGen_unforgeable_256",
      "Dahlias.Security.unmaskXor_maskXor",
      "Dahlias.Security.bytes_nonceGenCtr_unforgeable_256",
      "Dahlias.Security.verify_val", "Dahlias.Security.sign_val"]),
    ("The byte encodings",
     ["Dahlias.Bytes.sigInput_injective", "Dahlias.Bytes.nonceCoefInput_injective",
      "Dahlias.Bytes.cbytes_injective", "Dahlias.Security.collision_bytes",
      "Dahlias.Bytes.cpoint_eq_some_iff", "Dahlias.Bytes.matchIdxs_bytes",
      "Dahlias.Security.sign_bytes", "Dahlias.Security.verify_bytes",
      "Dahlias.Bytes.hashes_sig", "Dahlias.Bytes.hashes_nonceCoef",
      "Dahlias.Security.length_sha256", "Dahlias.Security.hashes_sig_eq_redFin",
      "Dahlias.Security.nonceInput_injective", "Dahlias.Security.nonceGen_eq",
      "Dahlias.Security.nonceGen_sk_eq"]),
    ("The games with the byte interface",
     ["Dahlias.Bytes.sign_eq_signWith", "Dahlias.Bytes.verify_eq_verifyWith",
      "Dahlias.Security.signWith_bytes", "Dahlias.Security.verifyWith_bytes",
      "Dahlias.Security.run_trB", "Dahlias.Security.wins_of_winsB",
      "Dahlias.Security.forgeExperimentB_imp", "Dahlias.Security.nonceGenExperimentB_imp",
      "Dahlias.Security.bytesGame_unforgeable_256",
      "Dahlias.Security.bytesGame_nonceGen_unforgeable_256",
      "Dahlias.Security.bytesGame_nonceGenSk_unforgeable_256",
      "Dahlias.Security.bytesGame_nonceGenCtr_unforgeable_256"]),
    ("Attacks on misuse and on a weakened `Sign`",
     ["Dahlias.Security.evenScalar_of_nonce_reuse",
      "Dahlias.Security.evenScalar_of_three_sessions", "Dahlias.Security.sign_eq_signPost",
      "Dahlias.Security.challengerWith_sign", "Dahlias.Security.msgSwap_wins",
      "Dahlias.Security.ros_bits", "Dahlias.Security.mulG_effNonce",
      "Dahlias.Security.ros_forgery"]),
]

# The main results: one for every property, in its general form. The other
# results are forms of these for other models of the hash functions and of the
# nonces, for secp256k1 and for bytes, and facts that support them. REVIEW.md
# prints the statements of the main results and what a reader of each has to
# read.
MAIN = [
    ("Correctness", ["Dahlias.verify_honest"]),
    ("Unforgeability", ["Dahlias.Security.unforgeable_sqrt", "Dahlias.Security.unforgeable"]),
    ("Strong binding", ["Dahlias.Security.strongly_binding"]),
    ("Finding a disruptive signer",
     ["Dahlias.partialSigVerify_iff_eq_sign", "Dahlias.exists_partialSigVerify_eq_false",
      "Dahlias.verify_eq_false_of_one_bad"]),
]

HEADER = '''
/-!
# The results and their axioms

Each check below fails the build if the axioms of a result change. The
theorems must depend only on Lean's standard axioms (`propext`,
`Classical.choice`, `Quot.sound`); a `sorry` would show up as `sorryAx`. This
includes the results about secp256k1: the order of its generator is checked by
the kernel (`Dahlias.OrderG`). Only the test vector checks use compiled
evaluation, with one `native_decide` axiom each.

Generated by `scripts/gen_summary.py`.
-/

set_option linter.style.longLine false
'''


INVENTORY = '''
/-! ## The axioms of the whole project

The checks above are about single results. This one is about every
declaration of the project: the axioms that its modules declare, and the
axioms that its declarations depend on. The only axioms of the project are
the ones of the test vector checks. -/
'''

SURFACE = '''
/-! ## The definitions behind the results

The definitions of the project that the statements of the results above depend
on, directly or through other definitions, by module. Proofs are not followed.
`REVIEW.md` lists the same definitions. -/
'''

READING = '''
/-! ## What to read for each main result

For every main result, the definitions of the project behind its statement:
how many there are, how many source lines they have, and their names by
module. The last check is for all main results together. `REVIEW.md` shows
these lists. -/
'''


def lean(imports, body):
    """The output of Lean on a file with the given imports and commands."""
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as f:
        f.write("\n".join(imports) + "\n" + body)
        path = f.name
    env = dict(os.environ, PATH=os.path.expanduser("~/.elan/bin") + os.pathsep + os.environ["PATH"])
    out = subprocess.run(["lake", "env", "lean", path], capture_output=True, text=True,
                         cwd=ROOT, env=env).stdout
    os.unlink(path)
    return out


SEPARATOR = "-- next command --"


def guards(imports, commands, start):
    """Guarded commands with the messages they print, each of which must begin
    with one of the strings in `start`. One run of Lean for all of them."""
    out = lean(imports, f'\n#eval IO.println "{SEPARATOR}"\n'.join(commands) + "\n")
    msgs = [m.strip() for m in out.split(SEPARATOR)]
    if len(msgs) != len(commands):
        sys.exit(f"expected {len(commands)} messages, got {len(msgs)}:\n{out}")
    for command, msg in zip(commands, msgs):
        if not msg.startswith(start):
            sys.exit(f"unexpected output of {command.split()[0]}:\n{msg}")
    return [f"\n/--\ninfo: {msg}\n-/\n#guard_msgs in\n{command}\n"
            for command, msg in zip(commands, msgs)]


def main():
    imports = [l for l in (ROOT / "Dahlias.lean").read_text().splitlines()
               if l.strip() and l.strip() != "import Dahlias.Summary"]
    names = [n for _, l in SECTIONS for n in l]
    out = lean(imports, "".join(f"#print axioms {n}\n" for n in names))
    msgs, cur = [], None
    for line in out.split("\n"):
        if line.startswith("'"):
            if cur is not None:
                msgs.append(cur)
            cur = line
        elif cur is not None and line.strip():
            cur += "\n" + line
    if cur is not None:
        msgs.append(cur)
    if len(msgs) != len(names):
        sys.exit(f"expected {len(names)} axiom reports, got {len(msgs)}:\n{out}")
    doc = "\n".join(imports) + "\n" + HEADER
    it = iter(msgs)
    for title, l in SECTIONS:
        doc += f"\n/-! ## {title} -/\n"
        for name in l:
            m = next(it)
            assert m.startswith(f"'{name}'"), (m, name)
            if "\n" in m:
                doc += f"\n/--\ninfo: {m}\n-/\n#guard_msgs in\n#print axioms {name}\n"
            else:
                doc += f"\n/-- info: {m} -/\n#guard_msgs in\n#print axioms {name}\n"
    main_names = [n for _, l in MAIN for n in l]
    if not set(main_names) <= set(names):
        sys.exit("a main result is not in SECTIONS")
    reading = MAIN + [("All main results", main_names)]
    inventory, surface, *lists = guards(
        imports,
        ["#project_axioms", "#surface " + " ".join(names)]
        + ["#reading " + " ".join(l) for _, l in reading],
        ("axioms declared in the project", "Dahlias.", "Dahlias: "))
    doc += INVENTORY + inventory + SURFACE + surface + READING
    for (title, _), text in zip(reading, lists):
        doc += f"\n/-! ### {title} -/\n" + text
    sys.stdout.write(doc)


if __name__ == "__main__":
    main()
