#!/usr/bin/env python3
"""Print the section "The statements" of REVIEW.md from the sources.

Usage: python3 scripts/gen_review.py          rewrite the section in REVIEW.md
       python3 scripts/gen_review.py --check  fail if REVIEW.md is out of date

A definition is printed with its comment and its body. A theorem, or a
definition marked "sig", is printed up to its `:=`. Every printed block is a
substring of a source file, which scripts/check.sh verifies.
"""

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
BEGIN, END = "<!-- statements:begin -->", "<!-- statements:end -->"
DECL = r"(?:noncomputable )?(?:def|abbrev|theorem|structure|inductive)"

# (heading, text, [(file, [names])]). A name ending in "!" is printed up to its `:=`.
SECTIONS = [
    ("The algorithms of BIP 459",
     "`Dahlias/Basic.lean`. `Ops` is the handful of curve operations the BIP uses, `Hashes` the "
     "two tagged hashes of the signing protocol. Points given as `0` stand for encodings that "
     "`cpoint` rejects.",
     [("Dahlias/Basic.lean",
       ["Ops", "Hashes", "evenScalar", "signOf", "tweakSK", "tweakPK", "nonceGen", "nonceAgg",
        "coefItems", "getSessionValues", "matchIdxs", "sign", "sigAgg", "partialSigVerify",
        "keySum", "verify"])]),
    ("Oracle algorithms and probabilities",
     "`Dahlias/Alg.lean` and `Dahlias/Prob.lean`. An adversary is a function from coins to a "
     "deterministic algorithm that makes queries. A probability is a fraction of a finite sample "
     "space.",
     [("Dahlias/Alg.lean", ["Alg", "bind", "run"]), ("Dahlias/Prob.lean", ["prob"])]),
    ("The unforgeability game",
     "`Dahlias/Security.lean`. `challengerG false` is the game. `challengerG true` is the "
     "variant the reduction works with: a single-party signature takes its nonce from both "
     "nonces of its slot.",
     [("Dahlias/Security.lean",
       ["BList", "SigIn", "hashesOf", "Tweak", "Tweak.sk", "AdvQ", "AdvR", "Forgery", "Adversary",
        "SignerState", "singleKeys", "singleNcIn", "singleNonce", "singleS", "challengerG",
        "challenger", "Wins", "ForgeSample", "forgeExperimentG", "forgeExperiment",
        "forgeAdvantageG", "forgeAdvantage", "HashBound"])]),
    ("The single-party signature of the game",
     "`Dahlias/Single.lean` and `Dahlias/SingleGame.lean`. The game's answer to a `single` "
     "query is the algorithm `signSingle`.",
     [("Dahlias/Single.lean", ["singleList", "signSingle"]),
      ("Dahlias/SingleGame.lean", ["challenger_single"])]),
    ("The AOMDL game",
     "`Dahlias/Security.lean`, with challenges that have nonzero discrete logarithms, and "
     "`Dahlias/OmdlStd.lean`, with uniform challenges.",
     [("Dahlias/Security.lean",
       ["OmdlQ", "OmdlR", "OmdlAdversary", "chalLogs", "omdlChallenger", "omdlExperiment",
        "omdlAdvantage"]),
      ("Dahlias/OmdlStd.lean",
       ["chalLogsStd", "omdlChallengerStd", "omdlExperimentStd", "omdlAdvantageStd",
        "omdlAdvantage_le_std"])]),
    ("Unforgeability",
     "`Dahlias/Unforgeability.lean`, `Dahlias/Proofs/Reduction.lean`, "
     "`Dahlias/LazyReduction.lean` and `Dahlias/LazyCollider.lean`. Of the reduction and the "
     "collision finder only the types are printed.",
     [("Dahlias/Proofs/Reduction.lean", ["ncHash", "IsCollision", "reduction!", "collider!"]),
      ("Dahlias/Unforgeability.lean",
       ["collisionAdvantage", "NoSingle", "unforgeable", "unforgeable_sqrt"]),
      ("Dahlias/OmdlStd.lean", ["unforgeable_sqrt_std"]),
      ("Dahlias/LazyReduction.lean", ["reductionLazy", "unforgeable_sqrt_lazy"]),
      ("Dahlias/LazyCollider.lean",
       ["LazyColliderSample", "colliderLazy", "collisionAdvantageLazy",
        "unforgeable_sqrt_lazy_both"])]),
    ("The additive term of the bound",
     "`Dahlias/Tightness.lean`. A forger that makes `q` random oracle queries, no signing "
     "queries and computes no discrete logarithm.",
     [("Dahlias/Tightness.lean",
       ["grindIn", "grindOut", "grindAlg", "grinder", "grinder_hashBound", "grinder_advantage",
        "grinder_advantage_ge"])]),
    ("The challenge hash reduced modulo `n`",
     "`Dahlias/Hashed.lean` and `Dahlias/BytesSecurity.lean`. The random oracle answers with "
     "hash outputs, which the adversary sees and the signer and the verifier reduce.",
     [("Dahlias/Hashed.lean",
       ["AdvRH", "AdversaryH", "challengerH", "ForgeSampleH", "forgeExperimentH",
        "forgeAdvantageH", "liftHash", "redFin", "liftFin", "unforgeable_sqrt_fin"]),
      ("Dahlias/BytesSecurity.lean",
       ["B32", "secp256k1X", "nonceCoef32", "bytes_unforgeable_256", "hash_gap"])]),
    ("Nonces derived by `NonceGen`",
     "`Dahlias/Second.lean`, `Dahlias/NonceGen.lean` and `Dahlias/NonceGenSk.lean`. The "
     "adversary may also query `hash_BIP0459/nonce` and `hash_BIP0459/aux` and set the "
     "`extra_in` of the next slot.",
     [("Dahlias/Second.lean", ["SumR", "answerG", "NBound"]),
      ("Dahlias/NonceGen.lean",
       ["NAdversary", "withTable", "challengerE", "Rest", "nvOf", "winE", "noncePt",
        "nonceGenExperiment", "nonceGenAdvantage", "nonceGen_unforgeable"]),
      ("Dahlias/NonceGenSk.lean",
       ["SkAdversary", "withAux", "winSk", "nonceGenSkExperiment", "nonceGenSkAdvantage",
        "nonceGenSk_advantage"])]),
    ("Binding",
     "`Dahlias/Binding.lean`, and `Dahlias/BindingHashed.lean` for the oracle with hash outputs.",
     [("Dahlias/QueryRun.lean", ["QTree", "eval", "flog", "fresh"]),
      ("Dahlias/Binding.lean", ["BindAdversary", "bindExperiment", "strongly_binding"]),
      ("Dahlias/BindingHashed.lean", ["BindAdversaryH", "bindExperimentH", "strongly_binding_fin"]),
      ("Dahlias/BytesSecurity.lean", ["bytes_strongly_binding_256"])]),
    ("Finding a disruptive signer",
     "`Dahlias/Correctness.lean` and `Dahlias/Blame.lean`. The statements hold for every choice "
     "of the hash functions.",
     [("Dahlias/Correctness.lean",
       ["partialSigVerify_sign", "verify_sigAgg_of_partialSigVerify"]),
      ("Dahlias/Blame.lean",
       ["partialSigVerify_iff_eq_sign", "exists_partialSigVerify_eq_false",
        "verify_eq_false_of_one_bad"])]),
    ("The bytes",
     "`Dahlias/Bytes.lean` and `Dahlias/Encoding.lean`. `Sign` and `Verify` on bytes parse "
     "their inputs and call the model.",
     [("Dahlias/Bytes.lean",
       ["specOps", "cbytes", "cpoint", "parseNonce", "scalar", "scalarWrap", "hashes",
        "wellFormed", "sign", "verify"]),
      ("Dahlias/BytesSecurity.lean", ["vals", "Agree"]),
      ("Dahlias/Encoding.lean",
       ["cpoint_eq_some_iff", "matchIdxs_bytes", "sigInput", "nonceCoefInput", "Pairs32",
        "sigInput_injective", "Items32", "nonceCoefInput_injective", "nonceCoefBytes",
        "collision_bytes", "verify_bytes",
        "sign_bytes"])]),
]


def block(path, name):
    sig = name.endswith("!")
    name = name.rstrip("!")
    lines = (ROOT / path).read_text().split("\n")
    pat = re.compile(rf"^{DECL}\s+{re.escape(name)}(?![\w.'])")
    hits = [i for i, l in enumerate(lines) if pat.match(l)]
    if len(hits) != 1:
        sys.exit(f"{path}: {len(hits)} declarations named {name}")
    start = at = hits[0]
    if lines[at - 1].rstrip().endswith("-/"):
        start = at - 1
        while not lines[start].startswith("/--"):
            start -= 1
    end = at + 1
    while end < len(lines):
        if lines[end] == "":
            rest = [l for l in lines[end:] if l != ""]
            if not rest or not rest[0].startswith((" ", "\t")):
                break
        end += 1
    text = "\n".join(lines[start:end])
    if sig or re.match(r"^(?:noncomputable )?theorem", lines[at]):
        m = re.search(r" :=" if sig else r" :=(?: by)?$", text, re.M)
        if not m:
            sys.exit(f"{path}: no := in {name}")
        text = text[:m.start()]
    return text


SURFACE = (
    "The definitions of the project that the statements of the results in `Dahlias/Summary.lean` "
    "depend on, directly or through other definitions. `#surface` in `Dahlias/Audit.lean` computes "
    "the list from the compiled project, `Dahlias/Summary.lean` guards it, and the build fails if "
    "it changes. Proofs are not followed, since what a proof uses does not change what a statement "
    "says. Whoever agrees with these definitions knows what the results say. The ones that are not "
    "printed above have to be read in the sources.")


def surface():
    """The definitions behind the results, from the guarded output in Dahlias/Summary.lean."""
    summary = (ROOT / "Dahlias/Summary.lean").read_text()
    end = summary.find("\n-/\n#guard_msgs in\n#surface ")
    start = summary.rfind("/--\ninfo: ", 0, end)
    if end < 0 or start < 0:
        sys.exit("Dahlias/Summary.lean has no guarded #surface")
    out = []
    for line in summary[start + len("/--\ninfo: "):end].split("\n"):
        module, names = line.split(": ", 1)
        shown = ", ".join(f"`{n.removeprefix('Dahlias.')}`" for n in names.split(", "))
        out.append(f"- `{module.replace('.', '/')}.lean`: {shown}")
    return out


def render():
    out = [BEGIN, ""]
    for heading, text, groups in SECTIONS:
        out += [f"### {heading}", "", text, ""]
        for path, names in groups:
            for name in names:
                out += ["```lean", block(path, name), "```", ""]
    out += ["### Every definition behind the results", "", SURFACE, ""] + surface() + [""]
    out.append(END)
    return "\n".join(out)


def main():
    review = (ROOT / "REVIEW.md").read_text()
    i, j = review.index(BEGIN), review.index(END) + len(END)
    new = review[:i] + render() + review[j:]
    if "--check" in sys.argv:
        if new != review:
            sys.exit("REVIEW.md is out of date: run scripts/gen_review.py")
    else:
        (ROOT / "REVIEW.md").write_text(new)


if __name__ == "__main__":
    main()
