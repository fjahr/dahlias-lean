#!/usr/bin/env python3
"""Write the generated parts of REVIEW.md.

Usage: python3 scripts/gen_review.py          rewrite the parts in REVIEW.md
       python3 scripts/gen_review.py --check  fail if REVIEW.md is out of date

Three parts of REVIEW.md are generated, each between two marker comments:

- the table of the main results with what a reader of each has to read, from
  the guarded outputs of `#reading` in Dahlias/Summary.lean,
- the statements of the main results and the definitions behind them, from
  the sources,
- the list of the definitions behind all results, from the guarded output of
  `#surface` in Dahlias/Summary.lean.

A definition is printed with its comment and its body. A theorem, or a
definition marked "sig", is printed up to its `:=`. Every printed block is a
substring of a source file, which scripts/check.sh verifies.
"""

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MAIN = ("<!-- main:begin -->", "<!-- main:end -->")
STATEMENTS = ("<!-- statements:begin -->", "<!-- statements:end -->")
DEFINITIONS = ("<!-- definitions:begin -->", "<!-- definitions:end -->")
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
    ("Correctness",
     "`Dahlias/Correctness.lean`. The statement holds for every choice of the hash functions.",
     [("Dahlias/Correctness.lean", ["Signer", "Signer.pkm", "Signer.pubnonce", "verify_honest"])]),
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
    ("The AOMDL game",
     "`Dahlias/Security.lean`. The challenges have nonzero discrete logarithms.",
     [("Dahlias/Security.lean",
       ["OmdlQ", "OmdlR", "OmdlAdversary", "chalLogs", "omdlChallenger", "omdlExperiment",
        "omdlAdvantage"])]),
    ("Unforgeability",
     "`Dahlias/Unforgeability.lean` and `Dahlias/Proofs/Reduction.lean`. Of the reduction and "
     "the collision finder only the types are printed.",
     [("Dahlias/Proofs/Reduction.lean", ["ncHash", "IsCollision", "reduction!", "collider!"]),
      ("Dahlias/Unforgeability.lean",
       ["collisionAdvantage", "NoSingle", "unforgeable", "unforgeable_sqrt"])]),
    ("Binding",
     "`Dahlias/Binding.lean`, with the deterministic query algorithms of "
     "`Dahlias/QueryRun.lean`.",
     [("Dahlias/QueryRun.lean", ["QTree", "eval", "flog", "fresh"]),
      ("Dahlias/Binding.lean", ["BindAdversary", "bindExperiment", "strongly_binding"])]),
    ("Finding a disruptive signer",
     "`Dahlias/Blame.lean`. The statements hold for every choice of the hash functions.",
     [("Dahlias/Blame.lean",
       ["partialSigVerify_iff_eq_sign", "exists_partialSigVerify_eq_false",
        "verify_eq_false_of_one_bad"])]),
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


READING = re.compile(
    r"/-! ### ([^\n]*) -/\n\n/--\ninfo: (.*?)\n-/\n#guard_msgs in\n#reading ([^\n]*)\n", re.S)
COUNT = re.compile(r"Dahlias: (\d+) definitions, (\d+) lines")


def modules(lines):
    """Lines `module: name, name, …` as bullet points."""
    out = []
    for line in lines:
        module, names = line.split(": ", 1)
        shown = ", ".join(f"`{n.removeprefix('Dahlias.')}`" for n in names.split(", "))
        out.append(f"- `{module.replace('.', '/')}.lean`: {shown}")
    return out


def render_main():
    """The main results with what a reader of each has to read."""
    summary = (ROOT / "Dahlias/Summary.lean").read_text()
    results = READING.findall(summary)
    if not results:
        sys.exit("Dahlias/Summary.lean has no guarded #reading")
    table = ["| Main result | Theorem | Definitions | Lines |", "|---|---|---|---|"]
    lists = []
    for title, info, names in results:
        count, *rest = info.split("\n")
        m = COUNT.fullmatch(count)
        if not m:
            sys.exit(f"unexpected #reading output for {title}")
        theorems = ", ".join(f"`{n.split('.')[-1]}`" for n in names.split())
        if title == "All main results":
            title, theorems = "All of them", ""
        else:
            lists += [f"**{title}**", ""] + modules(rest) + [""]
        table.append(f"| {title} | {theorems} | {m.group(1)} | {m.group(2)} |")
    return "\n".join([MAIN[0], ""] + table + ["", "The definitions of the project behind each "
                      "main result, by file:", ""] + lists + [MAIN[1]])


def render_statements():
    out = [STATEMENTS[0], ""]
    for heading, text, groups in SECTIONS:
        out += [f"### {heading}", "", text, ""]
        for path, names in groups:
            for name in names:
                out += ["```lean", block(path, name), "```", ""]
    out.append(STATEMENTS[1])
    return "\n".join(out)


def render_definitions():
    """The definitions behind the results, from the guarded output in Dahlias/Summary.lean."""
    summary = (ROOT / "Dahlias/Summary.lean").read_text()
    end = summary.find("\n-/\n#guard_msgs in\n#surface ")
    start = summary.rfind("/--\ninfo: ", 0, end)
    if end < 0 or start < 0:
        sys.exit("Dahlias/Summary.lean has no guarded #surface")
    lines = summary[start + len("/--\ninfo: "):end].split("\n")
    return "\n".join([DEFINITIONS[0], "", "## Every definition behind the results", "", SURFACE,
                      ""] + modules(lines) + ["", DEFINITIONS[1]])


def main():
    review = (ROOT / "REVIEW.md").read_text()
    new = review
    for (begin, end), text in ((MAIN, render_main()), (STATEMENTS, render_statements()),
                               (DEFINITIONS, render_definitions())):
        i, j = new.index(begin), new.index(end) + len(end)
        new = new[:i] + text + new[j:]
    if "--check" in sys.argv:
        if new != review:
            sys.exit("REVIEW.md is out of date: run scripts/gen_review.py")
    else:
        (ROOT / "REVIEW.md").write_text(new)


if __name__ == "__main__":
    main()
