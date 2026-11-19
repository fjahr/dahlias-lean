#!/usr/bin/env python3
"""
Mutation test of libsecp256k1's fullagg module.

Usage:
    python3 scripts/mutate_secp256k1.py path/to/secp256k1 path/to/bips/bip-0459
        [--cases N] [--seed S] [--no-exhaustive] [--only NAME,NAME,...]

Exports HEAD of the secp256k1 checkout into a temporary directory, applies
patches/secp256k1-fullagg-exhaustive-tests.patch and builds there, so the
checkout is not touched. For each small mutant of
src/modules/fullagg/main_impl.h it rebuilds and asks three oracles:

  tests       the module's unit tests, run one by one (this includes the BIP's
              test vectors),
  cases       the cases of scripts/fuzz.py, run through the driver built from
              scripts/fuzz_secp256k1.c: the number of cases on which the
              mutant's output differs from the unmutated library's, which
              agrees with BIP 459's Python reference up to the known
              differences listed in fuzz.py,
  exhaustive  the exhaustive tests on the group of order 13, with the patch.

A mutant that none of them notices is a survivor.

Mutants whose code ends in `*` cannot be noticed with the real group by
anyone who cannot break the hash functions (see BY_DESIGN); the exhaustive
tests on a small group are the only oracle that can catch them.
"""

import argparse
import random
import subprocess
import sys
import tempfile
from pathlib import Path

import fuzz

MODULE = "src/modules/fullagg/main_impl.h"
CMAKE = ["-DBUILD_SHARED_LIBS=OFF", "-DSECP256K1_EXPERIMENTAL=ON",
         "-DSECP256K1_ENABLE_MODULE_FULLAGG=ON", "-DSECP256K1_BUILD_BENCHMARK=OFF",
         "-DSECP256K1_BUILD_CTIME_TESTS=OFF", "-DSECP256K1_BUILD_EXAMPLES=OFF"]

CLEAR = "        secp256k1_fullagg_partial_sign_clear(&sk, k);\n        return 0;\n    }\n"
INF = ("    if (secp256k1_gej_is_infinity(&aggnonce_ptsj[0]) || "
       "secp256k1_gej_is_infinity(&aggnonce_ptsj[1])) {\n")
R_INF = "    if (secp256k1_ge_is_infinity(&r)) {\n"
SIG_L = ("        secp256k1_fe_get_b32(buf, &pk_ge.x);\n"
         "        secp256k1_sha256_write(hash_ctx, &sha, buf, 32);\n"
         "        secp256k1_sha256_write(hash_ctx, &sha, messages[i], 32);\n"
         "    }\n\n    /* Write bytes(R) */\n")
VER_L = ("        secp256k1_fe_get_b32(buf, &pk_ge.x);\n"
         "        secp256k1_sha256_write(hash_ctx, &ecmult_data.sha_l, buf, 32);\n"
         "        secp256k1_sha256_write(hash_ctx, &ecmult_data.sha_l, messages[i], 32);\n")
SIG_R = "    secp256k1_sha256_write(hash_ctx, &sha, r32, 32);\n"
VER_R = "    secp256k1_sha256_write(hash_ctx, &sha, ecmult_data->sig64, 32);\n"
SIG_PK = ("    secp256k1_fe_get_b32(buf, &pk_ge.x);\n"
          "    secp256k1_sha256_write(hash_ctx, &sha, buf, 32);\n\n"
          "    /* Write m_i for this signer */\n")
VER_PK = ("    secp256k1_fe_get_b32(buf, &pt->x);\n"
          "    secp256k1_sha256_write(hash_ctx, &sha, buf, 32);\n")
SIG_M = "    secp256k1_sha256_write(hash_ctx, &sha, messages[signer_index], 32);\n"
VER_M = "    secp256k1_sha256_write(hash_ctx, &sha, ecmult_data->messages[idx], 32);\n"
NC_PK = ("        secp256k1_fe_get_b32(buf, &pk_ge.x);\n"
         "        secp256k1_sha256_write(hash_ctx, &sha, buf, 32);\n\n"
         "        /* Write m_i */\n")
NC_M = "        /* Write m_i */\n        secp256k1_sha256_write(hash_ctx, &sha, messages[i], 32);\n"
NC_R2 = ("        secp256k1_ge_serialize33(&nonce_pts[1], buf);\n"
         "        secp256k1_sha256_write(hash_ctx, &sha, buf, 33);\n")
AUX = ("        secp256k1_fullagg_sha256_tagged_aux(&sha);\n"
       "        secp256k1_sha256_write(hash_ctx, &sha, session_secrand, 32);\n"
       "        secp256k1_sha256_finalize(hash_ctx, &sha, rand);\n")
EXTRA = ("    if (extra_input32 != NULL) {\n"
         "        secp256k1_sha256_write(hash_ctx, &sha, extra_input32, 32);\n    }\n")
IDX = "        secp256k1_sha256_write(hash_ctx, &sha_tmp, &i, 1);\n"
NEG_SK = "    if (secp256k1_fe_is_odd(&keypair_pk.y)) {\n"
NEG_K = ("    if (fin_nonce_parity) {\n        secp256k1_scalar_negate(&k[0], &k[0]);\n"
         "        secp256k1_scalar_negate(&k[1], &k[1]);\n    }\n")
S_LIN = ("    secp256k1_scalar_mul(&s, &noncecoef, &k[1]);  /* b*k2_i */\n"
         "    secp256k1_scalar_add(&s, &s, &k[0]);          /* + k1_i */\n")
Q_SIG = ("                                           fin_nonce, signer_index)) {\n"
         "        return 0;\n    }\n\n    /* Verify: s_i*G")
V_S = ("    secp256k1_scalar_set_b32(&s, &sig64[32], &overflow);\n"
       "    if (overflow) {\n        return 0;\n    }\n")
V_END = ("    secp256k1_gej_add_ge_var(&resj, &resj, &r, NULL);\n"
         "    return secp256k1_gej_is_infinity(&resj);\n")
Q_END = ("    secp256k1_gej_add_var(&tmp, &tmp, &rj, NULL);\n\n"
         "    return secp256k1_gej_is_infinity(&tmp);\n")
PS_PARSE = ("    secp256k1_scalar_set_b32(&tmp, in32, &overflow);\n"
            "    if (overflow) {\n        return 0;\n    }\n")

# An edit is (old, new, occurrence): the occurrence index, or None if old is unique.
E_SIG_L = (SIG_L, "    }\n\n    /* Write bytes(R) */\n", None)
E_VER_L = (VER_L, "", None)
E_SIG_LM = (SIG_L, SIG_L.replace("        secp256k1_sha256_write(hash_ctx, &sha, messages[i], 32);\n", ""), None)
E_VER_LM = (VER_L, VER_L.replace(
    "        secp256k1_sha256_write(hash_ctx, &ecmult_data.sha_l, messages[i], 32);\n", ""), None)
E_SIG_R = (SIG_R, "    (void)r32;\n", None)
E_VER_R = (VER_R, "", None)
E_SIG_PK = (SIG_PK, "    secp256k1_fe_get_b32(buf, &pk_ge.x);\n\n    /* Write m_i for this signer */\n", None)
E_VER_PK = (VER_PK, "    secp256k1_fe_get_b32(buf, &pt->x);\n", None)
E_SIG_M = (SIG_M, "", None)
E_VER_M = (VER_M, "", None)

MUTANTS = [
    # NonceGen
    ("N1", "nonce_gen: sk not xored into rand",
     [("            rand[i] ^= seckey32[i];\n", "            rand[i] ^= 0;\n", None)]),
    ("N2", "nonce_gen: rand' not hashed before the xor with sk",
     [(AUX, "        memcpy(rand, session_secrand, sizeof(rand));\n", None)]),
    ("N3", "nonce_gen: extra_in not hashed", [(EXTRA, "    (void)extra_input32;\n", None)]),
    ("N4", "nonce_gen: nonce index not hashed, so r1 = r2", [(IDX, "", None)]),
    ("N5", "nonce_gen: nonce indices 1 and 2 instead of 0 and 1",
     [(IDX, "        { unsigned char i1 = (unsigned char)(i + 1);"
            " secp256k1_sha256_write(hash_ctx, &sha_tmp, &i1, 1); }\n", None)]),
    ("N6", "nonce_gen: all-zero rand' accepted",
     [("    ret &= !secp256k1_is_zero_array(session_secrand32, 32);\n", "    ret &= 1;\n", None)]),
    ("N7", "nonce_gen: invalid sk accepted",
     [("        ret &= secp256k1_scalar_set_b32_seckey(&sk, seckey);\n",
       "        (void)secp256k1_scalar_set_b32_seckey(&sk, seckey);\n", None)]),
    ("N8", "nonce_gen: rand' not cleared after use",
     [("    secp256k1_memczero(session_secrand32, 32, ret);\n", "", None)]),
    # NonceAgg
    ("G1", "nonce_agg: R1 at infinity accepted",
     [(INF, "    if (secp256k1_gej_is_infinity(&aggnonce_ptsj[1])) {\n", 0)]),
    ("G2", "nonce_agg: R2 at infinity accepted",
     [(INF, "    if (secp256k1_gej_is_infinity(&aggnonce_ptsj[0])) {\n", 0)]),
    ("G3", "nonce_agg: first halves summed twice",
     [("&summed_pubnonces[j], &nonce_pts[j], NULL);", "&summed_pubnonces[j], &nonce_pts[0], NULL);",
       None)]),
    # the nonce coefficient hash (shared by session_init, partial_sign, partial_sig_verify)
    ("B1", "noncecoef: aggregate nonce not hashed",
     [("    secp256k1_sha256_write(hash_ctx, &sha, aggnonce_ser66, 66);\n",
       "    (void)aggnonce_ser66;\n", None)]),
    ("B2", "noncecoef: public keys not hashed",
     [(NC_PK, "        secp256k1_fe_get_b32(buf, &pk_ge.x);\n\n        /* Write m_i */\n", None)]),
    ("B3", "noncecoef: messages not hashed", [(NC_M, "        /* Write m_i */\n", None)]),
    ("B4", "noncecoef: R2_i not hashed",
     [(NC_R2, "        secp256k1_ge_serialize33(&nonce_pts[1], buf);\n", None)]),
    ("B5", "noncecoef: R1_i hashed in place of R2_i",
     [(NC_R2, NC_R2.replace("&nonce_pts[1]", "&nonce_pts[0]"), None)]),
    ("B6", "noncecoef: R2_i hashed without its parity byte",
     [(NC_R2, NC_R2.replace("buf, 33);", "buf + 1, 32);"), None)]),
    # GetSessionValues
    ("I1", "session: R = R2 + b*R1",
     [("    secp256k1_gej_set_ge(&tmp, &nonce_pts[1]);\n", "    secp256k1_gej_set_ge(&tmp, &nonce_pts[0]);\n", None),
      ("    secp256k1_gej_add_ge_var(out_nonce, out_nonce, &nonce_pts[0], NULL);\n",
       "    secp256k1_gej_add_ge_var(out_nonce, out_nonce, &nonce_pts[1], NULL);\n", None)]),
    ("I2", "session_init: parity of R not recorded",
     [("    fin_nonce_parity = secp256k1_fe_is_odd(&r.y);\n\n    secp256k1_fullagg_session_save",
       "    fin_nonce_parity = 0;\n\n    secp256k1_fullagg_session_save", None)]),
    ("I3*", "session_init: R at infinity accepted", [(R_INF, "    if (0) {\n", 0)]),
    ("I4", "session_init: empty lists accepted",
     [("    ARG_CHECK(pubnonces != NULL);\n    ARG_CHECK(n_signers > 0);\n    for (i = 0; i < n_signers; i++) {\n"
       "        ARG_CHECK(pubkeys[i] != NULL);\n        ARG_CHECK(messages[i] != NULL);\n"
       "        ARG_CHECK(pubnonces[i] != NULL);\n    }\n\n    if (!secp256k1_fullagg_aggnonce_load",
       "    ARG_CHECK(pubnonces != NULL);\n    for (i = 0; i < n_signers; i++) {\n"
       "        ARG_CHECK(pubkeys[i] != NULL);\n        ARG_CHECK(messages[i] != NULL);\n"
       "        ARG_CHECK(pubnonces[i] != NULL);\n    }\n\n    if (!secp256k1_fullagg_aggnonce_load", None)]),
    # Sign
    ("P1", "sign: secnonce not cleared, so it can be used twice",
     [("    secp256k1_memzero_explicit(secnonce, sizeof(*secnonce));\n", "", None)]),
    ("P2", "sign: keypair need not match the secnonce",
     [("    if (!secp256k1_fe_equal(&pk.x, &keypair_pk.x)) {\n", "    if (0) {\n", None)]),
    ("P3", "sign: secret key not negated for an odd-y public key", [(NEG_SK, "    if (0) {\n", None)]),
    ("P4", "sign: public key at the signer's index not compared",
     [("        if (!secp256k1_fe_equal(&keypair_pk.x, &signer_pk.x)) {\n", "        if (0) {\n", None)]),
    ("P5", "sign: message at the signer's index not compared",
     [("    if (secp256k1_memcmp_var(messages[signer_index], msg32, 32) != 0) {\n", "    if (0) {\n",
       None)]),
    ("P6", "sign: the signer's R2 may appear more than once",
     [("        if (found_count != 1 || found_index != (int)signer_index) {\n",
       "        if (found_count < 1 || found_index != (int)signer_index) {\n", None)]),
    ("P7", "sign: the signer's R2 need not be at the signer's index",
     [("        if (found_count != 1 || found_index != (int)signer_index) {\n",
       "        if (found_count != 1) {\n", None)]),
    ("P8", "sign: R2 compared by x-coordinate only",
     [("\n                && secp256k1_fe_equal(&r2_self.y, &nonce_pts[1].y)) {", ") {", None)]),
    ("P9", "sign: session not compared with the lists",
     [("        if (!secp256k1_scalar_eq(&noncecoef_check, &noncecoef)) {\n", "        if (0) {\n", None)]),
    ("P10", "sign: nonces not negated for an odd-y R", [(NEG_K, NEG_K.replace("if (fin_nonce_parity)", "if (0)"), None)]),
    ("P11", "sign: only r1 negated for an odd-y R",
     [(NEG_K, NEG_K.replace("        secp256k1_scalar_negate(&k[1], &k[1]);\n", ""), None)]),
    ("P12", "sign: b multiplies r1 instead of r2",
     [(S_LIN, S_LIN.replace("&k[1]);  /*", "&k[0]);  /*").replace("&k[0]);          /*", "&k[1]);          /*"),
       None)]),
    ("P13", "sign: number of signers not compared with the session",
     [("    ARG_CHECK(n_signers == n_session_signers);\n", "    (void)n_session_signers;\n", None)]),
    # PartialSigVerify
    ("Q1", "partial_sig_verify: aggregate nonce at infinity not rejected", [(INF, "    if (0) {\n", 1)]),
    ("Q2", "partial_sig_verify: nonce not negated for an odd-y R",
     [("    if (fin_nonce_parity) {\n        secp256k1_gej_neg(&rj, &rj);\n", "    if (0) {\n        secp256k1_gej_neg(&rj, &rj);\n", None)]),
    ("Q3", "partial_sig_verify: aggregate nonce in place of the signer's",
     [("    secp256k1_fullagg_effective_nonce(&rj, nonce_pts, &noncecoef);\n",
       "    secp256k1_fullagg_effective_nonce(&rj, aggnonce_pts, &noncecoef);\n", None)]),
    ("Q4", "partial_sig_verify: equation not checked", [(Q_END, Q_END.replace("return secp256k1_gej_is_infinity(&tmp);", "return 1;"), None)]),
    ("Q5", "partial_sig_verify: challenge of signer 0", [(Q_SIG, Q_SIG.replace("signer_index", "0"), None)]),
    ("Q6", "partial_sig_verify: public key of signer 0",
     [("    if (!secp256k1_xonly_pubkey_load(ctx, &pk, pubkeys[signer_index])) {\n",
       "    if (!secp256k1_xonly_pubkey_load(ctx, &pk, pubkeys[0])) {\n", None)]),
    ("Q7*", "partial_sig_verify: R at infinity not rejected", [(R_INF, "    if (0) {\n", 1)]),
    # SigAgg
    ("A1", "partial_sig_agg: number of partial signatures not compared with the session",
     [("    ARG_CHECK(n_sigs == n_signers);\n", "    (void)n_signers;\n", None)]),
    ("A2", "partial_sig_agg: first partial signature left out",
     [("    for (i = 0; i < n_sigs; i++) {\n        secp256k1_scalar s_i;\n",
       "    for (i = 1; i < n_sigs; i++) {\n        secp256k1_scalar s_i;\n", None)]),
    ("A3", "partial_sig_parse: s >= n accepted", [(PS_PARSE, PS_PARSE.replace("if (overflow)", "if (0)"), None)]),
    # Verify
    ("V1", "verify: empty list accepted",
     [("    if (n_signers == 0) {\n        return 0;\n    }\n", "", None)]),
    ("V2*", "verify: r >= p reduced mod p instead of rejected",
     [("    if (!secp256k1_fe_set_b32_limit(&r.x, sig64)) {\n        return 0;\n    }\n",
       "    secp256k1_fe_set_b32_mod(&r.x, sig64);\n", None)]),
    ("V3*", "verify: s >= n reduced mod n instead of rejected", [(V_S, V_S.replace("if (overflow)", "if (0)"), None)]),
    ("V4", "verify: R lifted with an odd y",
     [("    if (!secp256k1_ge_set_xo_var(&r, &r.x, 0)) {\n", "    if (!secp256k1_ge_set_xo_var(&r, &r.x, 1)) {\n", None)]),
    ("V5", "verify: R left out of the equation", [(V_END, "    return secp256k1_gej_is_infinity(&resj);\n", None)]),
    ("V6", "verify: equation not checked", [(V_END, V_END.replace("return secp256k1_gej_is_infinity(&resj);", "return 1;"), None)]),
    ("V7", "verify: R not hashed into the challenges", [E_VER_R]),
    ("V8", "verify: messages left out of L", [E_VER_LM]),
    # the challenge hash, changed alike in Sign, PartialSigVerify and Verify
    ("C1", "sig hash, all three: L not hashed", [E_SIG_L, E_VER_L]),
    ("C2", "sig hash, all three: messages left out of L", [E_SIG_LM, E_VER_LM]),
    ("C3", "sig hash, all three: R not hashed", [E_SIG_R, E_VER_R]),
    ("C4", "sig hash, all three: the signer's public key not hashed after R", [E_SIG_PK, E_VER_PK]),
    ("C5", "sig hash, all three: the signer's message not hashed after R", [E_SIG_M, E_VER_M]),
]

BY_DESIGN = {
    "I3*": "R = R1 + b*R2 is the point at infinity only for one value of the hash output b",
    "Q7*": "as I3*",
    "V2*": "r is hashed as given, so a signature with r + p in place of r needs a nonce point "
           "with an x-coordinate below 2^256 - p and a new forgery",
    "V3*": "needs a valid signature with s < 2^256 - n",
}


def mutate(src, edits):
    for old, new, occurrence in edits:
        count = src.count(old)
        if occurrence is None:
            if count != 1:
                sys.exit(f"expected one occurrence, found {count}:\n{old}")
            src = src.replace(old, new)
        else:
            if count <= occurrence:
                sys.exit(f"expected more than {occurrence} occurrences, found {count}:\n{old}")
            parts = src.split(old)
            src = old.join(parts[:occurrence + 1]) + new + old.join(parts[occurrence + 1:])
    return src


def run(cmd, cwd, stdin=None, timeout=900):
    try:
        r = subprocess.run(cmd, cwd=cwd, input=stdin, capture_output=True, text=True,
                           timeout=timeout)
        return r.returncode, r.stdout
    except subprocess.TimeoutExpired:
        return -1, ""


def unit_tests(tree):
    out = run(["./build/bin/tests", "--list_tests"], tree)[1].split("\n")
    start = next(i for i, l in enumerate(out) if "Module: fullagg" in l)
    names = []
    for l in out[start + 1:]:
        if "]" not in l:
            break
        names.append(l.split("]")[1].strip())
    return names


def run_driver(tree, driver_src, lines):
    """The driver's output for the cases; None if it crashes or loses lines."""
    if run(["cc", "-O2", "-Iinclude", str(driver_src), "build/lib/libsecp256k1.a", "-o",
            "build/driver"], tree)[0] != 0:
        sys.exit("the driver does not compile")
    code, out = run(["./build/driver"], tree, "\n".join(lines) + "\n")
    got = out.split("\n")[:-1]
    return got if code == 0 and len(got) == len(lines) else None


def evaluate(tree, tests, driver_src, lines, base, exhaustive):
    """(failed unit tests, cases that differ from `base`, exhaustive tests failed, outputs);
    None if it does not build."""
    if run(["cmake", "--build", "build", "-j4"], tree)[0] != 0:
        return None
    failed = [t for t in tests if run(["./build/bin/tests", f"--target={t}"], tree)[0] != 0]
    got = run_driver(tree, driver_src, lines)
    if base is None:
        differ = 0
    elif got is None:
        differ = len(lines)
    else:
        differ = sum(g != b for g, b in zip(got, base))
    ex = exhaustive and run(["./build/bin/exhaustive_tests", "1"], tree)[0] != 0
    return failed, differ, ex, got


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("secp256k1", help="path to a secp256k1 checkout with the fullagg module")
    ap.add_argument("bip_dir", help="path to bips/bip-0459")
    ap.add_argument("--cases", type=int, default=3300)
    ap.add_argument("--seed", type=int, default=7)
    ap.add_argument("--no-exhaustive", action="store_true",
                    help="do not apply the patch and do not run the exhaustive tests")
    ap.add_argument("--only", help="comma-separated mutant names")
    ap.add_argument("--check", action="store_true", help="only check that every mutant applies")
    args = ap.parse_args()

    root = Path(__file__).resolve().parent.parent
    module = Path(args.secp256k1) / MODULE
    if args.check:
        src = subprocess.run(["git", "-C", args.secp256k1, "show", f"HEAD:{MODULE}"],
                             capture_output=True, text=True, check=True).stdout
        for name, _, edits in MUTANTS:
            assert mutate(src, edits) != src, name
        print(f"{len(MUTANTS)} mutants apply")
        return
    del module

    bip_dir = Path(args.bip_dir).resolve()
    sys.path.insert(0, str(bip_dir))
    sys.path.insert(0, str(bip_dir / "secp256k1lab/src"))
    import reference as ref
    from secp256k1lab import secp256k1 as lab

    gen = fuzz.Gen(random.Random(args.seed), ref, lab)
    cases, known = fuzz.make_cases(gen, args.cases, True)
    expected = [gen.run_ref(c) for c in cases]
    lines = [fuzz.encode(c) for c in cases]
    driver_src = root / "scripts" / "fuzz_secp256k1.c"
    exhaustive = not args.no_exhaustive
    wanted = set(args.only.split(",")) if args.only else None

    with tempfile.TemporaryDirectory() as tmp:
        tree = Path(tmp)
        archive = subprocess.run(["git", "-C", args.secp256k1, "archive", "HEAD"],
                                 capture_output=True, check=True).stdout
        subprocess.run(["tar", "-x", "-C", tmp], input=archive, check=True)
        cmake = list(CMAKE)
        if exhaustive:
            patch = (root / "patches" / "secp256k1-fullagg-exhaustive-tests.patch").read_bytes()
            subprocess.run(["patch", "-p1", "-s"], cwd=tmp, input=patch, check=True)
            cmake.append("-DSECP256K1_BUILD_EXHAUSTIVE_TESTS=ON")
        else:
            cmake.append("-DSECP256K1_BUILD_EXHAUSTIVE_TESTS=OFF")
        if run(["cmake", "-S", ".", "-B", "build"] + cmake, tree)[0] != 0:
            sys.exit("cmake failed")
        original = (tree / MODULE).read_text()
        if evaluate(tree, [], driver_src, lines, None, False) is None:
            sys.exit("the unmutated module does not build")
        tests = unit_tests(tree)
        failed, _, ex, base = evaluate(tree, tests, driver_src, lines, None, exhaustive)
        if failed or ex or base is None:
            sys.exit(f"the unmutated module fails: {failed}, exhaustive tests fail: {ex}")
        bad = [l for l, e, g, k in zip(lines, expected, base, known)
               if g != "SKIP" and e != g and k is None]
        if bad:
            sys.exit(f"the unmutated module differs from the reference on {len(bad)} cases, "
                     f"the first one:\n{bad[0]}")
        print(f"{len(tests)} unit tests, {len(lines)} cases"
              f"{', exhaustive tests' if exhaustive else ''}", flush=True)
        survivors, only_ex = [], []
        for name, description, edits in MUTANTS:
            if wanted is not None and name not in wanted:
                continue
            (tree / MODULE).write_text(mutate(original, edits))
            result = evaluate(tree, tests, driver_src, lines, base, exhaustive)
            if result is None:
                print(f"{name:5}{description}: does not compile")
                continue
            failed, differ, ex, _ = result
            short = ", ".join(t.replace("fullagg_", "") for t in failed) or "none"
            print(f"{name:5}{description}\n      tests: {short}\n      cases: {differ}"
                  + (f"\n      exhaustive: {'fails' if ex else 'passes'}" if exhaustive else ""),
                  flush=True)
            if not failed and not differ:
                (only_ex if ex else survivors).append(name)
        print(f"only the exhaustive tests catch: {', '.join(only_ex) or 'none'}")
        print(f"survivors: {', '.join(survivors) or 'none'}")
        for name in survivors + only_ex:
            if name in BY_DESIGN:
                print(f"  {name}: {BY_DESIGN[name]}")


if __name__ == "__main__":
    main()
