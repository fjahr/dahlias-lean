#!/usr/bin/env python3
"""
Differential test of the Lean byte-level model against BIP 459's Python reference.

Usage:
    python3 scripts/fuzz.py path/to/bips/bip-0459 [--cases N] [--seed S]
        [--secp256k1 path/to/fuzz_secp256k1] [--no-lean]

Generates honest signing sessions and malformed variants of every input of
NonceGen, NonceAgg, Sign, SigAgg, PartialSigVerify, Verify and the key tweaks,
runs them through reference.py and through the Lean model (scripts/Fuzz.lean),
and reports every case where the two disagree.

reference.py takes parsed points and scalars. The byte arrays are parsed here
the way bip-0459/run_test_vectors.py parses them, so a parse failure counts as
a failure of the algorithm. Lengths are checked here first: secp256k1lab
accepts scalars of any length and asserts on the length of a public key.

With --secp256k1, the same cases also run through libsecp256k1's fullagg
module, using the driver built from scripts/fuzz_secp256k1.c. The C API cannot
express fields of the wrong length; the driver skips those cases.

Two more kinds of cases test the state that only the C API keeps: signing
twice with the same secnonce object (the second call must fail), and signing
with lists that differ from the ones the session was initialized with (must
fail unless the lists give the same nonce coefficient input).

The specification text, the reference and the C API disagree on some malformed
inputs (see KNOWN below). Those cases are counted separately and do not fail
the run.
"""

import argparse
import os
import random
import subprocess
import sys
from pathlib import Path

P = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
EDGES = [0, 1, 2, 5, P - 1, P, P + 1, N - 1, N, N + 1, 2**255, 2**256 - 1]

# Malformed inputs on which the specification text and reference.py differ.
KNOWN = {
    "lazy-pk": "a public key of another signer does not lift; the specification of Sign, "
               "SigAgg and PartialSigVerify never decodes it, the reference runner does",
    "lazy-r1": "the first half of another signer's public nonce is not a point; the "
               "specification of Sign and SigAgg only decodes the second halves",
    "empty-nonceagg": "NonceAgg of an empty array: the specification fails, the reference "
                      "raises IndexError",
    "secnonce-range": "a secret nonce scalar is zero or not below n; the specification fails, "
                      "the C secnonce object is opaque and partial_sign only rejects the "
                      "all-zero nonce and reduces mod n",
}


def b32(x):
    return x.to_bytes(32, "big")


def flip_parity(c):
    return bytes([c[0] ^ 1]) + c[1:]


class Session:
    """An honest session, as byte arrays."""

    def __init__(self, gen, u):
        ref, rng = gen.ref, gen.rng
        self.sks = [rng.choice(gen.keys) for _ in range(u)]
        self.msgs = [rng.choice(gen.msgs) if rng.random() < 0.5 else rng.randbytes(32)
                     for _ in range(u)]
        self.pks = [(gen.Scalar.from_bytes_checked(sk) * gen.G).to_bytes_xonly()
                    for sk in self.sks]
        self.secnonces, self.pubnonces = [], []
        for sk in self.sks:
            (r1, r2), (R1, R2) = ref.NonceGenInternal(rng.randbytes(32))
            self.secnonces.append(r1.to_bytes() + r2.to_bytes())
            self.pubnonces.append(R1.to_bytes_compressed() + R2.to_bytes_compressed())
        self.aggnonce = gen.run_ref(("N", list(self.pubnonces)))
        self.aggnonce = bytes.fromhex(self.aggnonce) if self.aggnonce != "FAIL" else b""

    def sign_case(self, i):
        return ["S", self.secnonces[i], self.sks[i], self.msgs[i], self.aggnonce,
                list(self.pks), list(self.msgs), list(self.pubnonces)]


class Gen:
    def __init__(self, rng, ref, lab):
        self.rng, self.ref = rng, ref
        self.G, self.GE, self.Scalar = lab.G, lab.GE, lab.Scalar
        # a small key pool, so that repeated keys and messages occur
        self.keys = [b32(rng.randrange(1, N)) for _ in range(4)]
        self.msgs = [rng.randbytes(32) for _ in range(4)]

    # ---- helpers

    def rbytes(self, n):
        return self.rng.randbytes(n)

    def odd_len(self, good):
        return self.rbytes(self.rng.choice([0, 1, good - 1, good + 1, 2 * good]))

    def edge(self):
        return b32(self.rng.choice(EDGES))

    def point(self):
        return (self.rng.randrange(1, N) * self.G).to_bytes_compressed()

    def bad_point(self):
        k = self.rng.randrange(5)
        if k == 0: return bytes(33)
        if k == 1: return bytes([self.rng.choice([0, 1, 4, 5, 6, 7])]) + self.point()[1:]
        if k == 2: return b"\x02" + b32(self.rng.choice([P, P + 1, 2**256 - 1]))
        if k == 3: return b"\x02" + b32(5)  # x = 5 is not on the curve
        return bytes([self.rng.choice([2, 3])]) + self.rbytes(32)

    def unliftable(self):
        return b32(self.rng.choice([5, P, P + 1, 2**256 - 1]))

    def session(self, lo=1, hi=4):
        return Session(self, self.rng.randint(lo, hi))

    def psigs(self, s):
        out = []
        for i in range(len(s.sks)):
            r = self.run_ref(tuple(s.sign_case(i)))
            out.append(bytes.fromhex(r) if r != "FAIL" else b32(0))
        return out

    # ---- running the reference on byte arrays

    def parse_nonce(self, b):
        if len(b) != 66:
            raise ValueError("nonce must be 66 bytes")
        return self.GE.from_bytes_compressed(b[:33]), self.GE.from_bytes_compressed(b[33:])

    def parse_secnonce(self, b):
        if len(b) != 64:
            raise ValueError("secnonce must be 64 bytes")
        return self.scalar(b[:32]), self.scalar(b[32:])

    def parse_pks(self, pks):
        if any(len(b) != 32 for b in pks):
            raise ValueError("public keys must be 32 bytes")
        return [self.GE.from_bytes_xonly(b) for b in pks]

    def scalar(self, b):
        # secp256k1lab's from_bytes_checked accepts any length
        if len(b) != 32:
            raise ValueError("scalars must be 32 bytes")
        return self.Scalar.from_bytes_checked(b)

    def run_ref(self, case):
        ref = self.ref
        kind = case[0]
        try:
            if kind == "G":
                _, rand, sk, extra = case
                sk = self.scalar(sk) if sk is not None else None
                (r1, r2), (R1, R2) = ref.NonceGenInternal(rand, sk, extra)
                return (r1.to_bytes() + r2.to_bytes()).hex() + ":" + \
                    (R1.to_bytes_compressed() + R2.to_bytes_compressed()).hex()
            if kind == "N":
                R1, R2 = ref.NonceAgg([self.parse_nonce(b) for b in case[1]])
                return (R1.to_bytes_compressed() + R2.to_bytes_compressed()).hex()
            if kind == "R":
                r = self.run_ref(("S",) + tuple(case[1:]))
                return r if r == "FAIL" else r + ":reuse-rejected"
            if kind == "X":
                _, secnonce, sk, m, aggnonce, pks, msgs, pubnonces, pks2, msgs2, pubnonces2 = case
                # the session must initialize on the first lists
                if len(pks) != len(msgs) or len(pks) != len(pubnonces) or not pks:
                    raise ValueError("list lengths")
                self.parse_nonce(aggnonce)
                self.parse_pks(pks)
                first = [self.parse_nonce(b) for b in pubnonces]
                # the first halves of the public nonces are not part of the session
                same = (pks == pks2 and msgs == msgs2 and len(pubnonces) == len(pubnonces2)
                        and all(a[33:] == b[33:] for a, b in zip(pubnonces, pubnonces2)))
                ref.GetSessionValues(self.parse_nonce(aggnonce), self.parse_pks(pks), msgs, first)
                if not same:
                    raise ValueError("session mismatch")
                return self.run_ref(("S", secnonce, sk, m, aggnonce, pks2, msgs2, pubnonces2))
            if kind == "S":
                _, secnonce, sk, m, aggnonce, pks, msgs, pubnonces = case
                return ref.Sign(self.parse_secnonce(secnonce), self.scalar(sk), m,
                                self.parse_nonce(aggnonce), self.parse_pks(pks), msgs,
                                [self.parse_nonce(b) for b in pubnonces]).to_bytes().hex()
            if kind == "A":
                _, aggnonce, pks, msgs, pubnonces, psigs = case
                R, s = ref.SigAgg(self.parse_nonce(aggnonce), self.parse_pks(pks), msgs,
                                  [self.parse_nonce(b) for b in pubnonces],
                                  [self.scalar(b) for b in psigs])
                return (R.to_bytes_xonly() + s.to_bytes()).hex()
            if kind == "P":
                _, psig, pks, msgs, pubnonces, i = case
                ok = ref.PartialSigVerify(self.scalar(psig), self.parse_pks(pks),
                                          msgs, [self.parse_nonce(b) for b in pubnonces], i)
                return "true" if ok else "false"
            if kind == "V":
                _, pks, msgs, sig = case
                if len(sig) != 64:
                    raise ValueError("signature must be 64 bytes")
                R = self.GE.from_bytes_xonly(sig[:32])
                s = self.scalar(sig[32:])
                return "true" if ref.Verify(self.parse_pks(pks), msgs, (R, s)) else "false"
            if kind == "T":
                _, sk, t, xonly = case
                sk = self.scalar(sk)
                if sk == 0:
                    raise ValueError("secret key is zero")
                t = self.scalar(t)
                outs = []
                for fn, key in ((ref.TweakSK, sk), (ref.TweakPK, sk * self.G)):
                    try:
                        outs.append(fn(key, t, xonly))
                    except ValueError:
                        outs.append(None)
                if outs[0] is None and outs[1] is None:
                    return "FAIL"
                if outs[0] is None or outs[1] is None:
                    return "MIXED"
                return outs[0].to_bytes().hex() + ":" + outs[1].to_bytes_compressed().hex()
        except ValueError:
            return "false" if kind in "PV" else "FAIL"
        except (IndexError, AssertionError) as e:
            return "RAISED " + type(e).__name__
        raise AssertionError(kind)

    # ---- cases; each returns (case, known-divergence label or None)

    def case_noncegen(self):
        sk = None
        if self.rng.random() < 0.6:
            sk = self.rng.choice(self.keys)
        extra = self.rbytes(self.rng.choice([0, 0, 1, 32, 33, 100]))
        return ("G", self.rbytes(32), sk, extra), None

    def case_nonceagg(self):
        s = self.session(1, 4)
        nonces = list(s.pubnonces)
        known = None
        r = self.rng.random()
        if r < 0.15:
            i = self.rng.randrange(len(nonces))
            h = self.rng.randrange(2)
            bad = self.bad_point()
            nonces[i] = bad + nonces[i][33:] if h == 0 else nonces[i][:33] + bad
        elif r < 0.25:
            # two nonces whose first or second halves cancel
            a = nonces[0]
            h = self.rng.randrange(2)
            neg = flip_parity(a[:33]) + self.point() if h == 0 else self.point() + flip_parity(a[33:])
            nonces = [a, neg]
        elif r < 0.32:
            nonces[self.rng.randrange(len(nonces))] = self.odd_len(66)
        elif r < 0.36:
            nonces, known = [], "empty-nonceagg"
        return ("N", nonces), known

    def case_sign(self):
        s = self.session(1, 4)
        u = len(s.sks)
        i = self.rng.randrange(u)
        c = s.sign_case(i)
        known = None
        r = self.rng.random()
        j = self.rng.randrange(u)
        if r < 0.40:
            pass
        elif r < 0.46 and u >= 2 and j != i:
            # the signer's R2 at a second index
            c[7][j] = c[7][j][:33] + c[7][i][33:]
        elif r < 0.50:
            c[7][i] = c[7][i][:33] + self.point()
        elif r < 0.54:
            c[6][i] = self.rbytes(32)
        elif r < 0.58:
            c[5][i] = s.pks[j] if s.pks[j] != s.pks[i] else b32(1)
        elif r < 0.62:
            c[3] = self.rbytes(32)
        elif r < 0.66:
            # any aggregate nonce the coordinator likes
            c[4] = self.point() + self.point()
        elif r < 0.70:
            h = self.rng.randrange(2)
            c[4] = self.bad_point() + c[4][33:] if h == 0 else c[4][:33] + self.bad_point()
        elif r < 0.73:
            c[4] = self.odd_len(66)
        elif r < 0.77:
            h = self.rng.randrange(2)
            e = self.edge()
            c[1] = e + c[1][32:] if h == 0 else c[1][:32] + e
            if not 0 < int.from_bytes(e, "big") < N:
                known = "secnonce-range"
        elif r < 0.80:
            c[2] = self.edge()
        elif r < 0.83:
            k = self.rng.choice([1, 2, 3, 5, 6, 7])
            c[k] = self.odd_len(len(c[k])) if isinstance(c[k], bytes) else c[k][:-1]
        elif r < 0.86:
            k = self.rng.choice([5, 6, 7])
            c[k][j] = self.odd_len(len(c[k][j]))
        elif r < 0.90 and u >= 2 and j != i:
            c[5][j], known = self.unliftable(), "lazy-pk"
        elif r < 0.94 and u >= 2 and j != i:
            c[7][j], known = self.bad_point() + c[7][j][33:], "lazy-r1"
        elif r < 0.97:
            c[7][j] = c[7][j][:33] + self.bad_point()
        else:
            # the signer's own R1 replaced: Sign does not look at it
            c[7][i] = self.point() + c[7][i][33:]
        return tuple(c), known

    def case_reuse(self):
        c, known = self.case_sign()
        return ("R",) + tuple(c[1:]), known

    def case_session(self):
        s = self.session(1, 4)
        u = len(s.sks)
        i = self.rng.randrange(u)
        c = s.sign_case(i)
        pks2, msgs2, nonces2 = list(c[5]), list(c[6]), list(c[7])
        j = self.rng.randrange(u)
        r = self.rng.random()
        if r < 0.20:
            pass
        elif r < 0.35:
            msgs2[j] = self.rbytes(32)
        elif r < 0.50:
            pks2[j] = s.pks[(j + 1) % u] if s.pks[(j + 1) % u] != pks2[j] else self.session(1, 1).pks[0]
        elif r < 0.65:
            nonces2[j] = nonces2[j][:33] + self.point()
        elif r < 0.80:
            # only the first half changes: not part of the session
            nonces2[j] = self.point() + nonces2[j][33:]
        elif r < 0.90 and u >= 2:
            pks2.pop(); msgs2.pop(); nonces2.pop()
        else:
            pks2.append(pks2[0]); msgs2.append(msgs2[0]); nonces2.append(self.point() + self.point())
        return ("X",) + tuple(c[1:]) + (pks2, msgs2, nonces2), None

    def case_sigagg(self):
        s = self.session(1, 4)
        u = len(s.sks)
        psigs = self.psigs(s)
        c = ["A", s.aggnonce, list(s.pks), list(s.msgs), list(s.pubnonces), psigs]
        known = None
        r = self.rng.random()
        j = self.rng.randrange(u)
        if r < 0.45:
            pass
        elif r < 0.55:
            c[5][j] = self.edge()
        elif r < 0.60:
            c[5][j] = self.odd_len(32)
        elif r < 0.67:
            k = self.rng.choice([2, 3, 4, 5])
            c[k] = c[k][:-1] if self.rng.random() < 0.5 else c[k] + [c[k][0]]
        elif r < 0.73:
            c[1] = self.point() + self.point()
        elif r < 0.79:
            c[1] = self.bad_point() + c[1][33:]
        elif r < 0.84:
            c[2][j], known = self.unliftable(), "lazy-pk"
        elif r < 0.89:
            c[4][j], known = self.bad_point() + c[4][j][33:], "lazy-r1"
        elif r < 0.94:
            c[4][j] = c[4][j][:33] + self.bad_point()
        else:
            c[3][j] = self.odd_len(32)
        return tuple(c), known

    def case_partial(self):
        s = self.session(1, 4)
        u = len(s.sks)
        psigs = self.psigs(s)
        i = self.rng.randrange(u)
        c = ["P", psigs[i], list(s.pks), list(s.msgs), list(s.pubnonces), i]
        known = None
        r = self.rng.random()
        j = self.rng.randrange(u)
        if r < 0.40:
            pass
        elif r < 0.48:
            c[1] = b32((int.from_bytes(c[1], "big") + 1) % N)
        elif r < 0.54:
            c[1] = self.edge()
        elif r < 0.60:
            c[5] = self.rng.choice([u, u + 1, (i + 1) % u])
        elif r < 0.66:
            c[3][j] = self.rbytes(32)
        elif r < 0.72:
            c[4][j] = self.point() + self.point()
        elif r < 0.78:
            h = self.rng.randrange(2)
            c[4][j] = self.bad_point() + c[4][j][33:] if h == 0 else c[4][j][:33] + self.bad_point()
        elif r < 0.84 and u >= 2 and j != i:
            c[2][j], known = self.unliftable(), "lazy-pk"
        elif r < 0.89:
            c[2][i] = self.unliftable()
        elif r < 0.94:
            k = self.rng.choice([2, 3, 4])
            c[k] = c[k][:-1] if self.rng.random() < 0.5 else c[k] + [c[k][0]]
        else:
            c[1] = self.odd_len(32)
        return tuple(c), known

    def case_verify(self):
        s = self.session(1, 4)
        u = len(s.sks)
        sig = self.run_ref(("A", s.aggnonce, s.pks, s.msgs, s.pubnonces, self.psigs(s)))
        sig = bytes.fromhex(sig) if sig != "FAIL" else self.rbytes(64)
        c = ["V", list(s.pks), list(s.msgs), sig]
        r = self.rng.random()
        j = self.rng.randrange(u)
        if r < 0.40:
            pass
        elif r < 0.48:
            a = bytearray(sig)
            a[self.rng.randrange(64)] ^= 1 << self.rng.randrange(8)
            c[3] = bytes(a)
        elif r < 0.54:
            c[3] = sig[:32] + self.edge()
        elif r < 0.60:
            c[3] = self.edge() + sig[32:]
        elif r < 0.64:
            c[3] = self.odd_len(64)
        elif r < 0.70:
            c[2][j] = self.rbytes(32)
        elif r < 0.76:
            c[1][j] = self.rng.choice([self.unliftable(), self.rbytes(32), self.odd_len(32)])
        elif r < 0.82 and u >= 2:
            k = self.rng.randrange(u - 1)
            c[1][k], c[1][k + 1] = c[1][k + 1], c[1][k]
            c[2][k], c[2][k + 1] = c[2][k + 1], c[2][k]
        elif r < 0.88:
            c[1].pop(); c[2].pop()
        elif r < 0.93:
            c[1].append(c[1][0]); c[2].append(c[2][0])
        elif r < 0.97:
            c[2][j] = self.odd_len(32)
        else:
            c[1].pop()
        return tuple(c), None

    def case_tweak(self):
        sk = self.rng.choice(self.keys + [self.edge()])
        r = self.rng.random()
        if r < 0.5:
            t = b32(self.rng.randrange(N))
        elif r < 0.7:
            t = self.edge()
        elif r < 0.9:
            # tweaks that cancel the key or its negation
            d = int.from_bytes(sk, "big") % N
            t = b32(self.rng.choice([(N - d) % N, d]))
        else:
            t = self.odd_len(32)
        return ("T", sk, t, self.rng.random() < 0.5), None


def hx(b):
    return b.hex() if b else "_"


def enc(x):
    if x is None: return "-"
    if isinstance(x, bool): return "1" if x else "0"
    if isinstance(x, int): return str(x)
    if isinstance(x, bytes): return hx(x)
    return ",".join(hx(b) for b in x) if x else "-"


def encode(case):
    return case[0] + " " + " ".join(enc(x) for x in case[1:])


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("bip_dir", help="path to bips/bip-0459")
    ap.add_argument("--cases", type=int, default=700)
    ap.add_argument("--seed", type=int, default=459)
    ap.add_argument("--secp256k1", help="path to the driver built from scripts/fuzz_secp256k1.c")
    ap.add_argument("--no-lean", action="store_true", help="skip the Lean model")
    args = ap.parse_args()

    bip_dir = Path(args.bip_dir).resolve()
    sys.path.insert(0, str(bip_dir))
    sys.path.insert(0, str(bip_dir / "secp256k1lab/src"))
    import reference as ref
    from secp256k1lab import secp256k1 as lab

    gen = Gen(random.Random(args.seed), ref, lab)
    makers = [gen.case_noncegen, gen.case_nonceagg, gen.case_sign, gen.case_sign, gen.case_sigagg,
              gen.case_partial, gen.case_verify, gen.case_verify, gen.case_tweak]
    if args.secp256k1:
        makers += [gen.case_reuse, gen.case_session]
    made = [makers[i % len(makers)]() for i in range(args.cases)]
    cases = [c for c, _ in made]
    known = [k for _, k in made]
    expected = [gen.run_ref(c) for c in cases]

    kinds = {}
    for c, e in zip(cases, expected):
        key = (c[0], "reject" if e in ("FAIL", "false") or e.startswith("RAISED") else "accept")
        kinds[key] = kinds.get(key, 0) + 1
    for key in sorted(kinds):
        print(f"{key[0]} {key[1]}: {kinds[key]}")

    root = Path(__file__).resolve().parent.parent
    env = dict(os.environ, PATH=os.path.expanduser("~/.elan/bin") + os.pathsep + os.environ["PATH"])
    targets = []
    if not args.no_lean:
        targets.append(("lean", ["lake", "env", "lean", "--run", "scripts/Fuzz.lean"]))
    if args.secp256k1:
        targets.append(("secp256k1", [str(Path(args.secp256k1).resolve())]))

    lines = [encode(c) for c in cases]
    failed = False
    for name, cmd in targets:
        out = subprocess.run(cmd, cwd=root, env=env, input="\n".join(lines) + "\n",
                             capture_output=True, text=True)
        got = out.stdout.split("\n")[:-1]
        if out.returncode != 0 or len(got) != len(cases):
            sys.exit(f"{name} driver failed ({len(got)} of {len(cases)} results):\n{out.stderr}")
        bad, skipped, diverged = 0, 0, {}
        for l, k, e, g in zip(lines, known, expected, got):
            if g == "SKIP":
                skipped += 1
            elif e == g:
                continue
            elif k is not None:
                diverged.setdefault(k, []).append((e, g))
            else:
                bad += 1
                if bad <= 10:
                    print(f"MISMATCH\n  case:   {l}\n  python: {e}\n  {name}: {g}")
        for k, d in sorted(diverged.items()):
            outcomes = sorted({(e if len(e) < 20 else "ok", g if len(g) < 20 else "ok")
                               for e, g in d})
            print(f"{name}: known difference '{k}' in {len(d)} cases, "
                  f"(python, {name}) = {outcomes}\n  {KNOWN[k]}")
        print(f"{name}: {len(cases) - skipped} cases compared, {skipped} skipped, "
              f"{bad} mismatches")
        failed = failed or bool(bad)
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()
