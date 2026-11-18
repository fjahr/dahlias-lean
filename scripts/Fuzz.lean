import Dahlias.Bytes

/-!
# Differential test driver

Reads one case per line from standard input, runs the byte-level model of
`Dahlias.Bytes` on it and prints one result per line. `scripts/fuzz.py`
generates the cases and compares the results with BIP 459's Python reference.

Line formats (hex fields, `_` for empty bytes, `-` for an empty list or an
absent optional argument, lists separated by `,`):

* `G rand sk extra_in`: `NonceGen` with the given `rand'`
* `N pubnonces`: `NonceAgg`
* `S secnonce sk m aggnonce pks msgs pubnonces`: `Sign`
* `A aggnonce pks msgs pubnonces psigs`: `SigAgg`
* `P psig pks msgs pubnonces index`: `PartialSigVerify`
* `V pks msgs sig`: `Verify`
* `T sk t xonly`: `TweakSK` and `TweakPK`
-/

open Dahlias Dahlias.Bytes Taproot.BIP340Vectors

def field (s : String) : Bytes := if s == "_" then [] else hex s

def toHex (b : Bytes) : String :=
  let d (x : Nat) : Char := "0123456789abcdef".toList.getD x '0'
  String.ofList (b.flatMap fun x => [d (x.toNat / 16), d (x.toNat % 16)])

def fields (s : String) : List Bytes := if s == "-" then [] else (s.splitOn ",").map field

def showOpt : Option Bytes → String
  | none => "FAIL"
  | some b => toHex b

def run (line : String) : String :=
  let O := fastOps
  match line.splitOn " " with
  | ["G", rand, sk, extraIn] =>
    match Bytes.nonceGen O (field rand) (if sk == "-" then none else some (field sk))
        (field extraIn) with
    | some (sec, pub) => toHex sec ++ ":" ++ toHex pub
    | none => "FAIL"
  | ["N", pubnonces] => showOpt (Bytes.nonceAgg O (fields pubnonces))
  | ["S", secnonce, sk, m, aggnonce, pks, msgs, pubnonces] =>
    showOpt (Bytes.sign O (field secnonce) (field sk) (field m) (field aggnonce) (fields pks)
      (fields msgs) (fields pubnonces))
  | ["A", aggnonce, pks, msgs, pubnonces, psigs] =>
    showOpt (Bytes.sigAgg O (field aggnonce) (fields pks) (fields msgs) (fields pubnonces)
      (fields psigs))
  | ["P", psig, pks, msgs, pubnonces, i] =>
    toString (Bytes.partialSigVerify O (field psig) (fields pks) (fields msgs) (fields pubnonces)
      i.toNat!)
  | ["V", pks, msgs, sig] => toString (Bytes.verify O (fields pks) (fields msgs) (field sig))
  | ["T", sk, t, xonly] =>
    match Bytes.tweakSK O (field sk) (field t) (xonly == "1"),
        Bytes.tweakPKOfSK O (field sk) (field t) (xonly == "1") with
    | some sk', some pk' => toHex sk' ++ ":" ++ toHex pk'
    | none, none => "FAIL"
    | _, _ => "MIXED"
  | _ => "BADLINE"

partial def loop (stdin stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  stdout.putStrLn (run (String.ofList (line.toList.filter (· != '\n'))))
  stdout.flush
  loop stdin stdout

def main : IO Unit := do
  loop (← IO.getStdin) (← IO.getStdout)
