/-
  Command line front end.

    hostname check REFERENCE PRESENTED...

  prints, for each presented identifier, `match` or `no match` against
  the reference identifier, and exits with 0 when one matches and 1
  when none does.

    hostname serve

  answers requests on standard input, one per line, for the
  differential tests. A string is sent as the hex digits of its UTF-8
  bytes, so that any character, a space or line break included, can
  be sent.

    match HEX HEX     prints 1 when the second string, a presented
                      identifier, matches the first, a reference
                      identifier, and 0 otherwise
    ref HEX           prints 1 when the string is a well formed
                      reference identifier, and 0 otherwise
    presented HEX     prints 1 when the string is a well formed
                      presented identifier, and 0 otherwise
    verify LIST LIST  prints 1 when some presented identifier in the
                      second list matches some reference identifier in
                      the first, and 0 otherwise. A list is its strings
                      in hex joined by `,`, or `-` when it is empty.

  A malformed request prints `error`: an unknown operation, the wrong
  number of arguments, hex digits that are not in pairs, or bytes that
  are not UTF-8. A request line may end in LF or CR LF.

  Every answer comes from the proved functions in `Hostname/`:
  `matchName`, `validReference`, `validPresented` and `verify`. The hex
  decoding and the request handling here are covered by the tests, not
  by a proof.
-/

import Hostname

open Hostname

def hexValue (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

def hexBytes : List Char → Option (List UInt8)
  | [] => some []
  | a :: b :: rest => do
    let hi ← hexValue a
    let lo ← hexValue b
    let bs ← hexBytes rest
    pure ((hi * 16 + lo).toUInt8 :: bs)
  | [_] => none

/-- The string whose UTF-8 bytes the hex digits give. -/
def fromHex (h : String) : Option String := do
  let bs ← hexBytes h.toList
  String.fromUTF8? ⟨bs.toArray⟩

/-- A list of strings: hex strings joined by `,`, or `-` for none. -/
def fromHexList (h : String) : Option (List String) :=
  if h == "-" then some [] else (h.splitOn ",").mapM fromHex

def showBool (b : Bool) : String := if b then "1" else "0"

/-- The answer to one request line, or `none` when it is malformed. -/
def request (line : String) : Option String :=
  match line.splitOn " " with
  | ["match", hr, hp] => do
    let r ← fromHex hr
    let p ← fromHex hp
    pure (showBool (matchName r p))
  | ["ref", h] => do
    let r ← fromHex h
    pure (showBool (validReference r))
  | ["presented", h] => do
    let p ← fromHex h
    pure (showBool (validPresented p))
  | ["verify", hrs, hps] => do
    let rs ← fromHexList hrs
    let ps ← fromHexList hps
    pure (showBool (verify rs ps))
  | _ => none

/-- The line without its line ending: LF, or CR LF. -/
def chomp (line : String) : String :=
  let cs := line.toList
  if cs.getLast? = some '\n' then
    let cs := cs.dropLast
    String.ofList (if cs.getLast? = some '\r' then cs.dropLast else cs)
  else line

def serve : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    stdout.putStrLn ((request (chomp line)).getD "error")

def check (reference : String) (presented : List String) : IO UInt32 := do
  let mut found := false
  for p in presented do
    if matchName reference p then
      IO.println s!"match\t{p}"
      found := true
    else
      IO.println s!"no match\t{p}"
  return if found then 0 else 1

def usage : String :=
  "usage: hostname check REFERENCE PRESENTED...\n       hostname serve"

def main (args : List String) : IO UInt32 := do
  match args with
  | "check" :: r :: ps@(_ :: _) => check r ps
  | ["serve"] => serve; return 0
  | _ => IO.eprintln usage; return 2
