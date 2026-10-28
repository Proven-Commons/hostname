/-
  Host name matching, RFC 9525 section 6.3: the code under proof.

  A TLS client compares the name it meant to reach, the reference
  identifier, with each DNS name in the server's certificate, the
  presented identifiers. `matchName` makes one such comparison. Labels
  are compared in order, with ASCII case ignored, and a presented name
  may start with the wildcard label `*`, which stands for exactly one
  label. A name that is not well formed matches nothing.

  The definitions work on lists of characters, which suit the proofs.
  `Spec.lean` states what they compute, from definitions written
  separately in `Spec/Defs.lean`.
-/

namespace Hostname

/-- An ASCII digit. -/
def isDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

/-- An ASCII letter or digit. -/
def isLetDig (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') || isDigit c

/-- An ASCII letter, digit or hyphen. -/
def isLDH (c : Char) : Bool := isLetDig c || c == '-'

/-- A label: 1 to 63 ASCII letters, digits and hyphens, starting and
    ending with a letter or digit. -/
def validLabel (l : List Char) : Bool :=
  match l.head?, l.getLast? with
  | some a, some b => l.length ≤ 63 && isLetDig a && isLetDig b && l.all isLDH
  | _, _ => false

/-- The last label holds a character other than a digit. -/
def lastNotNumeric (ls : List (List Char)) : Bool :=
  match ls.getLast? with
  | some l => !l.all isDigit
  | none => false

/-- A host name: at most 253 characters, labels between dots, and a
    last label that is not all digits, so that no IPv4 address in
    dotted form is a host name. -/
def validName (cs : List Char) : Bool :=
  cs.length ≤ 253 && (cs.splitOn '.').all validLabel && lastNotNumeric (cs.splitOn '.')

/-- The name without the trailing dot of an absolute name, if it has
    one. -/
def dropDot (cs : List Char) : List Char :=
  if cs.getLast? = some '.' then cs.dropLast else cs

/-- What follows `*.` at the start of a presented name. -/
def wildcardSuffix? : List Char → Option (List Char)
  | '*' :: '.' :: s => some s
  | _ => none

/-- What follows the first dot. -/
def afterFirstDot : List Char → Option (List Char)
  | [] => none
  | c :: cs => if c = '.' then some cs else afterFirstDot cs

/-- ASCII lower case. Every other character is left as it is. -/
def lowerAscii (c : Char) : Char :=
  if 'A' ≤ c && c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c

/-- The same characters, with ASCII case ignored. -/
def sameIgnoringCase (a b : List Char) : Bool :=
  a.map lowerAscii == b.map lowerAscii

/-- A well formed reference identifier: a host name, written with or
    without the trailing dot of an absolute name. -/
def validReference (reference : String) : Bool :=
  validName (dropDot reference.toList)

/-- A well formed presented identifier: a host name, or `*.` followed
    by a host name of at least two labels, at most 253 characters in
    all. -/
def validPresented (presented : String) : Bool :=
  match wildcardSuffix? presented.toList with
  | some s => s.length ≤ 251 && validName s && s.contains '.'
  | none => validName presented.toList

/-- Whether the presented identifier matches the reference identifier,
    by RFC 9525 section 6.3. -/
def matchName (reference presented : String) : Bool :=
  validReference reference && validPresented presented &&
    match wildcardSuffix? presented.toList with
    | some s =>
      match afterFirstDot (dropDot reference.toList) with
      | some rest => sameIgnoringCase rest s
      | none => false
    | none => sameIgnoringCase (dropDot reference.toList) presented.toList

/-- Whether some presented identifier matches some reference
    identifier: the search of RFC 9525 section 6.2. -/
def verify (references presented : List String) : Bool :=
  references.any fun r => presented.any fun p => matchName r p

end Hostname
