/-
  The definitions the statements in `Hostname/Spec.lean` use, written from the
  standards, separately from the code in `Hostname/`.

  - A label is `<label>` of RFC 1034, section 3.5 ("preferred name
    syntax"), with a digit allowed first, as RFC 1123, section 2.1,
    allows, and at most 63 characters.
  - A host name is labels joined by dots, at most 253 characters (RFC
    1034, section 3.1, limits a name to 255 octets in the wire form,
    which is 253 characters written out). Its last label is not all
    digits, as RFC 1123, section 2.1, notes of every valid host name,
    so that no IPv4 address in dotted form is one.
  - A reference identifier is a host name, written with or without the
    trailing dot of an absolute name (RFC 1034, section 3.1).
  - A presented identifier is a host name, or the wildcard label `*`,
    a dot, and a host name of at least two labels: RFC 9525, section
    6.3, allows one wildcard, as the whole left-most label. A wildcard
    over a single label, such as `*.com`, is turned away, as a partial
    guard against wildcards over a public suffix (RFC 9525, section
    7.1).
  - Labels compare with ASCII case ignored (RFC 4343, section 3), and
    nothing else is ignored.
  - A presented name matches a reference name when it is not a
    wildcard and every label matches, or when it is a wildcard, the
    reference name has exactly one label more, and every label after
    the reference name's first matches (RFC 9525, section 6.3).
-/

namespace Hostname.Spec

/-! ## Characters -/

/-- An ASCII letter. -/
abbrev Letter (c : Char) : Prop := ('a' ≤ c ∧ c ≤ 'z') ∨ ('A' ≤ c ∧ c ≤ 'Z')

/-- An ASCII digit. -/
abbrev Digit (c : Char) : Prop := '0' ≤ c ∧ c ≤ '9'

/-- `<let-dig>` of RFC 1034, section 3.5. -/
abbrev LetDig (c : Char) : Prop := Letter c ∨ Digit c

/-- `<let-dig-hyp>` of RFC 1034, section 3.5. -/
abbrev LetDigHyp (c : Char) : Prop := LetDig c ∨ c = '-'

/-! ## Names -/

/-- `<label>` of RFC 1034, section 3.5: a letter or digit, then
    letters, digits and hyphens, ending with a letter or digit, at most
    63 characters. RFC 1123, section 2.1, allows the digit first. -/
def Label (l : List Char) : Prop :=
  l.length ≤ 63 ∧ ∃ a, LetDig a ∧
    (l = [a] ∨ ∃ mid b, l = a :: mid ++ [b] ∧ (∀ c ∈ mid, LetDigHyp c) ∧ LetDig b)

/-- A host name: labels joined by dots, at most 253 characters, with
    a last label that is not all digits. -/
def HostName (cs : List Char) : Prop :=
  cs.length ≤ 253 ∧
    ∃ init last, cs = ['.'].intercalate (init ++ [last]) ∧
      (∀ l ∈ init, Label l) ∧ Label last ∧ ∃ c ∈ last, ¬ Digit c

/-- `r` is a reference identifier, and `name` the host name it gives:
    `r` is `name`, or `name` and the trailing dot of an absolute name. -/
def Reference (r : String) (name : List Char) : Prop :=
  HostName name ∧ (r.toList = name ∨ r.toList = name ++ ['.'])

/-- `p` is a presented identifier without a wildcard. -/
def ExactName (p : String) : Prop := HostName p.toList

/-- `p` is a presented identifier with a wildcard: `*.` and then
    `suffix`, a host name of at least two labels, at most 253
    characters in all. -/
def WildcardName (p : String) (suffix : List Char) : Prop :=
  p.toList = '*' :: '.' :: suffix ∧ p.toList.length ≤ 253 ∧ HostName suffix ∧ '.' ∈ suffix

/-- A well formed reference identifier. -/
def ValidReference (r : String) : Prop := ∃ name, Reference r name

/-- A well formed presented identifier. -/
def ValidPresented (p : String) : Prop := ExactName p ∨ ∃ suffix, WildcardName p suffix

/-! ## Case -/

/-- Two characters that are the same with ASCII case ignored (RFC
    4343, section 3): the same character, or an upper case ASCII letter
    and the lower case letter 32 code points above it. -/
def SameChar (a b : Char) : Prop :=
  a = b ∨ ('A' ≤ a ∧ a ≤ 'Z' ∧ b.toNat = a.toNat + 32) ∨
    ('A' ≤ b ∧ b ≤ 'Z' ∧ a.toNat = b.toNat + 32)

/-- Two strings of the same length whose characters are the same, one
    by one, with ASCII case ignored. -/
def Same : List Char → List Char → Prop
  | [], [] => True
  | a :: as, b :: bs => SameChar a b ∧ Same as bs
  | _, _ => False

/-! ## Matching -/

/-- RFC 9525, section 6.3: the presented identifier `p` matches the
    reference identifier `r`. Both are well formed, and either `p` has
    no wildcard and is the reference name with ASCII case ignored, or
    `p` is `*.` and a suffix, and the reference name is one label, a
    dot, and that suffix with ASCII case ignored. -/
def Matches (r p : String) : Prop :=
  ∃ name, Reference r name ∧
    ((ExactName p ∧ Same name p.toList) ∨
      (∃ suffix label rest, WildcardName p suffix ∧ name = label ++ '.' :: rest ∧
        Label label ∧ Same rest suffix))

end Hostname.Spec
