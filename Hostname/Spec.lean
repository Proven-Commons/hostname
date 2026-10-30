/-
  The specification as Lean statements: the challenge file.

  A reviewer who did not write this file approves it, and `bar.toml`
  records the hash it had then. The proofs live in `Hostname/Proofs.lean`, under
  the same names; `lake comparator` checks that each one proves exactly
  the statement written here. The `sorry`s below are expected in this
  file only.

  The definitions the statements use, written from RFC 9525, RFC 1034,
  RFC 1123 and RFC 4343, are in `Hostname/Spec/Defs.lean`. That file is part of
  the specification too.
-/

import Hostname
import Hostname.Spec.Defs

open Hostname

/-! ## What `matchName` computes -/

/-- `matchName r p` is true exactly when the presented identifier `p`
    matches the reference identifier `r` by RFC 9525, section 6.3, as
    `Hostname.Spec.Matches` sets it out. -/
theorem Hostname.Spec.matchName_iff (r p : String) : matchName r p = true ↔ Hostname.Spec.Matches r p := sorry

/-- `validReference` accepts exactly the well formed reference
    identifiers. -/
theorem Hostname.Spec.validReference_iff (r : String) :
    validReference r = true ↔ Hostname.Spec.ValidReference r := sorry

/-- `validPresented` accepts exactly the well formed presented
    identifiers. -/
theorem Hostname.Spec.validPresented_iff (p : String) :
    validPresented p = true ↔ Hostname.Spec.ValidPresented p := sorry

/-- `verify` succeeds exactly when some presented identifier matches
    some reference identifier (RFC 9525, section 6.2). -/
theorem Hostname.Spec.verify_iff (rs ps : List String) :
    verify rs ps = true ↔ ∃ r ∈ rs, ∃ p ∈ ps, Hostname.Spec.Matches r p := sorry

/-! ## Wildcards -/

/-- A presented identifier that holds `*` matches something only when
    it starts with `*.` and holds no other `*`. So two wildcards, a
    partial wildcard such as `f*.example.com`, and a wildcard outside
    the left-most label, as in `foo.*.example.com`, match nothing. -/
theorem Hostname.Spec.wildcard_leftmost_only (r p : String) (h : matchName r p = true)
    (hs : '*' ∈ p.toList) : ∃ s, p.toList = '*' :: '.' :: s ∧ '*' ∉ s := sorry

/-- A wildcard stands for exactly one label: when `*.s` matches `r`,
    the reference name is one label, a dot, and `s` with ASCII case
    ignored. So `*.example.com` matches neither `example.com` nor
    `a.b.example.com`. -/
theorem Hostname.Spec.wildcard_one_label (r : String) (s : List Char)
    (h : matchName r (String.ofList ('*' :: '.' :: s)) = true) :
    ∃ label rest, Hostname.Spec.Label label ∧ Hostname.Spec.Same rest s ∧
      (r.toList = label ++ '.' :: rest ∨ r.toList = label ++ '.' :: rest ++ ['.']) := sorry

/-- A wildcard over a single label, such as `*.com`, matches nothing. -/
theorem Hostname.Spec.wildcard_two_labels (r : String) (s : List Char)
    (h : matchName r (String.ofList ('*' :: '.' :: s)) = true) : '.' ∈ s := sorry

/-! ## Case -/

/-- Changing the ASCII case of the reference identifier changes no
    answer. -/
theorem Hostname.Spec.matchName_case_left (r r' p : String) (h : Hostname.Spec.Same r.toList r'.toList) :
    matchName r p = matchName r' p := sorry

/-- Changing the ASCII case of the presented identifier changes no
    answer. -/
theorem Hostname.Spec.matchName_case_right (r p p' : String) (h : Hostname.Spec.Same p.toList p'.toList) :
    matchName r p = matchName r p' := sorry

/-- A reference identifier holding a character outside ASCII matches
    nothing: U-labels must be turned into A-labels first, and no
    Unicode case folding applies. -/
theorem Hostname.Spec.matchName_ascii_left (r p : String) (h : ∃ c ∈ r.toList, 127 < c.toNat) :
    matchName r p = false := sorry

/-- A presented identifier holding a character outside ASCII matches
    nothing. -/
theorem Hostname.Spec.matchName_ascii_right (r p : String) (h : ∃ c ∈ p.toList, 127 < c.toNat) :
    matchName r p = false := sorry

/-! ## Names without a wildcard -/

/-- Without a wildcard, matching is sameness with ASCII case ignored:
    `p` matches `r` exactly when both are well formed and `p` is the
    reference name with ASCII case ignored. -/
theorem Hostname.Spec.matchName_exact (r p : String) (hs : '*' ∉ p.toList) :
    matchName r p = true ↔
      Hostname.Spec.ExactName p ∧ ∃ name, Hostname.Spec.Reference r name ∧ Hostname.Spec.Same name p.toList := sorry

/-- Every host name matches itself. -/
theorem Hostname.Spec.matchName_refl (s : String) (h : Hostname.Spec.HostName s.toList) : matchName s s = true :=
  sorry

/-- Swapping two names without a wildcard or a trailing dot keeps a
    match. -/
theorem Hostname.Spec.matchName_symm (r p : String) (h : matchName r p = true) (hs : '*' ∉ p.toList)
    (hd : r.toList.getLast? ≠ some '.') : matchName p r = true := sorry

/-- Matching chains: when `b` matches `a` and `c` matches `b`, `c`
    matches `a`. -/
theorem Hostname.Spec.matchName_trans (a b c : String) (hab : matchName a b = true)
    (hbc : matchName b c = true) : matchName a c = true := sorry

/-! ## Test vectors -/

/-- The examples of RFC 9525: section 6.3 on case, section 6.1.2 on a
    label that differs, and section 7.1 on wildcards. -/
theorem Hostname.Spec.rfc9525_examples :
    matchName "www.bigcompany.example" "WWW.BigCompany.Example" = true ∧
    matchName "WWW.BigCompany.Example" "www.bigcompany.example" = true ∧
    matchName "www.bigcompany.example" "web.bigcompany.example" = false ∧
    matchName "mail.isp.example" "mail.isp.example" = true ∧
    matchName "messenger.example" "messenger.example" = true ∧
    matchName "foo.bigcompany.example" "*.bigcompany.example" = true ∧
    matchName "foo.bar.bigcompany.example" "*.*.bigcompany.example" = false ∧
    matchName "foo.bar.bigcompany.example" "*.bigcompany.example" = false :=
  sorry

/-- The wildcard examples of RFC 6125, section 6.4.3, which RFC 9525
    replaced. A wildcard matches one label only, and the partial
    wildcards RFC 6125 left to the client are turned away. -/
theorem Hostname.Spec.rfc6125_examples :
    matchName "foo.example.com" "*.example.com" = true ∧
    matchName "bar.foo.example.com" "*.example.com" = false ∧
    matchName "example.com" "*.example.com" = false ∧
    matchName "baz1.example.net" "baz*.example.net" = false ∧
    matchName "foobaz.example.net" "*baz.example.net" = false ∧
    matchName "buzz.example.net" "b*z.example.net" = false :=
  sorry

/-- The name checks of the x509-limbo test suite (groups `webpki::san`
    and `rfc5280::san`), each with the answer the suite expects. -/
theorem Hostname.Spec.limbo_vectors :
    matchName "example.com" "example.com" = true ∧
    matchName "example2.com" "example.com" = false ∧
    matchName "def.example.com" "abc.example.com" = false ∧
    matchName "abc.example.com" "example.com" = false ∧
    matchName "example.com" "abc.example.com" = false ∧
    matchName "example.com" "*.com" = false ∧
    matchName "foo.example.com" "*.example.com" = true ∧
    matchName "baz.example.com" "ba*.example.com" = false ∧
    matchName "foo.bar.example.com" "foo.*.example.com" = false ∧
    matchName "foo.bar.example.com" "*.example.com" = false ∧
    matchName "xn--bliss-1b3c148a.example.com" "xn--*-1b3c148a.example.com" = false ∧
    matchName "xn--628h.example.com" "😜.example.com" = false ∧
    matchName "example.com" "*" = false ∧
    matchName "com" "*" = false ∧
    matchName "foo_bar.example.com" "foo_bar.example.com" = false ∧
    matchName "8.8.8.8" "8.8.8.8" = false :=
  sorry

/-- What this library does not catch: a wildcard over a public suffix
    of two or more labels. x509-limbo expects both to fail, which needs
    the Public Suffix List. -/
theorem Hostname.Spec.public_suffix_limit :
    matchName "example.co.uk" "*.co.uk" = true ∧
    matchName "example.s3.amazonaws.com" "*.s3.amazonaws.com" = true :=
  sorry

/-- Names that are not well formed, and pairs that must not match. -/
theorem Hostname.Spec.reject_vectors :
    matchName "Key.example" "key.example" = false ∧
    matchName "key.example" "Key.example" = false ∧
    matchName "example.com" "example.com." = false ∧
    matchName "example.com.." "example.com" = false ∧
    matchName ".example.com" "example.com" = false ∧
    matchName "" "" = false ∧
    matchName "." "." = false ∧
    matchName "-a.example" "-a.example" = false ∧
    matchName "a-.example" "a-.example" = false ∧
    matchName "a..example" "a..example" = false ∧
    matchName "1.2.3.4" "*.2.3.4" = false ∧
    matchName "example.123" "example.123" = false ∧
    matchName "a.example.com" "**.example.com" = false ∧
    matchName "a.example.com" "*.*.com" = false ∧
    matchName "*.example.com" "*.example.com" = false ∧
    matchName "a.example" "*.example" = false ∧
    matchName "a.example.com" "*a.example.com" = false ∧
    matchName "a.example.com" "*.example.com." = false ∧
    matchName "a b.example" "a b.example" = false ∧
    matchName "a\x00.example" "a\x00.example" = false ∧
    matchName "example.com" "example.com\x00" = false :=
  sorry

/-- Pairs that must match: case, a trailing dot on the reference, a
    digit first, a one-label name, A-labels, and hyphens inside a
    label. -/
theorem Hostname.Spec.accept_vectors :
    matchName "FOO.Example.COM" "*.example.com" = true ∧
    matchName "foo.example.com" "*.EXAMPLE.com" = true ∧
    matchName "foo.example.com." "*.example.com" = true ∧
    matchName "example.com." "Example.Com" = true ∧
    matchName "1foo.example.com" "1foo.example.com" = true ∧
    matchName "123.example.com" "123.example.com" = true ∧
    matchName "localhost" "localhost" = true ∧
    matchName "xn--bcher-kva.example" "XN--BCHER-KVA.example" = true ∧
    matchName "xn--bcher-kva.example.com" "*.example.com" = true ∧
    matchName "a--b.example" "a--b.example" = true ∧
    matchName "a-b.c-d.example" "*.c-d.example" = true :=
  sorry

/-- The length limits: a label of 63 characters and a name of 253 are
    accepted; a label of 64 and a name of 254 are not. -/
theorem Hostname.Spec.length_vectors :
    validReference (String.ofList (List.replicate 63 'a' ++ ".example".toList)) = true ∧
    validReference (String.ofList (List.replicate 64 'a' ++ ".example".toList)) = false ∧
    validReference (String.ofList
      ((List.replicate 3 (List.replicate 63 'a' ++ ['.'])).flatten ++ List.replicate 61 'b')) =
      true ∧
    validReference (String.ofList
      ((List.replicate 3 (List.replicate 63 'a' ++ ['.'])).flatten ++ List.replicate 62 'b')) =
      false ∧
    validPresented (String.ofList
      ('*' :: '.' :: (List.replicate 3 (List.replicate 63 'a' ++ ['.'])).flatten ++
        List.replicate 59 'b')) = true ∧
    validPresented (String.ofList
      ('*' :: '.' :: (List.replicate 3 (List.replicate 63 'a' ++ ['.'])).flatten ++
        List.replicate 60 'b')) = false :=
  sorry
