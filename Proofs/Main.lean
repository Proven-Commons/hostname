/-
  The proofs of the statements in `Spec.lean`, under the same names.
  Each statement is copied from `Spec.lean` word for word; `lake
  comparator` checks that they match. The work is in `Proofs/`; the
  test vectors are checked by the kernel with `decide`.
-/

import Hostname
import Spec.Defs
import Proofs.Match

open Hostname


/-! ## What `matchName` computes -/

/-- `matchName r p` is true exactly when the presented identifier `p`
    matches the reference identifier `r` by RFC 9525, section 6.3, as
    `Spec.Matches` sets it out. -/
theorem Spec.matchName_iff (r p : String) : matchName r p = true ↔ Spec.Matches r p :=
  Hostname.Proofs.matchName_iff' r p

/-- `validReference` accepts exactly the well formed reference
    identifiers. -/
theorem Spec.validReference_iff (r : String) :
    validReference r = true ↔ Spec.ValidReference r :=
  Hostname.Proofs.validReference_iff' r

/-- `validPresented` accepts exactly the well formed presented
    identifiers. -/
theorem Spec.validPresented_iff (p : String) :
    validPresented p = true ↔ Spec.ValidPresented p :=
  Hostname.Proofs.validPresented_iff' p

/-- `verify` succeeds exactly when some presented identifier matches
    some reference identifier (RFC 9525, section 6.2). -/
theorem Spec.verify_iff (rs ps : List String) :
    verify rs ps = true ↔ ∃ r ∈ rs, ∃ p ∈ ps, Spec.Matches r p :=
  Hostname.Proofs.verify_iff' rs ps

/-! ## Wildcards -/

/-- A presented identifier that holds `*` matches something only when
    it starts with `*.` and holds no other `*`. So two wildcards, a
    partial wildcard such as `f*.example.com`, and a wildcard outside
    the left-most label, as in `foo.*.example.com`, match nothing. -/
theorem Spec.wildcard_leftmost_only (r p : String) (h : matchName r p = true)
    (hs : '*' ∈ p.toList) : ∃ s, p.toList = '*' :: '.' :: s ∧ '*' ∉ s :=
  Hostname.Proofs.wildcard_leftmost_only' r p h hs

/-- A wildcard stands for exactly one label: when `*.s` matches `r`,
    the reference name is one label, a dot, and `s` with ASCII case
    ignored. So `*.example.com` matches neither `example.com` nor
    `a.b.example.com`. -/
theorem Spec.wildcard_one_label (r : String) (s : List Char)
    (h : matchName r (String.ofList ('*' :: '.' :: s)) = true) :
    ∃ label rest, Spec.Label label ∧ Spec.Same rest s ∧
      (r.toList = label ++ '.' :: rest ∨ r.toList = label ++ '.' :: rest ++ ['.']) :=
  Hostname.Proofs.wildcard_one_label' r s h

/-- A wildcard over a single label, such as `*.com`, matches nothing. -/
theorem Spec.wildcard_two_labels (r : String) (s : List Char)
    (h : matchName r (String.ofList ('*' :: '.' :: s)) = true) : '.' ∈ s :=
  Hostname.Proofs.wildcard_two_labels' r s h

/-! ## Case -/

/-- Changing the ASCII case of the reference identifier changes no
    answer. -/
theorem Spec.matchName_case_left (r r' p : String) (h : Spec.Same r.toList r'.toList) :
    matchName r p = matchName r' p :=
  Hostname.Proofs.matchName_case_left' r r' p h

/-- Changing the ASCII case of the presented identifier changes no
    answer. -/
theorem Spec.matchName_case_right (r p p' : String) (h : Spec.Same p.toList p'.toList) :
    matchName r p = matchName r p' :=
  Hostname.Proofs.matchName_case_right' r p p' h

/-- A reference identifier holding a character outside ASCII matches
    nothing: U-labels must be turned into A-labels first, and no
    Unicode case folding applies. -/
theorem Spec.matchName_ascii_left (r p : String) (h : ∃ c ∈ r.toList, 127 < c.toNat) :
    matchName r p = false :=
  Hostname.Proofs.matchName_ascii_left' r p h

/-- A presented identifier holding a character outside ASCII matches
    nothing. -/
theorem Spec.matchName_ascii_right (r p : String) (h : ∃ c ∈ p.toList, 127 < c.toNat) :
    matchName r p = false :=
  Hostname.Proofs.matchName_ascii_right' r p h

/-! ## Names without a wildcard -/

/-- Without a wildcard, matching is sameness with ASCII case ignored:
    `p` matches `r` exactly when both are well formed and `p` is the
    reference name with ASCII case ignored. -/
theorem Spec.matchName_exact (r p : String) (hs : '*' ∉ p.toList) :
    matchName r p = true ↔
      Spec.ExactName p ∧ ∃ name, Spec.Reference r name ∧ Spec.Same name p.toList :=
  Hostname.Proofs.matchName_exact' r p hs

/-- Every host name matches itself. -/
theorem Spec.matchName_refl (s : String) (h : Spec.HostName s.toList) : matchName s s = true :=
  Hostname.Proofs.matchName_refl' s h

/-- Swapping two names without a wildcard or a trailing dot keeps a
    match. -/
theorem Spec.matchName_symm (r p : String) (h : matchName r p = true) (hs : '*' ∉ p.toList)
    (hd : r.toList.getLast? ≠ some '.') : matchName p r = true :=
  Hostname.Proofs.matchName_symm' r p h hs hd

/-- Matching chains: when `b` matches `a` and `c` matches `b`, `c`
    matches `a`. -/
theorem Spec.matchName_trans (a b c : String) (hab : matchName a b = true)
    (hbc : matchName b c = true) : matchName a c = true :=
  Hostname.Proofs.matchName_trans' a b c hab hbc

/-! ## Test vectors -/

/-- The examples of RFC 9525: section 6.3 on case, section 6.1.2 on a
    label that differs, and section 7.1 on wildcards. -/
theorem Spec.rfc9525_examples :
    matchName "www.bigcompany.example" "WWW.BigCompany.Example" = true ∧
    matchName "WWW.BigCompany.Example" "www.bigcompany.example" = true ∧
    matchName "www.bigcompany.example" "web.bigcompany.example" = false ∧
    matchName "mail.isp.example" "mail.isp.example" = true ∧
    matchName "messenger.example" "messenger.example" = true ∧
    matchName "foo.bigcompany.example" "*.bigcompany.example" = true ∧
    matchName "foo.bar.bigcompany.example" "*.*.bigcompany.example" = false ∧
    matchName "foo.bar.bigcompany.example" "*.bigcompany.example" = false := by
  decide +kernel

/-- The wildcard examples of RFC 6125, section 6.4.3, which RFC 9525
    replaced. A wildcard matches one label only, and the partial
    wildcards RFC 6125 left to the client are turned away. -/
theorem Spec.rfc6125_examples :
    matchName "foo.example.com" "*.example.com" = true ∧
    matchName "bar.foo.example.com" "*.example.com" = false ∧
    matchName "example.com" "*.example.com" = false ∧
    matchName "baz1.example.net" "baz*.example.net" = false ∧
    matchName "foobaz.example.net" "*baz.example.net" = false ∧
    matchName "buzz.example.net" "b*z.example.net" = false := by
  decide +kernel

/-- The name checks of the x509-limbo test suite (groups `webpki::san`
    and `rfc5280::san`), each with the answer the suite expects. -/
theorem Spec.limbo_vectors :
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
    matchName "8.8.8.8" "8.8.8.8" = false := by
  decide +kernel

/-- What this library does not catch: a wildcard over a public suffix
    of two or more labels. x509-limbo expects both to fail, which needs
    the Public Suffix List. -/
theorem Spec.public_suffix_limit :
    matchName "example.co.uk" "*.co.uk" = true ∧
    matchName "example.s3.amazonaws.com" "*.s3.amazonaws.com" = true := by
  decide +kernel

/-- Names that are not well formed, and pairs that must not match. -/
theorem Spec.reject_vectors :
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
    matchName "example.com" "example.com\x00" = false := by
  decide +kernel

/-- Pairs that must match: case, a trailing dot on the reference, a
    digit first, a one-label name, A-labels, and hyphens inside a
    label. -/
theorem Spec.accept_vectors :
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
    matchName "a-b.c-d.example" "*.c-d.example" = true := by
  decide +kernel

/-- The length limits: a label of 63 characters and a name of 253 are
    accepted; a label of 64 and a name of 254 are not. -/
theorem Spec.length_vectors :
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
        List.replicate 60 'b')) = false := by
  decide +kernel
