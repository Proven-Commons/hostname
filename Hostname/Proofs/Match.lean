/-
  Matching: `validReference`, `validPresented` and `matchName` against
  `Hostname.Spec.ValidReference`, `Hostname.Spec.ValidPresented` and `Hostname.Spec.Matches`, and
  the laws that follow.
-/

import Hostname
import Hostname.Spec.Defs
import Hostname.Proofs.Chars
import Hostname.Proofs.Lists
import Hostname.Proofs.Names

open Hostname

namespace Hostname.Proofs

/-! ## Reference identifiers -/

/-- The host name a reference identifier gives is what `dropDot`
    leaves. -/
theorem reference_dropDot {r : String} {name : List Char} (h : Hostname.Spec.Reference r name) :
    dropDot r.toList = name := by
  rcases h with ⟨hn, h | h⟩
  · rw [h]; exact dropDot_of_getLast (hostName_getLast hn)
  · rw [h]; exact dropDot_append_dot name

theorem reference_of_valid {r : String} (h : validReference r = true) :
    Hostname.Spec.Reference r (dropDot r.toList) :=
  ⟨(validName_iff _).mp h, eq_dropDot _⟩

theorem validReference_iff' (r : String) : validReference r = true ↔ Hostname.Spec.ValidReference r := by
  constructor
  · intro h; exact ⟨_, reference_of_valid h⟩
  · rintro ⟨name, h⟩
    unfold validReference
    rw [reference_dropDot h]
    exact (validName_iff _).mpr h.1

/-! ## Presented identifiers -/

theorem hostName_wildcardSuffix {cs : List Char} (h : Hostname.Spec.HostName cs) :
    wildcardSuffix? cs = none := by
  rw [wildcardSuffix?_eq_none]
  intro s hs
  obtain ⟨a, t, rfl, ha⟩ := hostName_head h
  simp only [List.cons.injEq] at hs
  rw [hs.1] at ha
  exact not_letDig_star ha

theorem exactName_of_none {p : String} (hw : wildcardSuffix? p.toList = none)
    (h : Hostname.Spec.ValidPresented p) : Hostname.Spec.ExactName p := by
  rcases h with h | ⟨s, hs⟩
  · exact h
  · rw [wildcardSuffix?_eq_some.mpr hs.1] at hw; cases hw

theorem wildcardName_of_some {p : String} {s : List Char} (hw : wildcardSuffix? p.toList = some s)
    (h : Hostname.Spec.ValidPresented p) : Hostname.Spec.WildcardName p s := by
  rcases h with h | ⟨s', hs⟩
  · rw [hostName_wildcardSuffix h] at hw; cases hw
  · rw [wildcardSuffix?_eq_some.mpr hs.1] at hw
    cases hw
    exact hs

theorem validPresented_iff' (p : String) : validPresented p = true ↔ Hostname.Spec.ValidPresented p := by
  unfold validPresented Hostname.Spec.ValidPresented Hostname.Spec.ExactName
  cases hw : wildcardSuffix? p.toList with
  | some s =>
    have hp := wildcardSuffix?_eq_some.mp hw
    simp only [Bool.and_eq_true, decide_eq_true_eq, validName_iff, List.contains_iff_mem]
    constructor
    · rintro ⟨⟨hlen, hs⟩, hdot⟩
      exact Or.inr ⟨s, hp, by rw [hp]; simp; omega, hs, hdot⟩
    · rintro (h | ⟨s', hp', hlen, hs', hdot⟩)
      · rw [hostName_wildcardSuffix h] at hw; cases hw
      · rw [hp] at hp'
        simp only [List.cons.injEq, true_and] at hp'
        subst hp'
        rw [hp] at hlen
        simp only [List.length_cons] at hlen
        exact ⟨⟨by omega, hs'⟩, hdot⟩
  | none =>
    simp only [validName_iff]
    constructor
    · exact Or.inl
    · rintro (h | ⟨s, hp, _⟩)
      · exact h
      · rw [wildcardSuffix?_eq_some.mpr hp] at hw; cases hw

/-! ## Matching -/

theorem matchName_iff' (r p : String) : matchName r p = true ↔ Hostname.Spec.Matches r p := by
  unfold matchName
  simp only [Bool.and_eq_true]
  constructor
  · rintro ⟨⟨hr, hp⟩, hm⟩
    have hname := reference_of_valid hr
    refine ⟨dropDot r.toList, hname, ?_⟩
    have hp' := (validPresented_iff' p).mp hp
    cases hw : wildcardSuffix? p.toList with
    | some s =>
      rw [hw] at hm
      cases ha : afterFirstDot (dropDot r.toList) with
      | none => rw [ha] at hm; cases hm
      | some rest =>
        rw [ha] at hm
        obtain ⟨label, heq, hdot⟩ := afterFirstDot_eq_some.mp ha
        exact Or.inr ⟨s, label, rest, wildcardName_of_some hw hp', heq,
          first_label hname.1 heq hdot, (sameIgnoringCase_iff _ _).mp hm⟩
    | none =>
      rw [hw] at hm
      exact Or.inl ⟨exactName_of_none hw hp', (sameIgnoringCase_iff _ _).mp hm⟩
  · rintro ⟨name, hname, h⟩
    have hd := reference_dropDot hname
    refine ⟨⟨(validReference_iff' r).mpr ⟨name, hname⟩, ?_⟩, ?_⟩
    · rcases h with ⟨hex, _⟩ | ⟨s, _, _, hw, _⟩
      · exact (validPresented_iff' p).mpr (Or.inl hex)
      · exact (validPresented_iff' p).mpr (Or.inr ⟨s, hw⟩)
    · rcases h with ⟨hex, hsame⟩ | ⟨s, label, rest, hw, heq, hl, hsame⟩
      · rw [hostName_wildcardSuffix hex, hd]
        exact (sameIgnoringCase_iff _ _).mpr hsame
      · rw [wildcardSuffix?_eq_some.mpr hw.1, hd,
          afterFirstDot_eq_some.mpr ⟨label, heq, label_dot hl⟩]
        exact (sameIgnoringCase_iff _ _).mpr hsame

theorem verify_iff' (rs ps : List String) :
    verify rs ps = true ↔ ∃ r ∈ rs, ∃ p ∈ ps, Hostname.Spec.Matches r p := by
  simp [verify, List.any_eq_true, matchName_iff']

/-! ## Wildcards -/

theorem wildcard_leftmost_only' (r p : String) (h : matchName r p = true)
    (hs : '*' ∈ p.toList) : ∃ s, p.toList = '*' :: '.' :: s ∧ '*' ∉ s := by
  obtain ⟨_, _, h⟩ := (matchName_iff' r p).mp h
  rcases h with ⟨hex, _⟩ | ⟨s, _, _, hw, _⟩
  · exact absurd hs (hostName_star hex)
  · exact ⟨s, hw.1, hostName_star hw.2.2.1⟩

theorem wildcard_parts {r : String} {s : List Char}
    (h : matchName r (String.ofList ('*' :: '.' :: s)) = true) :
    ∃ name label rest, Hostname.Spec.Reference r name ∧ name = label ++ '.' :: rest ∧
      Hostname.Spec.Label label ∧ Hostname.Spec.Same rest s ∧ '.' ∈ s := by
  obtain ⟨name, hname, h⟩ := (matchName_iff' _ _).mp h
  rcases h with ⟨hex, _⟩ | ⟨s', label, rest, hw, heq, hl, hsame⟩
  · have := hostName_wildcardSuffix hex
    rw [String.toList_ofList] at this
    simp [wildcardSuffix?] at this
  · have hp := hw.1
    rw [String.toList_ofList] at hp
    simp only [List.cons.injEq, true_and] at hp
    subst hp
    exact ⟨name, label, rest, hname, heq, hl, hsame, hw.2.2.2⟩

theorem wildcard_one_label' (r : String) (s : List Char)
    (h : matchName r (String.ofList ('*' :: '.' :: s)) = true) :
    ∃ label rest, Hostname.Spec.Label label ∧ Hostname.Spec.Same rest s ∧
      (r.toList = label ++ '.' :: rest ∨ r.toList = label ++ '.' :: rest ++ ['.']) := by
  obtain ⟨name, label, rest, hname, rfl, hl, hsame, _⟩ := wildcard_parts h
  exact ⟨label, rest, hl, hsame, hname.2⟩

theorem wildcard_two_labels' (r : String) (s : List Char)
    (h : matchName r (String.ofList ('*' :: '.' :: s)) = true) : '.' ∈ s := by
  obtain ⟨_, _, _, _, _, _, _, hdot⟩ := wildcard_parts h
  exact hdot

/-! ## ASCII lower case -/

/-- The string with every ASCII letter in lower case. -/
def lowerStr (s : String) : String := String.ofList (s.toList.map lowerAscii)

theorem toList_lowerStr (s : String) : (lowerStr s).toList = s.toList.map lowerAscii := by
  simp [lowerStr]

theorem sameIgnoringCase_lower_left (a b : List Char) :
    sameIgnoringCase (a.map lowerAscii) b = sameIgnoringCase a b := by
  simp only [sameIgnoringCase, map_lower_lower]

theorem sameIgnoringCase_lower_right (a b : List Char) :
    sameIgnoringCase a (b.map lowerAscii) = sameIgnoringCase a b := by
  simp only [sameIgnoringCase, map_lower_lower]

theorem validReference_lower (r : String) : validReference (lowerStr r) = validReference r := by
  unfold validReference
  rw [toList_lowerStr, dropDot_map lowerAscii_dot, validName_lower]

theorem contains_dot_lower (s : List Char) :
    (s.map lowerAscii).contains '.' = s.contains '.' := by
  rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem]
  exact (same_mem_dot (same_lower s)).symm

theorem validPresented_lower (p : String) : validPresented (lowerStr p) = validPresented p := by
  unfold validPresented
  rw [toList_lowerStr, wildcardSuffix?_map lowerAscii_dot lowerAscii_eq_star]
  cases wildcardSuffix? p.toList with
  | none => simp only [Option.map_none, validName_lower]
  | some s => simp only [Option.map_some, List.length_map, validName_lower, contains_dot_lower]

theorem matchName_lower_left (r p : String) : matchName (lowerStr r) p = matchName r p := by
  unfold matchName
  rw [validReference_lower, toList_lowerStr, dropDot_map lowerAscii_dot,
    afterFirstDot_map lowerAscii_dot]
  cases afterFirstDot (dropDot r.toList) <;>
    simp only [Option.map_none, Option.map_some, sameIgnoringCase_lower_left]

theorem matchName_lower_right (r p : String) : matchName r (lowerStr p) = matchName r p := by
  unfold matchName
  rw [validPresented_lower, toList_lowerStr,
    wildcardSuffix?_map lowerAscii_dot lowerAscii_eq_star]
  cases wildcardSuffix? p.toList <;>
    simp only [Option.map_none, Option.map_some, sameIgnoringCase_lower_right]

theorem lowerStr_eq_of_same {s s' : String} (h : Hostname.Spec.Same s.toList s'.toList) :
    lowerStr s = lowerStr s' := by
  unfold lowerStr; rw [same_iff.mp h]

theorem matchName_case_left' (r r' p : String) (h : Hostname.Spec.Same r.toList r'.toList) :
    matchName r p = matchName r' p := by
  rw [← matchName_lower_left r, ← matchName_lower_left r', lowerStr_eq_of_same h]

theorem matchName_case_right' (r p p' : String) (h : Hostname.Spec.Same p.toList p'.toList) :
    matchName r p = matchName r p' := by
  rw [← matchName_lower_right r p, ← matchName_lower_right r p', lowerStr_eq_of_same h]

/-! ## ASCII only -/

theorem hostName_ascii {cs : List Char} (h : Hostname.Spec.HostName cs) {c : Char} (hc : c ∈ cs) :
    c.toNat ≤ 127 := by
  rcases hostName_mem h hc with hc | rfl
  · exact toNat_le_of_letDigHyp hc
  · decide

theorem matchName_ascii_left' (r p : String) (h : ∃ c ∈ r.toList, 127 < c.toNat) :
    matchName r p = false := by
  rw [Bool.eq_false_iff]
  intro hm
  obtain ⟨c, hc, hn⟩ := h
  obtain ⟨name, hname, _⟩ := (matchName_iff' r p).mp hm
  have hd := reference_dropDot hname
  have hne : c ≠ '.' := by rintro rfl; exact absurd hn (by decide)
  have := hostName_ascii hname.1 (hd ▸ mem_dropDot hc hne)
  omega

theorem matchName_ascii_right' (r p : String) (h : ∃ c ∈ p.toList, 127 < c.toNat) :
    matchName r p = false := by
  rw [Bool.eq_false_iff]
  intro hm
  obtain ⟨c, hc, hn⟩ := h
  obtain ⟨_, _, h⟩ := (matchName_iff' r p).mp hm
  rcases h with ⟨hex, _⟩ | ⟨s, _, _, hw, _⟩
  · have := hostName_ascii hex hc; omega
  · rw [hw.1] at hc
    simp only [List.mem_cons] at hc
    rcases hc with rfl | rfl | hc
    · exact absurd hn (by decide)
    · exact absurd hn (by decide)
    · have := hostName_ascii hw.2.2.1 hc; omega

/-! ## Names without a wildcard -/

theorem matchName_exact' (r p : String) (hs : '*' ∉ p.toList) :
    matchName r p = true ↔
      Hostname.Spec.ExactName p ∧ ∃ name, Hostname.Spec.Reference r name ∧ Hostname.Spec.Same name p.toList := by
  rw [matchName_iff']
  constructor
  · rintro ⟨name, hname, ⟨hex, hsame⟩ | ⟨_, _, _, hw, _⟩⟩
    · exact ⟨hex, name, hname, hsame⟩
    · exact absurd (hw.1 ▸ List.mem_cons_self) hs
  · rintro ⟨hex, name, hname, hsame⟩
    exact ⟨name, hname, Or.inl ⟨hex, hsame⟩⟩

theorem matchName_refl' (s : String) (h : Hostname.Spec.HostName s.toList) : matchName s s = true :=
  (matchName_iff' s s).mpr ⟨s.toList, ⟨h, Or.inl rfl⟩, Or.inl ⟨h, same_refl _⟩⟩

theorem matchName_symm' (r p : String) (h : matchName r p = true) (hs : '*' ∉ p.toList)
    (hd : r.toList.getLast? ≠ some '.') : matchName p r = true := by
  obtain ⟨hex, name, ⟨hn, hr⟩, hsame⟩ := (matchName_exact' r p hs).mp h
  have hr' : r.toList = name := by
    rcases hr with hr | hr
    · exact hr
    · rw [hr] at hd; simp at hd
  rw [← hr'] at hn hsame
  exact (matchName_iff' p r).mpr ⟨p.toList, ⟨hex, Or.inl rfl⟩, Or.inl ⟨hn, same_symm hsame⟩⟩

theorem matchName_trans' (a b c : String) (hab : matchName a b = true)
    (hbc : matchName b c = true) : matchName a c = true := by
  obtain ⟨nameA, hA, hab⟩ := (matchName_iff' a b).mp hab
  obtain ⟨nameB, hB, hbc⟩ := (matchName_iff' b c).mp hbc
  -- `b` is a reference identifier, so it holds no `*`, and so it is no wildcard.
  have hbstar : '*' ∉ b.toList := by
    intro hm
    rcases hB.2 with he | he
    · exact hostName_star hB.1 (he ▸ hm)
    · rw [he] at hm
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with hm | hm
      · exact hostName_star hB.1 hm
      · exact absurd hm (by decide)
  obtain ⟨hexB, hAB⟩ : Hostname.Spec.ExactName b ∧ Hostname.Spec.Same nameA b.toList := by
    rcases hab with h | ⟨_, _, _, hw, _⟩
    · exact h
    · exact absurd (hw.1 ▸ List.mem_cons_self) hbstar
  have hbname : b.toList = nameB := by
    rw [← reference_dropDot hB]
    exact (dropDot_of_getLast (hostName_getLast hexB)).symm
  rw [hbname] at hAB
  refine (matchName_iff' a c).mpr ⟨nameA, hA, ?_⟩
  rcases hbc with ⟨hexC, hBC⟩ | ⟨s, label, rest, hw, heq, hl, hsame⟩
  · exact Or.inl ⟨hexC, same_trans hAB hBC⟩
  · rw [heq] at hAB
    obtain ⟨l', r', rfl, hl', hr'⟩ := same_split hAB
    have hdot : '.' ∉ l' := fun h => label_dot hl ((same_mem_dot hl').mp h)
    exact Or.inr ⟨s, l', r', hw, rfl, first_label hA.1 rfl hdot, same_trans hr' hsame⟩

end Hostname.Proofs
