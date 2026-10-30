/-
  Labels and host names: the code's checks against the specification's
  `Hostname.Spec.Label` and `Hostname.Spec.HostName`, and what ASCII lower case does to
  them.
-/

import Hostname
import Hostname.Spec.Defs
import Hostname.Proofs.Chars
import Hostname.Proofs.Lists

open Hostname

namespace Hostname.Proofs

/-! ## Labels -/

/-- `Hostname.Spec.Label`, said through the first and last characters. -/
theorem label_iff' (l : List Char) : Hostname.Spec.Label l ↔
    l.length ≤ 63 ∧ (∀ c ∈ l, Hostname.Spec.LetDigHyp c) ∧
      (∃ a, l.head? = some a ∧ Hostname.Spec.LetDig a) ∧ (∃ b, l.getLast? = some b ∧ Hostname.Spec.LetDig b) := by
  constructor
  · rintro ⟨hlen, a, ha, rfl | ⟨mid, b, rfl, hmid, hb⟩⟩
    · exact ⟨hlen, by simp [letDig_letDigHyp ha], ⟨a, rfl, ha⟩, ⟨a, rfl, ha⟩⟩
    · refine ⟨hlen, ?_, ⟨a, rfl, ha⟩, ⟨b, by rw [List.getLast?_concat], hb⟩⟩
      intro c hc
      simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil,
        or_false] at hc
      rcases hc with rfl | hc | rfl
      · exact letDig_letDigHyp ha
      · exact hmid c hc
      · exact letDig_letDigHyp hb
  · rintro ⟨hlen, hall, ⟨a, ha, hla⟩, ⟨b, hb, hlb⟩⟩
    refine ⟨hlen, a, hla, ?_⟩
    cases l with
    | nil => simp at ha
    | cons a' t =>
      simp only [List.head?_cons, Option.some.injEq] at ha
      subst ha
      rcases List.eq_nil_or_concat t with rfl | ⟨mid, b', rfl⟩
      · exact Or.inl rfl
      · right
        rw [List.concat_eq_append] at hb hall ⊢
        have : b' = b := by
          rw [← List.cons_append, List.getLast?_concat] at hb
          exact Option.some.inj hb
        subst this
        refine ⟨mid, b', rfl, fun c hc => hall c (by simp [hc]), hlb⟩

theorem validLabel_iff (l : List Char) : validLabel l = true ↔ Hostname.Spec.Label l := by
  rw [label_iff']
  unfold validLabel
  split
  · rename_i a b ha hb
    simp only [Bool.and_eq_true, decide_eq_true_eq, isLetDig_iff, List.all_eq_true, isLDH_iff]
    constructor
    · rintro ⟨⟨⟨hlen, hla⟩, hlb⟩, hall⟩
      exact ⟨hlen, hall, ⟨a, ha, hla⟩, ⟨b, hb, hlb⟩⟩
    · rintro ⟨hlen, hall, ⟨a', ha', hla⟩, ⟨b', hb', hlb⟩⟩
      rw [ha] at ha'; rw [hb] at hb'
      cases ha'; cases hb'
      exact ⟨⟨⟨hlen, hla⟩, hlb⟩, hall⟩
  · rename_i hne
    simp only [Bool.false_eq_true, false_iff]
    rintro ⟨_, _, ⟨a, ha, _⟩, ⟨b, hb, _⟩⟩
    exact hne a b ha hb

theorem label_mem {l : List Char} (h : Hostname.Spec.Label l) {c : Char} (hc : c ∈ l) :
    Hostname.Spec.LetDigHyp c :=
  ((label_iff' l).mp h).2.1 c hc

theorem label_dot {l : List Char} (h : Hostname.Spec.Label l) : '.' ∉ l :=
  fun hc => not_letDigHyp_dot (label_mem h hc)

theorem label_head {l : List Char} (h : Hostname.Spec.Label l) : ∃ a t, l = a :: t ∧ Hostname.Spec.LetDig a := by
  obtain ⟨_, _, ⟨a, ha, hla⟩, _⟩ := (label_iff' l).mp h
  cases l with
  | nil => simp at ha
  | cons a' t => simp only [List.head?_cons, Option.some.injEq] at ha; exact ⟨a, t, ha ▸ rfl, hla⟩

theorem label_last {l : List Char} (h : Hostname.Spec.Label l) : ∃ i b, l = i ++ [b] ∧ Hostname.Spec.LetDig b := by
  obtain ⟨_, _, _, ⟨b, hb, hlb⟩⟩ := (label_iff' l).mp h
  obtain ⟨i, rfl⟩ := List.getLast?_eq_some_iff.mp hb
  exact ⟨i, b, rfl, hlb⟩

/-! ## Host names -/

theorem lastNotNumeric_iff (ls : List (List Char)) : lastNotNumeric ls = true ↔
    ∃ init last, ls = init ++ [last] ∧ ∃ c ∈ last, ¬ Hostname.Spec.Digit c := by
  unfold lastNotNumeric
  split
  · rename_i l hl
    obtain ⟨init, rfl⟩ := List.getLast?_eq_some_iff.mp hl
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, List.all_eq_false, isDigit_iff]
    constructor
    · rintro ⟨c, hc, hd⟩; exact ⟨init, l, rfl, c, hc, by simpa using hd⟩
    · rintro ⟨init', last, he, c, hc, hd⟩
      have := List.append_inj_right' he rfl
      simp only [List.cons.injEq, and_true] at this
      subst this
      exact ⟨c, hc, by simpa using hd⟩
  · rename_i hl
    simp only [Bool.false_eq_true, false_iff]
    rintro ⟨init, last, rfl, _⟩
    simp at hl

/-- The labels of a host name are the parts between its dots. -/
theorem hostName_splitOn {init : List (List Char)} {last : List Char}
    (hinit : ∀ l ∈ init, Hostname.Spec.Label l) (hl : Hostname.Spec.Label last) :
    (['.'].intercalate (init ++ [last])).splitOn '.' = init ++ [last] := by
  apply List.splitOn_intercalate
  · intro l hm
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hm | rfl
    · exact label_dot (hinit l hm)
    · exact label_dot hl
  · simp

theorem validName_iff (cs : List Char) : validName cs = true ↔ Hostname.Spec.HostName cs := by
  unfold validName Hostname.Spec.HostName
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, validLabel_iff]
  constructor
  · rintro ⟨⟨hlen, hall⟩, hlast⟩
    obtain ⟨init, last, hls, hc⟩ := (lastNotNumeric_iff _).mp hlast
    refine ⟨hlen, init, last, ?_, ?_, ?_, hc⟩
    · rw [← hls, List.intercalate_splitOn]
    · intro l hl; exact hall l (hls ▸ List.mem_append_left _ hl)
    · exact hall last (hls ▸ by simp)
  · rintro ⟨hlen, init, last, rfl, hinit, hl, hc⟩
    rw [hostName_splitOn hinit hl]
    refine ⟨⟨hlen, ?_⟩, (lastNotNumeric_iff _).mpr ⟨init, last, rfl, hc⟩⟩
    intro l hm
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hm | rfl
    · exact hinit l hm
    · exact hl

/-- Every character of a host name is a letter, digit, hyphen or dot. -/
theorem hostName_mem {cs : List Char} (h : Hostname.Spec.HostName cs) {c : Char} (hc : c ∈ cs) :
    Hostname.Spec.LetDigHyp c ∨ c = '.' := by
  obtain ⟨_, init, last, rfl, hinit, hl, _⟩ := h
  rcases mem_intercalate hc with hdot | ⟨l, hm, hcl⟩
  · exact Or.inr hdot
  · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hm | hm
    · exact Or.inl (label_mem (hinit l hm) hcl)
    · rw [hm] at hcl; exact Or.inl (label_mem hl hcl)

theorem hostName_star {cs : List Char} (h : Hostname.Spec.HostName cs) : '*' ∉ cs := by
  intro hc
  rcases hostName_mem h hc with hc | hc
  · exact not_letDigHyp_star hc
  · exact absurd hc (by decide)

theorem intercalate_cons_eq (l : List Char) (ls : List (List Char)) :
    ∃ rest, ['.'].intercalate (l :: ls) = l ++ rest := by
  cases ls with
  | nil => exact ⟨[], by simp⟩
  | cons l' ls => exact ⟨_, by rw [List.intercalate_cons_cons, List.append_assoc]⟩

theorem intercalate_concat_eq : ∀ (ls : List (List Char)) (l : List Char),
    ∃ pre, ['.'].intercalate (ls ++ [l]) = pre ++ l
  | [], l => ⟨[], by simp⟩
  | l' :: ls, l => by
    obtain ⟨pre, hpre⟩ := intercalate_concat_eq ls l
    cases ls with
    | nil => exact ⟨l' ++ ['.'], by simp [List.intercalate_cons_cons]⟩
    | cons l'' ls =>
      refine ⟨l' ++ ['.'] ++ pre, ?_⟩
      rw [List.cons_append, List.cons_append, List.intercalate_cons_cons, ← List.cons_append,
        hpre]
      simp [List.append_assoc]

/-- A host name starts with a letter or digit. -/
theorem hostName_head {cs : List Char} (h : Hostname.Spec.HostName cs) :
    ∃ a t, cs = a :: t ∧ Hostname.Spec.LetDig a := by
  obtain ⟨_, init, last, rfl, hinit, hl, _⟩ := h
  cases init with
  | nil =>
    obtain ⟨a, t, rfl, ha⟩ := label_head hl
    exact ⟨a, t, by simp, ha⟩
  | cons l init =>
    obtain ⟨a, t, rfl, ha⟩ := label_head (hinit l (by simp))
    obtain ⟨rest, hrest⟩ := intercalate_cons_eq (a :: t) (init ++ [last])
    exact ⟨a, t ++ rest, by rw [List.cons_append, hrest]; rfl, ha⟩

/-- A host name ends with a letter or digit. -/
theorem hostName_last {cs : List Char} (h : Hostname.Spec.HostName cs) :
    ∃ i b, cs = i ++ [b] ∧ Hostname.Spec.LetDig b := by
  obtain ⟨_, init, last, rfl, _, hl, _⟩ := h
  obtain ⟨i, b, rfl, hb⟩ := label_last hl
  obtain ⟨pre, hpre⟩ := intercalate_concat_eq init (i ++ [b])
  exact ⟨pre ++ i, b, by rw [hpre, List.append_assoc], hb⟩

theorem hostName_getLast {cs : List Char} (h : Hostname.Spec.HostName cs) : cs.getLast? ≠ some '.' := by
  obtain ⟨i, b, rfl, hb⟩ := hostName_last h
  rw [List.getLast?_concat]
  intro he
  cases he
  exact not_letDig_dot hb

theorem hostName_ne_nil {cs : List Char} (h : Hostname.Spec.HostName cs) : cs ≠ [] := by
  obtain ⟨a, t, rfl, _⟩ := hostName_head h
  simp

/-- The part of a host name before its first dot is a label. -/
theorem first_label {name label rest : List Char} (h : Hostname.Spec.HostName name)
    (he : name = label ++ '.' :: rest) (hd : '.' ∉ label) : Hostname.Spec.Label label := by
  have hv := (validName_iff name).mpr h
  unfold validName at hv
  simp only [Bool.and_eq_true, List.all_eq_true] at hv
  rw [he, List.splitOn_append_cons_self_of_not_mem hd] at hv
  exact (validLabel_iff label).mp (hv.1.2 label (by simp))

/-! ## ASCII lower case -/

theorem lowerAscii_dot : ∀ c, lowerAscii c = '.' ↔ c = '.' := lowerAscii_eq_dot

theorem validLabel_lower (l : List Char) : validLabel (l.map lowerAscii) = validLabel l := by
  unfold validLabel
  rw [List.head?_map, List.getLast?_map]
  cases l.head? <;> cases l.getLast? <;>
    simp [isLetDig_lowerAscii, isLDH_lowerAscii, List.all_map, Function.comp_def]

theorem lastNotNumeric_lower (ls : List (List Char)) :
    lastNotNumeric (ls.map (List.map lowerAscii)) = lastNotNumeric ls := by
  unfold lastNotNumeric
  rw [List.getLast?_map]
  cases ls.getLast? <;> simp [isDigit_lowerAscii, List.all_map, Function.comp_def]

theorem validName_lower (cs : List Char) : validName (cs.map lowerAscii) = validName cs := by
  unfold validName
  rw [splitOn_map lowerAscii_dot, List.length_map, lastNotNumeric_lower, List.all_map]
  simp [Function.comp_def, validLabel_lower]

end Hostname.Proofs
