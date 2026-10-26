/-
  Lists of characters: labels joined by dots, the split at the first
  dot, the trailing dot, and sameness up to ASCII case.
-/

import Hostname
import Spec.Defs
import Proofs.Chars

open Hostname

namespace Hostname.Proofs

/-! ## Labels joined by dots -/

theorem mem_intercalate {c : Char} : ∀ {ls : List (List Char)},
    c ∈ ['.'].intercalate ls → c = '.' ∨ ∃ l ∈ ls, c ∈ l
  | [], h => by simp at h
  | [l], h => Or.inr ⟨l, by simp, by simpa using h⟩
  | l :: l' :: ls, h => by
    rw [List.intercalate_cons_cons] at h
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with (h | h) | h
    · exact Or.inr ⟨l, by simp, h⟩
    · exact Or.inl h
    · rcases mem_intercalate h with h | ⟨l'', hl, hc⟩
      · exact Or.inl h
      · exact Or.inr ⟨l'', List.mem_cons_of_mem _ hl, hc⟩

theorem not_mem_intercalate {c : Char} {ls : List (List Char)} (hc : c ≠ '.')
    (h : ∀ l ∈ ls, c ∉ l) : c ∉ ['.'].intercalate ls := by
  intro hm
  rcases mem_intercalate hm with hm | ⟨l, hl, hm⟩
  · exact hc hm
  · exact h l hl hm

/-- Splitting commutes with a map that sends dots, and only dots, to
    dots. -/
theorem splitOn_map {f : Char → Char} (hf : ∀ c, f c = '.' ↔ c = '.') :
    ∀ cs : List Char, (cs.map f).splitOn '.' = (cs.splitOn '.').map (List.map f)
  | [] => by simp
  | c :: cs => by
    rw [List.map_cons, List.splitOn_cons_eq_ite_modifyHead,
      List.splitOn_cons_eq_ite_modifyHead, splitOn_map hf cs]
    by_cases hc : c = '.'
    · subst hc
      have : f '.' = '.' := (hf '.').mpr rfl
      simp [this]
    · have : f c ≠ '.' := fun h => hc ((hf c).mp h)
      simp only [beq_iff_eq, this, hc, ↓reduceIte]
      generalize List.splitOn '.' cs = ls
      cases ls <;> simp

/-! ## The first dot -/

theorem afterFirstDot_eq_some {rest : List Char} : ∀ {cs : List Char},
    afterFirstDot cs = some rest ↔ ∃ label, cs = label ++ '.' :: rest ∧ '.' ∉ label
  | [] => by simp [afterFirstDot]
  | c :: cs => by
    unfold afterFirstDot
    by_cases hc : c = '.'
    · subst hc
      simp only [↓reduceIte, Option.some.injEq]
      constructor
      · rintro rfl; exact ⟨[], rfl, by simp⟩
      · rintro ⟨label, h, hl⟩
        cases label with
        | nil => simpa using h
        | cons a label =>
          simp only [List.cons_append, List.cons.injEq] at h
          exact absurd (h.1 ▸ List.mem_cons_self) hl
    · simp only [hc, ↓reduceIte]
      rw [afterFirstDot_eq_some]
      constructor
      · rintro ⟨label, rfl, hl⟩
        exact ⟨c :: label, rfl, by simp [Ne.symm hc, hl]⟩
      · rintro ⟨label, h, hl⟩
        cases label with
        | nil => simp at h; exact absurd h.1 hc
        | cons a label =>
          simp only [List.cons_append, List.cons.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨label, rfl, fun h => hl (List.mem_cons_of_mem _ h)⟩

theorem afterFirstDot_map {f : Char → Char} (hf : ∀ c, f c = '.' ↔ c = '.') :
    ∀ cs : List Char, afterFirstDot (cs.map f) = (afterFirstDot cs).map (List.map f)
  | [] => rfl
  | c :: cs => by
    simp only [List.map_cons, afterFirstDot]
    by_cases hc : c = '.'
    · subst hc
      have : f '.' = '.' := (hf '.').mpr rfl
      simp [this]
    · have : f c ≠ '.' := fun h => hc ((hf c).mp h)
      simp only [this, hc, ↓reduceIte]
      exact afterFirstDot_map hf cs

/-! ## The trailing dot -/

theorem dropDot_of_getLast {cs : List Char} (h : cs.getLast? ≠ some '.') : dropDot cs = cs := by
  simp [dropDot, h]

theorem dropDot_append_dot (cs : List Char) : dropDot (cs ++ ['.']) = cs := by
  simp [dropDot]

/-- A list is what `dropDot` leaves, with or without a dot after it. -/
theorem eq_dropDot (cs : List Char) : cs = dropDot cs ∨ cs = dropDot cs ++ ['.'] := by
  unfold dropDot
  split
  · rename_i h
    obtain ⟨ys, rfl⟩ := List.getLast?_eq_some_iff.mp h
    simp
  · exact Or.inl rfl

theorem mem_dropDot {c : Char} {cs : List Char} (h : c ∈ cs) (hc : c ≠ '.') : c ∈ dropDot cs := by
  rcases eq_dropDot cs with h' | h'
  · rwa [← h']
  · rw [h'] at h
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
    exact h.resolve_right hc

theorem getLast?_map {f : Char → Char} (cs : List Char) :
    (cs.map f).getLast? = cs.getLast?.map f := by
  simp [List.getLast?_map]

theorem dropDot_map {f : Char → Char} (hf : ∀ c, f c = '.' ↔ c = '.') (cs : List Char) :
    dropDot (cs.map f) = (dropDot cs).map f := by
  unfold dropDot
  rw [getLast?_map]
  cases h : cs.getLast? with
  | none => simp
  | some c =>
    by_cases hc : c = '.'
    · subst hc; simp [(hf '.').mpr rfl, List.map_dropLast]
    · have : f c ≠ '.' := fun h => hc ((hf c).mp h)
      simp [hc, this]

/-! ## The wildcard -/

theorem wildcardSuffix?_eq_some {s : List Char} :
    ∀ {cs : List Char}, wildcardSuffix? cs = some s ↔ cs = '*' :: '.' :: s
  | [] => by simp [wildcardSuffix?]
  | [_] => by simp [wildcardSuffix?]
  | a :: b :: t => by
    by_cases ha : a = '*'
    · by_cases hb : b = '.'
      · subst ha hb; simp [wildcardSuffix?]
      · simp [wildcardSuffix?, hb]
    · simp [wildcardSuffix?, ha]

theorem wildcardSuffix?_eq_none {cs : List Char} :
    wildcardSuffix? cs = none ↔ ∀ s, cs ≠ '*' :: '.' :: s := by
  constructor
  · intro h s hs
    rw [← wildcardSuffix?_eq_some] at hs
    rw [h] at hs; cases hs
  · intro h
    cases h' : wildcardSuffix? cs with
    | none => rfl
    | some s => exact absurd (wildcardSuffix?_eq_some.mp h') (h s)

theorem wildcardSuffix?_map {f : Char → Char} (hd : ∀ c, f c = '.' ↔ c = '.')
    (hs : ∀ c, f c = '*' ↔ c = '*') (cs : List Char) :
    wildcardSuffix? (cs.map f) = (wildcardSuffix? cs).map (List.map f) := by
  cases h : wildcardSuffix? cs with
  | some s =>
    rw [wildcardSuffix?_eq_some] at h
    subst h
    simp [wildcardSuffix?, (hd '.').mpr rfl, (hs '*').mpr rfl]
  | none =>
    rw [Option.map_none, wildcardSuffix?_eq_none]
    rw [wildcardSuffix?_eq_none] at h
    intro s hs'
    cases cs with
    | nil => simp at hs'
    | cons a t =>
      cases t with
      | nil => simp at hs'
      | cons b t =>
        simp only [List.map_cons, List.cons.injEq] at hs'
        obtain ⟨ha, hb, -⟩ := hs'
        exact h t (by rw [(hs a).mp ha, (hd b).mp hb])

/-! ## Sameness up to ASCII case -/

theorem same_iff : ∀ {xs ys : List Char},
    Spec.Same xs ys ↔ xs.map lowerAscii = ys.map lowerAscii
  | [], [] => by simp [Spec.Same]
  | [], _ :: _ => by simp [Spec.Same]
  | _ :: _, [] => by simp [Spec.Same]
  | a :: as, b :: bs => by
    simp only [Spec.Same, List.map_cons, List.cons.injEq, sameChar_iff, same_iff]

theorem same_refl (xs : List Char) : Spec.Same xs xs := same_iff.mpr rfl

theorem same_symm {xs ys : List Char} (h : Spec.Same xs ys) : Spec.Same ys xs :=
  same_iff.mpr (same_iff.mp h).symm

theorem same_trans {xs ys zs : List Char} (h : Spec.Same xs ys) (h' : Spec.Same ys zs) :
    Spec.Same xs zs :=
  same_iff.mpr ((same_iff.mp h).trans (same_iff.mp h'))

theorem sameIgnoringCase_iff (a b : List Char) : sameIgnoringCase a b = true ↔ Spec.Same a b := by
  simp [sameIgnoringCase, same_iff]

theorem map_lower_lower (cs : List Char) : (cs.map lowerAscii).map lowerAscii = cs.map lowerAscii := by
  simp [Function.comp_def, lowerAscii_lowerAscii]

theorem same_lower (cs : List Char) : Spec.Same cs (cs.map lowerAscii) :=
  same_iff.mpr (map_lower_lower cs).symm

/-- A list the same as `l ++ '.' :: r` splits at a dot in the same
    place. -/
theorem same_split {xs l r : List Char} (h : Spec.Same xs (l ++ '.' :: r)) :
    ∃ l' r', xs = l' ++ '.' :: r' ∧ Spec.Same l' l ∧ Spec.Same r' r := by
  rw [same_iff, List.map_append, List.map_cons, List.map_eq_append_iff] at h
  obtain ⟨l', t, rfl, hl, ht⟩ := h
  rw [List.map_eq_cons_iff] at ht
  obtain ⟨d, r', rfl, hd, hr⟩ := ht
  have hd' : d = '.' := by
    rw [← lowerAscii_eq_dot, hd]; exact lowerAscii_eq_dot '.' |>.mpr rfl
  subst hd'
  exact ⟨l', r', rfl, same_iff.mpr hl, same_iff.mpr hr⟩

theorem same_mem_dot {xs ys : List Char} (h : Spec.Same xs ys) : '.' ∈ xs ↔ '.' ∈ ys := by
  rw [same_iff] at h
  constructor
  · intro hx
    have : lowerAscii '.' ∈ ys.map lowerAscii := h ▸ List.mem_map_of_mem hx
    obtain ⟨c, hc, he⟩ := List.mem_map.mp this
    rwa [(lowerAscii_eq_dot c).mp (he.trans ((lowerAscii_eq_dot '.').mpr rfl))] at hc
  · intro hy
    have : lowerAscii '.' ∈ xs.map lowerAscii := h.symm ▸ List.mem_map_of_mem hy
    obtain ⟨c, hc, he⟩ := List.mem_map.mp this
    rwa [(lowerAscii_eq_dot c).mp (he.trans ((lowerAscii_eq_dot '.').mpr rfl))] at hc

end Hostname.Proofs
