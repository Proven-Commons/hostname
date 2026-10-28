/-
  Characters: the code's character classes against the specification's,
  and what `lowerAscii` does to each class.
-/

import Hostname
import Spec.Defs

open Hostname

namespace Hostname.Proofs

theorem le_iff_toNat {a b : Char} : a ≤ b ↔ a.toNat ≤ b.toNat := by
  rw [Char.le_def, UInt32.le_iff_toNat_le]; rfl

theorem digit_iff (c : Char) : Spec.Digit c ↔ 48 ≤ c.toNat ∧ c.toNat ≤ 57 := by
  simp only [Spec.Digit, le_iff_toNat]; rfl

theorem letter_iff (c : Char) :
    Spec.Letter c ↔ (97 ≤ c.toNat ∧ c.toNat ≤ 122) ∨ (65 ≤ c.toNat ∧ c.toNat ≤ 90) := by
  simp only [Spec.Letter, le_iff_toNat]; rfl

theorem eq_iff_toNat {c d : Char} : c = d ↔ c.toNat = d.toNat := Char.toNat_inj.symm

theorem isDigit_iff (c : Char) : isDigit c = true ↔ Spec.Digit c := by
  simp [isDigit, Spec.Digit]

theorem isLetDig_iff (c : Char) : isLetDig c = true ↔ Spec.LetDig c := by
  simp [isLetDig, isDigit, Spec.LetDig, Spec.Letter, Spec.Digit, or_assoc]

theorem isLDH_iff (c : Char) : isLDH c = true ↔ Spec.LetDigHyp c := by
  simp [isLDH, isLetDig_iff, Spec.LetDigHyp]

theorem letDig_iff (c : Char) : Spec.LetDig c ↔
    (97 ≤ c.toNat ∧ c.toNat ≤ 122) ∨ (65 ≤ c.toNat ∧ c.toNat ≤ 90) ∨
      (48 ≤ c.toNat ∧ c.toNat ≤ 57) := by
  simp only [Spec.LetDig, letter_iff, digit_iff, or_assoc]

theorem letDigHyp_iff (c : Char) : Spec.LetDigHyp c ↔
    (97 ≤ c.toNat ∧ c.toNat ≤ 122) ∨ (65 ≤ c.toNat ∧ c.toNat ≤ 90) ∨
      (48 ≤ c.toNat ∧ c.toNat ≤ 57) ∨ c.toNat = 45 := by
  show Spec.LetDig c ∨ c = '-' ↔ _
  rw [letDig_iff, eq_iff_toNat]
  show _ ∨ c.toNat = 45 ↔ _
  constructor <;> intro h <;> omega

theorem toNat_dot : '.'.toNat = 46 := rfl
theorem toNat_star : '*'.toNat = 42 := rfl
theorem toNat_hyphen : '-'.toNat = 45 := rfl

theorem not_letDigHyp_dot : ¬ Spec.LetDigHyp '.' := by decide
theorem not_letDigHyp_star : ¬ Spec.LetDigHyp '*' := by decide
theorem not_letDig_star : ¬ Spec.LetDig '*' := by decide
theorem not_letDig_dot : ¬ Spec.LetDig '.' := by decide
theorem letDig_letDigHyp {c : Char} (h : Spec.LetDig c) : Spec.LetDigHyp c := Or.inl h

/-- A letter, digit, hyphen or dot is ASCII. -/
theorem toNat_le_of_letDigHyp {c : Char} (h : Spec.LetDigHyp c) : c.toNat ≤ 127 := by
  rw [letDigHyp_iff] at h; omega

/-! ## ASCII lower case -/

theorem toNat_ofNat_lt {n : Nat} (h : n < 0xd800) : (Char.ofNat n).toNat = n := by
  have hv : n.isValidChar := Or.inl h
  simp [Char.ofNat, hv, Char.ofNatAux, Char.toNat]

theorem upper_iff (c : Char) : ('A' ≤ c && c ≤ 'Z') = true ↔ 65 ≤ c.toNat ∧ c.toNat ≤ 90 := by
  simp only [Bool.and_eq_true, decide_eq_true_eq, le_iff_toNat]; rfl

/-- What `lowerAscii` does, as numbers: an upper case letter moves up
    32 code points, and every other character stays. -/
theorem lower_cases (c : Char) :
    (65 ≤ c.toNat ∧ c.toNat ≤ 90 ∧ (lowerAscii c).toNat = c.toNat + 32) ∨
      (¬ (65 ≤ c.toNat ∧ c.toNat ≤ 90) ∧ (lowerAscii c).toNat = c.toNat) := by
  unfold lowerAscii
  by_cases h : 65 ≤ c.toNat ∧ c.toNat ≤ 90
  · have h' := (upper_iff c).mpr h
    refine Or.inl ⟨h.1, h.2, ?_⟩
    simp only [h', ↓reduceIte, toNat_ofNat_lt (show c.toNat + 32 < 0xd800 by omega)]
  · have h' : ('A' ≤ c && c ≤ 'Z') = false := by
      rw [Bool.eq_false_iff]; intro h''; exact h ((upper_iff c).mp h'')
    refine Or.inr ⟨h, ?_⟩
    simp only [h', Bool.false_eq_true, ↓reduceIte]

theorem sameChar_iff (a b : Char) : Spec.SameChar a b ↔ lowerAscii a = lowerAscii b := by
  rw [eq_iff_toNat (c := lowerAscii a)]
  simp only [Spec.SameChar, le_iff_toNat, eq_iff_toNat (c := a)]
  show _ ∨ (65 ≤ a.toNat ∧ a.toNat ≤ 90 ∧ _) ∨ (65 ≤ b.toNat ∧ b.toNat ≤ 90 ∧ _) ↔ _
  rcases lower_cases a with ha | ha <;> rcases lower_cases b with hb | hb <;>
    constructor <;> intro h <;> omega

theorem lowerAscii_lowerAscii (c : Char) : lowerAscii (lowerAscii c) = lowerAscii c := by
  rw [eq_iff_toNat]
  rcases lower_cases c with h | h <;> rcases lower_cases (lowerAscii c) with h' | h' <;> omega

theorem lowerAscii_eq_dot (c : Char) : lowerAscii c = '.' ↔ c = '.' := by
  rw [eq_iff_toNat, eq_iff_toNat (c := c), toNat_dot]
  rcases lower_cases c with h | h <;> omega

theorem lowerAscii_eq_star (c : Char) : lowerAscii c = '*' ↔ c = '*' := by
  rw [eq_iff_toNat, eq_iff_toNat (c := c), toNat_star]
  rcases lower_cases c with h | h <;> omega

theorem lowerAscii_eq_hyphen (c : Char) : lowerAscii c = '-' ↔ c = '-' := by
  rw [eq_iff_toNat, eq_iff_toNat (c := c), toNat_hyphen]
  rcases lower_cases c with h | h <;> omega

theorem isDigit_lowerAscii (c : Char) : isDigit (lowerAscii c) = isDigit c := by
  rw [Bool.eq_iff_iff, isDigit_iff, isDigit_iff, digit_iff, digit_iff]
  rcases lower_cases c with h | h <;> omega

theorem isLetDig_lowerAscii (c : Char) : isLetDig (lowerAscii c) = isLetDig c := by
  rw [Bool.eq_iff_iff, isLetDig_iff, isLetDig_iff, letDig_iff, letDig_iff]
  rcases lower_cases c with h | h <;> omega

theorem isLDH_lowerAscii (c : Char) : isLDH (lowerAscii c) = isLDH c := by
  rw [Bool.eq_iff_iff, isLDH_iff, isLDH_iff, letDigHyp_iff, letDigHyp_iff]
  rcases lower_cases c with h | h <;> omega

end Hostname.Proofs
