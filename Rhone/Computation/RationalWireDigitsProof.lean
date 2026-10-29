/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.RationalWire
public import Rhone.Computation.ConfigDecimalProof

/-! # Unbounded exact digit-run decoding -/

@[expose] public section
namespace Rhone.Computation.RationalWire

theorem digits_eq_ok_iff (xs : List Char) (n : Nat) :
    digits xs = .ok n ↔ xs ≠ [] ∧
      (∀ ch ∈ xs, ch.isDigit = true) ∧ n = decimal xs := by
  by_cases hn : xs = []
  · subst xs
    simp [digits]
  · have hem : xs.isEmpty = false := List.isEmpty_eq_false_iff.mpr hn
    cases hd : xs.all Char.isDigit with
    | false =>
      have hnot : ¬ ∀ ch ∈ xs, ch.isDigit = true := by
        intro hchars
        have ht := List.all_eq_true.mpr hchars
        rw [hd] at ht
        contradiction
      simp [digits, hem, hd, hnot]
    | true =>
      have hchars := List.all_eq_true.mp hd
      simp only [digits, hem, hd, Bool.not_true, Bool.false_or,
        Bool.false_eq_true, ↓reduceIte, Except.ok.injEq]
      exact ⟨fun h => ⟨hn, hchars, h.symm⟩, fun h => h.2.2.symm⟩

theorem decimal_toDigits (n : Nat) : decimal (Nat.toDigits 10 n) = n :=
  decimalValue_toDigits n

theorem digits_toDigits (n : Nat) : digits (Nat.toDigits 10 n) = .ok n := by
  apply (digits_eq_ok_iff _ _).2
  exact ⟨toDigits_ne_nil n, toDigits_digits n, (decimal_toDigits n).symm⟩

theorem slash_absent_of_digits {xs : List Char}
    (h : ∀ ch ∈ xs, ch.isDigit = true) :
    ∀ ch ∈ xs, (ch == '/') = false := by
  intro ch hc
  apply beq_eq_false_iff_ne.mpr
  intro he
  subst ch
  have hf := h '/' hc
  have hn : '/'.isDigit = false := by decide
  rw [hn] at hf
  contradiction

theorem minus_head_absent_of_digits {xs : List Char}
    (h : ∀ ch ∈ xs, ch.isDigit = true) : xs.head? ≠ some '-' := by
  cases xs with
  | nil => simp
  | cons ch xs =>
    simp only [List.head?_cons]
    intro he
    have he := Option.some.inj he
    subst ch
    have hf := h '-' (by simp)
    have hn : '-'.isDigit = false := by decide
    rw [hn] at hf
    contradiction

theorem integer_of_digits (xs : List Char) (hn : xs ≠ [])
    (hd : ∀ ch ∈ xs, ch.isDigit = true) :
    integer xs = .ok (decimal xs : Int) := by
  have hm := minus_head_absent_of_digits hd
  have hx := (digits_eq_ok_iff xs (decimal xs)).2 ⟨hn, hd, rfl⟩
  simp [integer, hm, hx, Except.mapError]

theorem integer_intChars (n : Int) : integer (intChars n) = .ok n := by
  cases n with
  | ofNat n =>
    simpa only [intChars, decimal_toDigits, Int.ofNat_eq_natCast] using
      integer_of_digits (Nat.toDigits 10 n) (toDigits_ne_nil n) (toDigits_digits n)
  | negSucc n =>
    simp only [integer, intChars, List.head?_cons, beq_self_eq_true,
      ↓reduceIte, List.tail_cons, digits_toDigits, Except.mapError,
      ]
    rfl

end Rhone.Computation.RationalWire
