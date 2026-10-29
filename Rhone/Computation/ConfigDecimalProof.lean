/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.Config
public import Mathlib.Data.Nat.Basic
import all Init.Data.Repr
import all Init.Data.Char.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

/-! # Decimal counts in configuration keys -/

@[expose] public section

namespace Rhone.Computation

def decimalValue (xs : List Char) (n : Nat := 0) : Nat :=
  xs.foldl (fun n ch => 10 * n + (ch.toNat - '0'.toNat)) n

private theorem digitChar_value {n : Nat} (h : n < 10) :
    (Nat.digitChar n).toNat - '0'.toNat = n := by
  interval_cases n <;> decide

private theorem digitChar_digit {n : Nat} (h : n < 10) :
    (Nat.digitChar n).isDigit = true := by
  interval_cases n <;> decide

private theorem decimalValue_acc (xs : List Char) (n : Nat) :
    decimalValue xs n = n * 10 ^ xs.length + decimalValue xs 0 := by
  induction xs generalizing n with
  | nil => simp [decimalValue]
  | cons ch xs ih =>
    simp only [decimalValue, List.foldl_cons, List.length_cons, Nat.mul_zero, Nat.zero_add]
    change decimalValue xs (10 * n + (ch.toNat - '0'.toNat)) =
      n * 10 ^ (xs.length + 1) + decimalValue xs (ch.toNat - '0'.toNat)
    rw [ih (10 * n + (ch.toNat - '0'.toNat)), ih (ch.toNat - '0'.toNat), Nat.pow_succ]
    ring

private theorem decimalValue_toDigitsCore (fuel n : Nat) (ds : List Char)
    (h : n < fuel) :
    decimalValue (Nat.toDigitsCore 10 fuel n ds) =
      n * 10 ^ ds.length + decimalValue ds := by
  induction fuel generalizing n ds with
  | zero => omega
  | succ fuel ih =>
    rw [Nat.toDigitsCore]
    split
    · rename_i hd
      simp only [decimalValue, List.foldl_cons]
      rw [← decimalValue, decimalValue_acc, digitChar_value (Nat.mod_lt _ (by decide))]
      have hn : n % 10 = n := Nat.mod_eq_of_lt (by omega)
      simp [hn, decimalValue]
    · rename_i hd
      rw [ih (n / 10) (Nat.digitChar (n % 10) :: ds) (by omega)]
      simp only [List.length_cons, decimalValue, List.foldl_cons]
      rw [← decimalValue, decimalValue_acc, digitChar_value (Nat.mod_lt _ (by decide))]
      rw [Nat.pow_succ]
      have hn := Nat.mod_add_div n 10
      calc
        _ = (n % 10 + 10 * (n / 10)) * 10 ^ ds.length + decimalValue ds := by ring
        _ = _ := by rw [hn]; rfl

private theorem toDigitsCore_digits (fuel n : Nat) (ds : List Char)
    (h : ∀ ch ∈ ds, ch.isDigit = true) :
    ∀ ch ∈ Nat.toDigitsCore 10 fuel n ds, ch.isDigit = true := by
  induction fuel generalizing n ds with
  | zero => exact h
  | succ fuel ih =>
    rw [Nat.toDigitsCore]
    have hd : ∀ ch ∈ Nat.digitChar (n % 10) :: ds, ch.isDigit = true := by
      simp only [List.mem_cons, forall_eq_or_imp]
      exact ⟨digitChar_digit (Nat.mod_lt _ (by decide)), h⟩
    split
    · exact hd
    · exact ih _ _ hd

private theorem toDigitsCore_ne_nil (fuel n : Nat) (ds : List Char) (h : n < fuel) :
    Nat.toDigitsCore 10 fuel n ds ≠ [] := by
  induction fuel generalizing n ds with
  | zero => omega
  | succ fuel ih =>
    rw [Nat.toDigitsCore]
    split
    · simp
    · exact ih _ _ (by omega)

private theorem saturated_step (n d : Nat) :
    min 65536 (10 * min 65536 n + d) = min 65536 (10 * n + d) := by
  by_cases hn : n ≤ 65536
  · simp [Nat.min_eq_right hn]
  · have hn' : 65536 ≤ n := by omega
    have hb : 65536 ≤ 10 * n + d := by omega
    have hh : 65536 ≤ 10 * 65536 + d := by omega
    simp [Nat.min_eq_left hn', Nat.min_eq_left hb, Nat.min_eq_left hh]

private theorem saturated_fold (xs : List Char) (n : Nat) :
    xs.foldl (fun n ch => min 65536 (10 * n + (ch.toNat - '0'.toNat)))
      (min 65536 n) = min 65536 (decimalValue xs n) := by
  induction xs generalizing n with
  | nil => rfl
  | cons ch xs ih =>
    simp only [List.foldl_cons]
    rw [saturated_step, ih]
    rfl

theorem decimalValue_toDigits (n : Nat) : decimalValue (Nat.toDigits 10 n) = n := by
  simpa [Nat.toDigits, decimalValue] using
    decimalValue_toDigitsCore (n + 1) n [] (by omega)

theorem decimalCount_toDigits (n : Nat) (hn : n ≤ 65535) :
    decimalCount (Nat.toDigits 10 n) = n := by
  have h := saturated_fold (Nat.toDigits 10 n) 0
  simpa [decimalCount, decimalValue_toDigits, Nat.min_eq_right (by omega : n ≤ 65536)] using h

theorem toDigits_digits (n : Nat) :
    ∀ ch ∈ Nat.toDigits 10 n, ch.isDigit = true :=
  toDigitsCore_digits (n + 1) n [] (by simp)

theorem toDigits_ne_nil (n : Nat) : Nat.toDigits 10 n ≠ [] :=
  toDigitsCore_ne_nil (n + 1) n [] (by omega)

end Rhone.Computation
