/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.RationalWireDigitsProof
public import Init.Data.Rat.Lemmas
public import Init.Data.Nat.ToString
public import Init.Data.Int.ToString
import all Init.Data.Int.Repr
import all Init.Data.Repr
import all Init.Data.ToString.Basic
import all Init.Data.String.Basic
public import Init.Data.String.Lemmas.Basic

/-! # Injectivity and decoding of the strict rational printer -/

@[expose] public section
namespace Rhone.Computation.RationalWire

private theorem natChars_noSlash (n : Nat) : '/' ∉ Nat.toDigits 10 n := by
  intro hm
  have hf := toDigits_digits n '/' hm
  have hn : '/'.isDigit = false := by decide
  rw [hn] at hf
  contradiction

private theorem intChars_noSlash (n : Int) : '/' ∉ intChars n := by
  cases n with
  | ofNat n => exact natChars_noSlash n
  | negSucc n => simpa [intChars] using natChars_noSlash (n + 1)

private theorem printed_split (r : Rat) :
    (intChars r.num ++ '/' :: Nat.toDigits 10 r.den).splitOn '/' =
      [intChars r.num, Nat.toDigits 10 r.den] := by
  have hx : ∀ xs ∈ [intChars r.num, Nat.toDigits 10 r.den], '/' ∉ xs := by
    intro xs hx
    rcases List.mem_cons.mp hx with he | ht
    · subst xs
      exact intChars_noSlash r.num
    · have he := List.mem_singleton.mp ht
      subst xs
      exact natChars_noSlash r.den
  simpa using List.splitOn_intercalate '/' hx (by simp)

private theorem intChars_asString (n : Int) : String.ofList (intChars n) = toString n := by
  rw [Int.toString_eq_repr]
  cases n with
  | ofNat n =>
    change String.ofList (Nat.toDigits 10 n) = toString n
    exact Nat.toString_eq_ofList_toDigits.symm
  | negSucc n =>
    change String.ofList ('-' :: Nat.toDigits 10 (n + 1)) =
      "-" ++ toString (n + 1)
    rw [String.ofList_cons, ← Nat.toString_eq_ofList_toDigits]
    rfl

theorem strictPrint_eq_num_den (r : Rat) : strictPrint r = s!"{r.num}/{r.den}" := by
  unfold strictPrint
  rw [String.ofList_append, String.ofList_cons, intChars_asString,
    ← Nat.toString_eq_ofList_toDigits]
  simp only [String.append_assoc]
  rfl

theorem decode_strictPrint (r : Rat) : decode (strictPrint r) = .ok r := by
  simp only [decode, strictPrint, String.toList_ofList, decodeChars, printed_split,
    List.head?_cons, Option.getD_some]
  rw [integer_intChars, digits_toDigits]
  simp only [Except.mapError]
  change (if r.den == 0 then Except.error "zero denominator"
    else Except.ok (mkRat r.num r.den)) = Except.ok r
  simp [r.den_nz, Rat.mkRat_self]

theorem strictPrint_injective : Function.Injective strictPrint := by
  intro a b he
  have hx := congrArg decode he
  simpa only [decode_strictPrint, Except.ok.injEq] using hx

theorem strictPrint_zero : strictPrint 0 = "0/1" := by
  rw [strictPrint_eq_num_den]
  simp only [Rat.zero_num, Rat.zero_den, Int.toString_eq_repr, Nat.toString_eq_repr]
  decide

end Rhone.Computation.RationalWire
