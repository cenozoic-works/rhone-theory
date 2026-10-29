/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.RationalWirePrintProof
import all Init.Control.Except

/-! # Exact grammar and value of every accepted rational input -/

@[expose] public section
namespace Rhone.Computation.RationalWire

def DigitSyntax (xs : List Char) : Prop :=
  xs ≠ [] ∧ xs.all Char.isDigit = true

def IntegerSyntax (xs : List Char) (n : Int) : Prop :=
  (DigitSyntax xs ∧ n = (decimal xs : Int)) ∨
    ∃ ds, xs = '-' :: ds ∧ DigitSyntax ds ∧ n = -(decimal ds : Int)

def RationalSyntax (xs : List Char) (r : Rat) : Prop :=
  (∃ n, IntegerSyntax xs n ∧ r = (n : Rat)) ∨
    ∃ a d n denominator, xs = a ++ '/' :: d ∧
      IntegerSyntax a n ∧ DigitSyntax d ∧ denominator = decimal d ∧
      0 < denominator ∧ r = mkRat n denominator

@[simp] private theorem ok_bind {α β : Type} (x : α) (f : α → Except String β) :
    ((Except.ok x : Except String α) >>= f) = f x := rfl

@[simp] private theorem error_bind {α β : Type} (e : String) (f : α → Except String β) :
    ((Except.error e : Except String α) >>= f) = .error e := rfl

@[simp] private theorem ok_map {α β : Type} (x : α) (f : α → β) :
    f <$> (Except.ok x : Except String α) = Except.ok (f x) := rfl

@[simp] private theorem error_map {α β : Type} (e : String) (f : α → β) :
    f <$> (Except.error e : Except String α) = Except.error e := rfl

@[simp] private theorem throw_def {α : Type} (e : String) :
    (throw e : Except String α) = Except.error e := rfl

private theorem digitSyntax_iff (xs : List Char) :
    DigitSyntax xs ↔ digits xs = .ok (decimal xs) := by
  simpa [DigitSyntax, List.all_eq_true] using
    (digits_eq_ok_iff xs (decimal xs)).symm

private theorem digits_map_iff (xs : List Char) (f : Nat → Int) (n : Int) :
    (f <$> (digits xs).mapError (fun _ => "invalid numerator")) = .ok n ↔
      DigitSyntax xs ∧ n = f (decimal xs) := by
  cases hx : digits xs with
  | error e =>
    have hn : ¬ DigitSyntax xs := by
      intro hsyntax
      have h := (digitSyntax_iff xs).1 hsyntax
      rw [hx] at h
      contradiction
    simp [Except.mapError, hn]
  | ok k =>
    obtain ⟨hne, hdigits, hk⟩ := (digits_eq_ok_iff xs k).1 hx
    subst k
    have hsyntax : DigitSyntax xs := ⟨hne, List.all_eq_true.mpr hdigits⟩
    simp only [Except.mapError, ok_map, Except.ok.injEq]
    exact ⟨fun h => ⟨hsyntax, h.symm⟩, fun h => h.2.symm⟩

theorem integer_eq_ok_iff (xs : List Char) (n : Int) :
    integer xs = .ok n ↔ IntegerSyntax xs n := by
  cases xs with
  | nil => simp [integer, digits, Except.mapError, IntegerSyntax, DigitSyntax]
  | cons ch ds =>
    by_cases hc : ch = '-'
    · subst ch
      simpa [integer, IntegerSyntax, DigitSyntax] using
        digits_map_iff ds (fun k => -(k : Int)) n
    · simpa [integer, hc, IntegerSyntax] using
        digits_map_iff (ch :: ds) (fun k => (k : Int)) n

private theorem integer_noSlash {xs : List Char} {n : Int}
    (h : IntegerSyntax xs n) : '/' ∉ xs := by
  rcases h with ⟨hd, _⟩ | ⟨ds, rfl, hd, _⟩
  · intro hm
    have hf := (List.all_eq_true.mp hd.2) '/' hm
    have hn : '/'.isDigit = false := by decide
    rw [hn] at hf
    contradiction
  · simp only [List.mem_cons, not_or]
    constructor
    · decide
    · intro hm
      have hf := (List.all_eq_true.mp hd.2) '/' hm
      have hn : '/'.isDigit = false := by decide
      rw [hn] at hf
      contradiction

theorem decode_integer {xs : List Char} {n : Int}
    (h : IntegerSyntax xs n) : decodeChars xs = .ok (n : Rat) := by
  have hs : xs.splitOn '/' = [xs] :=
    List.splitOn_eq_singleton (integer_noSlash h)
  have hi := (integer_eq_ok_iff xs n).2 h
  simp [decodeChars, hs, hi]

theorem decode_fraction {a d : List Char} {n : Int}
    (ha : IntegerSyntax a n) (hd : DigitSyntax d) (hpos : 0 < decimal d) :
    decodeChars (a ++ '/' :: d) = .ok (mkRat n (decimal d)) := by
  have hna := integer_noSlash ha
  have hnd : '/' ∉ d := by
    intro hm
    have hf := (List.all_eq_true.mp hd.2) '/' hm
    have hn : '/'.isDigit = false := by decide
    rw [hn] at hf
    contradiction
  have hs : (a ++ '/' :: d).splitOn '/' = [a, d] := by
    simpa using List.splitOn_intercalate (ls := [a, d]) '/'
      (by
        intro xs hx
        rcases List.mem_cons.mp hx with he | ht
        · subst xs
          exact hna
        · have he := List.mem_singleton.mp ht
          subst xs
          exact hnd) (by simp)
  have hi := (integer_eq_ok_iff a n).2 ha
  have hx := (digits_eq_ok_iff d (decimal d)).2
    ⟨hd.1, List.all_eq_true.mp hd.2, rfl⟩
  simp [decodeChars, hs, hi, hx, Except.mapError, Nat.ne_of_gt hpos]

theorem decode_of_syntax {xs : List Char} {r : Rat}
    (h : RationalSyntax xs r) : decodeChars xs = .ok r := by
  rcases h with ⟨n, hn, rfl⟩ | ⟨a, d, n, denominator, rfl, ha, hd, rfl, hpos, rfl⟩
  · exact decode_integer hn
  · exact decode_fraction ha hd hpos

theorem syntax_of_decode {xs : List Char} {r : Rat}
    (h : decodeChars xs = .ok r) : RationalSyntax xs r := by
  have hrec := List.intercalate_splitOn (xs := xs) '/'
  cases hs : xs.splitOn '/' with
  | nil =>
    have hn := List.splitOn_ne_nil '/' xs
    exact False.elim (hn hs)
  | cons a rest =>
    cases hi : integer a with
    | error e => simp [decodeChars, hs, hi] at h
    | ok n =>
      have ha := (integer_eq_ok_iff a n).1 hi
      cases rest with
      | nil =>
        have hv : (n : Rat) = r := by simpa [decodeChars, hs, hi] using h
        have hx : xs = a := by simpa [hs] using hrec.symm
        subst xs
        exact Or.inl ⟨n, ha, hv.symm⟩
      | cons d rest =>
        cases rest with
        | cons e more => simp [decodeChars, hs, hi] at h
        | nil =>
          cases hd : digits d with
          | error e => simp [decodeChars, hs, hi, hd, Except.mapError] at h
          | ok denominator =>
            by_cases hz : denominator = 0
            · simp [decodeChars, hs, hi, hd, Except.mapError, hz] at h
            · have hpos : 0 < denominator := Nat.pos_of_ne_zero hz
              have hv : mkRat n denominator = r := by
                simpa [decodeChars, hs, hi, hd, Except.mapError, hz] using h
              have hx : xs = a ++ '/' :: d := by simpa [hs] using hrec.symm
              obtain ⟨hnd, hchars, hvalue⟩ := (digits_eq_ok_iff d denominator).1 hd
              exact Or.inr ⟨a, d, n, denominator, hx, ha,
                ⟨hnd, List.all_eq_true.mpr hchars⟩, hvalue, hpos, hv.symm⟩

theorem decodeChars_eq_ok_iff (xs : List Char) (r : Rat) :
    decodeChars xs = .ok r ↔ RationalSyntax xs r :=
  ⟨syntax_of_decode, decode_of_syntax⟩

theorem decode_eq_ok_iff (s : String) (r : Rat) :
    decode s = .ok r ↔ RationalSyntax s.toList r :=
  decodeChars_eq_ok_iff s.toList r

end Rhone.Computation.RationalWire
