/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.ConfigDecimalProof
import Mathlib.Data.List.Range
import Mathlib.Data.List.Basic
import all Init.Data.String.Basic
import all Init.Data.ToString.Basic
import all Init.Data.Repr

/-! # Counts recovered from printed keys -/

@[expose] public section

namespace Rhone.Computation

private def charCounts (decode : List Char → Nat) (xs : List Char) : List Nat :=
  (xs.splitOnP fun ch => !ch.isDigit).filterMap fun digits =>
    if digits = [] then none else some (decode digits)

private theorem charCounts_nil (decode : List Char → Nat) : charCounts decode [] = [] := by
  simp [charCounts]

private theorem charCounts_separator (decode : List Char → Nat) (xs ys : List Char) (ch : Char)
    (hch : ch.isDigit = false) :
    charCounts decode (xs ++ ch :: ys) = charCounts decode xs ++ charCounts decode ys := by
  unfold charCounts
  rw [List.splitOnP_append_cons (p := fun c => !c.isDigit) xs ys (by simp [hch])]
  exact List.filterMap_append

private theorem charCounts_cons_separator (decode : List Char → Nat) (xs : List Char) (ch : Char)
    (hch : ch.isDigit = false) : charCounts decode (ch :: xs) = charCounts decode xs := by
  simpa [charCounts_nil] using charCounts_separator decode [] xs ch hch

private theorem charCounts_intercalate (decode : List Char → Nat) (xs : List (List Char)) :
    charCounts decode ([','].intercalate xs) = xs.flatMap (charCounts decode) := by
  induction xs with
  | nil => simp [charCounts_nil]
  | cons x xs ih =>
    cases xs with
    | nil => simp
    | cons y ys =>
      rw [List.intercalate_cons_cons]
      simp only [List.append_assoc, List.singleton_append]
      rw [charCounts_separator decode _ _ ',' (by decide), ih]
      simp

private theorem charCounts_toDigits (decode : List Char → Nat) (n : Nat)
    (hn : decode (Nat.toDigits 10 n) = n) :
    charCounts decode (Nat.toDigits 10 n) = [n] := by
  unfold charCounts
  rw [List.splitOnP_eq_singleton (by simpa using toDigits_digits n)]
  simp [toDigits_ne_nil n, hn]

private theorem charCounts_formatCounts (decode : List Char → Nat) (xs : Array Nat)
    (h : ∀ n ∈ xs.toList, decode (Nat.toDigits 10 n) = n) :
    charCounts decode (formatCounts xs).toList = xs.toList := by
  unfold formatCounts
  simp only [toString, Nat.repr, String.toList_append, String.toList_intercalate,
    List.map_map, String.toList_ofList, Function.comp_def]
  change charCounts decode ('(' :: ([','].intercalate
    (xs.toList.map fun n => Nat.toDigits 10 n)) ++ [')']) = _
  simp only [List.cons_append]
  rw [charCounts_cons_separator decode _ '(' (by decide),
    charCounts_separator decode _ [] ')' (by decide), charCounts_nil, List.append_nil,
    charCounts_intercalate decode, List.flatMap_map]
  change xs.toList.flatMap (fun n => charCounts decode (Nat.toDigits 10 n)) = xs.toList
  calc
    _ = xs.toList.flatMap (fun n => [n]) :=
      List.flatMap_congr (fun n hn => charCounts_toDigits decode n (h n hn))
    _ = _ := List.flatMap_singleton' xs.toList

private theorem charCounts_rows (decode : List Char → Nat) (rows : List (Array Nat))
    (h : ∀ row ∈ rows, ∀ n ∈ row.toList, decode (Nat.toDigits 10 n) = n) :
    charCounts decode ([','].intercalate (rows.map fun row => (formatCounts row).toList)) =
      rows.flatMap Array.toList := by
  rw [charCounts_intercalate decode, List.flatMap_map]
  apply List.flatMap_congr
  intro row hr
  exact charCounts_formatCounts decode row (h row hr)

private theorem range_rows (ka kb : Nat) (f : Nat → Nat) :
    (List.range ka).flatMap (fun i => (List.range kb).map (fun j => f (i * kb + j))) =
      (List.range (ka * kb)).map f := by
  induction ka with
  | zero => simp
  | succ ka ih =>
    rw [List.range_succ, List.flatMap_append, ih]
    simp only [List.flatMap_singleton]
    rw [Nat.succ_mul, List.range_add, List.map_append, List.map_map]
    simp [Nat.add_comm]

private theorem array_range_getD (xs : Array Nat) :
    (List.range xs.size).map (fun i => xs.getD i 0) = xs.toList := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    rw [← Array.getElem_eq_getD (h := by simpa using h1) 0]
    simp

private theorem charCounts_key (decode : List Char → Nat) (c : Config) (ka kb : Nat)
    (ha : c.a.size = ka) (hb : c.b.size = kb) (hc : c.c.size = ka * kb)
    (hu : ∀ n ∈ c.a.toList ++ c.b.toList ++ c.c.toList, decode (Nat.toDigits 10 n) = n) :
    charCounts decode c.key.toList = c.a.toList ++ c.b.toList ++ c.c.toList := by
  have hau : ∀ n ∈ c.a.toList, decode (Nat.toDigits 10 n) = n := by
    intro n hn; exact hu n (by simp [hn])
  have hbu : ∀ n ∈ c.b.toList, decode (Nat.toDigits 10 n) = n := by
    intro n hn; exact hu n (by simp [hn])
  have hcu : ∀ n ∈ c.c.toList, decode (Nat.toDigits 10 n) = n := by
    intro n hn; exact hu n (by simp [hn])
  unfold Config.key
  simp only [toString, String.toList_append, String.toList_intercalate,
    List.map_map, Function.comp_def]
  have hat : "a=".toList = ['a', '='] := by decide
  have hbt : ";b=".toList = [';', 'b', '='] := by decide
  have hct : ";c=(".toList = [';', 'c', '=', '('] := by decide
  have hcomma : ",".toList = [','] := by decide
  have hend : ")".toList = [')'] := by decide
  rw [hat, hbt, hct, hcomma, hend]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  simp only [charCounts_cons_separator decode _ 'a' (by decide),
    charCounts_cons_separator decode _ 'b' (by decide),
    charCounts_cons_separator decode _ 'c' (by decide),
    charCounts_cons_separator decode _ '=' (by decide),
    charCounts_cons_separator decode _ '(' (by decide),
    charCounts_separator decode _ _ ';' (by decide),
    charCounts_separator decode _ [] ')' (by decide),
    charCounts_nil, List.append_nil]
  rw [show charCounts decode (formatCounts c.a).toList = c.a.toList from
      charCounts_formatCounts decode _ hau,
    show charCounts decode (formatCounts c.b).toList = c.b.toList from
      charCounts_formatCounts decode _ hbu]
  have hrows := charCounts_rows decode
    ((List.range c.a.size).map fun i => (List.range c.b.size).toArray.map fun j =>
      c.c.getD (i * c.b.size + j) 0) (by
        intro row hr n hn
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
        simp only [Array.toList_map, List.mem_map] at hn
        obtain ⟨j, hj, rfl⟩ := hn
        have hij : i * c.b.size + j < c.c.size := by
          rw [ha, hb, hc] at *
          have hi' := List.mem_range.mp hi
          have hj' := List.mem_range.mp hj
          have hm : (i + 1) * kb ≤ ka * kb := Nat.mul_le_mul_right kb (by omega)
          rw [Nat.add_mul] at hm
          omega
        rw [← Array.getElem_eq_getD (h := hij) 0]
        exact hcu _ (by simp))
  simp only [List.map_map, Function.comp_def] at hrows
  rw [hrows]
  simp only [List.flatMap_map, Array.toList_map, ha, hb]
  rw [range_rows ka kb (fun i => c.c.getD i 0), ← hc, array_range_getD]

theorem keyCounts_formatCounts (xs : Array Nat)
    (h : ∀ n ∈ xs.toList, n ≤ 65535) :
    keyCounts (formatCounts xs) = xs.toList :=
  charCounts_formatCounts decimalCount xs (fun n hn => decimalCount_toDigits n (h n hn))

theorem keyCounts_key (c : Config) (ka kb : Nat)
    (ha : c.a.size = ka) (hb : c.b.size = kb) (hc : c.c.size = ka * kb)
    (hu : ∀ n ∈ c.a.toList ++ c.b.toList ++ c.c.toList, n ≤ 65535) :
    keyCounts c.key = c.a.toList ++ c.b.toList ++ c.c.toList :=
  charCounts_key decimalCount c ka kb ha hb hc
    (fun n hn => decimalCount_toDigits n (hu n hn))

theorem Config.key_injective {c d : Config} {ka kb : Nat}
    (ca : c.a.size = ka) (cb : c.b.size = kb) (cc : c.c.size = ka * kb)
    (da : d.a.size = ka) (db : d.b.size = kb) (dc : d.c.size = ka * kb)
    (h : c.key = d.key) : c = d := by
  have hc := charCounts_key decimalValue c ka kb ca cb cc
    (fun n _ => decimalValue_toDigits n)
  have hd := charCounts_key decimalValue d ka kb da db dc
    (fun n _ => decimalValue_toDigits n)
  have he : c.a.toList ++ c.b.toList ++ c.c.toList =
      d.a.toList ++ d.b.toList ++ d.c.toList := by
    rw [← hc, ← hd, h]
  obtain ⟨hab, hh⟩ := List.append_inj he (by simp [ca, cb, da, db])
  obtain ⟨ha, hb⟩ := List.append_inj hab (by simp [ca, da])
  have haa : c.a = d.a := by simpa using congrArg List.toArray ha
  have hbb : c.b = d.b := by simpa using congrArg List.toArray hb
  have hcc : c.c = d.c := by simpa using congrArg List.toArray hh
  cases c; cases d
  simp_all

end Rhone.Computation
