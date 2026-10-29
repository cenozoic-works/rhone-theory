/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.Checker
public import Rhone.Computation.CheckerRowsProof
public import Mathlib.Data.List.Range

/-! # Conditions established by exact checker acceptance -/

@[expose] public section
namespace Rhone.Computation

theorem checkTable_true_iff {p : Params} {n : Nat} {entries : Array (Config × Rat)} :
    checkTable p n entries = true ↔
    ∃ table : Std.HashMap String Rat,
      insertTableRows n entries.toList {} = some table ∧ p.valid = true ∧
      entries.size = (closure n).size ∧
      (∀ s ∈ closure n, table.contains s.key = true) ∧
      table.getD (configOfCounts 0 0 0 0 0 0 0 0).key 0 = 1 ∧
      (∀ s ∈ closure n, checkerEquation p (fun s => table.getD s.key 0) s = true) ∧
      (∀ size, size ≤ n →
        checkerNormalization (fun s => table.getD s.key 0) (closure n) size = 1) := by
  by_cases hp : p.valid = true
  · cases ht : insertTableRows n entries.toList {} with
    | none => simp [checkTable, hp, ht]
    | some table =>
      simp [checkTable, hp, ht, Array.all_eq_true', -Array.all_eq_true,
        and_assoc, Nat.lt_succ_iff]
  · simp [checkTable, hp]

theorem checkTable_rows {p : Params} {n : Nat} {entries : Array (Config × Rat)}
    (h : checkTable p n entries = true) :
    ∃ table : Std.HashMap String Rat,
      insertTableRows n entries.toList {} = some table ∧
      ∀ entry ∈ entries, checkerRowValid n entry.1 = true ∧
        table.contains entry.1.key = true ∧ table.getD entry.1.key 0 = entry.2 := by
  obtain ⟨table, ht, _⟩ := checkTable_true_iff.mp h
  refine ⟨table, ht, ?_⟩
  intro entry he
  have hl : entry ∈ entries.toList := Array.mem_toList_iff.mpr he
  exact ⟨(insertTableRows_valid_novel ht entry hl).1, insertTableRows_values ht entry hl⟩

theorem checkTable_nodup {p : Params} {n : Nat} {entries : Array (Config × Rat)}
    (h : checkTable p n entries = true) :
    (entries.toList.map fun entry => entry.1.key).Nodup := by
  obtain ⟨table, ht, _⟩ := checkTable_true_iff.mp h
  exact insertTableRows_nodup ht

theorem checkTable_singleton {p : Params} {n : Nat} {entries : Array (Config × Rat)}
    (h : checkTable p n entries = true) {s : Config} (hs : s ∈ closure n)
    (hn : checkerLineages s = 1) :
    ∃ table : Std.HashMap String Rat,
      insertTableRows n entries.toList {} = some table ∧
      table.getD s.key 0 = checkerBoundary p s := by
  obtain ⟨table, ht, _, _, _, _, he, _⟩ := checkTable_true_iff.mp h
  refine ⟨table, ht, ?_⟩
  have hrow := (Bool.and_eq_true_iff.mp (he s hs)).1
  simpa [checkerEquation, hn] using hrow

theorem checkTable_recursion {p : Params} {n : Nat} {entries : Array (Config × Rat)}
    (h : checkTable p n entries = true) {s : Config} (hs : s ∈ closure n)
    (hn : 2 ≤ checkerLineages s) :
    ∃ table : Std.HashMap String Rat,
      insertTableRows n entries.toList {} = some table ∧
      checkerDiagonal p s * table.getD s.key 0 =
        recursionRhs p (fun s => table.getD s.key 0) s := by
  obtain ⟨table, ht, _, _, _, _, he, _⟩ := checkTable_true_iff.mp h
  refine ⟨table, ht, ?_⟩
  have hrow := (Bool.and_eq_true_iff.mp (he s hs)).2
  simpa [checkerEquation, hn] using hrow

end Rhone.Computation
