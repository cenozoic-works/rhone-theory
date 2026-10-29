/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.CheckerRows
public import Std.Data.HashMap.Lemmas
public import Mathlib.Data.List.Basic

/-! # Table-construction invariants -/

@[expose] public section
namespace Rhone.Computation

theorem insertTableRows_valid_novel {n : Nat} {rows : List (Config × Rat)}
    {table result : Std.HashMap String Rat}
    (h : insertTableRows n rows table = some result) :
    ∀ entry ∈ rows, checkerRowValid n entry.1 = true ∧ table.contains entry.1.key = false := by
  induction rows generalizing table with
  | nil => simp
  | cons entry rows ih =>
    obtain ⟨s, v⟩ := entry
    simp only [insertTableRows] at h
    split at h
    · rename_i hs
      have hg : checkerRowValid n s = true ∧ table.contains s.key = false := by
        simpa using hs
      intro entry he
      rcases List.mem_cons.mp he with rfl | he
      · exact hg
      · obtain ⟨hv, ht⟩ := ih h entry he
        exact ⟨hv, (Bool.or_eq_false_iff.mp (by
          simpa only [Std.HashMap.contains_insert] using ht)).2⟩
    · contradiction

theorem insertTableRows_preserves {n : Nat} {rows : List (Config × Rat)}
    {table result : Std.HashMap String Rat}
    (h : insertTableRows n rows table = some result) {key : String}
    (hk : table.contains key = true) :
    result.contains key = true ∧ result.getD key 0 = table.getD key 0 := by
  induction rows generalizing table with
  | nil =>
    simp only [insertTableRows, Option.some.injEq] at h
    subst result
    exact ⟨hk, rfl⟩
  | cons entry rows ih =>
    obtain ⟨s, v⟩ := entry
    simp only [insertTableRows] at h
    split at h
    · rename_i hs
      have hg : checkerRowValid n s = true ∧ table.contains s.key = false := by
        simpa using hs
      have ha := hg.2
      have hn : s.key ≠ key := by
        intro he
        rw [he, hk] at ha
        contradiction
      have hc : (table.insert s.key v).contains key = true := by
        simp [Std.HashMap.contains_insert, hk]
      obtain ⟨hp, hv⟩ := ih h hc
      exact ⟨hp, hv.trans (by simp [Std.HashMap.getD_insert, hn])⟩
    · contradiction

theorem insertTableRows_values {n : Nat} {rows : List (Config × Rat)}
    {table result : Std.HashMap String Rat}
    (h : insertTableRows n rows table = some result) :
    ∀ entry ∈ rows, result.contains entry.1.key = true ∧ result.getD entry.1.key 0 = entry.2 := by
  induction rows generalizing table with
  | nil => simp
  | cons entry rows ih =>
    obtain ⟨s, v⟩ := entry
    simp only [insertTableRows] at h
    split at h
    · intro entry he
      rcases List.mem_cons.mp he with rfl | he
      · obtain ⟨hp, hv⟩ := insertTableRows_preserves h
          (Std.HashMap.contains_insert_self (m := table) (k := s.key) (v := v))
        exact ⟨hp, hv.trans Std.HashMap.getD_insert_self⟩
      · exact ih h entry he
    · contradiction

theorem insertTableRows_nodup {n : Nat} {rows : List (Config × Rat)}
    {table result : Std.HashMap String Rat}
    (h : insertTableRows n rows table = some result) :
    (rows.map fun entry => entry.1.key).Nodup := by
  induction rows generalizing table with
  | nil => simp
  | cons entry rows ih =>
    obtain ⟨s, v⟩ := entry
    simp only [insertTableRows] at h
    split at h
    · rw [List.map_cons, List.nodup_cons]
      refine ⟨?_, ih h⟩
      intro hm
      obtain ⟨entry, he, hk⟩ := List.mem_map.mp hm
      have ht := (insertTableRows_valid_novel h entry he).2
      simp only [hk, Std.HashMap.contains_insert_self] at ht
      contradiction
    · contradiction

end Rhone.Computation
