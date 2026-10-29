/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.CheckerClosureNodupProof
public import Rhone.Computation.CheckerClosureEnumerationProof
public import Rhone.Computation.CheckerRowsProof
public import Rhone.Computation.ConfigKeyProof

/-! # Exact restrictions populate the complete table -/

@[expose] public section
namespace Rhone.Computation

theorem closureList_shape {n : Nat} {s : Config} (hs : s ∈ closureList n) :
    s.a.size = 2 ∧ s.b.size = 2 ∧ s.c.size = 4 := by
  simp only [closureList, List.mem_flatMap, List.mem_map] at hs
  rcases hs with ⟨c00, _, c01, _, c10, _, c11, _, a0, _, a1, _, b0, _, b1, _, rfl⟩
  exact ⟨rfl, rfl, rfl⟩

theorem closureList_rowValid {n : Nat} {s : Config} (hs : s ∈ closureList n) :
    checkerRowValid n s = true := by
  simp only [closureList, List.mem_flatMap, List.mem_range, List.mem_map] at hs
  rcases hs with ⟨c00, h00, c01, h01, c10, h10, c11, h11,
    a0, ha0, a1, ha1, b0, hb0, b1, hb1, rfl⟩
  simp [checkerRowValid, configOfCounts, Config.block]
  omega

theorem closureList_keys_nodup (n : Nat) :
    ((closureList n).map Config.key).Nodup := by
  refine (closureList_nodup n).map_on ?_
  intro c hc d hd he
  obtain ⟨ca, cb, cc⟩ := closureList_shape hc
  obtain ⟨da, db, dc⟩ := closureList_shape hd
  exact Config.key_injective ca cb cc da db dc he

theorem insertTableRows_of_valid_nodup {n : Nat} {rows : List (Config × Rat)}
    (valid : ∀ entry ∈ rows, checkerRowValid n entry.1 = true)
    (nodup : (rows.map fun entry => entry.1.key).Nodup)
    (table : Std.HashMap String Rat)
    (absent : ∀ entry ∈ rows, table.contains entry.1.key = false) :
    ∃ result, insertTableRows n rows table = some result := by
  induction rows generalizing table with
  | nil => exact ⟨table, rfl⟩
  | cons entry rows ih =>
    obtain ⟨s, v⟩ := entry
    have hv := valid (s, v) (List.mem_cons_self ..)
    have ha := absent (s, v) (List.mem_cons_self ..)
    have hn := List.nodup_cons.mp nodup
    obtain ⟨result, hr⟩ := ih (fun entry he => valid entry (List.mem_cons_of_mem _ he))
      hn.2 (table.insert s.key v) (by
        intro entry he
        have hk : entry.1.key ≠ s.key := by
          intro hk
          exact hn.1 (List.mem_map.mpr ⟨entry, he, hk⟩)
        simp [Std.HashMap.contains_insert, Ne.symm hk,
          absent entry (List.mem_cons_of_mem _ he)])
    refine ⟨result, ?_⟩
    simpa [insertTableRows, hv, ha] using hr

theorem insertTableRows_closure (n : Nat) (value : Config → Rat) :
    ∃ result, insertTableRows n ((closureList n).map fun s => (s, value s)) ∅ =
      some result := by
  apply insertTableRows_of_valid_nodup
  · intro entry he
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp he
    exact closureList_rowValid hs
  · simpa only [List.map_map, Function.comp_def] using closureList_keys_nodup n
  · intro entry _
    exact Std.HashMap.contains_empty

theorem insertTableRows_closure_values {n : Nat} {value : Config → Rat}
    {result : Std.HashMap String Rat}
    (h : insertTableRows n ((closureList n).map fun s => (s, value s)) ∅ = some result)
    {s : Config} (hs : s ∈ closureList n) :
    result.contains s.key = true ∧ result.getD s.key 0 = value s :=
  insertTableRows_values h (s, value s) (List.mem_map.mpr ⟨s, hs, rfl⟩)

end Rhone.Computation
