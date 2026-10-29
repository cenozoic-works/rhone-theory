/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.BlockSolverProof
public import Rhone.Computation.SourceLowerProof
public import Rhone.Computation.HierarchyValueSpec
public import Rhone.Computation.HierarchyBoundaryProof

/-! # Identifying each executable hierarchy block -/

@[expose] public section

namespace Rhone.Computation

theorem solveBlock_source_eq_ok (p : Params) (tab : PhiTable)
    (value : Nat → Nat → Nat → Rat) (laws : HierarchyValueLaws p value)
    (i j : Nat) (hθA : 0 < p.thetaA) (hθB : 0 < p.thetaB) (hρ : 0 ≤ p.rho)
    (hij : 0 < i + j)
    (h : ∀ a b d, a ≤ i → b ≤ j → a + b < i + j → d ≤ min a b →
      tab.get a b d = value a b d) :
    solveBlock p i j ((List.range (min i j + 1)).toArray.map (source p tab i j)) =
      .ok (((List.range (min i j + 1)).map (value i j)).toArray) := by
  rw [solveBlock_eq_ok_spec p i j _ hθA hθB hρ hij]
  congr 2
  apply List.map_congr_left
  intro t hmem
  have ht : t ≤ min i j := by have := List.mem_range.mp hmem; omega
  rw [laws.block i j t hij ht]
  congr 1
  apply Finset.sum_congr rfl
  intro u hmem'
  have hu : u ≤ min i j := by have := Finset.mem_range.mp hmem'; omega
  have hult : u < min i j + 1 := by omega
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map, List.getElem?_toArray,
    List.getElem?_range hult, Option.map_some, Option.getD_some]
  rw [source_eq_srcR_of_lower p tab value i j u hu h]
  simp only [Array.getD_eq_getD_getElem?]

private theorem value_singleton_zero (p : Params) (value : Nat → Nat → Nat → Rat)
    (laws : HierarchyValueLaws p value) (i j : Nat) (hij : i + j = 1) :
    value i j 0 = 0 := by
  have hz : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by omega
  rcases hz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    rw [laws.block _ _ 0 (by omega) (by simp)] <;>
    simp [Rhone.Probability.ExplicitFormula.srcR]

private theorem value_one_one_zero (p : Params) (value : Nat → Nat → Nat → Rat)
    (laws : HierarchyValueLaws p value) (t : Nat) (ht : t ≤ 1) :
    value 1 1 t = 0 := by
  rw [laws.block 1 1 t (by omega) (by simpa using ht)]
  have hs : ∀ u ∈ Finset.range 2,
      Rhone.Probability.ExplicitFormula.srcR
        (p.piA.getD 0 0 * p.piA.getD 1 0) (p.piA.getD 1 0 - p.piA.getD 0 0)
        (p.piB.getD 0 0 * p.piB.getD 1 0) (p.piB.getD 1 0 - p.piB.getD 0 0)
        value 1 1 u = 0 := by
    intro u hu
    have he : u = 0 ∨ u = 1 := by have := Finset.mem_range.mp hu; omega
    rcases he with rfl | rfl <;> simp [Rhone.Probability.ExplicitFormula.srcR]
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro u hu
  rw [hs u hu, mul_zero]

theorem hierarchyBlock_eq_ok_value (p : Params) (tab : PhiTable)
    (value : Nat → Nat → Nat → Rat) (laws : HierarchyValueLaws p value)
    (i j : Nat) (hθA : 0 < p.thetaA) (hθB : 0 < p.thetaB) (hρ : 0 ≤ p.rho)
    (h : ∀ a b d, a ≤ i → b ≤ j → a + b < i + j → d ≤ min a b →
      tab.get a b d = value a b d) :
    hierarchyBlock p tab i j =
      .ok (((List.range (min i j + 1)).map (value i j)).toArray) := by
  unfold hierarchyBlock
  split
  · rename_i h00
    simp only [Bool.and_eq_true_iff, beq_iff_eq] at h00
    obtain ⟨rfl, rfl⟩ := h00
    simp [laws.empty]
    rfl
  · rename_i h00
    split
    · rename_i h1
      simp only [beq_iff_eq] at h1
      have hm : min i j = 0 := by omega
      simp [hm, value_singleton_zero p value laws i j h1]
      rfl
    · split
      · rename_i h11
        simp only [Bool.and_eq_true_iff, beq_iff_eq] at h11
        obtain ⟨rfl, rfl⟩ := h11
        simp [source_one_one p tab 0 (by omega), List.range_succ,
          value_one_one_zero p value laws 0 (by omega),
          value_one_one_zero p value laws 1 (by omega)]
        rfl
      · have hij : 0 < i + j := by
          simp only [Bool.and_eq_true_iff, beq_iff_eq] at h00
          omega
        exact solveBlock_source_eq_ok p tab value laws i j hθA hθB hρ hij h

end Rhone.Computation
