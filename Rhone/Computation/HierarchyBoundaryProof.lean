/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.HierarchySuccessProof
public import Rhone.Computation.BlockApplyProof
public import Rhone.Computation.SourceProof

/-! # Special hierarchy branches and block lengths -/

@[expose] public section

namespace Rhone.Computation

theorem source_one_one (p : Params) (tab : PhiTable) (t : Nat) (ht : t ≤ 1) :
    source p tab 1 1 t = 0 := by
  have he : t = 0 ∨ t = 1 := by omega
  rcases he with rfl | rfl <;> simp [source_eq_srcR, Rhone.Probability.ExplicitFormula.srcR]

theorem hierarchyBlock_one_one (p : Params) (tab : PhiTable) :
    hierarchyBlock p tab 1 1 = .ok #[0, 0] := by
  simp [hierarchyBlock, source_one_one p tab 0 (by omega)]
  rfl

theorem hierarchyBlock_exists_sized (p : Params) (tab : PhiTable) (i j : Nat)
    (hθA : 0 < p.thetaA) (hθB : 0 < p.thetaB) (hρ : 0 ≤ p.rho) :
    ∃ block, hierarchyBlock p tab i j = .ok block ∧ block.size = min i j + 1 := by
  obtain ⟨block, hb⟩ := hierarchyBlock_success p tab i j hθA hθB hρ
  refine ⟨block, hb, ?_⟩
  unfold hierarchyBlock at hb
  split at hb
  · rename_i h00
    simp only [Bool.and_eq_true_iff, beq_iff_eq] at h00
    obtain ⟨rfl, rfl⟩ := h00
    cases hb
    rfl
  · rename_i h00
    split at hb
    · rename_i h1
      simp only [beq_iff_eq] at h1
      have hz : i = 0 ∨ j = 0 := by omega
      cases hb
      rcases hz with rfl | rfl <;> simp
    · split at hb
      · rename_i h11
        simp only [Bool.and_eq_true_iff, beq_iff_eq] at h11
        obtain ⟨rfl, rfl⟩ := h11
        cases hb
        rfl
      · have hij : 0 < i + j := by
          simp only [Bool.and_eq_true_iff, beq_iff_eq] at h00
          omega
        rw [solveBlock_eq_ok p i j _ hθA hθB hρ hij] at hb
        cases hb
        exact applyBlockInverse_size p i j _ _ _ _

end Rhone.Computation
