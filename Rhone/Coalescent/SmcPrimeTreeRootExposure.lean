/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.SmcPrimeSpatialGeometry
public import Rhone.Coalescent.SmcPrimeAttachmentHazard

/-! # The exact integrated branch-count exposure, including the immortal root stem -/

@[expose] public section

namespace Rhone.Coalescent.SmcPrime
open MeasureTheory
open scoped BigOperators

private noncomputable def openBranchCount {N : ℕ} (b : Branch N) (q : ℝ) : ℝ :=
  if 0 < branchLength b then (Set.Ioo b.2.1 b.2.2).indicator (fun _ => 1) q else 0

private theorem openBranchCount_integrable {N : ℕ} (b : Branch N) :
    Integrable (openBranchCount b) := by
  classical
  change Integrable (fun q => if 0 < branchLength b then
    (Set.Ioo b.2.1 b.2.2).indicator (fun _ => (1 : ℝ)) q else 0)
  by_cases hb : 0 < branchLength b
  · simp only [hb, ↓reduceIte]
    exact (integrableOn_const (C := (1 : ℝ)) (by simp)).integrable_indicator measurableSet_Ioo
  · simp [hb]

private theorem openBranchCount_integral {N : ℕ} (b : Branch N) :
    (∫ q, openBranchCount b q) = branchLength b := by
  classical
  by_cases hb : 0 < branchLength b
  · have hc : ¬ (b.1 = ∅ ∨ b.1 = Finset.univ) := by
      intro hc
      simp [branchLength, hc] at hb
    simp only [openBranchCount, hb, ↓reduceIte]
    rw [integral_indicator measurableSet_Ioo, integral_const]
    simp [Measure.real, Real.volume_Ioo, branchLength, hc, max_comm,
      ENNReal.toReal_ofReal']
  · have hz : branchLength b = 0 := le_antisymm (le_of_not_gt hb) (branchLength_nonneg b)
    simp [openBranchCount, hz]

private theorem openBranchCount_interval {N : ℕ} (T : Tree N)
    (hn : TreeNonnegative T) (i : Fin T.1) :
    (∫ q in 0..rootHeight T, openBranchCount (T.2 i) q) = branchLength (T.2 i) := by
  rw [intervalIntegral.integral_eq_integral_of_support_subset, openBranchCount_integral]
  intro q hq
  have hp : 0 < branchLength (T.2 i) := by
    by_contra hp
    simp [Function.mem_support, openBranchCount, hp] at hq
  have hi : q ∈ Set.Ioo (T.2 i).2.1 (T.2 i).2.2 := by
    by_contra hi
    simp [Function.mem_support, openBranchCount, hp, hi] at hq
  exact ⟨(hn i).trans_lt hi.1, hi.2.le.trans (branch_hi_le_root T i hp)⟩

private theorem attachment_hazard_to_root {N : ℕ} (T : Tree N)
    (hn : TreeNonnegative T) : attachmentHazard T 0 (rootHeight T) = treeLength T := by
  classical
  have ha : ∀ᵐ q : ℝ ∂volume, ∀ i : Fin T.1, q ≠ (T.2 i).2.1 :=
    ae_all_iff.mpr (fun i => volume.ae_ne _)
  have hr : ∀ᵐ q : ℝ ∂volume, q ≠ rootHeight T := volume.ae_ne _
  have heq : (∫ q in 0..rootHeight T, attachmentRate T q) =
      ∫ q in 0..rootHeight T, ∑ i, openBranchCount (T.2 i) q := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [ha, hr] with q hq hqr hmem
    rw [Set.uIoc_of_le (root_height_nonneg T)] at hmem
    have hroot : q < rootHeight T := lt_of_le_of_ne hmem.2 hqr
    simp only [attachmentRate, not_le.mpr hroot, ↓reduceIte, activeBranches]
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    simp only [Nat.cast_one, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    have hli : (T.2 i).2.1 ≤ q ↔ (T.2 i).2.1 < q :=
      ⟨fun h => lt_of_le_of_ne h (Ne.symm (hq i)), fun h => h.le⟩
    by_cases hp : 0 < branchLength (T.2 i)
    · simp [openBranchCount, hp, hli, Set.indicator_apply, Set.mem_Ioo]
    · simp [openBranchCount, hp]
  rw [attachmentHazard, heq, intervalIntegral.integral_finsetSum]
  · simp only [openBranchCount_interval T hn, treeLength]
  · intro i _
    exact (openBranchCount_integrable (T.2 i)).intervalIntegrable

theorem attachment_hazard_root_stem {N : ℕ} (T : Tree N)
    (hn : TreeNonnegative T) (S : ℝ) (hS : rootHeight T ≤ S) :
    attachmentHazard T 0 S = treeLength T + (S-rootHeight T) := by
  rw [← attachmentHazard_add T 0 (rootHeight T) S, attachment_hazard_to_root T hn,
    attachmentHazard_above_root T (rootHeight T) S le_rfl hS]

end Rhone.Coalescent.SmcPrime
