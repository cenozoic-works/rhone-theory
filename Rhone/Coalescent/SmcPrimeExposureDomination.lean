/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeCarrierDomination
public import Rhone.Coalescent.SmcPrimeTreeRootExposure
public import Rhone.Coalescent.SmcSupport.SingleCutReachableExposure

/-! # Tree lengths are dominated by the hull exposure of the ARG prefix -/

@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open MeasureTheory IntervalProcess SmcSupport
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem tree_length_le_clock_exposure {N : ℕ} (T : Tree N) (hn : TreeNonnegative T)
    (n : ℕ) (τ C : ℕ → ℝ) (hzero : τ 0 = 0) (hmono : Monotone τ)
    (hroot : rootHeight T ≤ τ n)
    (hbound : ∀ k < n, ∀ t ∈ Set.Ioo (τ k) (τ (k + 1)), attachmentRate T t ≤ C k) :
    treeLength T ≤ ∑ k ∈ Finset.range n, C k * (τ (k + 1) - τ k) := by
  have hle : treeLength T ≤ attachmentHazard T 0 (τ n) := by
    rw [attachment_hazard_root_stem T hn (τ n) hroot]
    linarith
  have hsum : attachmentHazard T 0 (τ n) =
      ∑ k ∈ Finset.range n, ∫ t in τ k..τ (k + 1), attachmentRate T t := by
    rw [intervalIntegral.sum_integral_adjacent_intervals
      (fun k _ => attachmentRate_intervalIntegrable T (τ k) (τ (k + 1))), hzero]
    rfl
  apply hle.trans
  rw [hsum]
  apply Finset.sum_le_sum
  intro k hk
  have h := intervalIntegral.integral_mono_on_of_le_Ioo (hmono (Nat.le_succ k))
    (attachmentRate_intervalIntegrable T (τ k) (τ (k + 1))) intervalIntegrable_const
    (hbound k (Finset.mem_range.mp hk))
  simpa only [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using h

theorem argHullExposure_ge_tree_lengths {N n : ℕ}
    (T U : Tree N) (hT : TreeNonnegative T) (hU : TreeNonnegative U)
    (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) (s : ℕ → State) (τ : ℕ → ℝ)
    (hzero : τ 0 = 0) (hmono : Monotone τ)
    (hrootT : rootHeight T ≤ τ n) (hrootU : rootHeight U ≤ τ n)
    (hs : ∀ k < n, ZeroSplitReachable (s k) ∨ OneSplitReachable x (s k))
    (hleft : ∀ k < n, ∀ t ∈ Set.Ioo (τ k) (τ (k + 1)),
      attachmentRate T t ≤ ∑ i, if materialContains ((s k).2.2.2 i).2 0 then (1 : ℝ) else 0)
    (hright : ∀ k < n, ∀ t ∈ Set.Ioo (τ k) (τ (k + 1)),
      attachmentRate U t ≤ ∑ i, if materialContains ((s k).2.2.2 i).2 x then (1 : ℝ) else 0) :
    x * treeLength T + (1 - x) * treeLength U ≤
      argHullExposure (fun k : Fin n => s k.val) (fun k => τ (k.val + 1) - τ k.val) := by
  have hL := tree_length_le_clock_exposure T hT n τ
    (fun k => ∑ i, if materialContains ((s k).2.2.2 i).2 0 then (1 : ℝ) else 0)
    hzero hmono hrootT hleft
  have hR := tree_length_le_clock_exposure U hU n τ
    (fun k => ∑ i, if materialContains ((s k).2.2.2 i).2 x then (1 : ℝ) else 0)
    hzero hmono hrootU hright
  rw [← Fin.sum_univ_eq_sum_range] at hL hR
  rw [pre_second_hull_exposure_carriers x hx0 hx1
    (fun k : Fin n => s k.val) (fun k => τ (k.val + 1) - τ k.val)
    (fun k => hs k.val k.isLt)]
  exact add_le_add (mul_le_mul_of_nonneg_left hL hx0.le)
    (mul_le_mul_of_nonneg_left hR (sub_nonneg.mpr hx1.le))

end Rhone.Coalescent.SmcPrime
