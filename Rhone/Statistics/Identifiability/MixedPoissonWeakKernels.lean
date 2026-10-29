/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeSampleCountObservation
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Data.Nat.Pairing

/-! # Bounded vanishing kernels for exact mixed Poisson counts -/

@[expose] public section

noncomputable section
open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction
namespace Rhone.Statistics.Identifiability
namespace MixedPoisson

lemma cell_le_one {r : ℝ} (hr : 0 ≤ r) (k : ℕ) : cell r k ≤ 1 := by
  have hs : HasSum (cell r) 1 := by simpa using hasSum_cell_pgf r 1
  exact le_hasSum hs k (fun i _ => cell_nonneg hr i)

lemma cell_tendsto_zero (k : ℕ) : Tendsto (fun r => cell r k) atTop (𝓝 0) := by
  convert (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).div_const (k.factorial : ℝ) using 1
  · ext r
    simp only [cell, mul_comm]
  · simp

def boundedCell (a b : ℝ) (k : ℕ × ℕ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (ℝ × ℝ) →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x => cell (a * |x.1|) k.1 * cell (b * |x.2|) k.2, by
      unfold cell
      fun_prop⟩ 1 (by
      intro x y
      change dist (cell (a * |x.1|) k.1 * cell (b * |x.2|) k.2)
        (cell (a * |y.1|) k.1 * cell (b * |y.2|) k.2) ≤ 1
      rw [Real.dist_eq, abs_le]
      have hx0 := mul_nonneg (cell_nonneg (mul_nonneg ha (abs_nonneg x.1)) k.1)
        (cell_nonneg (mul_nonneg hb (abs_nonneg x.2)) k.2)
      have hy0 := mul_nonneg (cell_nonneg (mul_nonneg ha (abs_nonneg y.1)) k.1)
        (cell_nonneg (mul_nonneg hb (abs_nonneg y.2)) k.2)
      have hx1 : cell (a * |x.1|) k.1 * cell (b * |x.2|) k.2 ≤ 1 :=
        (mul_le_of_le_one_left (cell_nonneg (mul_nonneg hb (abs_nonneg x.2)) k.2)
          (cell_le_one (mul_nonneg ha (abs_nonneg x.1)) k.1)).trans
        (cell_le_one (mul_nonneg hb (abs_nonneg x.2)) k.2)
      have hy1 : cell (a * |y.1|) k.1 * cell (b * |y.2|) k.2 ≤ 1 :=
        (mul_le_of_le_one_left (cell_nonneg (mul_nonneg hb (abs_nonneg y.2)) k.2)
          (cell_le_one (mul_nonneg ha (abs_nonneg y.1)) k.1)).trans
        (cell_le_one (mul_nonneg hb (abs_nonneg y.2)) k.2)
      exact ⟨by linarith, by linarith⟩)

@[simp] lemma boundedCell_apply (a b : ℝ) (k : ℕ × ℕ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (x : ℝ × ℝ) :
    boundedCell a b k ha hb x = cell (a * |x.1|) k.1 * cell (b * |x.2|) k.2 := rfl

lemma boundedCell_nonneg (a b : ℝ) (k : ℕ × ℕ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (x : ℝ × ℝ) :
    0 ≤ boundedCell a b k ha hb x :=
  mul_nonneg (cell_nonneg (mul_nonneg ha (abs_nonneg x.1)) k.1)
    (cell_nonneg (mul_nonneg hb (abs_nonneg x.2)) k.2)

lemma integral_boundedCell (μ : Measure (ℝ × ℝ))
    (hμ : FiniteSiteObservation.NonnegativeTimes μ)
    (a b : ℝ) (k : ℕ × ℕ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∫ x, boundedCell a b k ha hb x ∂μ) = mass a b μ k := by
  apply integral_congr_ae
  filter_upwards [hμ] with x hx
  simp only [boundedCell_apply, abs_of_nonneg hx.1, abs_of_nonneg hx.2]

lemma boundedCell_vanishes {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (k : ℕ × ℕ) :
    Tendsto (boundedCell a b k ha.le hb.le) (cocompact (ℝ × ℝ)) (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have h1 : ∀ᶠ r : ℝ in atTop, cell (a * r) k.1 < ε :=
    ((cell_tendsto_zero k.1).comp (tendsto_id.const_mul_atTop ha)).eventually
      (eventually_lt_nhds hε)
  have h2 : ∀ᶠ r : ℝ in atTop, cell (b * r) k.2 < ε :=
    ((cell_tendsto_zero k.2).comp (tendsto_id.const_mul_atTop hb)).eventually
      (eventually_lt_nhds hε)
  obtain ⟨R, hR⟩ := eventually_atTop.mp h1
  obtain ⟨S, hS⟩ := eventually_atTop.mp h2
  apply mem_cocompact.mpr
  refine ⟨Icc (-R) R ×ˢ Icc (-S) S, isCompact_Icc.prod isCompact_Icc, ?_⟩
  intro x hx
  have hx' : ¬ ((-R ≤ x.1 ∧ x.1 ≤ R) ∧ (-S ≤ x.2 ∧ x.2 ≤ S)) := hx
  have hn := boundedCell_nonneg a b k ha.le hb.le x
  change dist (boundedCell a b k ha.le hb.le x) 0 < ε
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hn]
  change cell (a * |x.1|) k.1 * cell (b * |x.2|) k.2 < ε
  by_cases hRx : R ≤ |x.1|
  · exact (mul_le_of_le_one_right
      (cell_nonneg (mul_nonneg ha.le (abs_nonneg x.1)) k.1)
      (cell_le_one (mul_nonneg hb.le (abs_nonneg x.2)) k.2)).trans_lt (hR _ hRx)
  · have hSx : S ≤ |x.2| := by
      by_contra h
      apply hx'
      exact ⟨(abs_le.mp (le_of_not_ge hRx)), (abs_le.mp (le_of_not_ge h))⟩
    exact (mul_le_of_le_one_left
      (cell_nonneg (mul_nonneg hb.le (abs_nonneg x.2)) k.2)
      (cell_le_one (mul_nonneg ha.le (abs_nonneg x.1)) k.1)).trans_lt (hS _ hSx)

end MixedPoisson
end Rhone.Statistics.Identifiability
