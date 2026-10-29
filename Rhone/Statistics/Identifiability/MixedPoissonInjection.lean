/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.PoissonLaplaceRectangle
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-! # Arbitrary finite product-Poisson mixing measures are identifiable -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
namespace Rhone.Statistics.Identifiability
namespace MixedPoisson

def cell (r : ℝ) (k : ℕ) : ℝ := Real.exp (-r) * r ^ k / (k.factorial : ℝ)

lemma cell_nonneg {r : ℝ} (hr : 0 ≤ r) (k : ℕ) : 0 ≤ cell r k := by
  unfold cell
  positivity

lemma hasSum_cell_pgf (r z : ℝ) :
    HasSum (fun k : ℕ => cell r k * z ^ k) (Real.exp (r * (z - 1))) := by
  have h := (NormedSpace.expSeries_div_hasSum_exp (r * z)).mul_left (Real.exp (-r))
  convert! h using 1
  · ext k
    simp only [cell, mul_pow]
    ring
  · rw [← Real.exp_eq_exp_ℝ, ← Real.exp_add]
    congr 1
    ring

set_option maxHeartbeats 800000 in
lemma hasSum_product_pgf (r s z w : ℝ) :
    HasSum (fun k : ℕ × ℕ => (cell r k.1 * z ^ k.1) * (cell s k.2 * w ^ k.2))
      (Real.exp (r * (z - 1)) * Real.exp (s * (w - 1))) := by
  have h1 := hasSum_cell_pgf r z
  have h2 := hasSum_cell_pgf s w
  exact h1.mul h2 (summable_mul_of_summable_norm h1.summable.norm h2.summable.norm)

lemma hasSum_product (r s : ℝ) :
    HasSum (fun k : ℕ × ℕ => cell r k.1 * cell s k.2) 1 := by
  simpa using hasSum_product_pgf r s 1 1

def mass (a b : ℝ) (μ : Measure (ℝ × ℝ)) (k : ℕ × ℕ) : ℝ :=
  ∫ x, cell (a * x.1) k.1 * cell (b * x.2) k.2 ∂μ

lemma mass_pgf_hasSum (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ]
    (hμ : FiniteSiteObservation.NonnegativeTimes μ)
    {a b z w : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hz : z ∈ Icc (0 : ℝ) 1) (hw : w ∈ Icc (0 : ℝ) 1) :
    HasSum (fun k : ℕ × ℕ => mass a b μ k * (z ^ k.1 * w ^ k.2))
      (∫ x, Real.exp (-(a * (1-z)) * x.1) *
        Real.exp (-(b * (1-w)) * x.2) ∂μ) := by
  let F : (ℕ × ℕ) → (ℝ × ℝ) → ℝ := fun k x =>
    (cell (a * x.1) k.1 * z ^ k.1) * (cell (b * x.2) k.2 * w ^ k.2)
  let D : (ℕ × ℕ) → (ℝ × ℝ) → ℝ := fun k x =>
    cell (a * x.1) k.1 * cell (b * x.2) k.2
  have hmeas : ∀ k, AEStronglyMeasurable (F k) μ := by
    intro k
    dsimp [F, cell]
    fun_prop
  have hbound : ∀ k, ∀ᵐ x ∂μ, ‖F k x‖ ≤ D k x := by
    intro k
    filter_upwards [hμ] with x hx
    have h1 := cell_nonneg (mul_nonneg ha hx.1) k.1
    have h2 := cell_nonneg (mul_nonneg hb hx.2) k.2
    have hz0 := pow_nonneg hz.1 k.1
    have hw0 := pow_nonneg hw.1 k.2
    have hz1 : z ^ k.1 ≤ 1 := pow_le_one₀ hz.1 hz.2
    have hw1 : w ^ k.2 ≤ 1 := pow_le_one₀ hw.1 hw.2
    dsimp [F, D]
    rw [abs_of_nonneg (by positivity)]
    exact mul_le_mul (mul_le_of_le_one_right h1 hz1)
      (mul_le_of_le_one_right h2 hw1) (mul_nonneg h2 hw0) h1
  have hsum : ∀ᵐ x ∂μ, Summable (fun k => D k x) :=
    Filter.Eventually.of_forall (fun x => (hasSum_product (a * x.1) (b * x.2)).summable)
  have hint : Integrable (fun x => ∑' k, D k x) μ := by
    have heq : (fun x => ∑' k, D k x) = fun _ : ℝ × ℝ => (1 : ℝ) := by
      funext x
      exact (hasSum_product (a * x.1) (b * x.2)).tsum_eq
    rw [heq]
    exact integrable_const _
  have hlim : ∀ᵐ x ∂μ, HasSum (fun k => F k x)
      (Real.exp (-(a * (1-z)) * x.1) * Real.exp (-(b * (1-w)) * x.2)) := by
    apply Filter.Eventually.of_forall
    intro x
    convert! hasSum_product_pgf (a * x.1) (b * x.2) z w using 1
    congr 2 <;> ring
  have h := hasSum_integral_of_dominated_convergence D hmeas hbound hsum hint hlim
  convert! h using 1
  ext k
  dsimp [mass, F]
  rw [← integral_mul_const]
  congr 1
  funext x
  ring

theorem mass_injective
    (μ ν : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : FiniteSiteObservation.NonnegativeTimes μ)
    (hν : FiniteSiteObservation.NonnegativeTimes ν)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hmass : ∀ k : ℕ × ℕ, mass a b μ k = mass a b ν k) : μ = ν := by
  apply nonnegative_bivariate_laplace_unique_of_rectangle μ ν hμ hν ha hb
  intro s hs t ht
  let z : ℝ := 1 - s / a
  let w : ℝ := 1 - t / b
  have hz : z ∈ Icc (0 : ℝ) 1 := by
    dsimp [z]
    constructor
    · exact sub_nonneg.mpr ((div_le_one ha).mpr hs.2)
    · linarith [div_nonneg hs.1 ha.le]
  have hw : w ∈ Icc (0 : ℝ) 1 := by
    dsimp [w]
    constructor
    · exact sub_nonneg.mpr ((div_le_one hb).mpr ht.2)
    · linarith [div_nonneg ht.1 hb.le]
  have h1 := mass_pgf_hasSum μ hμ ha.le hb.le hz hw
  have h2 := mass_pgf_hasSum ν hν ha.le hb.le hz hw
  have hseries : (fun k : ℕ × ℕ => mass a b μ k * (z ^ k.1 * w ^ k.2)) =
      (fun k : ℕ × ℕ => mass a b ν k * (z ^ k.1 * w ^ k.2)) := by
    funext k
    rw [hmass k]
  rw [hseries] at h1
  have h := h1.unique h2
  have haz : a * (1-z) = s := by dsimp [z]; field_simp; ring
  have hbw : b * (1-w) = t := by dsimp [w]; field_simp; ring
  simpa only [haz, hbw] using h

end MixedPoisson
end Rhone.Statistics.Identifiability
