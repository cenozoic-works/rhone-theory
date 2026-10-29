/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ErlangPhase.Transform
public import Rhone.Statistics.ErlangPhase.DensityFactor
public import Rhone.Statistics.FoldedCounts.DurationSwap

/-! # Ordered duration product and its Laplace transform in the Erlang-phase model -/

@[expose] public section

noncomputable section
open Matrix MeasureTheory Set Filter
open scoped Matrix Topology ENNReal
namespace Rhone.Statistics.ErlangPhase
open MarkovChain.Identifiability Identifiability FinitePhase
variable {J N : ℕ}
set_option backward.isDefEq.respectTransparency false

lemma ordered_product (r w : Fin J → ℝ) (b : ℝ) (hN : 0 < N)
    (hr : ∀ j, 0 < r j) (hw : ∀ j, 0 < w j) (hsum : ∑ j, w j = 1) (hb : 0 < b) :
    ((WeightedExit.law (generator (N := N) r) (weights w)).prod
      (FoldedCounts.exponential b)).map PanThreeSample.toOrdered =
      (model r w b hN hr hw hsum hb).law := by
  change ((WeightedExit.law (generator (N := N) r) (weights w)).prod
    (FoldedCounts.exponential b)).map upperShear = _
  rw [WeightedExit.law, FoldedCounts.exponential, shear_product_density _ _
    (WeightedExit.density_continuous _ _).measurable.ennreal_ofReal (by fun_prop)]
  change _ = triangularDensityLaw
    (FinitePhase.density (generator (N := N) r) (flux r) (post b) (weights w))
  unfold triangularDensityLaw
  congr 1
  funext p
  rcases p with ⟨u, v⟩
  rw [← ENNReal.ofReal_mul' (mul_nonneg hb.le (Real.exp_pos _).le)]
  exact congrArg ENNReal.ofReal (density_factor r w b u v).symm

lemma model_duration_product (r w : Fin J → ℝ) (b : ℝ) (hN : 0 < N)
    (hr : ∀ j, 0 < r j) (hw : ∀ j, 0 < w j) (hsum : ∑ j, w j = 1) (hb : 0 < b) :
    (model r w b hN hr hw hsum hb).durationLaw =
      (WeightedExit.law (generator (N := N) r) (weights w)).prod
        (FoldedCounts.exponential b) := by
  rw [Model.durationLaw, ← ordered_product r w b hN hr hw hsum hb,
    Measure.map_map PanThreeSample.measurable_toDurations PanThreeSample.measurable_toOrdered]
  have he : PanThreeSample.toDurations ∘ PanThreeSample.toOrdered = id := by
    funext p
    simp [PanThreeSample.toDurations, PanThreeSample.toOrdered]
  rw [he, Measure.map_id]

lemma exponential_laplace (b t : ℝ) (hb : 0 < b) (ht : 0 ≤ t) :
    (∫ x, Real.exp (-t * x) ∂FoldedCounts.exponential b) = b / (b + t) := by
  rw [FoldedCounts.exponential, integral_withDensity_eq_integral_toReal_smul₀
    (by fun_prop) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  have he : (fun x : ℝ => (ENNReal.ofReal (b * Real.exp (-b * x))).toReal •
      Real.exp (-t * x)) = fun x => b * Real.exp (-(b + t) * x) := by
    funext x
    rw [ENNReal.toReal_ofReal (mul_nonneg hb.le (Real.exp_pos _).le), smul_eq_mul,
      mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [he, integral_const_mul, integral_exp_mul_Ioi (by linarith : -(b + t) < 0)]
  simp only [mul_zero, Real.exp_zero, neg_div_neg_eq, mul_one_div]

lemma model_duration_laplace (r w : Fin J → ℝ) (b : ℝ) (hN : 0 < N)
    (hr : ∀ j, 0 < r j) (hw : ∀ j, 0 < w j) (hsum : ∑ j, w j = 1) (hb : 0 < b)
    (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (∫ p, Real.exp (-s * p.1 - t * p.2)
      ∂(model r w b hN hr hw hsum hb).durationLaw) =
      (∑ j, w j * (r j / (r j + s)) ^ N) * (b / (b + t)) := by
  let M := model r w b hN hr hw hsum hb
  let := model_probability r w b hN hr hw hsum hb
  let : IsProbabilityMeasure (WeightedExit.law (generator (N := N) r) (weights w)) := by
    change IsProbabilityMeasure (WeightedExit.law M.A M.α)
    rw [← M.first_marginal]
    exact inferInstance
  let := FoldedCounts.exponential_probability hb
  rw [model_duration_product r w b hN hr hw hsum hb]
  have he : (fun p : ℝ × ℝ => Real.exp (-s * p.1 - t * p.2)) =
      fun p => Real.exp (-s * p.1) * Real.exp (-t * p.2) := by
    funext p
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he, integral_prod_mul (fun x : ℝ => Real.exp (-s * x))
    (fun x : ℝ => Real.exp (-t * x)),
    mixture_law_laplace r w hr (fun j => (hw j).le) hN s hs,
    exponential_laplace b t hb ht]

end Rhone.Statistics.ErlangPhase
