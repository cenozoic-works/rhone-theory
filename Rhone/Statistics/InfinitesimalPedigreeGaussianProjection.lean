/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Statistics.InfinitesimalPedigreeProjectedMoments
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
/-!
# Finite product-Gaussian scalar projections

Source: barton_etheridge_veber2017, sec. 3.1, Thm A.2. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Rhone.Statistics Rhone.Combinatorics
open scoped ENNReal
namespace Rhone.Statistics
theorem gaussian_product_projection_law {n : Nat} (s : Fin n → NNReal) (t : Fin n → Real) :
    HasLaw (fun z : Fin n → Real => ∑ i, t i * z i)
      (gaussianReal 0 (∑ i, (t i)^2 * (s i : Real)).toNNReal)
      (Measure.pi fun i : Fin n => gaussianReal 0 (s i)) := by
  let μ := fun i : Fin n => gaussianReal 0 (s i)
  have hc (i : Fin n) : HasGaussianLaw (fun z : Fin n → Real => z i) (Measure.pi μ) := by
    have h : HasLaw (fun z : Fin n → Real => z i) (μ i) (Measure.pi μ) :=
      ⟨(measurable_pi_apply i).aemeasurable, (measurePreserving_eval μ i).map_eq⟩
    exact h.hasGaussianLaw
  have hi : iIndepFun (fun i : Fin n => fun z : Fin n → Real => t i * z i) (Measure.pi μ) :=
    iIndepFun_pi (μ := μ) (X := fun i => fun x : Real => t i * x) (fun _ => by fun_prop)
  have hg : HasGaussianLaw (fun z : Fin n → Real => ∑ i, t i * z i) (Measure.pi μ) :=
    hi.hasGaussianLaw_fun_sum (fun i => (hc i).fun_smul (t i))
  have hm : (∫ z : Fin n → Real, ∑ i, t i * z i ∂Measure.pi μ) = 0 := by
    rw [integral_finsetSum _ (fun i _ =>
      ((hc i).memLp_two.const_mul (t i)).integrable (by norm_num))]
    simp_rw [integral_const_mul, integral_eval]
    simp [μ, integral_id_gaussianReal]
  have hv : Var[fun z : Fin n → Real => ∑ i, t i * z i; Measure.pi μ] =
      ∑ i, (t i)^2 * (s i : Real) := by
    have h := variance_sum_pi (μ := μ) (X := fun i => fun x : Real => t i * x)
      (fun i => (memLp_id_gaussianReal (μ := 0) (v := s i) 2).const_mul (t i))
    convert h using 1
    · congr 1
      funext z
      simp
    · apply Finset.sum_congr rfl
      intro i _
      change (t i)^2 * (s i : Real) = Var[fun x : Real => t i * id x; gaussianReal 0 (s i)]
      rw [variance_const_mul, variance_id_gaussianReal]
  exact ⟨hg.aemeasurable, by rw [hg.map_eq_gaussianReal, hm, hv]⟩
end Rhone.Statistics
