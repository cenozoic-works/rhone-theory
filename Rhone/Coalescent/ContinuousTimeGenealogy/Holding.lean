/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.ContinuousTimeGenealogy.Traj

/-! # The holding time at a visited state is `Exp(rateTot)`, and its two moments -/

@[expose] public section

namespace Rhone.Coalescent.ContinuousTimeGenealogy

open Finset TwoLocusGenealogy TypedAncestralChain BranchLengthMoments
open SecondMoments
open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {n KA KB : ℕ} {θA θB ρ : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ}

theorem lintegral_clocks_holdTime {f : ℝ → ℝ≥0∞} (hf : Measurable f)
    (ω : (_ : ℕ) → TS n KA KB) (k : ℕ) (hpos : 0 < rateTotS θA θB ρ (ω k)) :
    (∫⁻ e, f (holdTime θA θB ρ (ω, e) k) ∂clocks)
      = ∫⁻ t, f t ∂(expMeasure (rateTotS θA θB ρ (ω k))) := by
  have hcongr : ∀ e : (_ : ℕ) → ℝ,
      f (holdTime θA θB ρ (ω, e) k) = f (e k / rateTotS θA θB ρ (ω k)) := fun _ => rfl
  rw [lintegral_congr hcongr, lintegral_expMeasure_of_map hpos hf,
    lintegral_clocks_eval (g := fun x : ℝ => f (x / rateTotS θA θB ρ (ω k))) (by fun_prop) k]

theorem lintegral_holdTime (ω : (_ : ℕ) → TS n KA KB) (k : ℕ)
    (hpos : 0 < rateTotS θA θB ρ (ω k)) :
    (∫⁻ e, ENNReal.ofReal (holdTime θA θB ρ (ω, e) k) ∂clocks)
      = ENNReal.ofReal (rateTotS θA θB ρ (ω k))⁻¹ := by
  rw [lintegral_clocks_holdTime (f := fun x : ℝ => ENNReal.ofReal x) (by fun_prop) ω k hpos,
    lintegral_id_expMeasure hpos]

theorem lintegral_holdTime_sq (ω : (_ : ℕ) → TS n KA KB) (k : ℕ)
    (hpos : 0 < rateTotS θA θB ρ (ω k)) :
    (∫⁻ e, ENNReal.ofReal (holdTime θA θB ρ (ω, e) k)
        * ENNReal.ofReal (holdTime θA θB ρ (ω, e) k) ∂clocks)
      = 2 * ((∫⁻ e, ENNReal.ofReal (holdTime θA θB ρ (ω, e) k) ∂clocks)
        * ∫⁻ e, ENNReal.ofReal (holdTime θA θB ρ (ω, e) k) ∂clocks) := by
  rw [lintegral_clocks_holdTime
      (f := fun x : ℝ => ENNReal.ofReal x * ENNReal.ofReal x) (by fun_prop) ω k hpos,
    lintegral_clocks_holdTime (f := fun x : ℝ => ENNReal.ofReal x) (by fun_prop) ω k hpos,
    lintegral_sq_expMeasure_eq_two_mul_sq hpos]

theorem lintegral_holdTime_sq_eq (ω : (_ : ℕ) → TS n KA KB) (k : ℕ)
    (hpos : 0 < rateTotS θA θB ρ (ω k)) :
    (∫⁻ e, ENNReal.ofReal (holdTime θA θB ρ (ω, e) k)
        * ENNReal.ofReal (holdTime θA θB ρ (ω, e) k) ∂clocks)
      = 2 * ENNReal.ofReal (rateTotS θA θB ρ (ω k))⁻¹
        * ENNReal.ofReal (rateTotS θA θB ρ (ω k))⁻¹ := by
  rw [lintegral_clocks_holdTime
      (f := fun x : ℝ => ENNReal.ofReal x * ENNReal.ofReal x) (by fun_prop) ω k hpos,
    lintegral_sq_expMeasure hpos]

end Rhone.Coalescent.ContinuousTimeGenealogy
