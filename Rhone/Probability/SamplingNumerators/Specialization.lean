/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.SamplingNumerators.Mapping
public import Rhone.Probability.SamplingNumerators.Assembly

/-! # A concrete mutation slice of the sampling probability at `(3,3)` -/

@[expose] public section

namespace Rhone.Probability.SamplingNumerators
open Polynomial

abbrev SamplingBivariate := Polynomial (Polynomial ℚ)

noncomputable def numeratorP : SamplingBivariate := samplingNumerator 1 (X - 1) (C X)
noncomputable def denominatorP : SamplingBivariate := d33 1 (X - 1) (C X)

noncomputable def paramEval {F : Type*} [CommRing F] [Algebra ℚ F] (θ ρ : F) :
    SamplingBivariate →ₐ[ℚ] F :=
  Polynomial.aevalTower (Polynomial.aeval ρ) θ

@[simp] theorem paramEval_X {F : Type*} [CommRing F] [Algebra ℚ F] (θ ρ : F) :
    paramEval θ ρ X = θ := by simp [paramEval, Polynomial.aevalTower]
@[simp] theorem paramEval_C_X {F : Type*} [CommRing F] [Algebra ℚ F] (θ ρ : F) :
    paramEval θ ρ (C X) = ρ := by simp [paramEval, Polynomial.aevalTower]

@[simp] theorem paramEval_numeratorP {F : Type*} [CommRing F] [Algebra ℚ F] (θ ρ : F) :
    paramEval θ ρ numeratorP = samplingNumerator 1 (θ - 1) ρ := by
  change (paramEval θ ρ).toRingHom (samplingNumerator 1 (X - 1) (C X)) = _
  rw [samplingNumerator_map _ (paramEval θ ρ).commutes]
  simp

@[simp] theorem paramEval_denominatorP {F : Type*} [CommRing F] [Algebra ℚ F] (θ ρ : F) :
    paramEval θ ρ denominatorP = d33 1 (θ - 1) ρ := by
  change (paramEval θ ρ).toRingHom (d33 1 (X - 1) (C X)) = _
  rw [d33_map]
  simp

theorem sampling33_on_slice
    {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    {θ ρ : F} {q : LinearAlgebra.Recursion.Config 2 2 → F}
    (hθ : 1 < θ) (hρ : 0 ≤ ρ)
    (hq : LinearAlgebra.Recursion.IsSolution 1 (θ - 1) ρ piThird piThird q) :
    q sampling33 = paramEval θ ρ numeratorP / paramEval θ ρ denominatorP := by
  rw [paramEval_numeratorP, paramEval_denominatorP]
  exact sampling33_eq_quotient (by norm_num) (by linarith) hρ hq

theorem denominatorP_ne_zero : denominatorP ≠ 0 := by
  intro h
  have hp : (0 : ℚ) < paramEval (2 : ℚ) 0 denominatorP := by
    rw [paramEval_denominatorP]
    norm_num only [show (2 : ℚ) - 1 = 1 by norm_num]
    exact d33_pos (by norm_num) (by norm_num) (by norm_num)
  rw [h, map_zero] at hp
  exact (lt_irrefl (0 : ℚ)) hp

end Rhone.Probability.SamplingNumerators
