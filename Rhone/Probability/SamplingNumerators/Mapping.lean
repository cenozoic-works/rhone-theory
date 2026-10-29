/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.SamplingNumerators.Numerator
public import Rhone.Probability.DiagonalChain.Cleared

/-! # Naturality of the explicit polynomial numerators -/

@[expose] public section

namespace Rhone.Probability.SamplingNumerators
open Matrix

section Maps
variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)

@[simp] theorem U_map (i j : ℕ) (a b r : R) (t s : Fin (min i j + 1)) :
    f (Analysis.DenominatorEquation.U R i j a b r t s) = Analysis.DenominatorEquation.U S i j (f a)
        (f b) (f r) t s := by
  rw [Analysis.DenominatorEquation.U_apply, Analysis.DenominatorEquation.U_apply,
      DiagonalChain.usmaniEntry_map]
  congr 1 <;> funext k <;>
    simp [LinearAlgebra.Tridiag.dcoef, LinearAlgebra.Tridiag.bcoef, LinearAlgebra.Tridiag.ccoef,
        map_ofNat]

@[simp] theorem c22_map (a b : R) : f (c22 a b) = c22 (f a) (f b) := by
  simp [c22]
@[simp] theorem d22_map (a b r : R) : f (d22 a b r) = d22 (f a) (f b) (f r) := by
  simp [d22, LinearAlgebra.Tridiag.E_map]
@[simp] theorem s22_map (a b : R) (t : Fin 3) :
    f (s22 a b t) = s22 (f a) (f b) t := by
  fin_cases t <;> simp [s22, map_ofNat]
@[simp] theorem n22_map (a b r : R) (t : Fin 3) :
    f (n22 a b r t) = n22 (f a) (f b) (f r) t := by
  unfold n22
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, U_map, s22_map]

@[simp] theorem c23_map (a b r : R) : f (c23 a b r) = c23 (f a) (f b) (f r) := by
  simp [c23, LinearAlgebra.Tridiag.E_map, map_ofNat]
@[simp] theorem d23_map (a b r : R) : f (d23 a b r) = d23 (f a) (f b) (f r) := by
  simp [d23, LinearAlgebra.Tridiag.E_map]
@[simp] theorem s23_map (a b r : R) (t : Fin 3) :
    f (s23 a b r t) = s23 (f a) (f b) (f r) t := by
  fin_cases t <;> simp [s23, LinearAlgebra.Tridiag.E_map, map_ofNat]
@[simp] theorem n23_map (a b r : R) (t : Fin 3) :
    f (n23 a b r t) = n23 (f a) (f b) (f r) t := by
  unfold n23
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, U_map, s23_map]

@[simp] theorem c32_map (a b r : R) : f (c32 a b r) = c32 (f a) (f b) (f r) := by
  simp [c32, LinearAlgebra.Tridiag.E_map, map_ofNat]
@[simp] theorem d32_map (a b r : R) : f (d32 a b r) = d32 (f a) (f b) (f r) := by
  simp [d32, LinearAlgebra.Tridiag.E_map]
@[simp] theorem s32_map (a b r : R) (t : Fin 3) :
    f (s32 a b r t) = s32 (f a) (f b) (f r) t := by
  fin_cases t <;> simp [s32, LinearAlgebra.Tridiag.E_map, map_ofNat]
@[simp] theorem n32_map (a b r : R) (t : Fin 3) :
    f (n32 a b r t) = n32 (f a) (f b) (f r) t := by
  unfold n32
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, U_map, s32_map]

@[simp] theorem c33_map (a b r : R) : f (c33 a b r) = c33 (f a) (f b) (f r) := by
  simp [c33, LinearAlgebra.Tridiag.E_map, map_ofNat]
@[simp] theorem d33_map (a b r : R) : f (d33 a b r) = d33 (f a) (f b) (f r) := by
  simp [d33, LinearAlgebra.Tridiag.E_map]
@[simp] theorem s33_map (a b r : R) (t : Fin 4) :
    f (s33 a b r t) = s33 (f a) (f b) (f r) t := by
  fin_cases t <;> simp [s33, LinearAlgebra.Tridiag.E_map, map_ofNat]
@[simp] theorem n33_map (a b r : R) (t : Fin 4) :
    f (n33 a b r t) = n33 (f a) (f b) (f r) t := by
  unfold n33
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, U_map, s33_map]

end Maps

section AlgebraMaps
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra ℚ R] [Algebra ℚ S]
  (f : R →+* S) (hf : ∀ q : ℚ, f (algebraMap ℚ R q) = algebraMap ℚ S q)

include hf

theorem lowerNumerator_map (a b r : R) :
    f (lowerNumerator a b r) = lowerNumerator (f a) (f b) (f r) := by
  simp only [lowerNumerator, map_add, map_mul, hf, map_ofNat, map_one,
    c33_map, LinearAlgebra.Tridiag.E_map, n22_map, n23_map, n32_map]

theorem samplingNumerator_map (a b r : R) :
    f (samplingNumerator a b r) = samplingNumerator (f a) (f b) (f r) := by
  simp only [samplingNumerator, map_add, map_mul, hf,
    n33_map, LinearAlgebra.Tridiag.E_map, lowerNumerator_map f hf]

end AlgebraMaps
end Rhone.Probability.SamplingNumerators
