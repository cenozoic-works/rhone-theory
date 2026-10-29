/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.DiagonalObstruction.SpectralPolynomial
public import Rhone.Algebra.DiagonalObstruction.CollisionSeries
public import Rhone.Algebra.DiagonalObstruction.CollisionLocal
public import Rhone.Algebra.DiagonalObstruction.CollisionFactor
public import Rhone.Algebra.DiagonalObstruction.PrimeOrbit
public import Rhone.Analysis.Rescale.Rescale

/-! # Transport of the integer spectral polynomial to power series, collision-closed -/

@[expose] public section

namespace Rhone.Analysis.DiagonalObstruction

open Polynomial LinearAlgebra.Tridiag

noncomputable def integerToSeries (R : Type*) [CommRing R] : ℤ[X] →+* PowerSeries R :=
  Polynomial.eval₂RingHom (Int.castRingHom (PowerSeries R)) PowerSeries.X

@[simp] theorem integerToSeries_X (R : Type*) [CommRing R] :
    integerToSeries R X = PowerSeries.X := by
  simp [integerToSeries]

@[simp] theorem integerToSeries_C (R : Type*) [CommRing R] (a : ℤ) :
    integerToSeries R (C a) = PowerSeries.C (a : R) := by
  simp [integerToSeries]

theorem constantCoeff_integerToSeries (R : Type*) [CommRing R] :
    (PowerSeries.constantCoeff (R := R)).comp (integerToSeries R) =
      (Int.castRingHom R).comp (evalRingHom (0 : ℤ)) := by
  ext <;> simp [RingHom.comp_apply, integerToSeries]

theorem map_constantCoeff_integerToSeries (R : Type*) [CommRing R]
    (F : Polynomial (Polynomial ℤ)) :
    (F.map (integerToSeries R)).map PowerSeries.constantCoeff =
      (F.map (evalRingHom (0 : ℤ))).map (Int.castRingHom R) := by
  rw [map_map, map_map, constantCoeff_integerToSeries]

theorem constantCoeff_eval_integerToSeries (R : Type*) [CommRing R]
    (F : Polynomial (Polynomial ℤ)) (a : ℤ) :
    PowerSeries.constantCoeff
        ((F.map (integerToSeries R)).eval (PowerSeries.C (a : R))) =
      (((F.map (evalRingHom (0 : ℤ))).eval a : ℤ) : R) := by
  rw [← eval₂_at_apply, PowerSeries.constantCoeff_C, eval₂_eq_eval_map,
    map_constantCoeff_integerToSeries]
  exact eval_map_apply (Int.castRingHom R) _

theorem constantCoeff_derivative_eval_integerToSeries (R : Type*) [CommRing R]
    (F : Polynomial (Polynomial ℤ)) (a : ℤ) :
    PowerSeries.constantCoeff
        ((F.map (integerToSeries R)).derivative.eval (PowerSeries.C (a : R))) =
      (((F.map (evalRingHom (0 : ℤ))).derivative.eval a : ℤ) : R) := by
  rw [derivative_map, constantCoeff_eval_integerToSeries, derivative_map]

theorem mapped_spectralPolynomial_eval (R : Type*) [CommRing R] (m : ℕ)
    (z : PowerSeries R) :
    ((Algebra.DiagonalObstruction.spectralPolynomial m).map (integerToSeries R)).eval z =
      cont (Algebra.DiagonalObstruction.spectralSeriesDiagonal
          (fun t => (Algebra.DiagonalObstruction.coalDiag m t : R)) (fun t => -(t : R)) z)
        (fun t => PowerSeries.C (2 * ((m : R) - t) ^ 2))
        (fun t => PowerSeries.X * PowerSeries.C ((t : R) + 1)) (m + 1) := by
  rw [Algebra.DiagonalObstruction.spectralPolynomial, ← Matrix.charpoly_map,
      Algebra.DiagonalObstruction.spectralMatrix_map, integerToSeries_X,
    Algebra.DiagonalObstruction.spectralMatrix, Algebra.DiagonalObstruction.charpoly_trid]
  change (evalRingHom z) (cont _ _ _ _) = _
  rw [Rhone.Analysis.Rescale.cont_map]
  congr 1 <;> funext t <;> simp [Algebra.DiagonalObstruction.spectralSeriesDiagonal, map_ofNat]
  ring

theorem factorLabels_collisionClosed {m : ℕ} (hm : 2 ≤ m)
    (F : Polynomial (Polynomial ℤ)) (hF : F.Monic)
        (hdiv : F ∣ Algebra.DiagonalObstruction.spectralPolynomial m) :
    Algebra.DiagonalObstruction.CollisionClosed m (Algebra.DiagonalObstruction.factorLabels m F) :=
        by
  intro p hp hmp i hi him j hj hcollision
  let : Fact p.Prime := ⟨hp⟩
  by_contra hjnot
  have hij : i ≠ j := by
    intro h
    exact hjnot (h ▸ hi)
  have heq : (Algebra.DiagonalObstruction.coalDiag m i : ZMod p) =
      (Algebra.DiagonalObstruction.coalDiag m j : ZMod p) := by
    apply sub_eq_zero.mp
    rw [← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hcollision
  let R := Algebra.DiagonalObstruction.PrimeIntegerLocal p
  let q : Polynomial (PowerSeries R) := F.map (integerToSeries R)
  have hroot : PowerSeries.constantCoeff
      (q.eval (PowerSeries.C (Algebra.DiagonalObstruction.coalDiag m i : R))) = 0 := by
    dsimp only [q]
    rw [constantCoeff_eval_integerToSeries,
        ((Algebra.DiagonalObstruction.mem_factorLabels m i F).mp hi).2]
    simp
  have hderiv : IsUnit (PowerSeries.constantCoeff
      (q.derivative.eval (PowerSeries.C (Algebra.DiagonalObstruction.coalDiag m i : R)))) := by
    dsimp only [q]
    rw [constantCoeff_derivative_eval_integerToSeries,
      Algebra.DiagonalObstruction.factor_zero_fiber_derivative (by omega) F hF hdiv hi]
    simp only [Int.cast_prod]
    apply IsUnit.prod_iff.mpr
    intro t ht
    have hts := (Finset.mem_erase.mp ht).2
    have hti := (Finset.mem_erase.mp ht).1
    have htj : t ≠ j := by
      intro h
      exact hjnot (h ▸ hts)
    exact Algebra.DiagonalObstruction.coalDiag_outside_gap_isUnit hmp him hj
        ((Algebra.DiagonalObstruction.mem_factorLabels m t F).mp hts).1
      hij hti htj heq
  obtain ⟨z, hz, hz0⟩ :=
      Algebra.DiagonalObstruction.exists_powerSeries_root_of_simple_constant_fiber q
    (hF.map _) (Algebra.DiagonalObstruction.coalDiag m i : R) hroot hderiv
  have hzfull := hz.dvd (Polynomial.map_dvd (integerToSeries R) hdiv)
  rw [Polynomial.IsRoot, mapped_spectralPolynomial_eval] at hzfull
  exact Algebra.DiagonalObstruction.no_integral_coal_collision_branch hm hmp him hj hij heq z hz0
      hzfull

theorem unbounded_distinguished_factor_degree (D : ℕ) :
    ∃ m : ℕ, 2 ≤ m ∧ ∀ F : Polynomial (Polynomial ℤ), F.Monic →
      F ∣ Algebra.DiagonalObstruction.spectralPolynomial m → 0 ∈
          Algebra.DiagonalObstruction.factorLabels m F → D < F.natDegree := by
  obtain ⟨m, hm, hcomponent⟩ := Algebra.DiagonalObstruction.unbounded_collision_component D
  refine ⟨m, hm, ?_⟩
  intro F hF hdiv hzero
  have hcard := hcomponent (Algebra.DiagonalObstruction.factorLabels m F) hzero
      (factorLabels_collisionClosed hm F hF hdiv)
  rwa [Algebra.DiagonalObstruction.factorLabels_card (by omega) F hF hdiv] at hcard

end Rhone.Analysis.DiagonalObstruction
