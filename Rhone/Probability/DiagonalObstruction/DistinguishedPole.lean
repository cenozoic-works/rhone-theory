/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.DiagonalObstruction.CollisionFactor
public import Rhone.Probability.DiagonalObstruction.MarkedPole
public import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-! # The distinguished spectral factor survives in the chain numerator -/

@[expose] public section

namespace Rhone.Probability.DiagonalObstruction

open Polynomial

attribute [local instance] Polynomial.algebra

noncomputable def spectralChainNumerator (m : ℕ) : Polynomial (Polynomial ℚ) :=
  DiagonalChain.W m (C (C (-1 / (m : ℚ))) * X) (C X)

theorem marked_spectral_coordinate {m : ℕ} (hm : 1 ≤ m) :
    (-1 / (m : ℚ)) * (Algebra.DiagonalObstruction.coalDiag m 0 : ℚ) =
        Algebra.DiagonalObstruction.markedPoint m := by
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  rw [Algebra.DiagonalObstruction.coalDiag_cast, Algebra.DiagonalObstruction.markedPoint]
  simp only [Nat.cast_zero, sub_zero]
  field_simp [hm0]

theorem spectralChainNumerator_marked {m : ℕ} (hm : 1 ≤ m) :
    ((spectralChainNumerator m).map (evalRingHom (0 : ℚ))).eval
      (Algebra.DiagonalObstruction.coalDiag m 0 : ℚ) = DiagonalChain.W m
          (Algebra.DiagonalObstruction.markedPoint m) 0 := by
  let φ : Polynomial (Polynomial ℚ) →+* ℚ :=
    (evalRingHom (Algebra.DiagonalObstruction.coalDiag m 0 : ℚ)).comp
        (mapRingHom (evalRingHom (0 : ℚ)))
  change φ (DiagonalChain.W m (C (C (-1 / (m : ℚ))) * X) (C X)) = _
  rw [DiagonalChain.W_map]
  have hθ : φ (C (C (-1 / (m : ℚ))) * X) = Algebra.DiagonalObstruction.markedPoint m := by
    simpa only [φ, RingHom.comp_apply, coe_mapRingHom, coe_evalRingHom,
      Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X] using marked_spectral_coordinate hm
  have hρ : φ (C X) = 0 := by simp [φ]
  rw [hθ, hρ]

theorem spectralChainNumerator_marked_ne_zero {m : ℕ} (hm : 2 ≤ m) :
    ((spectralChainNumerator m).map (evalRingHom (0 : ℚ))).eval
      (Algebra.DiagonalObstruction.coalDiag m 0 : ℚ) ≠ 0 := by
  rw [spectralChainNumerator_marked (by omega)]
  exact W_marked_ne_zero hm

theorem distinguishedFactor_marked_zero {m : ℕ} (F : Polynomial (Polynomial ℤ))
    (hzero : 0 ∈ Algebra.DiagonalObstruction.factorLabels m F) :
    ((F.map (algebraMap (Polynomial ℤ) (Polynomial ℚ))).map
      (evalRingHom (0 : ℚ))).eval (Algebra.DiagonalObstruction.coalDiag m 0 : ℚ) = 0 := by
  rw [Algebra.DiagonalObstruction.integer_factor_zero_fiber_map]
  change ((F.map (evalRingHom (0 : ℤ))).map (algebraMap ℤ ℚ)).eval
    ((algebraMap ℤ ℚ) (Algebra.DiagonalObstruction.coalDiag m 0)) = 0
  rw [Polynomial.eval_map_apply, ((Algebra.DiagonalObstruction.mem_factorLabels m 0 F).mp hzero).2,
      map_zero]

theorem distinguishedFactor_not_dvd_chain {m : ℕ} (hm : 2 ≤ m)
    (F : Polynomial (Polynomial ℤ)) (hzero : 0 ∈ Algebra.DiagonalObstruction.factorLabels m F) :
    ¬ F.map (algebraMap (Polynomial ℤ) (Polynomial ℚ)) ∣ spectralChainNumerator m := by
  intro hd
  have hz : ((F.map (algebraMap (Polynomial ℤ) (Polynomial ℚ))).map
      (evalRingHom (0 : ℚ))).IsRoot (Algebra.DiagonalObstruction.coalDiag m 0 : ℚ) :=
    distinguishedFactor_marked_zero F hzero
  exact spectralChainNumerator_marked_ne_zero hm
    (hz.dvd (Polynomial.map_dvd (evalRingHom (0 : ℚ)) hd))

theorem distinguishedFactor_not_dvd_chain_fraction {m : ℕ} (hm : 2 ≤ m)
    (F : Polynomial (Polynomial ℤ)) (hF : F.Monic)
        (hzero : 0 ∈ Algebra.DiagonalObstruction.factorLabels m F) :
    ¬ (F.map (algebraMap (Polynomial ℤ) (Polynomial ℚ))).map
        (algebraMap (Polynomial ℚ) (RatFunc ℚ)) ∣
      (spectralChainNumerator m).map (algebraMap (Polynomial ℚ) (RatFunc ℚ)) := by
  intro hd
  exact distinguishedFactor_not_dvd_chain hm F hzero
    ((hF.map _).isPrimitive.dvd_of_fraction_map_dvd_fraction_map hd)

end Rhone.Probability.DiagonalObstruction
