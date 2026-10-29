/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.RecombinationDegree.ChainSurvival
public import Rhone.Algebra.SamplingUniform.NestedLocalization

/-! # Convert spectral coefficients to the standard total-mutation coordinate -/

@[expose] public section

namespace Rhone.Probability.RecombinationDegree

open Polynomial Algebra.DiagonalObstruction Analysis.DiagonalObstruction DiagonalObstruction
    Algebra.SamplingUniform

noncomputable def mutationCoefficientEquiv (m : ℕ) (hm : m ≠ 0) :
    RatFunc ℚ ≃ₐ[ℚ] RatFunc ℚ :=
  IsFractionRing.algEquivOfAlgEquiv (spectralVariableEquiv ℚ m hm)

@[simp] theorem mutationCoefficientEquiv_C (m : ℕ) (hm : m ≠ 0) (c : ℚ) :
    mutationCoefficientEquiv m hm (RatFunc.C c) = RatFunc.C c := by
  exact DFunLike.congr_fun (Subsingleton.elim
    ((mutationCoefficientEquiv m hm).toRingHom.comp RatFunc.C) RatFunc.C) c

@[simp] theorem mutationCoefficientEquiv_X (m : ℕ) (hm : m ≠ 0) :
    mutationCoefficientEquiv m hm RatFunc.X = -(m : RatFunc ℚ) * RatFunc.X := by
  change IsFractionRing.algEquivOfAlgEquiv (spectralVariableEquiv ℚ m hm)
    (algebraMap (Polynomial ℚ) (RatFunc ℚ) Polynomial.X) = _
  rw [IsFractionRing.algEquivOfAlgEquiv_algebraMap, spectralVariableEquiv_apply]
  simp

noncomputable def spectralToMutation (m : ℕ) (hm : m ≠ 0) :
    Polynomial (Polynomial ℚ) →+* Polynomial (RatFunc ℚ) :=
  (Polynomial.mapRingHom (mutationCoefficientEquiv m hm).toRingHom).comp swapLocal

@[simp] theorem spectralToMutation_C_C (m : ℕ) (hm : m ≠ 0) (c : ℚ) :
    spectralToMutation m hm (C (C c)) = C (RatFunc.C c) := by
  simp [spectralToMutation]

@[simp] theorem spectralToMutation_C_X (m : ℕ) (hm : m ≠ 0) :
    spectralToMutation m hm (C X) = X := by
  simp [spectralToMutation]

@[simp] theorem spectralToMutation_X (m : ℕ) (hm : m ≠ 0) :
    spectralToMutation m hm X = C (-(m : RatFunc ℚ) * RatFunc.X) := by
  simp [spectralToMutation]

theorem spectralToMutation_chain {m : ℕ} (hm : m ≠ 0) :
    spectralToMutation m hm (spectralChainNumerator m) =
      Rhone.Probability.DiagonalChain.W m (C (RatFunc.X : RatFunc ℚ)) X := by
  unfold spectralChainNumerator
  rw [Rhone.Probability.DiagonalChain.W_map, map_mul, spectralToMutation_C_C,
    spectralToMutation_X, spectralToMutation_C_X]
  congr 1
  rw [← Polynomial.C_mul]
  congr 1
  have hn : (m : RatFunc ℚ) ≠ 0 := by exact_mod_cast hm
  simp only [map_div₀, map_neg, map_one, map_natCast]
  field_simp

attribute [local instance] Polynomial.algebra

theorem spectralToMutation_integer (m : ℕ) (hm : m ≠ 0)
    (F : Polynomial (Polynomial ℤ)) :
    spectralToMutation m hm (F.map (algebraMap (Polynomial ℤ) (Polynomial ℚ))) =
      F.eval₂ (Polynomial.mapRingHom (Int.castRingHom (RatFunc ℚ)))
        (-C (RatFunc.X : RatFunc ℚ) * m) := by
  have h : (spectralToMutation m hm).comp
      (Polynomial.mapRingHom (algebraMap (Polynomial ℤ) (Polynomial ℚ))) =
      Polynomial.eval₂RingHom (Polynomial.mapRingHom (Int.castRingHom (RatFunc ℚ)))
        (-C (RatFunc.X : RatFunc ℚ) * m) := by
    ext <;> simp [mul_comm, ite_mul]
  exact DFunLike.congr_fun h F

theorem spectralToMutation_denominator {m : ℕ} (hm : 2 ≤ m) :
    spectralToMutation m (by omega)
      ((spectralPolynomial m).map (algebraMap (Polynomial ℤ) (Polynomial ℚ))) =
      (-1) ^ (m + 1) *
        Rhone.LinearAlgebra.Tridiag.E (Polynomial (RatFunc ℚ)) m m (C RatFunc.X) 0 X := by
  rw [spectralToMutation_integer, spectralPolynomial_eval₂_eq_E (by omega)]
  simp

theorem unbounded_surviving_recombination_factor (D : ℕ) :
    ∃ m : ℕ, 2 ≤ m ∧ ∃ G : Polynomial (RatFunc ℚ), Irreducible G ∧
      G ∣ Rhone.LinearAlgebra.Tridiag.E (Polynomial (RatFunc ℚ)) m m (C RatFunc.X) 0 X ∧
      ¬ G ∣ Rhone.Probability.DiagonalChain.W m (C RatFunc.X) X ∧ D < G.natDegree := by
  obtain ⟨m, hm, F, hirr, hdiv, hn, hdeg⟩ :=
    unbounded_surviving_recombination_chain_factor D
  let e := Polynomial.mapEquiv (mutationCoefficientEquiv m (by omega)).toRingEquiv
  have heirr : Irreducible (e (recombinationFactor F)) :=
    (MulEquiv.irreducible_iff e).mpr hirr
  refine ⟨m, hm, e (recombinationFactor F), heirr, ?_, ?_, ?_⟩
  · have hd := map_dvd e.toRingHom hdiv
    change e (recombinationFactor F) ∣ spectralToMutation m (by omega)
      ((spectralPolynomial m).map (algebraMap (Polynomial ℤ) (Polynomial ℚ))) at hd
    rw [spectralToMutation_denominator hm] at hd
    exact (heirr.prime.dvd_mul.mp hd).resolve_left (fun h =>
      heirr.not_isUnit (isUnit_of_dvd_unit h (isUnit_neg_one.pow _)))
  · intro h
    apply hn
    apply (map_dvd_iff e).mp
    change e (recombinationFactor F) ∣ spectralToMutation m (by omega)
      (spectralChainNumerator m)
    rwa [spectralToMutation_chain]
  · change D < (Polynomial.map (mutationCoefficientEquiv m (by omega)).toRingHom
      (recombinationFactor F)).natDegree
    rw [Polynomial.natDegree_map_eq_of_injective
      (f := (mutationCoefficientEquiv m (by omega)).toRingHom)
      (mutationCoefficientEquiv m (by omega)).injective]
    exact hdeg

end Rhone.Probability.RecombinationDegree
