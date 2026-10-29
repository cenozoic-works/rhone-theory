/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.RecombinationDegree.SamplingPole

/-! # No formula of bounded recombination degree for the generic sampling recursion -/

@[expose] public section

namespace Rhone.Probability.RecombinationDegree

open Polynomial LinearAlgebra.Recursion LinearAlgebra.SlotDeletion SlotDeletion DiagonalChain
  Algebra.SamplingUniform SamplingUniform

abbrev RecombBase := RatFunc ℚ
abbrev RecombCoefficient := RatFunc (RatFunc (RatFunc RecombBase))
abbrev RecombPolynomial := Polynomial RecombCoefficient
abbrev RecombField := RatFunc RecombCoefficient

noncomputable def recombLambda : RecombCoefficient :=
  RatFunc.C (RatFunc.C (RatFunc.X : RatFunc RecombBase))
noncomputable def recombA : RecombField :=
  algebraMap RecombPolynomial RecombField (C recombLambda)
noncomputable def recombB : RecombField :=
  algebraMap RecombPolynomial RecombField
    (C (nestedConstant (RatFunc.X : RecombBase)) - C recombLambda)
noncomputable def recombRho : RecombField :=
  algebraMap RecombPolynomial RecombField X
noncomputable def recombP : RecombField :=
  algebraMap RecombPolynomial RecombField (C (RatFunc.X : RecombCoefficient))
noncomputable def recombR : RecombField :=
  algebraMap RecombPolynomial RecombField
    (C (RatFunc.C (RatFunc.X : RatFunc (RatFunc RecombBase))))
noncomputable def recombSamplingValue (m : ℕ) : RecombField :=
  algebraMap RecombPolynomial RecombField (samplingRecombinationNumerator m) /
    algebraMap RecombPolynomial RecombField (samplingRecombinationDenominator m)

theorem exists_recomb_real_point :
    ∃ ι : RecombField →+* ℝ, 0 < ι recombA ∧ 0 < ι recombB ∧ 0 ≤ ι recombRho := by
  have h1 : Countable (RatFunc ℚ) := countable_ratFunc ℚ
  have h2 : Countable (RatFunc (RatFunc ℚ)) := countable_ratFunc _
  have h3 : Countable (RatFunc (RatFunc (RatFunc ℚ))) := countable_ratFunc _
  have h4 : Countable (RatFunc (RatFunc (RatFunc (RatFunc ℚ)))) := countable_ratFunc _
  obtain ⟨g1, -, ht, -⟩ :=
    exists_ratFunc_extension (algebraMap ℚ ℝ) (by norm_num : (2 : ℝ) < 3)
  obtain ⟨g2, hg2, hl, hl1⟩ := exists_ratFunc_extension g1 (zero_lt_one' ℝ)
  obtain ⟨g3, hg3, -, -⟩ := exists_ratFunc_extension g2 (zero_lt_one' ℝ)
  obtain ⟨g4, hg4, -, -⟩ := exists_ratFunc_extension g3 (zero_lt_one' ℝ)
  obtain ⟨g5, hg5, hr, -⟩ := exists_ratFunc_extension g4 (zero_lt_one' ℝ)
  refine ⟨g5, ?_, ?_, ?_⟩
  · simpa only [recombA, RatFunc.algebraMap_C, recombLambda, hg5, hg4, hg3] using hl
  · simp only [recombB, map_sub, RatFunc.algebraMap_C, recombLambda,
      nestedConstant, RingHom.comp_apply, hg5, hg4, hg3, hg2]
    linarith
  · simpa only [recombRho, RatFunc.algebraMap_X] using hr.le

theorem recomb_detNeZero :
    Algebra.Rational.DetNeZero recombA recombB recombRho (piOf recombP) (piOf recombR) := by
  obtain ⟨ι, hA, hB, hR⟩ := exists_recomb_real_point
  intro N
  exact Algebra.Rational.det_bMat_ne_zero_of_hom ι hA hB hR N

theorem existsUnique_recomb_solution :
    ∃! q : Config 2 2 → RecombField,
      IsSolution recombA recombB recombRho (piOf recombP) (piOf recombR) q :=
  ⟨Algebra.Rational.qOfDet recomb_detNeZero, Algebra.Rational.qOfDet_isSolution recomb_detNeZero,
    fun _ hq => Algebra.Rational.qOfDet_unique recomb_detNeZero hq⟩

theorem recombSamplingValue_eq_of_isSolution {q : Config 2 2 → RecombField}
    (hq : IsSolution recombA recombB recombRho (piOf recombP) (piOf recombR) q)
    (m : ℕ) : q (samplingMM m) = recombSamplingValue m := by
  obtain ⟨ι, hA, hB, hR⟩ := exists_recomb_real_point
  have hq' : IsSolution (ι recombA) (ι recombB) (ι recombRho)
      (piOf (ι recombP)) (piOf (ι recombR)) (fun η => ι (q η)) := by
    have h := Algebra.Rational.isSolution_map ι hq
    rwa [piOf_map, piOf_map] at h
  let ψ : RecombPolynomial →+* ℝ := ι.comp (algebraMap RecombPolynomial RecombField)
  let φ : MvPolynomial (Fin 2) (Polynomial (Polynomial RecombBase)) →+* ℝ :=
    ψ.comp nestedLocalization
  have hφA : φ (MvPolynomial.C X) = ι recombA := by
    change ι (algebraMap RecombPolynomial RecombField
      (nestedLocalization (MvPolynomial.C X))) = _
    rw [nestedLocalization_lambda]
    rfl
  have hφB : φ (MvPolynomial.C (C (C RatFunc.X) - X)) = ι recombB := by
    change ι (algebraMap RecombPolynomial RecombField
      (nestedLocalization (MvPolynomial.C (C (C RatFunc.X) - X)))) = _
    rw [map_sub MvPolynomial.C, map_sub nestedLocalization, nestedLocalization_scalar,
      nestedLocalization_lambda]
    rfl
  have hφR : φ (MvPolynomial.C (C X)) = ι recombRho := by
    change ι (algebraMap RecombPolynomial RecombField
      (nestedLocalization (MvPolynomial.C (C X)))) = _
    rw [nestedLocalization_theta]
    rfl
  have hφp : φ (MvPolynomial.X 0) = ι recombP := by
    change ι (algebraMap RecombPolynomial RecombField
      (nestedLocalization (MvPolynomial.X 0))) = _
    rw [nestedLocalization_p]
    rfl
  have hφr : φ (MvPolynomial.X 1) = ι recombR := by
    change ι (algebraMap RecombPolynomial RecombField
      (nestedLocalization (MvPolynomial.X 1))) = _
    rw [nestedLocalization_r]
    rfl
  have hnum := map_samplingNumerator_eq_Dfull_mul_q hA hB hR hq' φ (MvPolynomial.C X)
    (MvPolynomial.C (C (C RatFunc.X) - X)) (MvPolynomial.C (C X))
    (MvPolynomial.X 0) (MvPolynomial.X 1) hφA hφB hφR hφp hφr m
  have hden : ψ (samplingRecombinationDenominator m) =
      Dfull (ι recombA) (ι recombB) (ι recombRho) m m := by
    have h := Dfull_map (φ.comp MvPolynomial.C) X (C (C RatFunc.X) - X) (C X) m m
    simp only [RingHom.comp_apply] at h hφA hφB hφR
    rw [hφA, hφB, hφR] at h
    exact h
  have hnum' : ψ (samplingRecombinationNumerator m) =
      ψ (samplingRecombinationDenominator m) * ι (q (samplingMM m)) := by
    rw [hden]
    exact hnum
  have key : algebraMap RecombPolynomial RecombField
        (samplingRecombinationNumerator m) =
      algebraMap RecombPolynomial RecombField
        (samplingRecombinationDenominator m) * q (samplingMM m) := by
    apply ringHom_injective_of_field ι
    rw [map_mul]
    exact hnum'
  rw [recombSamplingValue, eq_div_iff
    (Rhone.Algebra.algebraMap_ne_zero
      (samplingRecombinationDenominator_ne_zero m)), key, mul_comm]

theorem unbounded_recombSamplingValue_denominator (D : ℕ) :
    ∃ m : ℕ, 2 ≤ m ∧ ∃ G : RecombPolynomial, Irreducible G ∧
      G ∣ (recombSamplingValue m).denom ∧ D < G.natDegree := by
  obtain ⟨m, hm, G, hirr, hdiv, hn, hdeg⟩ :=
    unbounded_surviving_recombination_factor D
  refine ⟨m, hm, G.map nestedConstant, irreducible_map_nestedConstant G hirr, ?_, ?_⟩
  · apply Rhone.Algebra.prime_dvd_denom (samplingRecombinationDenominator_ne_zero m) rfl
      (irreducible_map_nestedConstant G hirr).prime
    · exact recombination_factor_dvd_samplingDenominator hm hdiv
    · exact recombination_factor_not_dvd_samplingNumerator hm hirr hn
  · rwa [natDegree_map_nestedConstant]

theorem unbounded_sampling_recombination_denominator (D : ℕ)
    {q : Config 2 2 → RecombField}
    (hq : IsSolution recombA recombB recombRho (piOf recombP) (piOf recombR) q) :
    ∃ m : ℕ, 2 ≤ m ∧ ∃ G : RecombPolynomial, Irreducible G ∧
      G ∣ (q (samplingMM m)).denom ∧ D < G.natDegree := by
  obtain ⟨m, hm, G, hirr, hdiv, hdeg⟩ := unbounded_recombSamplingValue_denominator D
  exact ⟨m, hm, G, hirr, (recombSamplingValue_eq_of_isSolution hq m) ▸ hdiv, hdeg⟩

theorem no_uniform_expression_recombSamplingValue (D : ℕ) :
    ∃ m : ℕ, 2 ≤ m ∧ ¬ ∃ e : Rhone.Algebra.Expr RecombCoefficient,
      Rhone.Algebra.DAdm recombA recombB recombRho D e ∧
      Rhone.Algebra.Expr.eval recombA recombB recombRho e = recombSamplingValue m := by
  obtain ⟨m, hm, G, hirr, hdiv, hdeg⟩ := unbounded_recombSamplingValue_denominator D
  refine ⟨m, hm, ?_⟩
  rintro ⟨e, hadm, heval⟩
  have hbound := Rhone.Algebra.natDegree_le_of_dvd_denom_eval
    (Rhone.Algebra.boundedDen_of_poly D (C recombLambda))
    (Rhone.Algebra.boundedDen_of_poly D
      (C (nestedConstant (RatFunc.X : RecombBase)) - C recombLambda))
    (Rhone.Algebra.boundedDen_of_poly D X) hadm hirr (by
      change G ∣ (Rhone.Algebra.Expr.eval recombA recombB recombRho e).denom
      rw [heval]
      exact hdiv)
  omega

theorem no_bounded_recombination_degree_formula_sampling (D : ℕ) {q : Config 2 2 → RecombField}
    (hq : IsSolution recombA recombB recombRho (piOf recombP) (piOf recombR) q) :
    ∃ m : ℕ, 2 ≤ m ∧ ¬ ∃ e : Rhone.Algebra.Expr RecombCoefficient,
      Rhone.Algebra.DAdm recombA recombB recombRho D e ∧
      Rhone.Algebra.Expr.eval recombA recombB recombRho e = q (samplingMM m) := by
  obtain ⟨m, hm, h⟩ := no_uniform_expression_recombSamplingValue D
  exact ⟨m, hm, (recombSamplingValue_eq_of_isSolution hq m) ▸ h⟩

end Rhone.Probability.RecombinationDegree
