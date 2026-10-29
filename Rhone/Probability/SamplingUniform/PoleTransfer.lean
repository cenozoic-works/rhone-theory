/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.SamplingUniform.NumeratorLeading
public import Rhone.Algebra.SamplingUniform.NestedLocalization
public import Rhone.Probability.DiagonalObstruction.Surviving
public import Rhone.Probability.SamplingNumerators.Algebra

/-! # Surviving factors in the arbitrary-size sampling numerator -/

@[expose] public section

namespace Rhone.Probability.SamplingUniform
open Polynomial LinearAlgebra.SlotDeletion SlotDeletion Analysis.RareAlleleHierarchy
    RareAlleleHierarchy
open DiagonalChain
variable {K : Type*} [Field K] [CharZero K]

theorem surviving_factor_not_dvd_frequencyNumerator (ρ : K) {m : ℕ} (hm : 2 ≤ m)
    {G : K[X]} (hG : Irreducible G) (hW : ¬ G ∣ W m X (C ρ)) :
    ¬ MvPolynomial.C (Polynomial.C G) ∣ lambdaFrequencyNumerator X (C ρ) m := by
  intro h
  have hmix := (MvPolynomial.C_dvd_iff_dvd_coeff _ _).mp h (mon 1 1)
  change Polynomial.C G ∣ lambdaSamplingNumerator X (C ρ) m at hmix
  have hc := (Polynomial.C_dvd_iff_dvd_coeff _ _).mp hmix (lambdaDenominatorDegree m)
  rw [lambdaSamplingNumerator_mutation_coeff ρ hm] at hc
  have hu : IsUnit (Polynomial.C (lambdaDenominatorConstant (K := K) m)) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (lambdaDenominatorConstant_ne_zero m))
  exact hW ((hG.prime.dvd_mul.mp hc).resolve_left
    (fun hd => hG.not_isUnit (isUnit_of_dvd_unit hd hu)))

noncomputable def samplingMutationNumerator (ρ : K) (m : ℕ) :
    Polynomial (RatFunc (RatFunc (RatFunc K))) :=
  Algebra.SamplingUniform.nestedLocalization (lambdaFrequencyNumerator X (C ρ) m)

noncomputable def samplingMutationDenominator (ρ : K) (m : ℕ) :
    Polynomial (RatFunc (RatFunc (RatFunc K))) :=
  Algebra.SamplingUniform.nestedLocalization (MvPolynomial.C
    (Dfull X (C (X : K[X]) - X) (C (C ρ)) m m))

theorem surviving_factor_not_dvd_samplingMutationNumerator (ρ : K)
    {m : ℕ} (hm : 2 ≤ m) {G : K[X]} (hG : Irreducible G)
    (hW : ¬ G ∣ W m X (C ρ)) :
    ¬ G.map Algebra.SamplingUniform.nestedConstant ∣ samplingMutationNumerator ρ m := by
  rw [samplingMutationNumerator, Algebra.SamplingUniform.nestedLocalization_dvd_iff G hG.ne_zero]
  exact surviving_factor_not_dvd_frequencyNumerator ρ hm hG hW

theorem surviving_factor_dvd_samplingMutationDenominator (ρ : K)
    {m : ℕ} (hm : 2 ≤ m) {G : K[X]} (hG : G ∣ ED m X (C ρ)) :
    G.map Algebra.SamplingUniform.nestedConstant ∣ samplingMutationDenominator ρ m := by
  unfold samplingMutationDenominator
  rw [Algebra.SamplingUniform.nestedLocalization_dvd_iff G (by
    intro hz
    rw [hz, zero_dvd_iff] at hG
    exact Analysis.DiagonalObstruction.E_mutationPolynomial_ne_zero (by omega) ρ hG)]
  apply _root_.map_dvd MvPolynomial.C
  apply dvd_trans (_root_.map_dvd Polynomial.C hG)
  rw [← E_diagonal_lambda (X : K[X]) (C ρ) m]
  exact ⟨Dcut X (C (X : K[X]) - X) (C (C ρ)) m m,
    by rw [mul_comm, Dcut_mul_E _ _ _ hm hm]⟩

end Rhone.Probability.SamplingUniform
