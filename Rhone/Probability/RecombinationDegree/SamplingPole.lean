/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.RecombinationDegree.MutationCoordinates
public import Rhone.Probability.SamplingUniform.NoFormula

/-! # The recombination pole of the universal sampling numerator -/

@[expose] public section

namespace Rhone.Probability.RecombinationDegree

open Polynomial LinearAlgebra.Tridiag DiagonalChain Algebra.SamplingUniform SamplingUniform
  LinearAlgebra.SlotDeletion SlotDeletion Analysis.RareAlleleHierarchy RareAlleleHierarchy

theorem generic_kappa_ne_zero {k : ℕ} (hk : 1 ≤ k) :
    kappaT k k (RatFunc.X : RatFunc ℚ) 0 ≠ 0 := by
  let P : Polynomial ℚ := C (k : ℚ) * X + C (2 * (k : ℚ) * (k - 1))
  have hp : P ≠ 0 := by
    intro h
    have h1 := congrArg (fun f : Polynomial ℚ => f.coeff 1) h
    simp only [P, coeff_add, coeff_C_mul_X, coeff_C, ite_true,
      Nat.one_ne_zero, ite_false, add_zero] at h1
    exact (Nat.cast_ne_zero.mpr (by omega : k ≠ 0)) h1
  have he : algebraMap (Polynomial ℚ) (RatFunc ℚ) P = kappaT k k RatFunc.X 0 := by
    simp [P, kappaT]
    ring
  rw [← he]
  simpa only [map_zero] using (RatFunc.algebraMap_injective ℚ).ne hp

theorem generic_recombination_ED_ne_zero {k : ℕ} (hk : 1 ≤ k) :
    ED k (C (RatFunc.X : RatFunc ℚ)) X ≠ 0 := by
  have h := natDegree_E_of_charZero k k (RatFunc.X : RatFunc ℚ) 0
    (generic_kappa_ne_zero hk)
  simp only [Nat.min_self, C_0] at h
  intro hz
  change E (Polynomial (RatFunc ℚ)) k k (C RatFunc.X) 0 X = 0 at hz
  rw [hz, natDegree_zero] at h
  omega

theorem recombination_sampling_coefficient {m : ℕ} (hm : 2 ≤ m) :
    (lambdaSamplingNumerator (C (RatFunc.X : RatFunc ℚ)) X m).coeff
      (lambdaDenominatorDegree m) =
      C (lambdaDenominatorConstant (K := RatFunc ℚ) m) * W m (C RatFunc.X) X := by
  let φ := algebraMap (Polynomial (RatFunc ℚ)) (RatFunc (RatFunc ℚ))
  have hE : ∀ k, 2 ≤ k → ED k (φ (C RatFunc.X)) (φ X) ≠ 0 := by
    intro k hk
    have h := (RatFunc.algebraMap_injective (RatFunc ℚ)).ne
      (generic_recombination_ED_ne_zero (by omega : 1 ≤ k))
    simpa only [map_zero, ED_map] using h
  apply RatFunc.algebraMap_injective (RatFunc ℚ)
  have hmap := lambdaSamplingNumerator_map φ (C RatFunc.X) X hE m
  have hcoeff := congrArg (fun f : Polynomial (RatFunc (RatFunc ℚ)) =>
    f.coeff (lambdaDenominatorDegree m)) hmap
  rw [Polynomial.coeff_map] at hcoeff
  rw [hcoeff, (lambdaSamplingNumerator_hasTop _ _ hE hm).2]
  rw [map_mul, W_map]
  congr 1
  simp only [RatFunc.algebraMap_C]
  exact (lambdaDenominatorConstant_map
    (RatFunc.C : RatFunc ℚ →+* RatFunc (RatFunc ℚ)) m).symm

noncomputable def samplingRecombinationNumerator (m : ℕ) :
    Polynomial (RatFunc (RatFunc (RatFunc (RatFunc ℚ)))) :=
  nestedLocalization (lambdaFrequencyNumerator (C (RatFunc.X : RatFunc ℚ)) X m)

noncomputable def samplingRecombinationDenominator (m : ℕ) :
    Polynomial (RatFunc (RatFunc (RatFunc (RatFunc ℚ)))) :=
  nestedLocalization (MvPolynomial.C
    (Dfull X (C (C (RatFunc.X : RatFunc ℚ)) - X) (C X) m m))

theorem recombination_factor_not_dvd_samplingNumerator {m : ℕ} (hm : 2 ≤ m)
    {G : Polynomial (RatFunc ℚ)} (hG : Irreducible G)
    (hW : ¬ G ∣ W m (C RatFunc.X) X) :
    ¬ G.map nestedConstant ∣ samplingRecombinationNumerator m := by
  rw [samplingRecombinationNumerator, nestedLocalization_dvd_iff G hG.ne_zero]
  intro h
  have hmix := (MvPolynomial.C_dvd_iff_dvd_coeff _ _).mp h (mon 1 1)
  change C G ∣ lambdaSamplingNumerator (C RatFunc.X) X m at hmix
  have hc := (Polynomial.C_dvd_iff_dvd_coeff _ _).mp hmix (lambdaDenominatorDegree m)
  rw [recombination_sampling_coefficient hm] at hc
  have hu : IsUnit (C (lambdaDenominatorConstant (K := RatFunc ℚ) m)) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (lambdaDenominatorConstant_ne_zero m))
  exact hW ((hG.prime.dvd_mul.mp hc).resolve_left
    (fun hd => hG.not_isUnit (isUnit_of_dvd_unit hd hu)))

theorem recombination_factor_dvd_samplingDenominator {m : ℕ} (hm : 2 ≤ m)
    {G : Polynomial (RatFunc ℚ)} (hG : G ∣ ED m (C RatFunc.X) X) :
    G.map nestedConstant ∣ samplingRecombinationDenominator m := by
  unfold samplingRecombinationDenominator
  rw [nestedLocalization_dvd_iff G (by
    intro hz
    rw [hz, zero_dvd_iff] at hG
    exact generic_recombination_ED_ne_zero (by omega) hG)]
  apply _root_.map_dvd MvPolynomial.C
  apply dvd_trans (_root_.map_dvd Polynomial.C hG)
  rw [← E_diagonal_lambda (C (RatFunc.X : RatFunc ℚ)) X m]
  exact ⟨Dcut X (C (C (RatFunc.X : RatFunc ℚ)) - X) (C X) m m,
    by rw [mul_comm, Dcut_mul_E _ _ _ hm hm]⟩

theorem samplingRecombinationDenominator_ne_zero (m : ℕ) :
    samplingRecombinationDenominator m ≠ 0 := by
  intro h
  have h0 : (MvPolynomial.C
      (Dfull X (C (C (RatFunc.X : RatFunc ℚ)) - X) (C X) m m) :
        MvPolynomial (Fin 2) (Polynomial (Polynomial (RatFunc ℚ)))) = 0 :=
    nestedLocalization_injective (by rw [map_zero]; exact h)
  have h1 : Dfull (X : Polynomial (Polynomial (RatFunc ℚ)))
      (C (C RatFunc.X) - X) (C X) m m = 0 :=
    MvPolynomial.C_injective (Fin 2) _ (by rw [h0, map_zero])
  have ht := (Dfull_lambda_hasTop (C (RatFunc.X : RatFunc ℚ)) X m).2
  rw [h1, coeff_zero] at ht
  have hne : lambdaDenominatorConstant (K := (RatFunc ℚ)[X]) m *
      frakE m (C RatFunc.X) X ≠ 0 := by
    apply mul_ne_zero (lambdaDenominatorConstant_ne_zero m)
    apply Finset.prod_ne_zero_iff.mpr
    intro k hk
    exact generic_recombination_ED_ne_zero
      (by have := (Finset.mem_Icc.mp hk).1; omega)
  exact hne ht.symm

end Rhone.Probability.RecombinationDegree
