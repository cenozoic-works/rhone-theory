/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Statistics.InfinitesimalPedigreeInheritedMoments
/-!
# Exact segregation-residual moments under the locus law

Source: barton_etheridge_veber2017, sec. 3.1. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Rhone.Statistics Rhone.Combinatorics
open scoped ENNReal
namespace Rhone.Statistics

theorem locus_residual_memLp {n : Nat} (P : Pedigree n) (ν : Measure Real)
    [IsProbabilityMeasure ν] (hν : MemLp id 2 ν) (m : Real) (i : Fin n) :
    MemLp (fun ω : (Fin n → Real) × (Fin n → Bool) =>
      locusSegregationResidual P m ω.1 ω.2 i) 2 (locusLaw n ν) := by
  have hy (j : Fin n) := inherited_effect_memLp ν hν m (fun c => geneFounder P c j)
  cases hp : P.parents i with
  | none =>
    simpa only [locusSegregationResidual, segregationResidual, hp, locusTraitDeviation] using hy i
  | some parents =>
    have h := (hy i).sub (((hy parents.1).add (hy parents.2)).mul_const (1 / 2))
    convert h using 1
    funext ω
    simp only [locusSegregationResidual, segregationResidual, hp, locusTraitDeviation,
      div_eq_mul_inv, Pi.sub_apply, Pi.add_apply, one_mul]

theorem locus_residual_mean_zero {n : Nat} (P : Pedigree n) (ν : Measure Real)
    [IsProbabilityMeasure ν] (hν : MemLp id 2 ν) (i : Fin n) :
    (∫ ω : (Fin n → Real) × (Fin n → Bool),
      locusSegregationResidual P (∫ x, x ∂ν) ω.1 ω.2 i ∂(locusLaw n ν)) = 0 := by
  cases hp : P.parents i with
  | none =>
    simp only [locusSegregationResidual, segregationResidual, hp, locusTraitDeviation]
    exact inherited_effect_mean ν hν (fun c => geneFounder P c i)
  | some parents =>
    have hi := (locus_residual_memLp P ν hν (∫ x, x ∂ν) i).integrable (by norm_num)
    rw [locusLaw, integral_prod _ hi]
    simp_rw [integral_coin_residual_zero P i parents hp]
    simp

theorem locus_residual_cross_earlier_zero {n : Nat} (P : Pedigree n) (ν : Measure Real)
    [IsProbabilityMeasure ν] (hν : MemLp id 2 ν) (i j : Fin n) (hji : j < i)
    (parents : Fin n × Fin n) (hi : P.parents i = some parents) :
    (∫ ω : (Fin n → Real) × (Fin n → Bool),
      locusSegregationResidual P (∫ x, x ∂ν) ω.1 ω.2 j *
      locusSegregationResidual P (∫ x, x ∂ν) ω.1 ω.2 i ∂(locusLaw n ν)) = 0 := by
  have hint : Integrable (fun ω : (Fin n → Real) × (Fin n → Bool) =>
      locusSegregationResidual P (∫ x, x ∂ν) ω.1 ω.2 j *
      locusSegregationResidual P (∫ x, x ∂ν) ω.1 ω.2 i) (locusLaw n ν) :=
    (locus_residual_memLp P ν hν _ j).integrable_mul (locus_residual_memLp P ν hν _ i)
  rw [locusLaw, integral_prod _ hint]
  simp_rw [integral_coin_cross_residual_zero P i j hji parents hi]
  simp

theorem identityByDescent_later_founder {n : Nat} (P : Pedigree n) (i j : Fin n)
    (hji : j < i) (hi : P.parents i = none) : identityByDescent P i j = 0 := by
  have hneq (c : Fin n → Bool) : geneFounder P c i ≠ geneFounder P c j := by
    rw [geneFounder_of_founder P c hi]
    have hle := geneFounder_le_birth P c j
    intro heq
    rw [← heq] at hle
    omega
  simp [identityByDescent, hneq]
private theorem integral_sq_sub_memLp {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A B : Ω → Real) (hA : MemLp A 2 μ) (hB : MemLp B 2 μ) :
    (∫ ω, (A ω - B ω)^2 ∂μ) =
      (∫ ω, (A ω)^2 ∂μ) + (∫ ω, (B ω)^2 ∂μ) - 2 * (∫ ω, A ω * B ω ∂μ) := by
  have hAB : Integrable (fun ω => A ω * B ω) μ := hA.integrable_mul hB
  have heq : (fun ω => (A ω - B ω)^2) =
      (fun ω => (A ω)^2 + (B ω)^2 - 2 * (A ω * B ω)) := by funext ω; ring
  have hs : Integrable (fun ω => (A ω)^2 + (B ω)^2) μ :=
    hA.integrable_sq.add hB.integrable_sq
  rw [heq, integral_sub hs (hAB.const_mul 2),
    integral_add hA.integrable_sq hB.integrable_sq, integral_const_mul]

theorem inherited_trait_sq_difference {n : Nat} (P : Pedigree n) (ν : Measure Real)
    [IsProbabilityMeasure ν] (hν : MemLp id 2 ν) (a b : Fin n) :
    (∫ ω : (Fin n → Real) × (Fin n → Bool),
      (locusTraitDeviation P (∫ x, x ∂ν) ω.1 ω.2 a -
      locusTraitDeviation P (∫ x, x ∂ν) ω.1 ω.2 b)^2 ∂(locusLaw n ν)) =
      2 * Var[id; ν] * (1 - identityByDescent P a b) := by
  have ha := inherited_effect_memLp ν hν (∫ x, x ∂ν) (fun c => geneFounder P c a)
  have hb := inherited_effect_memLp ν hν (∫ x, x ∂ν) (fun c => geneFounder P c b)
  have haa : MemLp (fun ω : (Fin n → Real) × (Fin n → Bool) =>
      locusTraitDeviation P (∫ x, x ∂ν) ω.1 ω.2 a) 2 (locusLaw n ν) := ha
  have hbb : MemLp (fun ω : (Fin n → Real) × (Fin n → Bool) =>
      locusTraitDeviation P (∫ x, x ∂ν) ω.1 ω.2 b) 2 (locusLaw n ν) := hb
  rw [integral_sq_sub_memLp _ _ _ haa hbb]
  have hs (j : Fin n) : (∫ ω : (Fin n → Real) × (Fin n → Bool),
      (locusTraitDeviation P (∫ x, x ∂ν) ω.1 ω.2 j)^2 ∂(locusLaw n ν)) = Var[id; ν] := by
    simp only [pow_two, locusTraitDeviation]
    rw [inherited_trait_cross P ν hν j j, identityByDescent_self, mul_one]
  rw [hs a, hs b]
  change _ - 2 * (∫ ω : (Fin n → Real) × (Fin n → Bool),
    (ω.1 (geneFounder P ω.2 a) - ∫ x, x ∂ν) *
    (ω.1 (geneFounder P ω.2 b) - ∫ x, x ∂ν) ∂(locusLaw n ν)) = _
  rw [inherited_trait_cross P ν hν a b]
  ring

theorem locus_residual_square_nonfounder {n : Nat} (P : Pedigree n) (i : Fin n)
    (parents : Fin n × Fin n) (hi : P.parents i = some parents)
    (m : Real) (e : Fin n → Real) (c : Fin n → Bool) :
    (locusSegregationResidual P m e c i)^2 =
      (1 / 4 : Real) * (locusTraitDeviation P m e c parents.1 -
        locusTraitDeviation P m e c parents.2)^2 := by
  rw [locusSegregationResidual_nonfounder P i parents hi]
  cases c i <;> simp only [Bool.false_eq_true, ↓reduceIte, locusTraitDeviation] <;> ring

theorem locus_residual_second_moment {n : Nat} (P : Pedigree n) (ν : Measure Real)
    [IsProbabilityMeasure ν] (hν : MemLp id 2 ν) (i : Fin n) :
    (∫ ω : (Fin n → Real) × (Fin n → Bool),
      (locusSegregationResidual P (∫ x, x ∂ν) ω.1 ω.2 i)^2 ∂(locusLaw n ν)) =
      segregationVariance P (Var[id; ν]) i := by
  cases hp : P.parents i with
  | none =>
    simp only [locusSegregationResidual, segregationResidual, hp, pow_two,
      locusTraitDeviation, segregationVariance]
    rw [inherited_trait_cross P ν hν i i, identityByDescent_self, mul_one]
  | some parents =>
    simp_rw [locus_residual_square_nonfounder P i parents hp]
    rw [integral_const_mul, inherited_trait_sq_difference P ν hν parents.1 parents.2]
    simp only [segregationVariance, hp]
    ring
private theorem integral_mul_sub_parent_average {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A B C D : Ω → Real) (hA : MemLp A 2 μ) (hB : MemLp B 2 μ)
    (hC : MemLp C 2 μ) (hD : MemLp D 2 μ) :
    (∫ ω, A ω * (B ω - (C ω + D ω) / 2) ∂μ) =
      (∫ ω, A ω * B ω ∂μ) -
        ((∫ ω, A ω * C ω ∂μ) + (∫ ω, A ω * D ω ∂μ)) / 2 := by
  have hab : Integrable (fun ω => A ω * B ω) μ := hA.integrable_mul hB
  have hac : Integrable (fun ω => A ω * C ω) μ := hA.integrable_mul hC
  have had : Integrable (fun ω => A ω * D ω) μ := hA.integrable_mul hD
  have hs : Integrable (fun ω => A ω * C ω + A ω * D ω) μ := hac.add had
  have heq : (fun ω => A ω * (B ω - (C ω + D ω) / 2)) =
      (fun ω => A ω * B ω - (A ω * C ω + A ω * D ω) / 2) := by
    funext ω
    ring
  rw [heq, integral_sub hab (hs.div_const 2), integral_div, integral_add hac had]

theorem locus_residual_cross_later_founder_zero {n : Nat} (P : Pedigree n) (ν : Measure Real)
    [IsProbabilityMeasure ν] (hν : MemLp id 2 ν) (i j : Fin n) (hji : j < i)
    (hi : P.parents i = none) :
    (∫ ω : (Fin n → Real) × (Fin n → Bool),
      locusSegregationResidual P (∫ x, x ∂ν) ω.1 ω.2 i *
      locusSegregationResidual P (∫ x, x ∂ν) ω.1 ω.2 j ∂(locusLaw n ν)) = 0 := by
  have hy (k : Fin n) : MemLp (fun ω : (Fin n → Real) × (Fin n → Bool) =>
      locusTraitDeviation P (∫ x, x ∂ν) ω.1 ω.2 k) 2 (locusLaw n ν) :=
    inherited_effect_memLp ν hν _ (fun c => geneFounder P c k)
  have hc (k : Fin n) (hki : k < i) :
      (∫ ω : (Fin n → Real) × (Fin n → Bool),
        locusTraitDeviation P (∫ x, x ∂ν) ω.1 ω.2 i *
        locusTraitDeviation P (∫ x, x ∂ν) ω.1 ω.2 k ∂(locusLaw n ν)) = 0 := by
    change (∫ ω : (Fin n → Real) × (Fin n → Bool),
      (ω.1 (geneFounder P ω.2 i) - ∫ x, x ∂ν) *
      (ω.1 (geneFounder P ω.2 k) - ∫ x, x ∂ν) ∂(locusLaw n ν)) = 0
    rw [inherited_trait_cross P ν hν i k, identityByDescent_later_founder P i k hki hi,
      mul_zero]
  cases hj : P.parents j with
  | none =>
    simp only [locusSegregationResidual, segregationResidual, hi, hj]
    exact hc j hji
  | some parents =>
    simp only [locusSegregationResidual, segregationResidual, hi, hj]
    rw [integral_mul_sub_parent_average _ _ _ _ _ (hy i) (hy j) (hy parents.1) (hy parents.2)]
    have hlt := P.parents_lt j parents hj
    rw [hc j hji, hc parents.1 (by omega), hc parents.2 (by omega)]
    norm_num

theorem locus_residual_cross_diagonal {n : Nat} (P : Pedigree n) (ν : Measure Real)
    [IsProbabilityMeasure ν] (hν : MemLp id 2 ν) (i j : Fin n) :
    (∫ ω : (Fin n → Real) × (Fin n → Bool),
      locusSegregationResidual P (∫ x, x ∂ν) ω.1 ω.2 i *
      locusSegregationResidual P (∫ x, x ∂ν) ω.1 ω.2 j ∂(locusLaw n ν)) =
      if i = j then segregationVariance P (Var[id; ν]) i else 0 := by
  classical
  by_cases hij : i = j
  · subst j
    simp only [↓reduceIte, ← pow_two]
    exact locus_residual_second_moment P ν hν i
  · simp only [hij, ↓reduceIte]
    have hlater (a b : Fin n) (hba : b < a) :
        (∫ ω : (Fin n → Real) × (Fin n → Bool),
          locusSegregationResidual P (∫ x, x ∂ν) ω.1 ω.2 a *
          locusSegregationResidual P (∫ x, x ∂ν) ω.1 ω.2 b ∂(locusLaw n ν)) = 0 := by
      cases ha : P.parents a with
      | none => exact locus_residual_cross_later_founder_zero P ν hν a b hba ha
      | some parents =>
        simp_rw [mul_comm (locusSegregationResidual P (∫ x, x ∂ν) _ _ a)]
        exact locus_residual_cross_earlier_zero P ν hν a b hba parents ha
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · simp_rw [mul_comm (locusSegregationResidual P (∫ x, x ∂ν) _ _ i)]
      exact hlater j i hlt
    · exact hlater i j hgt
end Rhone.Statistics
