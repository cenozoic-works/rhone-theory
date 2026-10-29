/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Statistics.InfinitesimalPedigreeFounderMoments
public import Rhone.Statistics.InfinitesimalPedigreeCoinMoments
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
/-!
# Moments of the inherited locus effects

Source: barton_etheridge_veber2017, sec. 3.1. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Rhone.Statistics
open scoped ENNReal
namespace Rhone.Statistics
theorem inherited_effect_memLp {n : Nat} (ν : Measure Real) [IsProbabilityMeasure ν]
    (hν : MemLp id 2 ν) (m : Real) (k : (Fin n → Bool) → Fin n) :
    MemLp (fun ω : (Fin n → Real) × (Fin n → Bool) => ω.1 (k ω.2) - m) 2
      (locusLaw n ν) := by
  classical
  have hi (a : Fin n) : MemLp (fun ω : (Fin n → Real) × (Fin n → Bool) => ω.1 a - m)
      2 (locusLaw n ν) := by
    have hc : MemLp (fun x : Real => x - m) 2 ν := hν.sub (memLp_const m)
    exact (hc.comp_measurePreserving (measurePreserving_eval (fun _ : Fin n => ν) a)).comp_fst _
  have hs (a : Fin n) : MeasurableSet {ω : (Fin n → Real) × (Fin n → Bool) | k ω.2 = a} := by
    exact (MeasurableSet.singleton a).preimage ((measurable_of_countable k).comp measurable_snd)
  have hm := memLp_finsetSum Finset.univ (fun a _ => (hi a).indicator (hs a))
  convert hm using 1
  funext ω
  simp [Set.indicator]
theorem inherited_effect_mean {n : Nat} (ν : Measure Real) [IsProbabilityMeasure ν]
    (hν : MemLp id 2 ν) (k : (Fin n → Bool) → Fin n) :
    (∫ ω : (Fin n → Real) × (Fin n → Bool), ω.1 (k ω.2) - ∫ x, x ∂ν
      ∂(locusLaw n ν)) = 0 := by
  rw [locusLaw, integral_prod_symm _ ((inherited_effect_memLp ν hν _ k).integrable (by norm_num))]
  simp_rw [integral_comp_eval (μ := fun _ : Fin n => ν)
    (f := fun x : Real => x - ∫ y, y ∂ν) (by fun_prop), centered_gene_mean ν hν]
  simp

theorem gene_identity_coin_average {n : Nat} (P : Rhone.Combinatorics.Pedigree n) (a b : Fin n) :
    (∫ c : Fin n → Bool, (if geneFounder P c a = geneFounder P c b then (1 : Real) else 0)
      ∂(Measure.pi fun _ : Fin n => (PMF.uniformOfFintype Bool).toMeasure)) =
      identityByDescent P a b := by
  classical
  rw [coinLaw_eq_uniform, PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, smul_eq_mul]
  rw [← Finset.mul_sum, Finset.sum_boole]
  simp [identityByDescent, ENNReal.toReal_inv, div_eq_mul_inv, mul_comm]

theorem inherited_trait_cross {n : Nat} (P : Rhone.Combinatorics.Pedigree n)
    (ν : Measure Real) [IsProbabilityMeasure ν] (hν : MemLp id 2 ν) (a b : Fin n) :
    (∫ ω : (Fin n → Real) × (Fin n → Bool),
      (ω.1 (geneFounder P ω.2 a) - ∫ x, x ∂ν) *
      (ω.1 (geneFounder P ω.2 b) - ∫ x, x ∂ν) ∂(locusLaw n ν)) =
      Var[id; ν] * identityByDescent P a b := by
  have ha := inherited_effect_memLp ν hν (∫ x, x ∂ν) (fun c => geneFounder P c a)
  have hb := inherited_effect_memLp ν hν (∫ x, x ∂ν) (fun c => geneFounder P c b)
  have hi : Integrable (fun ω : (Fin n → Real) × (Fin n → Bool) =>
      (ω.1 (geneFounder P ω.2 a) - ∫ x, x ∂ν) *
      (ω.1 (geneFounder P ω.2 b) - ∫ x, x ∂ν)) (locusLaw n ν) :=
    ha.integrable_mul hb
  rw [locusLaw, integral_prod_symm _ hi]
  simp_rw [centered_founder_cross ν hν]
  have heq : (fun c : Fin n → Bool =>
      if geneFounder P c a = geneFounder P c b then Var[id; ν] else 0) =
      (fun c => Var[id; ν] *
        (if geneFounder P c a = geneFounder P c b then (1 : Real) else 0)) := by
    funext c
    split_ifs <;> simp
  rw [heq, integral_const_mul, gene_identity_coin_average]
end Rhone.Statistics
