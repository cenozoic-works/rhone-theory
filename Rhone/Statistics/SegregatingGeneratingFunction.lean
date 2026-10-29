/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Statistics.TreeLengthLaplace
public import Rhone.Statistics.SegregatingMarkingTransfer
public import Rhone.Probability.PoissonGeneratingFunction

/-!
# Generating function of the segregating-site count under the marked Kingman law

Source: watterson1975, p. 258, eq. (1.3a); tajima1989, p. 588, eq. (40)–(41). -/

@[expose] public section
namespace Rhone.Statistics
open MeasureTheory ProbabilityTheory Finset MarkovChain Coalescent Rhone.Combinatorics Probability
open scoped NNReal ENNReal

/-- Source: watterson1975, p. 264, eq. (2.2)–(2.3). -/
theorem integral_kingmanBranchMutationKernel_pow_sum (n : ℕ) (θ : ℝ≥0)
    (h : KingmanMutationHistory n) (z : ℝ) :
    ∫ m, z ^ (∑ b, m b) ∂kingmanBranchMutationKernel n θ h =
      Real.exp (-((θ : ℝ) / 2 *
        kingmanFiniteReward n (fun π => (π.parts.card : ℝ)) h * (1 - z))) := by
  change (∫ m : KingmanMutationBranch n → ℕ, z ^ (∑ b, m b)
    ∂Measure.pi (fun b => poissonMeasure (kingmanBranchMutationRate n θ h b))) = _
  rw [pi_poisson_integral_pow_sum, sum_kingmanBranchMutationRate]

/-- Source: watterson1975, p. 264, eq. (2.2)–(2.3). -/
theorem kingmanBranchMutationKernel_real_sum_eq (n : ℕ) (θ : ℝ≥0)
    (h : KingmanMutationHistory n) (k : ℕ) :
    (kingmanBranchMutationKernel n θ h).real
        {m : KingmanMutationBranch n → ℕ | ∑ b, m b = k} =
      Real.exp (-((θ : ℝ) / 2 * kingmanFiniteReward n (fun π => (π.parts.card : ℝ)) h)) *
        ((θ : ℝ) / 2 * kingmanFiniteReward n (fun π => (π.parts.card : ℝ)) h) ^ k /
          (k.factorial : ℝ) := by
  change (Measure.pi (fun b => poissonMeasure (kingmanBranchMutationRate n θ h b))).real
    {m : KingmanMutationBranch n → ℕ | ∑ b, m b = k} = _
  rw [pi_poisson_real_sum_eq, sum_kingmanBranchMutationRate]

theorem measurableSet_markedKingman_sum_eq (n k : ℕ) :
    MeasurableSet {x : KingmanMutationHistory n × (KingmanMutationBranch n → ℕ) |
      ∑ b, x.2 b = k} := by
  have hm : Measurable (fun x : KingmanMutationHistory n × (KingmanMutationBranch n → ℕ) =>
      ∑ b, x.2 b) := by fun_prop
  exact hm (measurableSet_singleton k)

/-- Source: watterson1975, p. 264, eq. (2.2)–(2.3). -/
theorem markedKingmanLaw_real_sum_eq (n : ℕ) (θ : ℝ≥0) (k : ℕ) :
    (markedKingmanLaw n θ).real {x | ∑ b, x.2 b = k} =
      ∫ h, Real.exp (-((θ : ℝ) / 2 *
          kingmanFiniteReward n (fun π => (π.parts.card : ℝ)) h)) *
        ((θ : ℝ) / 2 * kingmanFiniteReward n (fun π => (π.parts.card : ℝ)) h) ^ k /
          (k.factorial : ℝ) ∂(partitionChain (Fin n)).jumpHoldLaw ⊥ := by
  have hS := measurableSet_markedKingman_sum_eq n k
  have hSm : MeasurableSet {m : KingmanMutationBranch n → ℕ | ∑ b, m b = k} :=
    MeasurableSet.of_discrete
  have hI : Integrable
      ({x : KingmanMutationHistory n × (KingmanMutationBranch n → ℕ) |
        ∑ b, x.2 b = k}.indicator
        (1 : KingmanMutationHistory n × (KingmanMutationBranch n → ℕ) → ℝ))
      (((partitionChain (Fin n)).jumpHoldLaw ⊥).compProd
        (kingmanBranchMutationKernel n θ)) :=
    (integrable_const (1 : ℝ)).indicator hS
  rw [← integral_indicator_one hS,
    show markedKingmanLaw n θ =
      ((partitionChain (Fin n)).jumpHoldLaw ⊥).compProd
        (kingmanBranchMutationKernel n θ) from rfl,
    Measure.integral_compProd hI]
  apply integral_congr_ae
  refine ae_of_all _ fun h => ?_
  refine Eq.trans ?_ (kingmanBranchMutationKernel_real_sum_eq n θ h k)
  refine Eq.trans ?_ (integral_indicator_one hSm)
  rfl

/-- Source: watterson1975, p. 258, eq. (1.3a); tajima1989, p. 588, eq. (40)–(41). -/
theorem markedKingmanSegregating_pgf (n : ℕ) (θ : ℝ≥0) {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    ∫ x, z ^ (∑ b, x.2 b) ∂markedKingmanLaw n θ =
      ∏ j ∈ Icc 1 (n - 1), (j : ℝ) / ((j : ℝ) + (θ : ℝ) * (1 - z)) := by
  have hmeas : Measurable
      (fun x : KingmanMutationHistory n × (KingmanMutationBranch n → ℕ) =>
        z ^ (∑ b, x.2 b)) :=
    (Measurable.of_discrete (f := fun k : ℕ => z ^ k)).comp (by fun_prop)
  have hint : Integrable
      (fun x : KingmanMutationHistory n × (KingmanMutationBranch n → ℕ) =>
        z ^ (∑ b, x.2 b)) (markedKingmanLaw n θ) := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) hmeas.aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hz0 _)]
    exact pow_le_one₀ hz0 hz1
  have hs : 0 ≤ (θ : ℝ) / 2 * (1 - z) :=
    mul_nonneg (by positivity) (sub_nonneg.mpr hz1)
  have hL := laplace_partitionTreeLength n hs
  rw [show markedKingmanLaw n θ =
      ((partitionChain (Fin n)).jumpHoldLaw ⊥).compProd
        (kingmanBranchMutationKernel n θ) from rfl,
    Measure.integral_compProd hint]
  have hin : ∀ h : KingmanMutationHistory n,
      ∫ m, z ^ (∑ b, m b) ∂kingmanBranchMutationKernel n θ h =
        Real.exp (-((θ : ℝ) / 2 *
          kingmanFiniteReward n (fun π => (π.parts.card : ℝ)) h * (1 - z))) :=
    fun h => integral_kingmanBranchMutationKernel_pow_sum n θ h z
  refine (integral_congr_ae (ae_of_all _ hin)).trans ?_
  have hprod : ∏ j ∈ Icc 1 (n - 1), (j : ℝ) / ((j : ℝ) + (θ : ℝ) * (1 - z)) =
      ∏ j ∈ Icc 1 (n - 1), (j : ℝ) / ((j : ℝ) + 2 * ((θ : ℝ) / 2 * (1 - z))) := by
    apply Finset.prod_congr rfl
    intro j _
    congr 2
    ring
  rw [hprod, ← hL]
  apply integral_congr_ae
  filter_upwards [partitionTreeLength_toReal_ae n] with h hh
  rw [hh]
  congr 2
  ring

/-- Source: watterson1975, p. 259, eq. (1.6a); tajima1989, p. 588, eq. (40)–(41). -/
theorem markedKingman_no_segregating (n : ℕ) (θ : ℝ≥0) :
    (markedKingmanLaw n θ).real {x | ∀ b, x.2 b = 0} =
      ∏ j ∈ Icc 1 (n - 1), (j : ℝ) / ((j : ℝ) + (θ : ℝ)) := by
  have hset : {x : KingmanMutationHistory n × (KingmanMutationBranch n → ℕ) |
      ∀ b, x.2 b = 0} = {x | ∑ b, x.2 b = 0} := by
    refine Set.ext fun x => ?_
    simp
  have hs : 0 ≤ (θ : ℝ) / 2 := by positivity
  have hL := laplace_partitionTreeLength n hs
  have hprod : ∏ j ∈ Icc 1 (n - 1), (j : ℝ) / ((j : ℝ) + (θ : ℝ)) =
      ∏ j ∈ Icc 1 (n - 1), (j : ℝ) / ((j : ℝ) + 2 * ((θ : ℝ) / 2)) := by
    apply Finset.prod_congr rfl
    intro j _
    congr 2
    ring
  rw [hset, markedKingmanLaw_real_sum_eq, hprod, ← hL]
  apply integral_congr_ae
  filter_upwards [partitionTreeLength_toReal_ae n] with h hh
  rw [hh]
  simp

/-- Source: watterson1975, p. 259, eq. (1.8); tajima1989, p. 588, eq. (40)–(41). -/
theorem markedKingman_two_segregating_geometric (θ : ℝ≥0) (k : ℕ) :
    (markedKingmanLaw 2 θ).real {x | ∑ b, x.2 b = k} =
      (θ : ℝ) ^ k / (1 + (θ : ℝ)) ^ (k + 1) := by
  have hg : Measurable (fun t : ℝ => (θ : ℝ) ^ k / (k.factorial : ℝ) *
      ((max 0 t) ^ k * Real.exp (-((θ : ℝ) * max 0 t)))) := by fun_prop
  rw [markedKingmanLaw_real_sum_eq]
  have h1 : ∫ h, Real.exp (-((θ : ℝ) / 2 *
          kingmanFiniteReward 2 (fun π => (π.parts.card : ℝ)) h)) *
        ((θ : ℝ) / 2 * kingmanFiniteReward 2 (fun π => (π.parts.card : ℝ)) h) ^ k /
          (k.factorial : ℝ) ∂(partitionChain (Fin 2)).jumpHoldLaw ⊥ =
      ∫ p, (fun e : ℕ → ℝ => (fun t : ℝ => (θ : ℝ) ^ k / (k.factorial : ℝ) *
        ((max 0 t) ^ k * Real.exp (-((θ : ℝ) * max 0 t)))) (e 0)) p.2
        ∂(partitionChain (Fin 2)).jumpHoldLaw ⊥ := by
    apply integral_congr_ae
    filter_upwards [kingmanFiniteLength_ae_eq_clock_sum 2] with h hh
    have hsum : ∑ j : Fin (2 - 1), 2 / (((2 : ℕ) : ℝ) - 1 - (j : ℕ)) * max 0 (h.2 j) =
        2 * max 0 (h.2 0) := by
      change ∑ j : Fin 1, 2 / (((2 : ℕ) : ℝ) - 1 - (j : ℕ)) * max 0 (h.2 j) = _
      rw [Fin.sum_univ_one]
      norm_num
    rw [hh, hsum]
    have he : (θ : ℝ) / 2 * (2 * max 0 (h.2 0)) = (θ : ℝ) * max 0 (h.2 0) := by ring
    rw [he, mul_pow]
    ring
  rw [h1, integral_jumpHoldLaw_clock 2 (G := fun e : ℕ → ℝ =>
      (fun t : ℝ => (θ : ℝ) ^ k / (k.factorial : ℝ) *
        ((max 0 t) ^ k * Real.exp (-((θ : ℝ) * max 0 t)))) (e 0))
      (hg.comp (measurable_pi_apply 0)),
    integral_clockLaw_eval 0 hg, integral_const_mul,
    integral_pow_mul_exp_expMeasure_one (NNReal.coe_nonneg θ) k]
  have hk : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  field_simp

end Rhone.Statistics
