/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.WFLDHeterozygosityPositive

/-!
# First-locus heterozygosity under finite sampling and mutation

Source: ewens2004, sec. 3.1. -/

@[expose] public section
noncomputable section
namespace Rhone.MarkovChain.WFAllocationLD
open Finset

/-- Source: ewens2004, sec. 3.1. -/
def ldMarginalH (g : Dynamics.Gametes ℝ) : ℝ := g.pA*(1-g.pA)

/-- Source: ewens2004, sec. 3.1. -/
theorem count_marginal_heterozygosity_nonneg (M : ℕ) (hM : 0 < M)
    (a : Rhone.MarkovChain.AlleleCounts M 4) : 0 ≤ ldMarginalH (countGametes M a) := by
  unfold ldMarginalH
  rw [← Dynamics.Gametes.pA'_eq (count_gametes_total M hM a)]
  unfold Dynamics.Gametes.pA Dynamics.Gametes.pA' countGametes Dynamics.TwoLocusSelection.fromVector
  positivity

/-- Source: ewens2004, sec. 3.1. -/
theorem sampling_marginal_heterozygosity (M : ℕ) (hM : 0 < M) (g : Dynamics.Gametes ℝ)
    (ht : g.total = 1) :
    samplingExpectation M g (fun a => ldMarginalH (countGametes M a)) =
      (1-1/(M : ℝ))*ldMarginalH g := by
  have ha := allocation_raw_moments M g ht
  have e1 := congrFun ha 1
  have e4 := congrFun ha 4
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at e1 e4
  have hp (a : Rhone.MarkovChain.AlleleCounts M 4) : ldMarginalH (countGametes M a) =
      rawCountFeatures M a 1 / M - rawCountFeatures M a 4 / (M : ℝ)^2 := by
    unfold ldMarginalH countGametes Dynamics.TwoLocusSelection.fromVector Dynamics.Gametes.pA
      rawCountFeatures rawFeatures
    norm_num
    field_simp [Nat.cast_ne_zero.mpr hM.ne']
  rw [sampling_expectation_allocation]
  simp_rw [hp, mul_sub, ← mul_div_assoc]
  rw [sum_sub_distrib, ← sum_div, ← sum_div, e1, e4]
  norm_num [rawMomentFormula, ldMarginalH]
  field_simp [Nat.cast_ne_zero.mpr hM.ne']
  ring

/-- Source: ewens2004, sec. 3.2, eq. (3.24), (3.28), pp. 96–98. -/
theorem forced_marginal_heterozygosity (c u : ℝ) (g : Dynamics.Gametes ℝ) (ht : g.total = 1) :
    ldMarginalH (forcedGametes c u g) = u*(1-u)+(1-2*u)^2*ldMarginalH g := by
  have hh : g.x22 = 1-g.x11-g.x12-g.x21 := by unfold Dynamics.Gametes.total at ht; linarith
  norm_num [ldMarginalH, forcedGametes, independentMutation, Dynamics.TwoLocusSelection.fromVector,
    Dynamics.TwoLocusSelection.vector, Fin.sum_univ_four, firstIndex, secondIndex,
    Rhone.Dynamics.MutationModels.pimTransition, Dynamics.Gametes.recombine,
    Dynamics.Gametes.pA, Dynamics.Gametes.pB, Dynamics.Gametes.pA', Dynamics.Gametes.pB']
  rw [hh]
  ring

/-- Source: ewens2004, sec. 3.1. -/
theorem ld_stationary_marginal_heterozygosity_bound (M : ℕ) (hM : 0 < M) (c u : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2)
    (π : Rhone.MarkovChain.AlleleCounts M 4 → ℝ) (hπ : ∀ a, 0 ≤ π a) (hnorm : ∑ a, π a = 1)
    (hstat : ∀ b, ∑ a, π a * forcedCountKernel M c u a b = π b) :
    (∑ a, π a*ldMarginalH (countGametes M a)) ≤ ((M : ℝ)-1)*u := by
  let H := ∑ a, π a*ldMarginalH (countGametes M a)
  have hH : 0 ≤ H := sum_nonneg fun a _ =>
    mul_nonneg (hπ a) (count_marginal_heterozygosity_nonneg M hM a)
  have ht (a : Rhone.MarkovChain.AlleleCounts M 4) :
      (forcedGametes c u (countGametes M a)).total = 1 := by
    have hg : ∀ i, 0 ≤ Dynamics.TwoLocusSelection.vector (countGametes M a) i := by
      intro i
      fin_cases i <;> change 0 ≤ (_ : ℝ)/M <;> positivity
    exact (forced_gametes_distribution c u _ hc0 hc1 hu0 hu1 hg (count_gametes_total M hM a)).2
  have he : H = (1-1/(M : ℝ))*(u*(1-u)+(1-2*u)^2*H) := by
    calc
      H = ∑ a, π a*samplingExpectation M (forcedGametes c u (countGametes M a))
          (fun b => ldMarginalH (countGametes M b)) := by
        symm
        unfold samplingExpectation H
        simp_rw [mul_sum, ← mul_assoc]
        rw [sum_comm]
        simp_rw [← sum_mul]
        exact sum_congr rfl fun b _ =>
          congrArg (fun r => r*ldMarginalH (countGametes M b)) (hstat b)
      _ = _ := by
        simp_rw [sampling_marginal_heterozygosity M hM _ (ht _),
          forced_marginal_heterozygosity c u _ (count_gametes_total M hM _)]
        have hreorder (a : Rhone.MarkovChain.AlleleCounts M 4) :
            π a*((1-1/(M : ℝ))*(u*(1-u)+(1-2*u)^2*ldMarginalH (countGametes M a))) =
            (1-1/(M : ℝ))*(π a*(u*(1-u))+(1-2*u)^2*(π a*ldMarginalH (countGametes M a))) := by
          ring
        simp_rw [hreorder]
        rw [← mul_sum, sum_add_distrib, ← sum_mul, ← mul_sum, hnorm]
        dsimp only [H]
        ring
  have hM1 : 0 ≤ (M : ℝ)-1 := by
    have hh : (1 : ℝ) ≤ M := by exact_mod_cast (by omega : 1 ≤ M)
    linarith
  have hu : 0 ≤ 1-2*u := by linarith
  have hu' : 1-2*u ≤ 1 := by linarith
  have hb : (1-2*u)^2 ≤ 1 := pow_le_one₀ hu hu'
  have ha : u*(1-u) ≤ u := by nlinarith [sq_nonneg u]
  have hA := mul_le_mul_of_nonneg_left ha hM1
  have hB := mul_le_mul_of_nonneg_left hb (mul_nonneg hM1 hH)
  field_simp [Nat.cast_ne_zero.mpr hM.ne'] at he
  change H ≤ ((M : ℝ)-1)*u
  nlinarith only [he,hA,hB]

end Rhone.MarkovChain.WFAllocationLD
