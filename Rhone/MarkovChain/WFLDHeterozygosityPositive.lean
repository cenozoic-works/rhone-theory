/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.WFLDStationaryMoments

/-!
# Positivity of finite two-locus heterozygosity-product expectations

Source: ewens2004, sec. 3.1. -/

@[expose] public section
noncomputable section
namespace Rhone.MarkovChain.WFAllocationLD
open Finset

theorem independent_mutation_lower_bound (u : ℝ) (g : Dynamics.Gametes ℝ)
    (hu0 : 0 < u) (hu1 : u ≤ 1 / 2)
    (hg : ∀ i, 0 ≤ Dynamics.TwoLocusSelection.vector g i) (ht : g.total = 1) (j : Fin 4) :
    u^2 ≤ Dynamics.TwoLocusSelection.vector (independentMutation u g) j := by
  have hm (i j : Fin 2) : u ≤
      Rhone.Dynamics.MutationModels.pimTransition (2*u) (fun _ : Fin 2 => 1/2) i j := by
    by_cases h : i=j
    · simp only [Rhone.Dynamics.MutationModels.pimTransition, h, ite_true]
      linarith
    · simp only [Rhone.Dynamics.MutationModels.pimTransition, h, ite_false]
      linarith
  have hv : Dynamics.TwoLocusSelection.vector (independentMutation u g) j =
      ∑ i : Fin 4, Dynamics.TwoLocusSelection.vector g i *
        Rhone.Dynamics.MutationModels.pimTransition (2*u) (fun _ : Fin 2 => 1/2)
          (firstIndex i) (firstIndex j) *
        Rhone.Dynamics.MutationModels.pimTransition (2*u) (fun _ : Fin 2 => 1/2)
          (secondIndex i) (secondIndex j) := by fin_cases j <;> rfl
  have ht' : ∑ i, Dynamics.TwoLocusSelection.vector g i = 1 := by
    simpa [Dynamics.TwoLocusSelection.vector, Fin.sum_univ_four, Dynamics.Gametes.total] using ht
  rw [hv]
  calc
    u^2 = ∑ i, Dynamics.TwoLocusSelection.vector g i*u^2 := by rw [← sum_mul, ht', one_mul]
    _ ≤ _ := by
      apply sum_le_sum
      intro i _
      have hprod := mul_le_mul (hm (firstIndex i) (firstIndex j))
        (hm (secondIndex i) (secondIndex j)) hu0.le
        (hu0.le.trans (hm (firstIndex i) (firstIndex j)))
      have hh := mul_le_mul_of_nonneg_left hprod (hg i)
      convert hh using 1 <;> ring

/-- Source: ewens2004, sec. 3.1. -/
theorem count_heterozygosity_nonneg (M : ℕ) (hM : 0 < M)
    (a : Rhone.MarkovChain.AlleleCounts M 4) : 0 ≤ momentStatistics (countGametes M a) 0 := by
  have ht := count_gametes_total M hM a
  change 0 ≤ (countGametes M a).pA*(1-(countGametes M a).pA)*
    (countGametes M a).pB*(1-(countGametes M a).pB)
  rw [← Dynamics.Gametes.pA'_eq ht, ← Dynamics.Gametes.pB'_eq ht]
  unfold countGametes Dynamics.TwoLocusSelection.fromVector Dynamics.Gametes.pA Dynamics.Gametes.pB
      Dynamics.Gametes.pA' Dynamics.Gametes.pB'
  positivity

/-- Source: ewens2004, sec. 3.1. -/
theorem allocation_heterozygosity_witness (M : ℕ) (hM : 2 ≤ M) :
    ∃ ω : Fin M → Fin 4,
      0 < momentStatistics (countGametes M (Rhone.MarkovChain.wfAlleleAllocationCounts M 4 ω)) 0 :=
          by
  have hM0 : 0 < M := by omega
  let z : Fin M := ⟨0,hM0⟩
  let ω : Fin M → Fin 4 := fun t => if t=z then 3 else 0
  let a := Rhone.MarkovChain.wfAlleleAllocationCounts M 4 ω
  have h1 : a.val 1 = 0 :=
      by simp [a, Rhone.MarkovChain.wfAlleleAllocationCounts_apply, ω, ite_eq_iff]
  have h2 : a.val 2 = 0 :=
      by simp [a, Rhone.MarkovChain.wfAlleleAllocationCounts_apply, ω, ite_eq_iff]
  have h3 : a.val 3 = 1 := by
    norm_num [a, Rhone.MarkovChain.wfAlleleAllocationCounts_apply, ω]
    simp [Finset.filter_eq']
  have hsum := a.sum_real
  norm_num [Fin.sum_univ_four, h1, h2, h3] at hsum
  have hnat := a.sum
  norm_num [Fin.sum_univ_four, h1, h2, h3] at hnat
  have h0 : 0 < (a.val 0 : ℝ) := by exact_mod_cast (by omega : 0 < a.val 0)
  have hfreq : 0 < (a.val 0 : ℝ)/M := div_pos h0 (by exact_mod_cast hM0)
  have hcomp : 0 < 1-(a.val 0 : ℝ)/M := by
    apply sub_pos.mpr
    rw [div_lt_one (by exact_mod_cast hM0)]
    linarith
  refine ⟨ω, ?_⟩
  change 0 < (countGametes M a).pA*(1-(countGametes M a).pA)*
    (countGametes M a).pB*(1-(countGametes M a).pB)
  have hp : (countGametes M a).pA = (a.val 0 : ℝ)/M := by
    simp [countGametes, Dynamics.TwoLocusSelection.fromVector, Dynamics.Gametes.pA, h1]
  have hq : (countGametes M a).pB = (a.val 0 : ℝ)/M := by
    simp [countGametes, Dynamics.TwoLocusSelection.fromVector, Dynamics.Gametes.pB, h2]
  rw [hp,hq]
  exact mul_pos (mul_pos (mul_pos hfreq hcomp) hfreq) hcomp

/-- Source: ewens2004, sec. 3.1. -/
theorem sampling_heterozygosity_pos (M : ℕ) (hM : 2 ≤ M) (g : Dynamics.Gametes ℝ)
    (hg : ∀ i, 0 < Dynamics.TwoLocusSelection.vector g i) :
    0 < samplingExpectation M g (fun a => momentStatistics (countGametes M a) 0) := by
  have hM0 : 0 < M := by omega
  rw [sampling_expectation_allocation]
  apply sum_pos'
  · intro ω _
    exact mul_nonneg (prod_nonneg fun t _ => (hg (ω t)).le)
      (count_heterozygosity_nonneg M hM0 _)
  · obtain ⟨ω, hω⟩ := allocation_heterozygosity_witness M hM
    exact ⟨ω, mem_univ ω, mul_pos (prod_pos fun t _ => hg (ω t)) hω⟩

/-- Source: ewens2004, sec. 3.1. -/
theorem ld_stationary_heterozygosity_pos (M : ℕ) (hM : 2 ≤ M) (c u : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hu0 : 0 < u) (hu1 : u < 1 / 2)
    (π : Rhone.MarkovChain.AlleleCounts M 4 → ℝ) (hπ : ∀ a, 0 ≤ π a) (hnorm : ∑ a, π a = 1)
    (hstat : ∀ b, ∑ a, π a * forcedCountKernel M c u a b = π b) :
    0 < ldStationaryMoments M π 0 := by
  have hM0 : 0 < M := by omega
  have hf (a : Rhone.MarkovChain.AlleleCounts M 4) :
      ∀ i, 0 < Dynamics.TwoLocusSelection.vector (forcedGametes c u (countGametes M a)) i := by
    have hg : ∀ i, 0 ≤ Dynamics.TwoLocusSelection.vector (countGametes M a) i := by
      intro i
      fin_cases i <;> change 0 ≤ (_ : ℝ)/M <;> positivity
    have hr := Dynamics.Gametes.recombine_nonneg hc0 hc1 (hg 0) (hg 1) (hg 2) (hg 3)
    have hr' : ∀ i, 0 ≤ Dynamics.TwoLocusSelection.vector ((countGametes M a).recombine c) i := by
      intro i
      fin_cases i
      · exact hr.1
      · exact hr.2.1
      · exact hr.2.2.1
      · exact hr.2.2.2
    intro i
    exact lt_of_lt_of_le (sq_pos_of_pos hu0)
      (independent_mutation_lower_bound u _ hu0 hu1.le hr'
        (Dynamics.Gametes.total_recombine c (count_gametes_total M hM0 a)) i)
  have hsample (a : Rhone.MarkovChain.AlleleCounts M 4) := sampling_heterozygosity_pos M hM _ (hf a)
  have he : (∑ a, π a*samplingExpectation M (forcedGametes c u (countGametes M a))
      (fun b => momentStatistics (countGametes M b) 0)) = ldStationaryMoments M π 0 := by
    unfold samplingExpectation ldStationaryMoments
    simp_rw [mul_sum, ← mul_assoc]
    rw [sum_comm]
    simp_rw [← sum_mul]
    exact sum_congr rfl fun b _ =>
      congrArg (fun r => r*momentStatistics (countGametes M b) 0) (hstat b)
  rw [← he]
  apply sum_pos'
  · exact fun a _ => mul_nonneg (hπ a) (hsample a).le
  · have hex : ∃ a, 0 < π a := by
      by_contra hh
      push Not at hh
      have hs : ∑ a, π a ≤ 0 := sum_nonpos fun a _ => hh a
      linarith
    obtain ⟨a, ha⟩ := hex
    exact ⟨a, mem_univ a, mul_pos ha (hsample a)⟩

end Rhone.MarkovChain.WFAllocationLD
