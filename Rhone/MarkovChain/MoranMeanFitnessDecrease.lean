/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Dynamics.TwoLocusSelection

/-!
# Mean fitness decrease in Moran's published fitness scheme

Source: moran1967_unsolved_evolutionary_theory, Table 86, p. 477;
moran1967_unsolved_evolutionary_theory, eq. 49–53, pp. 470–471. -/

@[expose] public section
namespace Rhone.MarkovChain.MoranMeanFitnessDecrease
open Rhone.Dynamics Dynamics.TwoLocusSelection

/-- Source: moran1967_unsolved_evolutionary_theory, Table 86, p. 477, eq. 53, p. 471. -/
def table86Fitness (a : ℝ) : Fin 4 → Fin 4 → ℝ :=
  ![![1,2,2,a],![2,1,a,2],![2,a,1,2],![a,2,2,1]]

noncomputable def couplingParental : Gametes ℝ := ⟨1/2,0,0,1/2⟩

/-- Source: moran1967_unsolved_evolutionary_theory, Table 86, p. 477. -/
theorem table86_admissible (a : ℝ) (ha : 0 < a) :
    (∀ i, 0 ≤ vector couplingParental i) ∧ couplingParental.total = 1 ∧
    (∀ i j, 0 ≤ table86Fitness a i j) ∧
    (∀ i j, table86Fitness a i j = table86Fitness a j i) ∧
    table86Fitness a 0 3 = table86Fitness a 1 2 ∧
    0 < multiMeanFit (table86Fitness a) (vector couplingParental) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i <;> norm_num [vector, couplingParental]
  · norm_num [couplingParental, Gametes.total]
  · intro i j
    fin_cases i <;> fin_cases j <;> norm_num [table86Fitness] <;> exact ha.le
  · intro i j; fin_cases i <;> fin_cases j <;> rfl
  · rfl
  · norm_num [multiMeanFit, marginalFit, table86Fitness, vector,
      couplingParental, Fin.sum_univ_four]
    linarith

/-- Source: moran1967_unsolved_evolutionary_theory, eq. 49–53, pp. 470–471, Table 86, p. 477. -/
theorem coupling_step (a : ℝ) (ha : 0 < a) :
    step (table86Fitness a) (1/2) couplingParental =
      ⟨(a+2)/(4*(a+1)),a/(4*(a+1)),a/(4*(a+1)),(a+2)/(4*(a+1))⟩ := by
  have hmean : (1 / 2 + a / 2 : ℝ) ≠ 0 := by linarith
  have hden : a + 1 ≠ 0 := by linarith
  norm_num [step, fromVector, vector, couplingParental, table86Fitness,
    sign, multiMeanFit, marginalFit, Gametes.D, Fin.sum_univ_four]
  repeat' constructor
  all_goals field_simp; ring

/-- Source: moran1967_unsolved_evolutionary_theory, eq. 49–52, p. 470. -/
theorem table86_step_simplex (a : ℝ) (ha : 0 < a) :
    (∀ i, 0 ≤ vector (step (table86Fitness a) (1/2) couplingParental) i) ∧
    (step (table86Fitness a) (1/2) couplingParental).total = 1 := by
  obtain ⟨hg, ht, hW, hsym, hpos, hmean⟩ := table86_admissible a ha
  exact step_simplex (table86Fitness a) (1/2) couplingParental
    hg ht hW hsym hpos (by norm_num) le_rfl hmean

/-- Source: moran1967_unsolved_evolutionary_theory, eq. 49–53, pp. 470–471, Table 86, p. 477. -/
theorem mean_fitness_drop (a : ℝ) (ha : 0 < a) :
    multiMeanFit (table86Fitness a) (vector couplingParental) -
      multiMeanFit (table86Fitness a)
        (vector (step (table86Fitness a) (1/2) couplingParental)) =
      a*(a-3)*(a+2)/(4*(a+1)^2) := by
  rw [coupling_step a ha]
  have hden : a + 1 ≠ 0 := by linarith
  norm_num [multiMeanFit, marginalFit, table86Fitness, vector,
    couplingParental, Fin.sum_univ_four]
  field_simp
  ring

/--
Source: moran1967_unsolved_evolutionary_theory, Table 86, p. 477; moran1964_adaptive_topographies,
pp. 389–390; felsenstein_teg2019, p. 376. -/
theorem mean_fitness_decreases (a : ℝ) (ha : 3 < a) :
    multiMeanFit (table86Fitness a)
        (vector (step (table86Fitness a) (1/2) couplingParental)) <
      multiMeanFit (table86Fitness a) (vector couplingParental) := by
  have ha0 : 0 < a := by linarith
  have hdrop := mean_fitness_drop a ha0
  have hpos : 0 < a*(a-3)*(a+2)/(4*(a+1)^2) := by positivity
  linarith

/-- Source: moran1967_unsolved_evolutionary_theory, Table 86, p. 477. -/
theorem multiplicative_case :
    step (table86Fitness 4) (1/2) couplingParental = ⟨3/10,1/5,1/5,3/10⟩ ∧
    multiMeanFit (table86Fitness 4) (vector couplingParental) = 5/2 ∧
    multiMeanFit (table86Fitness 4)
      (vector (step (table86Fitness 4) (1/2) couplingParental)) = 113/50 ∧
    multiMeanFit (table86Fitness 4)
        (vector (step (table86Fitness 4) (1/2) couplingParental)) <
      multiMeanFit (table86Fitness 4) (vector couplingParental) := by
  have hs : step (table86Fitness 4) (1/2) couplingParental = ⟨3/10,1/5,1/5,3/10⟩ := by
    have h := coupling_step 4 (by norm_num)
    norm_num at h
    exact h
  refine ⟨hs, ?_, ?_, mean_fitness_decreases 4 (by norm_num)⟩
  · norm_num [multiMeanFit, marginalFit, table86Fitness, vector,
      couplingParental, Fin.sum_univ_four]
  · rw [hs]
    norm_num [multiMeanFit, marginalFit, table86Fitness, vector, Fin.sum_univ_four]

end Rhone.MarkovChain.MoranMeanFitnessDecrease
