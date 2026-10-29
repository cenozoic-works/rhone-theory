/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Statistics.GaussianBulmerVariance
public import Rhone.MarkovChain.GaussianHouseOfCards

/-!
# Gaussian stabilizing selection and free assortment

Source: bulmer1971, eq. (17), (22), pp. 206, 208; bulmer1974, p. 282; turelli2017_infinitesimal,
sec. 4, p. 48. -/

@[expose] public section
noncomputable section
namespace Rhone.Statistics.GaussianBulmer
open MeasureTheory ProbabilityTheory GaussianBreeder

def stabilizingFitness (n : ℕ) (S : ℝ) (z : V n) : ℝ :=
  MarkovChain.GaussianHouseOfCards.gaussianFitness S (∑ i, z i)

theorem stabilizingFitness_measurable (n : ℕ) (S : ℝ) :
    Measurable (stabilizingFitness n S) := by
  unfold stabilizingFitness MarkovChain.GaussianHouseOfCards.gaussianFitness
  fun_prop

theorem stabilizingFitness_bounds (n : ℕ) (S : ℝ) (hS : 0 < S) (z : V n) :
    0 < stabilizingFitness n S z ∧ stabilizingFitness n S z ≤ 1 :=
  MarkovChain.GaussianHouseOfCards.gaussian_fitness_bounds S hS _

theorem stabilizing_mean_fitness_pos (n : ℕ) (G E : Matrix (Fin n) (Fin n) ℝ)
    (S : ℝ) (hS : 0 < S) (m : V n) :
    0 < gaussianMeanFitness n G E (stabilizingFitness n S) m := by
  have hi := bounded_fitness_integrable n G E _ (stabilizingFitness_measurable n S)
    (fun z => (stabilizingFitness_bounds n S hS z).1.le) 1
    (fun z => (stabilizingFitness_bounds n S hS z).2) m
  exact integral_exp_pos hi

theorem gaussian_stabilizing_free_assortment_variance (n : ℕ)
    (G E : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosSemidef) (hE : E.PosSemidef)
    (S : ℝ) (hS : 0 < S) (m : V n) :
    Var[fun z => ∑ i, z i;
      freelyAssortingOffspringLaw n G E (stabilizingFitness n S) m] =
      Var[fun q => ∑ i, gaussianBreedingValue q i;
        gaussianSelectedParentLaw n G E (stabilizingFitness n S) m]/2 +
        (∑ i, G i i)/2 := by
  exact gaussian_input_free_assortment_variance n G E hG hE _
    (stabilizingFitness_measurable n S)
    (fun z => (stabilizingFitness_bounds n S hS z).1.le) 1 zero_le_one
    (fun z => (stabilizingFitness_bounds n S hS z).2) m
    (stabilizing_mean_fitness_pos n G E S hS m)

end Rhone.Statistics.GaussianBulmer
