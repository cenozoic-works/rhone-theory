/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.DelayedPrefixHistory
public import Rhone.Statistics.Identifiability.PositiveEdgeExposure
public import Rhone.Statistics.Identifiability.SimultaneousOnsetBounds

/-! # Required prefix masses are positive by literal migration/recombination exposure -/

@[expose] public section

open Set MeasureTheory
open scoped BigOperators Topology Matrix
namespace Rhone.Statistics.Identifiability
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma inhomogeneousTransition_diagonal_positive (Q : ℝ → Matrix ι ι ℝ)
    (hQ : ∀ i j, Continuous (fun t => Q t i j))
    (hQn : ∀ u, 0 ≤ u → ∀ i j, i ≠ j → 0 ≤ Q u i j)
    (i : ι) {t : ℝ} (ht : 0 ≤ t) : 0 < inhomogeneousTransition Q 0 t i i := by
  apply inhomogeneous_row_coordinate_positive Q (fun u => inhomogeneousTransition Q 0 u i) i
    (hQ i i) (fun u hu l hli => hQn u hu l i hli)
    (fun u _ => inhomogeneousTransition_hasDerivAt_right Q hQ 0 u i i)
    (fun u hu l => inhomogeneousTransition_nonneg Q hQ hQn le_rfl hu i l) _ ht
  simp [inhomogeneousTransition_self Q hQ]

lemma inhomogeneousTransition_positive_of_edge_exposure (Q : ℝ → Matrix ι ι ℝ)
    (hQ : ∀ i j, Continuous (fun t => Q t i j))
    (hQn : ∀ u, 0 ≤ u → ∀ i j, i ≠ j → 0 ≤ Q u i j)
    (i j : ι) (hij : i ≠ j) {t : ℝ} (ht : 0 ≤ t)
    (hexp : 0 < ∫ u in (0 : ℝ)..t, Q u i j) :
    0 < inhomogeneousTransition Q 0 t i j := by
  apply inhomogeneous_row_positive_of_edge_exposure Q
    (fun u => inhomogeneousTransition Q 0 u i) hQ hQn
    (fun u l => inhomogeneousTransition_hasDerivAt_right Q hQ 0 u i l)
    (fun u hu l => inhomogeneousTransition_nonneg Q hQ hQn le_rfl hu i l) i j hij _ ht hexp
  simp [inhomogeneousTransition_self Q hQ]

namespace DelayedOnset
open SimultaneousOnset

lemma pairRow_together_positive (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hqn : ∀ u, 0 ≤ u → 0 ≤ q u)
    {t : ℝ} (ht : 0 ≤ t) : 0 < pairRow k c q t 0 :=
  inhomogeneousTransition_diagonal_positive _ (pairGenerator_continuous k c q hc hq)
    (fun u hu => pairGenerator_metzler k (hqn u hu)) 0 ht

lemma pairRow_apart_positive (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hqn : ∀ u, 0 ≤ u → 0 ≤ q u)
    {t : ℝ} (ht : 0 ≤ t) (hexp : 0 < ∫ u in (0 : ℝ)..t, q u) :
    0 < pairRow k c q t 1 := by
  apply inhomogeneousTransition_positive_of_edge_exposure _
    (pairGenerator_continuous k c q hc hq)
    (fun u hu => pairGenerator_metzler k (hqn u hu)) 0 1 (by decide) ht
  simp only [MarkovChain.Identifiability.pairGenerator, Matrix.cons_val_zero, Matrix.cons_val_one,
    MarkovChain.Identifiability.totalMigration]
  have he : (fun u => 2 * ((k + 1 : ℝ) * q u)) =
      fun u => (2 * (k + 1 : ℝ)) * q u := by funext u; ring
  rw [he, intervalIntegral.integral_const_mul]
  positivity

lemma preRow_recombined_positive (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r)
    (hcn : ∀ u, 0 ≤ u → 0 ≤ c u) (hqn : ∀ u, 0 ≤ u → 0 ≤ q u)
    (hrn : ∀ u, 0 ≤ u → 0 ≤ r u) {t : ℝ} (ht : 0 ≤ t)
    (hexp : 0 < ∫ u in (0 : ℝ)..t, r u) : 0 < preRow k c q r t 2 := by
  apply inhomogeneousTransition_positive_of_edge_exposure _
    (preGenerator_continuous k c q r hc hq hr)
    (fun u hu => generator_metzler k (hcn u hu) (hqn u hu) (hrn u hu)) 0 2 (by decide) ht
  have he (u : ℝ) : MarkovChain.Identifiability.generator k (c u) (q u) (r u) 0 2 = 2 * r u := by
    simp [MarkovChain.Identifiability.generator, MarkovChain.Identifiability.coalescenceTable,
        MarkovChain.Identifiability.recombinationTable, MarkovChain.Identifiability.occupiedTable,
      MarkovChain.Identifiability.emptyTable, MarkovChain.Identifiability.occupiedDemes, mul_comm]
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul]
  positivity

end DelayedOnset
end Rhone.Statistics.Identifiability
