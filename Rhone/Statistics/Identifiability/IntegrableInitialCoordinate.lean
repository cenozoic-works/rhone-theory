/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.IntegrableTransitionStochastic
public import Rhone.Statistics.Identifiability.IntegrableMarkovCoordinate

/-! # A positive initial state retains positive mass under locally L1 Metzler evolution -/

@[expose] public section

noncomputable section
open Set Filter Matrix MeasureTheory
open scoped BigOperators Topology Matrix
namespace Rhone.Statistics.Identifiability
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma integrableTransition_initial_diagonal_positive (Q : ℝ → Matrix ι ι ℝ)
    (hQi : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume)
    (hQ : ∀ᵐ t, 0 ≤ t → ∀ i j, i ≠ j → 0 ≤ Q t i j)
    (i : ι) {t : ℝ} (ht : 0 ≤ t) : 0 < inhomogeneousTransition Q 0 t i i := by
  apply integrable_row_coordinate_pos Q (fun u => inhomogeneousTransition Q 0 u i) i hQ
    (fun u _ j => integrableTransition_entry_ac_right Q hQi 0 0 u i j) _
    (fun u hu j => integrableTransition_nonneg Q hQi hQ le_rfl hu i j) (hQi i i) _ ht
  · filter_upwards [integrableTransition_ae_hasDerivAt_right Q hQi] with u hu _ j
    exact hu 0 i j
  · simp [integrableTransition_self Q hQi]

end Rhone.Statistics.Identifiability
