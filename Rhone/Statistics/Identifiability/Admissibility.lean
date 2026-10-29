/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.Cemetery

/-! # Invariance of the admissible state set under the island flow -/

@[expose] public section

open scoped Matrix Matrix.Norms.Operator
namespace Rhone.Statistics.Identifiability

def Admissible (k : Nat) (i : MarkovChain.Identifiability.State) : Prop :=
    MarkovChain.Identifiability.occupiedDemes i ≤ k + 2

theorem event_deme_support : ∀ i j : MarkovChain.Identifiability.State,
    (MarkovChain.Identifiability.occupiedDemes i < MarkovChain.Identifiability.occupiedDemes j →
      MarkovChain.Identifiability.coalescenceTable i j = 0 ∧
          MarkovChain.Identifiability.recombinationTable i j = 0 ∧
          MarkovChain.Identifiability.occupiedTable i j = 0) ∧
    (MarkovChain.Identifiability.occupiedDemes i + 1 < MarkovChain.Identifiability.occupiedDemes j →
        MarkovChain.Identifiability.emptyTable i j = 0) := by
  intro i
  fin_cases i <;> decide

theorem initial_admissible (k : Nat) : Admissible k 0 := by
  change 1 ≤ k + 2
  omega

theorem generator_no_escape (k : Nat) (c q r : ℝ) (i j : MarkovChain.Identifiability.State)
    (hi : Admissible k i) (hj : ¬ Admissible k j) : MarkovChain.Identifiability.generator k c q r i
        j = 0 := by
  have hij : MarkovChain.Identifiability.occupiedDemes i < MarkovChain.Identifiability.occupiedDemes
      j := by
    unfold Admissible at hi hj
    omega
  obtain ⟨hC, hR, hO⟩ := (event_deme_support i j).1 hij
  by_cases h : MarkovChain.Identifiability.occupiedDemes i = k + 2
  · simp [MarkovChain.Identifiability.generator, hC, hR, hO, h]
  · have hE := (event_deme_support i j).2 (by unfold Admissible at hi hj; omega)
    simp [MarkovChain.Identifiability.generator, hC, hR, hO, hE]

theorem matrix_power_no_escape {d : Nat} (Q : Matrix (Fin d) (Fin d) ℝ)
    (P : Fin d → Prop) (hQ : ∀ i j, P i → ¬ P j → Q i j = 0) (n : Nat) :
    ∀ i j, P i → ¬ P j → (Q ^ n) i j = 0 := by
  classical
  induction n with
  | zero =>
    intro i j hi hj
    have hij : i ≠ j := fun h => hj (h ▸ hi)
    simp [hij]
  | succ n ih =>
    intro i j hi hj
    rw [pow_succ', Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro a _
    by_cases ha : P a
    · rw [ih a j ha hj, mul_zero]
    · rw [hQ i a hi ha, zero_mul]

set_option backward.isDefEq.respectTransparency false in
theorem matrix_exp_no_escape {d : Nat} (Q : Matrix (Fin d) (Fin d) ℝ)
    (P : Fin d → Prop) (hQ : ∀ i j, P i → ¬ P j → Q i j = 0)
    (t : ℝ) (i j : Fin d) (hi : P i) (hj : ¬ P j) :
    NormedSpace.exp (t • Q) i j = 0 := by
  have htQ : ∀ a b, P a → ¬ P b → (t • Q) a b = 0 := by
    intro a b ha hb
    simp [hQ a b ha hb]
  have h := exp_entry_hasSum (t • Q) i j
  simp only [matrix_power_no_escape _ P htQ _ i j hi hj, mul_zero] at h
  exact h.unique hasSum_zero

theorem island_exp_admissible (k : Nat) (c q r t : ℝ) (j : MarkovChain.Identifiability.State)
    (hj : ¬ Admissible k j) :
    NormedSpace.exp (t • MarkovChain.Identifiability.generator k c q r) 0 j = 0 :=
  matrix_exp_no_escape _ (Admissible k) (generator_no_escape k c q r)
    t 0 j (initial_admissible k) hj

end Rhone.Statistics.Identifiability
