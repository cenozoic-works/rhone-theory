/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.Identifiability.EventKernel
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

/-! # Generator and exact low-order observable coefficients -/

@[expose] public section

open scoped Matrix

namespace Rhone.MarkovChain.Identifiability

noncomputable def totalMigration (k : Nat) (q : ℝ) : ℝ := (k + 1) * q

noncomputable def generator (k : Nat) (c q r : ℝ) : Matrix State State ℝ :=
  fun i j => c * (coalescenceTable i j : ℝ) +
    r * (recombinationTable i j : ℝ) + q * (occupiedTable i j : ℝ) +
    q * ((k + 2 - occupiedDemes i : Nat) : ℝ) * (emptyTable i j : ℝ)

noncomputable def firstA (c : ℝ) : State → ℝ :=
  fun i => c * (firstATable i : ℝ)

noncomputable def nextB (c : ℝ) : State → ℝ :=
  fun i => c ^ 2 * (firstAThenBTable i : ℝ)

noncomputable def pairGenerator (k : Nat) (c q : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  ![![-c - 2 * totalMigration k q, 2 * totalMigration k q], ![2*q, -2*q]]

noncomputable def pairSurvival : Fin 2 → ℝ := fun _ => 1
noncomputable def pairDensity (c : ℝ) : Fin 2 → ℝ := ![c, 0]

theorem row_zero (k : Nat) (c q r : ℝ) (v : State → ℝ) :
    (generator k c q r *ᵥ v) 0 =
      (-c - 2 * totalMigration k q - 2*r) * v 0 +
      2 * totalMigration k q * v 1 + 2*r * v 2 := by
  have hn : k + 2 - 1 = k + 1 := by omega
  simp [generator, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    coalescenceTable, recombinationTable, occupiedTable, emptyTable,
    occupiedDemes, totalMigration, hn]
  ring

@[simp] theorem firstA_initial (c : ℝ) : firstA c 0 = 0 := by
  simp [firstA, firstATable]

@[simp] theorem nextB_initial (c : ℝ) : nextB c 0 = 0 := by
  simp [nextB, firstAThenBTable]

theorem firstA_row_one (k : Nat) (c q r : ℝ) :
    (generator k c q r *ᵥ firstA c) 1 = 0 := by
  simp [generator, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    coalescenceTable, recombinationTable, occupiedTable, emptyTable,
    occupiedDemes, firstA, firstATable]

theorem nextB_row_one (k : Nat) (c q r : ℝ) :
    (generator k c q r *ᵥ nextB c) 1 = 0 := by
  simp [generator, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    coalescenceTable, recombinationTable, occupiedTable, emptyTable,
    occupiedDemes, nextB, firstAThenBTable]

theorem firstA_row_two (k : Nat) (c q r : ℝ) :
    (generator k c q r *ᵥ firstA c) 2 =
      -3*c^2 - 2 * totalMigration k q * c := by
  have hn : k + 2 - 1 = k + 1 := by omega
  simp [generator, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    coalescenceTable, recombinationTable, occupiedTable, emptyTable,
    occupiedDemes, firstA, firstATable, totalMigration, hn]
  ring

theorem nextB_row_two (k : Nat) (c q r : ℝ) :
    (generator k c q r *ᵥ nextB c) 2 =
      -3*c^3 - 3 * totalMigration k q * c^2 := by
  have hn : k + 2 - 1 = k + 1 := by omega
  simp [generator, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    coalescenceTable, recombinationTable, occupiedTable, emptyTable,
    occupiedDemes, nextB, firstAThenBTable, totalMigration, hn]
  ring

theorem firstA_jet_one (k : Nat) (c q r : ℝ) :
    (generator k c q r *ᵥ firstA c) 0 = 2*r*c := by
  rw [row_zero]
  simp [firstA, firstATable]

theorem nextB_jet_one (k : Nat) (c q r : ℝ) :
    (generator k c q r *ᵥ nextB c) 0 = 2*r*c^2 := by
  rw [row_zero]
  simp [nextB, firstAThenBTable]

theorem firstA_jet_two (k : Nat) (c q r : ℝ) :
    ((generator k c q r)^2 *ᵥ firstA c) 0 =
      -2*r*c*(4*c + 4*totalMigration k q + 2*r) := by
  rw [pow_two, ← Matrix.mulVec_mulVec, row_zero, firstA_jet_one,
    firstA_row_one, firstA_row_two]
  ring

theorem nextB_jet_two (k : Nat) (c q r : ℝ) :
    ((generator k c q r)^2 *ᵥ nextB c) 0 =
      -2*r*c^2*(4*c + 5*totalMigration k q + 2*r) := by
  rw [pow_two, ← Matrix.mulVec_mulVec, row_zero, nextB_jet_one,
    nextB_row_one, nextB_row_two]
  ring

@[simp] theorem pairSurvival_initial : pairSurvival 0 = 1 := rfl
@[simp] theorem pairDensity_initial (c : ℝ) : pairDensity c 0 = c := rfl

theorem pair_survival_jet_one (k : Nat) (c q : ℝ) :
    (pairGenerator k c q *ᵥ pairSurvival) 0 = -c := by
  simp [pairGenerator, pairSurvival, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem pair_density_jet_one (k : Nat) (c q : ℝ) :
    (pairGenerator k c q *ᵥ pairDensity c) 0 = -c*(c+2*totalMigration k q) := by
  simp [pairGenerator, pairDensity, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

end Rhone.MarkovChain.Identifiability
