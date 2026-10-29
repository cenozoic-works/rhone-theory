/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.Identifiability.Generator
public import Rhone.Statistics.Identifiability.EventMarks

/-! # Product-state generator and witness vectors for simultaneous-onset certificates -/

@[expose] public section

open scoped Matrix
open Rhone.MarkovChain.Identifiability Rhone.Statistics.Identifiability

namespace Rhone.Statistics.Identifiability.SimultaneousOnset

abbrev ProductState := State × Fin 2

noncomputable def productGenerator (k : ℕ) (c q r : ℝ) :
    Matrix ProductState ProductState ℝ := fun i j =>
  generator k c q r i.1 j.1 * (if i.2 = j.2 then 1 else 0) +
    (if i.1 = j.1 then 1 else 0) * pairGenerator k c q i.2 j.2

noncomputable def witnessVec (i : ProductState) : ℝ :=
  (firstAThenBTable i.1 : ℝ) - (firstATable i.1 : ℝ) * (if i.2 = 0 then 1 else 0)

noncomputable def coalescenceMark (k : ℕ) := productGenerator k 1 0 0
noncomputable def migrationMark (k : ℕ) := productGenerator k 0 1 0
noncomputable def recombinationMark (k : ℕ) := productGenerator k 0 0 1

theorem productGenerator_affine (k : ℕ) (c q r : ℝ) :
    productGenerator k c q r =
      c • coalescenceMark k + q • migrationMark k + r • recombinationMark k := by
  ext ⟨i, a⟩ ⟨j, b⟩
  fin_cases a <;> fin_cases b <;> by_cases h : i = j <;>
    simp [h, productGenerator, coalescenceMark, migrationMark, recombinationMark,
      generator, pairGenerator, totalMigration, Matrix.add_apply, Matrix.smul_apply] <;> ring

theorem productGenerator_mulVec (k : ℕ) (c q r : ℝ) (v : ProductState → ℝ)
    (i : State) (a : Fin 2) :
    (productGenerator k c q r *ᵥ v) (i, a) =
      (generator k c q r *ᵥ fun j => v (j, a)) i +
      (pairGenerator k c q *ᵥ fun b => v (i, b)) a := by
  simp [productGenerator, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    add_mul, Finset.sum_add_distrib]

@[simp] theorem witnessVec_initial : witnessVec (0, 0) = 0 := by
  simp [witnessVec, firstATable, firstAThenBTable]

theorem productGenerator_initial (k : ℕ) (c q r : ℝ) (v : ProductState → ℝ) :
    (productGenerator k c q r *ᵥ v) (0, 0) =
      (-2*c - 4*totalMigration k q - 2*r) * v (0, 0) +
        2*totalMigration k q * v (1, 0) + 2*r * v (2, 0) +
        2*totalMigration k q * v (0, 1) := by
  rw [productGenerator_mulVec, row_zero]
  simp [pairGenerator, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

theorem coalescenceMark_initial (k : ℕ) (v : ProductState → ℝ) :
    (coalescenceMark k *ᵥ v) (0, 0) = -2 * v (0, 0) := by
  simp [coalescenceMark, productGenerator_initial, totalMigration]

theorem migrationMark_initial (k : ℕ) (v : ProductState → ℝ) :
    (migrationMark k *ᵥ v) (0, 0) =
      -4 * (k + 1 : ℝ) * v (0, 0) +
        2 * (k + 1 : ℝ) * v (1, 0) + 2 * (k + 1 : ℝ) * v (0, 1) := by
  simp [migrationMark, productGenerator_initial, totalMigration]

theorem recombinationMark_initial (k : ℕ) (v : ProductState → ℝ) :
    (recombinationMark k *ᵥ v) (0, 0) = -2 * v (0, 0) + 2 * v (2, 0) := by
  simp [recombinationMark, productGenerator_initial, totalMigration]

@[simp] theorem coalescenceMark_witness_initial (k : ℕ) :
    (coalescenceMark k *ᵥ witnessVec) (0, 0) = 0 := by
  simp [coalescenceMark_initial]

@[simp] theorem migrationMark_witness_initial (k : ℕ) :
    (migrationMark k *ᵥ witnessVec) (0, 0) = 0 := by
  simp [migrationMark_initial, witnessVec, firstATable, firstAThenBTable]

@[simp] theorem recombinationMark_witness_initial (k : ℕ) :
    (recombinationMark k *ᵥ witnessVec) (0, 0) = 0 := by
  simp [recombinationMark_initial, witnessVec, firstATable, firstAThenBTable]

theorem recombinationMark_witness_one_zero (k : ℕ) :
    (recombinationMark k *ᵥ witnessVec) (1, 0) = 0 := by
  rw [recombinationMark, productGenerator_mulVec]
  simp [generator, pairGenerator, totalMigration, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ, recombinationTable, witnessVec, firstATable, firstAThenBTable]

theorem recombinationMark_witness_zero_one (k : ℕ) :
    (recombinationMark k *ᵥ witnessVec) (0, 1) = 2 := by
  rw [recombinationMark, productGenerator_mulVec]
  simp [generator, pairGenerator, totalMigration, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ, recombinationTable, witnessVec, firstATable, firstAThenBTable]

theorem migrationMark_witness_two_zero (k : ℕ) :
    (migrationMark k *ᵥ witnessVec) (2, 0) = (k + 1 : ℝ) := by
  have hn : k + 2 - 1 = k + 1 := by omega
  rw [migrationMark, productGenerator_mulVec]
  simp [generator, pairGenerator, totalMigration, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ, occupiedTable, emptyTable, occupiedDemes, hn,
    witnessVec, firstATable, firstAThenBTable]
  ring

theorem migration_recombination_witness (k : ℕ) :
    ((migrationMark k * recombinationMark k) *ᵥ witnessVec) (0, 0) =
      4 * (k + 1 : ℝ) := by
  rw [← Matrix.mulVec_mulVec, migrationMark_initial]
  simp [recombinationMark_witness_one_zero, recombinationMark_witness_zero_one]
  ring

theorem recombination_migration_witness (k : ℕ) :
    ((recombinationMark k * migrationMark k) *ᵥ witnessVec) (0, 0) =
      2 * (k + 1 : ℝ) := by
  rw [← Matrix.mulVec_mulVec, recombinationMark_initial]
  simp [migrationMark_witness_two_zero]

def zeroMigrationReachable (i : ProductState) : Prop :=
  (i.1 = 0 ∨ i.1 = 2 ∨ i.1 = 7) ∧ i.2 = 0

def zeroRecombinationReachable (i : ProductState) : Prop :=
  i.1 = 0 ∨ i.1 = 1

@[simp] theorem zeroMigrationReachable_initial : zeroMigrationReachable (0, 0) := by
  simp [zeroMigrationReachable]

@[simp] theorem zeroRecombinationReachable_initial : zeroRecombinationReachable (0, 0) := by
  simp [zeroRecombinationReachable]

theorem zeroMigrationReachable_witness (i : ProductState)
    (hi : zeroMigrationReachable i) : witnessVec i = 0 := by
  rcases i with ⟨i, a⟩
  rcases hi with ⟨hi, rfl⟩
  rcases hi with rfl | rfl | rfl <;>
    simp [witnessVec, firstATable, firstAThenBTable]

theorem zeroRecombinationReachable_witness (i : ProductState)
    (hi : zeroRecombinationReachable i) : witnessVec i = 0 := by
  rcases i with ⟨i, a⟩
  rcases hi with rfl | rfl <;>
    simp [witnessVec, firstATable, firstAThenBTable]

set_option maxHeartbeats 800000 in
theorem zeroMigrationReachable_closed (k : ℕ) (c r : ℝ)
    (i j : ProductState) (hi : zeroMigrationReachable i)
    (hj : ¬zeroMigrationReachable j) : productGenerator k c 0 r i j = 0 := by
  rcases i with ⟨i, a⟩
  rcases j with ⟨j, b⟩
  rcases hi with ⟨hi, rfl⟩
  rcases hi with rfl | rfl | rfl <;>
    fin_cases j <;> fin_cases b <;>
    simp_all [zeroMigrationReachable, productGenerator, generator, pairGenerator,
      totalMigration, coalescenceTable, recombinationTable]

set_option maxHeartbeats 800000 in
theorem zeroRecombinationReachable_closed (k : ℕ) (c q : ℝ)
    (i j : ProductState) (hi : zeroRecombinationReachable i)
    (hj : ¬zeroRecombinationReachable j) : productGenerator k c q 0 i j = 0 := by
  rcases i with ⟨i, a⟩
  rcases j with ⟨j, b⟩
  rcases hi with rfl | rfl <;>
    fin_cases a <;> fin_cases j <;> fin_cases b <;>
    simp_all [zeroRecombinationReachable, productGenerator, generator, pairGenerator,
      totalMigration, coalescenceTable, occupiedTable, emptyTable]

end Rhone.Statistics.Identifiability.SimultaneousOnset
