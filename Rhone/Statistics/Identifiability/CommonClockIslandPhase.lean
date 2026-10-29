/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.EventMarks
public import Rhone.Statistics.Identifiability.MatrixFlow
public import Mathlib.Data.Matrix.Block
public import Mathlib.Tactic

/-! # Exact finite phase-type candidate for the constant-island sum-time density -/

@[expose] public section

open scoped Matrix Matrix.Norms.Operator
namespace Rhone.Statistics.Identifiability

def commonClockMarkTable : Matrix MarkovChain.Identifiability.State (Fin 5) ℕ :=
  ![![1,0,0,0,0], ![0,0,0,0,0], ![0,1,0,1,0], ![0,0,0,0,1],
    ![0,0,0,0,0], ![0,0,1,0,0], ![0,0,0,0,0], ![0,1,0,1,0],
    ![0,0,0,0,1], ![0,1,0,1,0], ![0,0,1,0,0], ![0,0,0,0,0],
    ![0,0,0,0,1], ![0,0,0,0,0], ![0,0,1,0,0], ![0,0,0,0,0]]

theorem commonClockMarkTable_correct (i : MarkovChain.Identifiability.State) (j : Fin 5) :
    markCount i j = commonClockMarkTable i j := by
  fin_cases i <;> fin_cases j <;> decide

noncomputable def commonClockFirstRate (c : ℝ) : Matrix MarkovChain.Identifiability.State (Fin 2)
    ℝ :=
  fun i j => if j = 0 then markRates c i 1 + markRates c i 3
    else markRates c i 2 + markRates c i 4

noncomputable def commonClockIslandPhase (k : ℕ) (c q r : ℝ) :
    Matrix (Fin 18) (Fin 18) ℝ :=
  fun i j => Fin.addCases
    (fun a => Fin.addCases (MarkovChain.Identifiability.generator k c q r a)
        (commonClockFirstRate c a) j)
    (fun a => Fin.addCases (fun _ => 0)
        (fun b => 2 * MarkovChain.Identifiability.pairGenerator k c q a b) j) i

noncomputable def commonClockIslandReward (c : ℝ) : Fin 18 → ℝ :=
  fun j => Fin.addCases (fun i => markRates c i 0 / 2) (MarkovChain.Identifiability.pairDensity c) j

noncomputable def commonClockIslandJet (k : ℕ) (c q r : ℝ) (j : ℕ) (t : ℝ) : ℝ :=
  flowOutput (commonClockIslandPhase k c q r) 0 (commonClockIslandReward c) j t

theorem commonClockIslandJet_hasDerivAt (k : ℕ) (c q r : ℝ) (j : ℕ) (t : ℝ) :
    HasDerivAt (commonClockIslandJet k c q r j)
      (commonClockIslandJet k c q r (j+1) t) t :=
  flowOutput_hasDerivAt _ _ _ _ _

@[simp] theorem commonClockIslandJet_zero_time (k : ℕ) (c q r : ℝ) (j : ℕ) :
    commonClockIslandJet k c q r j 0 =
      ((commonClockIslandPhase k c q r)^j *ᵥ commonClockIslandReward c) 0 :=
  flowOutput_zero _ _ _ _

theorem phase_row_zero (k : ℕ) (c q r : ℝ) (v : Fin 18 → ℝ) :
    (commonClockIslandPhase k c q r *ᵥ v) 0 =
      (-c - 2 * MarkovChain.Identifiability.totalMigration k q - 2*r) * v 0 +
      2 * MarkovChain.Identifiability.totalMigration k q * v 1 + 2*r * v 2 := by
  have hn : k + 2 - 1 = k + 1 := by omega
  simp [commonClockIslandPhase, commonClockFirstRate, markRates,
    commonClockMarkTable_correct, commonClockMarkTable, MarkovChain.Identifiability.generator,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.addCases,
    MarkovChain.Identifiability.coalescenceTable, MarkovChain.Identifiability.recombinationTable,
        MarkovChain.Identifiability.occupiedTable, MarkovChain.Identifiability.emptyTable,
    MarkovChain.Identifiability.occupiedDemes, MarkovChain.Identifiability.totalMigration, hn]
  ring

@[simp] theorem commonClockIslandJet_initial (k : ℕ) (c q r : ℝ) :
    commonClockIslandJet k c q r 0 0 = c / 2 := by
  simp [commonClockIslandReward, Fin.addCases, markRates,
    commonClockMarkTable_correct, commonClockMarkTable]

theorem commonClockIslandJet_one (k : ℕ) (c q r : ℝ) :
    commonClockIslandJet k c q r 1 0 =
      -c * (c + 2 * MarkovChain.Identifiability.totalMigration k q + 2*r) / 2 := by
  simp only [commonClockIslandJet_zero_time, pow_one]
  rw [phase_row_zero]
  simp [commonClockIslandReward, Fin.addCases, markRates,
    commonClockMarkTable_correct, commonClockMarkTable]
  ring

theorem phase_row_one (k : ℕ) (c q r : ℝ) (v : Fin 18 → ℝ) :
    (commonClockIslandPhase k c q r *ᵥ v) 1 =
      2*q*v 0 + (-2*q-2*r)*v 1 + 2*r*v 4 := by
  simp [commonClockIslandPhase, commonClockFirstRate, markRates,
    commonClockMarkTable_correct, commonClockMarkTable, MarkovChain.Identifiability.generator,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.addCases,
    MarkovChain.Identifiability.coalescenceTable, MarkovChain.Identifiability.recombinationTable,
        MarkovChain.Identifiability.occupiedTable, MarkovChain.Identifiability.emptyTable]
  ring

theorem phase_row_two (k : ℕ) (c q r : ℝ) (v : Fin 18 → ℝ) :
    (commonClockIslandPhase k c q r *ᵥ v) 2 =
      c*v 0 + (-3*c-r-3*MarkovChain.Identifiability.totalMigration k q)*v 2 +
      MarkovChain.Identifiability.totalMigration k q * (v 3 + v 4 + v 5) + r*v 7 + 2*c*v 16 := by
  have hn : k + 2 - 1 = k + 1 := by omega
  simp [commonClockIslandPhase, commonClockFirstRate, markRates,
    commonClockMarkTable_correct, commonClockMarkTable, MarkovChain.Identifiability.generator,
    Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.addCases,
    MarkovChain.Identifiability.coalescenceTable, MarkovChain.Identifiability.recombinationTable,
        MarkovChain.Identifiability.occupiedTable, MarkovChain.Identifiability.emptyTable,
    MarkovChain.Identifiability.occupiedDemes, MarkovChain.Identifiability.totalMigration, hn]
  ring

noncomputable def commonClockIslandRewardOne (k : ℕ) (c q r : ℝ) : Fin 18 → ℝ :=
  ![-c*(c+2*MarkovChain.Identifiability.totalMigration k q+2*r)/2, c*q, 5*c^2/2, 0,0,0,0,2*c^2,
    0,2*c^2,0,0,0,0,0,0,-2*c*(c+2*MarkovChain.Identifiability.totalMigration k q),4*c*q]

set_option maxHeartbeats 800000 in
theorem phase_mul_reward (k : ℕ) (c q r : ℝ) :
    commonClockIslandPhase k c q r *ᵥ commonClockIslandReward c =
      commonClockIslandRewardOne k c q r := by
  have hn : k + 2 - 1 = k + 1 := by omega
  ext i
  fin_cases i <;>
    simp [commonClockIslandPhase, commonClockIslandReward, commonClockFirstRate,
      commonClockIslandRewardOne, markRates, commonClockMarkTable_correct,
      commonClockMarkTable, MarkovChain.Identifiability.generator,
          MarkovChain.Identifiability.pairGenerator, MarkovChain.Identifiability.pairDensity,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.addCases,
      MarkovChain.Identifiability.coalescenceTable, MarkovChain.Identifiability.recombinationTable,
          MarkovChain.Identifiability.occupiedTable, MarkovChain.Identifiability.emptyTable,
      MarkovChain.Identifiability.occupiedDemes, MarkovChain.Identifiability.totalMigration, hn] <;>
          ring

theorem phase_power_two_zero (k : ℕ) (c q r : ℝ) :
    ((commonClockIslandPhase k c q r)^2 *ᵥ commonClockIslandReward c) 0 =
      c * ((c + 2*MarkovChain.Identifiability.totalMigration k q + 2*r)^2 +
        4*MarkovChain.Identifiability.totalMigration k q*q + 10*c*r) / 2 := by
  rw [pow_two, ← Matrix.mulVec_mulVec, phase_mul_reward, phase_row_zero]
  simp [commonClockIslandRewardOne]
  ring

theorem phase_power_two_one (k : ℕ) (c q r : ℝ) :
    ((commonClockIslandPhase k c q r)^2 *ᵥ commonClockIslandReward c) 1 =
      -c*q*(c + 2*MarkovChain.Identifiability.totalMigration k q + 2*q + 4*r) := by
  rw [pow_two, ← Matrix.mulVec_mulVec, phase_mul_reward, phase_row_one]
  simp [commonClockIslandRewardOne]
  ring

theorem phase_power_two_two (k : ℕ) (c q r : ℝ) :
    ((commonClockIslandPhase k c q r)^2 *ᵥ commonClockIslandReward c) 2 =
      -c^2*(24*c + 33*MarkovChain.Identifiability.totalMigration k q + 3*r)/2 := by
  rw [pow_two, ← Matrix.mulVec_mulVec, phase_mul_reward, phase_row_two]
  simp [commonClockIslandRewardOne]
  ring

noncomputable def commonClockIslandCubic (c m q r : ℝ) : ℝ :=
  c^3 + 6*c^2*m + 64*c^2*r + 12*c*m^2 + 8*c*m*q + 110*c*m*r + 38*c*r^2 +
    8*m^3 + 16*m^2*q + 24*m^2*r + 8*m*q^2 + 24*m*q*r + 24*m*r^2 + 8*r^3

theorem commonClockIslandJet_two (k : ℕ) (c q r : ℝ) :
    commonClockIslandJet k c q r 2 0 =
      c * ((c + 2*MarkovChain.Identifiability.totalMigration k q + 2*r)^2 +
        4*MarkovChain.Identifiability.totalMigration k q*q + 10*c*r) / 2 := by
  rw [commonClockIslandJet_zero_time, phase_power_two_zero]

theorem commonClockIslandJet_three (k : ℕ) (c q r : ℝ) :
    commonClockIslandJet k c q r 3 0 =
      -c * commonClockIslandCubic c (MarkovChain.Identifiability.totalMigration k q) q r / 2 := by
  rw [commonClockIslandJet_zero_time, show (3 : ℕ) = 2+1 from rfl,
    pow_succ', ← Matrix.mulVec_mulVec, phase_row_zero,
    phase_power_two_zero, phase_power_two_one, phase_power_two_two]
  unfold commonClockIslandCubic
  ring

end Rhone.Statistics.Identifiability
