/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeSamplePairProjection
public import Rhone.Statistics.Identifiability.IslandThreeJointTimes
public import Rhone.Statistics.ThreeTipSites.Channel

/-! # Labelled island occupancy and the first cherry -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Matrix Matrix.Norms.Operator ENNReal
open MeasureTheory
namespace Rhone.Statistics.IslandLabelledCherry
open MarkovChain.Identifiability Identifiability

def labelledPre (k : ℕ) (c q : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  !![-3*c-3*totalMigration k q, totalMigration k q, totalMigration k q,
      totalMigration k q, 0;
    q, -c-3*q-2*k*q, q, q, 2*k*q;
    q, q, -c-3*q-2*k*q, q, 2*k*q;
    q, q, q, -c-3*q-2*k*q, 2*k*q;
    0, 2*q, 2*q, 2*q, -6*q]

def firstFlux (c : ℝ) (i : Fin 3) : Matrix (Fin 5) (Fin 2) ℝ :=
  !![c, 0; 0, if i = 0 then c else 0; 0, if i = 1 then c else 0;
    0, if i = 2 then c else 0; 0, 0]

def split : Matrix (Fin 3) (Fin 5) ℝ :=
  !![1, 0, 0, 0, 0; 0, 1/3, 1/3, 1/3, 0; 0, 0, 0, 0, 1]

theorem labelledPre_metzler (k : ℕ) (c : ℝ) {q : ℝ} (hq : 0 ≤ q) :
    IsMetzler (labelledPre k c q) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    norm_num [labelledPre, totalMigration] at * <;> positivity

theorem labelledPre_row_sum (k : ℕ) (c q : ℝ) :
    labelledPre k c q *ᵥ (fun _ => 1) = ![-3*c, -c, -c, -c, 0] := by
  ext i
  fin_cases i <;>
    norm_num [labelledPre, totalMigration, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] <;> ring

theorem labelledPre_rows_nonpos (k : ℕ) {c q : ℝ} (hc : 0 ≤ c) (a : Fin 5) :
    (∑ b, labelledPre k c q a b) ≤ 0 := by
  have h := congrFun (labelledPre_row_sum k c q) a
  simp only [Matrix.mulVec, dotProduct, mul_one] at h
  rw [h]
  fin_cases a <;> simp <;> linarith

theorem firstFlux_nonneg {c : ℝ} (hc : 0 ≤ c) (i : Fin 3)
    (a : Fin 5) (b : Fin 2) : 0 ≤ firstFlux c i a b := by
  fin_cases i <;> fin_cases a <;> fin_cases b <;> simp [firstFlux, hc]

theorem total_flux (k : ℕ) (c q : ℝ) :
    (∑ i : Fin 3, firstFlux c i) *ᵥ (fun _ => 1) =
      exitRate (labelledPre k c q) := by
  rw [exitRate, labelledPre_row_sum]
  ext a
  fin_cases a <;>
    norm_num [firstFlux, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

theorem generator_split (k : ℕ) (c q : ℝ) :
    threeGenerator k c q * split = split * labelledPre k c q := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [threeGenerator, labelledPre, split, totalMigration,
      Matrix.mul_apply, Fin.sum_univ_succ, Fin.ext_iff] <;> ring

theorem split_firstFlux (c : ℝ) (i : Fin 3) :
    split * firstFlux c i = (1/3 : ℝ) • IslandThreeTimes.firstRate c := by
  ext a b
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    norm_num [split, firstFlux, IslandThreeTimes.firstRate,
      Matrix.mul_apply, Fin.sum_univ_succ, Fin.ext_iff] <;> ring

theorem exp_split (k : ℕ) (c q t : ℝ) :
    NormedSpace.exp (t • threeGenerator k c q) * split =
      split * NormedSpace.exp (t • labelledPre k c q) := by
  apply matrix_exp_rectangular_intertwining
  rw [Matrix.smul_mul, Matrix.mul_smul, generator_split]

def entryFlux (k : ℕ) (c q : ℝ) (i : Fin 3) (j : Fin 2) (s : ℝ) : ℝ :=
  (NormedSpace.exp (s • labelledPre k c q) * firstFlux c i) 0 j

theorem entryFlux_factor (k : ℕ) (c q s : ℝ) (i : Fin 3) (j : Fin 2) :
    entryFlux k c q i j s = (1/3 : ℝ) * IslandThreeTimes.entryFlux k c q j s := by
  have h := congrArg (fun M : Matrix (Fin 3) (Fin 5) ℝ =>
    (M * firstFlux c i) 0 j) (exp_split k c q s)
  rw [Matrix.mul_assoc, split_firstFlux, Matrix.mul_smul,
    Matrix.mul_assoc] at h
  simpa [split, entryFlux, IslandThreeTimes.entryFlux, flowOutput,
    Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using h.symm

def density (k : ℕ) (c q : ℝ) (i : Fin 3) (p : ℝ × ℝ) : ℝ :=
  ∑ j : Fin 2, entryFlux k c q i j p.1 *
    IslandThreeTimes.postDensity k c q j (p.2-p.1)

theorem density_factor (k : ℕ) (c q : ℝ) (i : Fin 3) (p : ℝ × ℝ) :
    density k c q i p = (1/3 : ℝ) * IslandThreeTimes.density k c q p := by
  simp only [density, entryFlux_factor, IslandThreeTimes.density,
    mul_assoc, Finset.mul_sum]

def law (k : ℕ) (c q : ℝ) (i : Fin 3) : Measure (ℝ × ℝ) :=
  triangularDensityLaw (density k c q i)

theorem law_factor (k : ℕ) (c q : ℝ) (i : Fin 3) :
    law k c q i = ENNReal.ofReal (1/3 : ℝ) • IslandThreeTimes.law k c q := by
  unfold law IslandThreeTimes.law triangularDensityLaw
  simp_rw [density_factor, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1/3)]
  exact withDensity_smul' _ _ ENNReal.ofReal_ne_top

theorem law_event_factor (k : ℕ) (c q : ℝ) (i : Fin 3) (A : Set (ℝ × ℝ)) :
    law k c q i A = ENNReal.ofReal (1/3 : ℝ) * IslandThreeTimes.law k c q A := by
  rw [law_factor, Measure.smul_apply, smul_eq_mul]

theorem law_univ (k : ℕ) {c q : ℝ} (hc : 0 < c) (hq : 0 < q) (i : Fin 3) :
    law k c q i Set.univ = ENNReal.ofReal (1/3 : ℝ) := by
  have := IslandThreeTimes.law_probability k hc hq
  rw [law_event_factor, measure_univ, mul_one]

theorem sequence_density_factor {K L : ℕ} (π : ThreeTipSites.Roots K L)
    (clock : ℝ) (k : ℕ) (c q : ℝ) (p : ℝ × ℝ)
    (x : ThreeTipSites.Panel K L) :
    (∑ i : Fin 3, density k c q i p *
      ThreeTipSites.fixedTopology π clock (p.1, p.2-p.1) i x) =
        IslandThreeTimes.density k c q p *
          ThreeTipSites.conditional π clock (p.1, p.2-p.1) x := by
  simp only [density_factor, ThreeTipSites.conditional]
  rw [← Finset.mul_sum]
  ring

end Rhone.Statistics.IslandLabelledCherry
