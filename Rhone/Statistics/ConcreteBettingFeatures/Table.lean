/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ConcretePatternMoments.Multiplicity

/-! # Explicit rational feature table, symmetrized over the three site positions -/

@[expose] public section

noncomputable section
namespace Rhone.Statistics.ConcreteBettingFeatures
open ConcretePatternMoments

def featureNumerators : Fin 14 → Fin 5 → ℤ :=
  ![![243, 243, 243, 243, 243], ![171, 99, 27, -9, -9], ![135, 27, -81, -27, -27], ![99,
  51, 99, 27, -21], ![99, 3, -45, -21, 3], ![63, -21, -9, 9, 9], ![27, -45, 27, -9, -9],
  ![27, 99, 75, -33, 15], ![27, 3, -21, -1, -1], ![-9, 27, -33, 13, -3], ![27, -45, 27, 15,
  -9], ![-9, -21, 15, -3, 5], ![-45, 3, 3, -5, -5], ![-81, 27, -9, 9, 9]]

def classTable : Fin 5 → Fin 5 → Fin 5 → Fin 14 :=
  ![![![0, 1, 1, 1, 2], ![1, 3, 4, 4, 5], ![1, 4, 3, 4, 5], ![1, 4, 4, 3, 5], ![2, 5, 5, 5,
  6]], ![![1, 3, 4, 4, 5], ![3, 7, 8, 8, 9], ![4, 8, 8, 10, 11], ![4, 8, 10, 8, 11], ![5,
  9, 11, 11, 12]], ![![1, 4, 3, 4, 5], ![4, 8, 8, 10, 11], ![3, 8, 7, 8, 9], ![4, 10, 8, 8,
  11], ![5, 11, 9, 11, 12]], ![![1, 4, 4, 3, 5], ![4, 8, 10, 8, 11], ![4, 10, 8, 8, 11],
  ![3, 8, 8, 7, 9], ![5, 11, 11, 9, 12]], ![![2, 5, 5, 5, 6], ![5, 9, 11, 11, 12], ![5, 11,
  9, 11, 12], ![5, 11, 11, 9, 12], ![6, 12, 12, 12, 13]]]

def rowClass (r : Row) : Fin 14 := classTable r.1 r.2.1 r.2.2

def numerator (i : Fin 5) (r : Row) : ℤ := featureNumerators (rowClass r) i

def feature (i : Fin 5) (r : Row) : ℝ := (numerator i r : ℝ) / 243

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem numerator_bounds : ∀ (i : Fin 5) (r : Row),
  -81 ≤ numerator i r ∧ numerator i r ≤ 243 := by
  have h : ∀ (i : Fin 5) (c : Fin 14),
      -81 ≤ featureNumerators c i ∧ featureNumerators c i ≤ 243 := by
    intro i c
    fin_cases i <;> fin_cases c <;> decide
  intro i r
  exact h i (rowClass r)

theorem feature_bounds (i : Fin 5) (r : Row) : -1 / 3 ≤ feature i r ∧ feature i r ≤ 1 := by
  obtain ⟨hl, hu⟩ := numerator_bounds i r
  have hl' : (-81 : ℝ) ≤ (numerator i r : ℝ) := by exact_mod_cast hl
  have hu' : (numerator i r : ℝ) ≤ 243 := by exact_mod_cast hu
  unfold feature
  constructor <;> linarith

end Rhone.Statistics.ConcreteBettingFeatures
