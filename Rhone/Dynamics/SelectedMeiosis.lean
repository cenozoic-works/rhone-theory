/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Dynamics.LDMeasures
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Tactic.FinCases
public import Mathlib.Basic.Real.Basic

/-!
# Diploid selection followed by Mendelian two-locus meiosis

Source: bulmer1974, p. 282, eq. (4). -/

@[expose] public section
namespace Rhone.Dynamics.SelectedMeiosis
open Finset
/-- Source: bulmer1974, p. 282, eq. (4). -/
noncomputable def firstAllele : Fin 4 → ℝ := ![1,1,0,0]
/-- Source: bulmer1974, p. 282, eq. (4). -/
noncomputable def secondAllele : Fin 4 → ℝ := ![1,0,1,0]
/-- Source: bulmer1974, p. 282, eq. (4). -/
noncomputable def jointTransmission (r : ℝ) (i j : Fin 4) : ℝ :=
  (1-r)/2*(firstAllele i*secondAllele i + firstAllele j*secondAllele j) +
  r/2*(firstAllele i*secondAllele j + firstAllele j*secondAllele i)

/-- Source: bulmer1974, p. 282, eq. (4). -/
noncomputable def transmission (r : ℝ) (i j : Fin 4) : Fin 4 → ℝ :=
  ![jointTransmission r i j,
    (firstAllele i+firstAllele j)/2-jointTransmission r i j,
    (secondAllele i+secondAllele j)/2-jointTransmission r i j,
    1-(firstAllele i+firstAllele j)/2-(secondAllele i+secondAllele j)/2+
      jointTransmission r i j]
/-- Source: bulmer1974, p. 282, eq. (4). -/
noncomputable def selectionMass (g : Fin 4 → ℝ) (w : Fin 4 → Fin 4 → ℝ) : ℝ :=
  ∑ i, ∑ j, g i*g j*w i j
/-- Source: bulmer1974, p. 282, eq. (4). -/
noncomputable def selectedExpectation (g : Fin 4 → ℝ)
    (w f : Fin 4 → Fin 4 → ℝ) : ℝ :=
  ∑ i, ∑ j, g i*g j*w i j/selectionMass g w*f i j
/-- Source: bulmer1974, p. 282, eq. (4). -/
noncomputable def selectedOffspring (g : Fin 4 → ℝ)
    (w : Fin 4 → Fin 4 → ℝ) (r : ℝ) : Rhone.Dynamics.Gametes ℝ :=
  ⟨selectedExpectation g w (fun i j => transmission r i j 0),
    selectedExpectation g w (fun i j => transmission r i j 1),
    selectedExpectation g w (fun i j => transmission r i j 2),
    selectedExpectation g w (fun i j => transmission r i j 3)⟩
/-- Source: bulmer1974, p. 282, eq. (4). -/
noncomputable def selectedFirst (g : Fin 4 → ℝ) (w : Fin 4 → Fin 4 → ℝ) : ℝ :=
  selectedExpectation g w (fun i j => (firstAllele i+firstAllele j)/2)
/-- Source: bulmer1974, p. 282, eq. (4). -/
noncomputable def selectedSecond (g : Fin 4 → ℝ) (w : Fin 4 → Fin 4 → ℝ) : ℝ :=
  selectedExpectation g w (fun i j => (secondAllele i+secondAllele j)/2)
/-- Source: bulmer1974, p. 282, eq. (4). -/
noncomputable def selectedWithinLD (g : Fin 4 → ℝ) (w : Fin 4 → Fin 4 → ℝ) : ℝ :=
  selectedExpectation g w (fun i j =>
    (firstAllele i*secondAllele i+firstAllele j*secondAllele j)/2) -
    selectedFirst g w*selectedSecond g w
/-- Source: bulmer1974, p. 282, eq. (4). -/
noncomputable def selectedCrossLD (g : Fin 4 → ℝ) (w : Fin 4 → Fin 4 → ℝ) : ℝ :=
  selectedExpectation g w (fun i j =>
    (firstAllele i*secondAllele j+firstAllele j*secondAllele i)/2) -
    selectedFirst g w*selectedSecond g w

/-- Source: bulmer1974, p. 282, eq. (4). -/
theorem transmission_distribution (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (i j : Fin 4) :
    (∀ k, 0 ≤ transmission r i j k) ∧ ∑ k, transmission r i j k = 1 := by
  constructor
  · intro k
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      simp [transmission, jointTransmission, firstAllele, secondAllele] <;> linarith
  · simp only [transmission, Fin.sum_univ_succ]
    simp

/-- Source: bulmer1974, p. 282, eq. (4). -/
theorem selected_offspring_distribution (g : Fin 4 → ℝ)
    (w : Fin 4 → Fin 4 → ℝ) (r : ℝ)
    (hg : ∀ i, 0 ≤ g i) (hw : ∀ i j, 0 ≤ w i j)
    (hmean : 0 < selectionMass g w) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    (selectedOffspring g w r).IsDist := by
  have hnonneg : ∀ k, 0 ≤ selectedExpectation g w (fun i j => transmission r i j k) := by
    intro k
    apply sum_nonneg
    intro i _
    apply sum_nonneg
    intro j _
    exact mul_nonneg (div_nonneg (mul_nonneg (mul_nonneg (hg i) (hg j)) (hw i j))
      hmean.le) ((transmission_distribution r hr0 hr1 i j).1 k)
  refine ⟨hnonneg 0, hnonneg 1, hnonneg 2, hnonneg 3, ?_⟩
  simp only [selectedOffspring, Rhone.Dynamics.Gametes.total, selectedExpectation,
    ← sum_add_distrib, ← mul_add]
  have ht : ∀ i j, transmission r i j 0+transmission r i j 1+
      transmission r i j 2+transmission r i j 3 = 1 := by
    intro i j
    have h := (transmission_distribution r hr0 hr1 i j).2
    simpa [Fin.sum_univ_succ, add_assoc] using h
  simp_rw [ht, mul_one]
  simp_rw [← sum_div]
  exact div_self (ne_of_gt hmean)

/-- Source: bulmer1974, p. 282, eq. (4). -/
theorem selected_offspring_marginals (g : Fin 4 → ℝ)
    (w : Fin 4 → Fin 4 → ℝ) (r : ℝ) :
    (selectedOffspring g w r).pA = selectedFirst g w ∧
    (selectedOffspring g w r).pB = selectedSecond g w := by
  constructor <;>
    simp only [selectedOffspring, Rhone.Dynamics.Gametes.pA, Rhone.Dynamics.Gametes.pB,
      selectedFirst, selectedSecond, selectedExpectation, ← sum_add_distrib, ← mul_add,
      transmission, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] <;>
      congr 1 <;> funext i <;> congr 1 <;> funext j <;> ring

/-- Source: bulmer1974, p. 282, eq. (4). -/
theorem selected_meiosis_ld_recursion (g : Fin 4 → ℝ)
    (w : Fin 4 → Fin 4 → ℝ) (r : ℝ)
    (hg : ∀ i, 0 ≤ g i) (hw : ∀ i j, 0 ≤ w i j)
    (hmean : 0 < selectionMass g w) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    (selectedOffspring g w r).D =
      (1-r)*selectedWithinLD g w+r*selectedCrossLD g w := by
  rw [Rhone.Dynamics.Gametes.D_eq_x11_sub
    (selected_offspring_distribution g w r hg hw hmean hr0 hr1).total_eq,
    (selected_offspring_marginals g w r).1,
    (selected_offspring_marginals g w r).2]
  simp only [selectedOffspring, selectedWithinLD, selectedCrossLD, selectedExpectation,
    transmission, Matrix.cons_val_zero, jointTransmission]
  simp only [Fin.sum_univ_succ]
  simp
  ring

end Rhone.Dynamics.SelectedMeiosis
