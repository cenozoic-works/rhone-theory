/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.IntegrableMarkovExistence

/-! # Locally integrable panmictic rates -/

@[expose] public section

open Set Filter MeasureTheory
open scoped BigOperators Topology
namespace Rhone.Statistics.Identifiability

noncomputable def panZeroExtension (f : ℝ → ℝ) : ℝ → ℝ := (Ici 0).indicator f

@[simp] theorem panZeroExtension_of_nonneg (f : ℝ → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    panZeroExtension f t = f t := by
  simp [panZeroExtension, ht]

@[simp] theorem panZeroExtension_of_neg (f : ℝ → ℝ) {t : ℝ} (ht : t < 0) :
    panZeroExtension f t = 0 := by
  simp [panZeroExtension, not_le.mpr ht]

theorem panZeroExtension_locallyIntegrable {f : ℝ → ℝ}
    (hf : LocallyIntegrableOn f (Ici 0) volume) :
    LocallyIntegrable (panZeroExtension f) volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  rw [panZeroExtension, integrableOn_indicator_iff measurableSet_Ici]
  exact hf.integrableOn_compact_subset inter_subset_left (by
    simpa only [inter_comm] using hK.inter_right (isClosed_Ici (a := (0 : ℝ))))

def integrablePanGenerator (rate recomb : ℝ) : Fin 3 → Fin 3 → ℝ :=
  ![![-(rate + 2 * recomb), 2 * recomb, 0],
    ![rate, -(3 * rate + recomb), recomb],
    ![0, 4 * rate, -6 * rate]]

theorem integrablePanGenerator_offdiag_nonneg {rate recomb : ℝ}
    (hr : 0 ≤ rate) (hρ : 0 ≤ recomb) :
    ∀ i j, i ≠ j → 0 ≤ integrablePanGenerator rate recomb i j := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [integrablePanGenerator]

theorem integrablePanGenerator_rows (rate recomb : ℝ) :
    (fun i => ∑ j, integrablePanGenerator rate recomb i j) = ![-rate, -2 * rate, -2 * rate] := by
  ext i
  fin_cases i <;> simp [integrablePanGenerator, Fin.sum_univ_three] <;> ring

theorem integrablePanGenerator_rows_nonpos {rate recomb : ℝ} (hr : 0 ≤ rate) :
    ∀ i, ∑ j, integrablePanGenerator rate recomb i j ≤ 0 := by
  intro i
  have h := congrFun (integrablePanGenerator_rows rate recomb) i
  rw [h]
  fin_cases i <;> simp <;> linarith

theorem integrablePanGenerator_locallyIntegrable {rate recomb : ℝ → ℝ}
    (hr : LocallyIntegrable rate volume) (hρ : LocallyIntegrable recomb volume) :
    ∀ i j, LocallyIntegrable (fun t => integrablePanGenerator (rate t) (recomb t) i j) volume := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp only [integrablePanGenerator]
  · exact (hr.add (hρ.smul (2 : ℝ))).neg
  · exact hρ.smul (2 : ℝ)
  · exact locallyIntegrable_const 0
  · exact hr
  · exact ((hr.smul (3 : ℝ)).add hρ).neg
  · exact hρ
  · exact locallyIntegrable_const 0
  · exact hr.smul (4 : ℝ)
  · exact hr.smul (-6 : ℝ)

theorem integrablePanGenerator_row_apply (rate recomb : ℝ) (v : Fin 3 → ℝ) :
    (fun j => ∑ i, v i * integrablePanGenerator rate recomb i j) =
      ![rate * (v 1 - v 0) - 2 * recomb * v 0,
        2 * recomb * v 0 - (3 * rate + recomb) * v 1 + 4 * rate * v 2,
        recomb * v 1 - 6 * rate * v 2] := by
  ext j
  fin_cases j <;> simp [integrablePanGenerator, Fin.sum_univ_three] <;> ring

end Rhone.Statistics.Identifiability
