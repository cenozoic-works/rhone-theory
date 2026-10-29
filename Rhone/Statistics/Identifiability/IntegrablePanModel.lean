/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.IntegrablePanRates

/-! # An AC/AE panmictic pre-model -/

@[expose] public section

open Set Filter MeasureTheory
open scoped BigOperators Topology
namespace Rhone.Statistics.Identifiability

def IntegrablePanPreEquations (rate recomb D R U : ℝ → ℝ) : Prop :=
  ∀ᵐ t, 0 ≤ t →
    HasDerivAt D (rate t * (R t - D t) - 2 * recomb t * D t) t ∧
    HasDerivAt R (2 * recomb t * D t - (3 * rate t + recomb t) * R t +
      4 * rate t * U t) t ∧
    HasDerivAt U (recomb t * R t - 6 * rate t * U t) t

structure IntegrablePanPreModel (rate : ℝ → ℝ) where
  recomb : ℝ → ℝ
  D : ℝ → ℝ
  R : ℝ → ℝ
  U : ℝ → ℝ
  rate_integrable : LocallyIntegrableOn rate (Ici 0) volume
  recomb_integrable : LocallyIntegrableOn recomb (Ici 0) volume
  rate_nonneg : ∀ᵐ t, 0 ≤ t → 0 ≤ rate t
  recomb_nonneg : ∀ᵐ t, 0 ≤ t → 0 ≤ recomb t
  D_ac : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval D 0 T
  R_ac : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval R 0 T
  U_ac : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval U 0 T
  D_positive : ∀ t, 0 ≤ t → 0 < D t
  R_nonneg : ∀ t, 0 ≤ t → 0 ≤ R t
  U_nonneg : ∀ t, 0 ≤ t → 0 ≤ U t
  initial : D 0 = 1 ∧ R 0 = 0 ∧ U 0 = 0
  equations : IntegrablePanPreEquations rate recomb D R U

def integrablePanRow (D R U : ℝ → ℝ) (t : ℝ) : Fin 3 → ℝ := ![D t, R t, U t]

theorem integrablePanPreEquations_row {rate recomb D R U : ℝ → ℝ}
    (he : IntegrablePanPreEquations rate recomb D R U) :
    ∀ᵐ t, 0 ≤ t → ∀ j,
      HasDerivAt (fun s => integrablePanRow D R U s j)
        (∑ i, integrablePanRow D R U t i *
          integrablePanGenerator (panZeroExtension rate t) (panZeroExtension recomb t) i j) t := by
  filter_upwards [he] with t ht ht0 j
  rw [panZeroExtension_of_nonneg rate ht0, panZeroExtension_of_nonneg recomb ht0,
    congrFun (integrablePanGenerator_row_apply (rate t) (recomb t)
      (integrablePanRow D R U t)) j]
  fin_cases j
  · exact (ht ht0).1
  · exact (ht ht0).2.1
  · exact (ht ht0).2.2

theorem integrablePanPreEquations_of_row {rate recomb : ℝ → ℝ} {v : ℝ → Fin 3 → ℝ}
    (he : ∀ᵐ t, 0 ≤ t → ∀ j, HasDerivAt (fun s => v s j)
      (∑ i, v t i *
        integrablePanGenerator (panZeroExtension rate t) (panZeroExtension recomb t) i j) t) :
    IntegrablePanPreEquations rate recomb (fun t => v t 0) (fun t => v t 1)
      (fun t => v t 2) := by
  filter_upwards [he] with t ht ht0
  have hh (j : Fin 3) := ht ht0 j
  simp only [panZeroExtension_of_nonneg rate ht0,
    panZeroExtension_of_nonneg recomb ht0] at hh
  simp_rw [congrFun (integrablePanGenerator_row_apply (rate t) (recomb t) (v t))] at hh
  exact ⟨hh 0, hh 1, hh 2⟩

theorem integrablePanPreEquations_unique (rate recomb D R U D' R' U' : ℝ → ℝ)
    (hr : LocallyIntegrableOn rate (Ici 0) volume)
    (hρ : LocallyIntegrableOn recomb (Ici 0) volume)
    (hrn : ∀ᵐ t, 0 ≤ t → 0 ≤ rate t)
    (hρn : ∀ᵐ t, 0 ≤ t → 0 ≤ recomb t)
    (hD : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval D 0 T)
    (hR : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval R 0 T)
    (hU : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval U 0 T)
    (hD' : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval D' 0 T)
    (hR' : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval R' 0 T)
    (hU' : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval U' 0 T)
    (he : IntegrablePanPreEquations rate recomb D R U)
    (he' : IntegrablePanPreEquations rate recomb D' R' U')
    (hzero : D 0 = D' 0 ∧ R 0 = R' 0 ∧ U 0 = U' 0) :
    EqOn D D' (Ici 0) ∧ EqOn R R' (Ici 0) ∧ EqOn U U' (Ici 0) := by
  let Q := fun t => integrablePanGenerator (panZeroExtension rate t) (panZeroExtension recomb t)
  have hQi : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume :=
    integrablePanGenerator_locallyIntegrable (panZeroExtension_locallyIntegrable hr)
      (panZeroExtension_locallyIntegrable hρ)
  have hQ : ∀ᵐ t, 0 ≤ t → ∀ i j, i ≠ j → 0 ≤ Q t i j := by
    filter_upwards [hrn, hρn] with t hrt hρt ht
    simpa only [Q, panZeroExtension_of_nonneg rate ht,
      panZeroExtension_of_nonneg recomb ht] using
      integrablePanGenerator_offdiag_nonneg (hrt ht) (hρt ht)
  have hac : ∀ T, 0 ≤ T → ∀ i,
      AbsolutelyContinuousOnInterval (fun t => integrablePanRow D R U t i) 0 T := by
    intro T hT i
    fin_cases i
    · exact hD T hT
    · exact hR T hT
    · exact hU T hT
  have hac' : ∀ T, 0 ≤ T → ∀ i,
      AbsolutelyContinuousOnInterval (fun t => integrablePanRow D' R' U' t i) 0 T := by
    intro T hT i
    fin_cases i
    · exact hD' T hT
    · exact hR' T hT
    · exact hU' T hT
  have h := integrable_row_solution_unique Q (integrablePanRow D R U)
    (integrablePanRow D' R' U') hQi hQ hac hac'
    (integrablePanPreEquations_row he) (integrablePanPreEquations_row he')
    (by simp [integrablePanRow, hzero.1, hzero.2.1, hzero.2.2])
  exact ⟨fun t ht => congrFun (h t ht) 0, fun t ht => congrFun (h t ht) 1,
    fun t ht => congrFun (h t ht) 2⟩

theorem IntegrablePanPreModel.states_unique {rate : ℝ → ℝ}
    (P Q : IntegrablePanPreModel rate) (hρ : P.recomb = Q.recomb) :
    EqOn P.D Q.D (Ici 0) ∧ EqOn P.R Q.R (Ici 0) ∧ EqOn P.U Q.U (Ici 0) := by
  apply integrablePanPreEquations_unique rate P.recomb P.D P.R P.U Q.D Q.R Q.U
    P.rate_integrable P.recomb_integrable P.rate_nonneg P.recomb_nonneg
    P.D_ac P.R_ac P.U_ac Q.D_ac Q.R_ac Q.U_ac P.equations
  · simpa only [hρ] using Q.equations
  · exact ⟨P.initial.1.trans Q.initial.1.symm, P.initial.2.1.trans Q.initial.2.1.symm,
      P.initial.2.2.trans Q.initial.2.2.symm⟩

theorem IntegrablePanPreEquations.congr_rates {rate recomb rate' recomb' D R U : ℝ → ℝ}
    (he : IntegrablePanPreEquations rate recomb D R U)
    (hr : ∀ᵐ t, 0 ≤ t → rate t = rate' t)
    (hρ : ∀ᵐ t, 0 ≤ t → recomb t = recomb' t) :
    IntegrablePanPreEquations rate' recomb' D R U := by
  filter_upwards [he, hr, hρ] with t ht hrt hρt ht0
  simpa only [hrt ht0, hρt ht0] using ht ht0

theorem IntegrablePanPreModel.states_unique_ae {rate rate' : ℝ → ℝ}
    (P : IntegrablePanPreModel rate) (Q : IntegrablePanPreModel rate')
    (hr : ∀ᵐ t, 0 ≤ t → rate t = rate' t)
    (hρ : ∀ᵐ t, 0 ≤ t → P.recomb t = Q.recomb t) :
    EqOn P.D Q.D (Ici 0) ∧ EqOn P.R Q.R (Ici 0) ∧ EqOn P.U Q.U (Ici 0) := by
  apply integrablePanPreEquations_unique rate' Q.recomb P.D P.R P.U Q.D Q.R Q.U
    Q.rate_integrable Q.recomb_integrable Q.rate_nonneg Q.recomb_nonneg
    P.D_ac P.R_ac P.U_ac Q.D_ac Q.R_ac Q.U_ac
    (P.equations.congr_rates hr hρ) Q.equations
  exact ⟨P.initial.1.trans Q.initial.1.symm, P.initial.2.1.trans Q.initial.2.1.symm,
    P.initial.2.2.trans Q.initial.2.2.symm⟩

end Rhone.Statistics.Identifiability
