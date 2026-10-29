/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.IntegrablePanClock
public import Rhone.Statistics.Identifiability.IntegrableMarkovCoordinate

/-! # Existence of the locally integrable pan model -/

@[expose] public section

open Set Filter MeasureTheory
open scoped BigOperators Topology
namespace Rhone.Statistics.Identifiability

theorem exists_integrablePanPreModel (rate recomb : ℝ → ℝ)
    (hr : LocallyIntegrableOn rate (Ici 0) volume)
    (hρ : LocallyIntegrableOn recomb (Ici 0) volume)
    (hrn : ∀ᵐ t, 0 ≤ t → 0 ≤ rate t)
    (hρn : ∀ᵐ t, 0 ≤ t → 0 ≤ recomb t) :
    ∃ P : IntegrablePanPreModel rate, P.recomb = recomb := by
  let Q := fun t => integrablePanGenerator (panZeroExtension rate t) (panZeroExtension recomb t)
  have hQi : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume :=
    integrablePanGenerator_locallyIntegrable (panZeroExtension_locallyIntegrable hr)
      (panZeroExtension_locallyIntegrable hρ)
  have hQ : ∀ᵐ t, 0 ≤ t → ∀ i j, i ≠ j → 0 ≤ Q t i j := by
    filter_upwards [hrn, hρn] with t hrt hρt ht
    simpa only [Q, panZeroExtension_of_nonneg rate ht,
      panZeroExtension_of_nonneg recomb ht] using
      integrablePanGenerator_offdiag_nonneg (hrt ht) (hρt ht)
  have hrows : ∀ᵐ t, 0 ≤ t → ∀ i, ∑ j, Q t i j ≤ 0 := by
    filter_upwards [hrn] with t hrt ht
    simpa only [Q, panZeroExtension_of_nonneg rate ht,
      panZeroExtension_of_nonneg recomb ht] using
      integrablePanGenerator_rows_nonpos (recomb := recomb t) (hrt ht)
  obtain ⟨v, hv0, _, _, hvac, _, hve, hn, _, _⟩ :=
    exists_integrable_subgenerator_solution Q hQi hQ hrows ![1, 0, 0]
      (by intro i; fin_cases i <;> norm_num)
  have ha := fun t (_ : 0 ≤ t) i => hvac 0 t i
  have he : ∀ᵐ t, 0 ≤ t → ∀ j,
      HasDerivAt (fun s => v s j) (∑ i, v t i * Q t i j) t :=
    hve.mono (fun _ ht _ => ht)
  have hDpos : ∀ t, 0 ≤ t → 0 < v t 0 := by
    intro t ht
    exact integrable_row_coordinate_pos Q v 0 hQ ha he hn (hQi 0 0)
      (by simp [hv0]) ht
  refine ⟨{
    recomb := recomb
    D := fun t => v t 0
    R := fun t => v t 1
    U := fun t => v t 2
    rate_integrable := hr
    recomb_integrable := hρ
    rate_nonneg := hrn
    recomb_nonneg := hρn
    D_ac := fun t ht => ha t ht 0
    R_ac := fun t ht => ha t ht 1
    U_ac := fun t ht => ha t ht 2
    D_positive := hDpos
    R_nonneg := fun t ht => hn t ht 1
    U_nonneg := fun t ht => hn t ht 2
    initial := by simp [hv0]
    equations := integrablePanPreEquations_of_row he }, rfl⟩

theorem exists_properIntegrablePanModel (rate recomb : ℝ → ℝ)
    (hr : LocallyIntegrableOn rate (Ici 0) volume)
    (hρ : LocallyIntegrableOn recomb (Ici 0) volume)
    (hrn : ∀ᵐ t, 0 ≤ t → 0 ≤ rate t)
    (hρn : ∀ᵐ t, 0 ≤ t → 0 ≤ recomb t)
    (htail : Tendsto (integrablePanClock rate) atTop atTop) :
    ∃ P : ProperIntegrablePanModel, P.rate = rate ∧ P.pre.recomb = recomb := by
  obtain ⟨P, hp⟩ := exists_integrablePanPreModel rate recomb hr hρ hrn hρn
  exact ⟨⟨rate, P, htail⟩, rfl, hp⟩

end Rhone.Statistics.Identifiability
