/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.IntegrableMarkovFlow
public import Rhone.Statistics.Identifiability.IntegrableMarkovMass

/-! # Locally integrable finite-state Markov evolution -/

@[expose] public section

open Set Filter MeasureTheory
open scoped BigOperators Topology
namespace Rhone.Statistics.Identifiability
variable {ι : Type*} [Fintype ι]

theorem exists_integrable_subgenerator_solution (Q : ℝ → ι → ι → ℝ)
    (hQi : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume)
    (hQ : ∀ᵐ t, 0 ≤ t → ∀ i j, i ≠ j → 0 ≤ Q t i j)
    (hrows : ∀ᵐ t, 0 ≤ t → ∀ i, ∑ j, Q t i j ≤ 0)
    (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) :
    ∃ v : ℝ → ι → ℝ, v 0 = x ∧ Continuous v ∧
      (∀ a b, AbsolutelyContinuousOnInterval v a b) ∧
      (∀ a b i, AbsolutelyContinuousOnInterval (fun t => v t i) a b) ∧
      (∀ t, v t = x + ∫ s in (0 : ℝ)..t, inhomogeneousRowOperator (Q s) (v s)) ∧
      (∀ᵐ t, ∀ j, HasDerivAt (fun s => v s j) (∑ i, v t i * Q t i j) t) ∧
      (∀ t, 0 ≤ t → ∀ i, 0 ≤ v t i) ∧
      AntitoneOn (fun t => ∑ i, v t i) (Ici 0) ∧
      (∀ t, 0 ≤ t → (∑ i, v t i) ≤ ∑ i, x i) := by
  obtain ⟨v, hv0, hvc, hvac, hvaci, hvi, hve⟩ := exists_integrable_row_solution Q hQi x
  have he : ∀ᵐ t, 0 ≤ t → ∀ j,
      HasDerivAt (fun s => v s j) (∑ i, v t i * Q t i j) t :=
    hve.mono (fun _ ht _ => ht)
  have ha := fun t (_ : 0 ≤ t) i => hvaci 0 t i
  have hn := integrable_row_solution_nonneg Q v hQi hQ ha he
    (fun i => by simpa only [hv0] using hx i)
  refine ⟨v, hv0, hvc, hvac, hvaci, hvi, hve, hn,
    integrable_finiteRowODE_mass_antitoneOn Q v ha he hn hrows, ?_⟩
  intro t ht
  simpa only [hv0] using integrable_finiteRowODE_mass_le_initial Q v ha he hn hrows ht

theorem exists_integrable_generator_solution (Q : ℝ → ι → ι → ℝ)
    (hQi : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume)
    (hQ : ∀ᵐ t, 0 ≤ t → ∀ i j, i ≠ j → 0 ≤ Q t i j)
    (hrows : ∀ᵐ t, 0 ≤ t → ∀ i, ∑ j, Q t i j = 0)
    (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) :
    ∃ v : ℝ → ι → ℝ, v 0 = x ∧ Continuous v ∧
      (∀ a b, AbsolutelyContinuousOnInterval v a b) ∧
      (∀ a b i, AbsolutelyContinuousOnInterval (fun t => v t i) a b) ∧
      (∀ t, v t = x + ∫ s in (0 : ℝ)..t, inhomogeneousRowOperator (Q s) (v s)) ∧
      (∀ᵐ t, ∀ j, HasDerivAt (fun s => v s j) (∑ i, v t i * Q t i j) t) ∧
      (∀ t, 0 ≤ t → ∀ i, 0 ≤ v t i) ∧
      (∀ t, 0 ≤ t → (∑ i, v t i) = ∑ i, x i) := by
  obtain ⟨v, hv0, hvc, hvac, hvaci, hvi, hve⟩ := exists_integrable_row_solution Q hQi x
  have he : ∀ᵐ t, 0 ≤ t → ∀ j,
      HasDerivAt (fun s => v s j) (∑ i, v t i * Q t i j) t :=
    hve.mono (fun _ ht _ => ht)
  have ha := fun t (_ : 0 ≤ t) i => hvaci 0 t i
  have hn := integrable_row_solution_nonneg Q v hQi hQ ha he
    (fun i => by simpa only [hv0] using hx i)
  refine ⟨v, hv0, hvc, hvac, hvaci, hvi, hve, hn, ?_⟩
  intro t ht
  simpa only [hv0] using integrable_finiteRowODE_mass_eq_initial Q v ha he hrows ht

theorem exists_integrable_subgenerator_solution_with_survival
    (Q : ℝ → ι → ι → ℝ) (c : ℝ → ℝ)
    (hQi : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume)
    (hQ : ∀ᵐ t, 0 ≤ t → ∀ i j, i ≠ j → 0 ≤ Q t i j)
    (hrows : ∀ᵐ t, 0 ≤ t → ∀ i, ∑ j, Q t i j ≤ 0)
    (hc : LocallyIntegrable c volume)
    (hlower : ∀ᵐ t, 0 ≤ t → ∀ i, -c t ≤ ∑ j, Q t i j)
    (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) :
    ∃ v : ℝ → ι → ℝ, v 0 = x ∧ Continuous v ∧
      (∀ a b, AbsolutelyContinuousOnInterval v a b) ∧
      (∀ a b i, AbsolutelyContinuousOnInterval (fun t => v t i) a b) ∧
      (∀ t, v t = x + ∫ s in (0 : ℝ)..t, inhomogeneousRowOperator (Q s) (v s)) ∧
      (∀ᵐ t, ∀ j, HasDerivAt (fun s => v s j) (∑ i, v t i * Q t i j) t) ∧
      (∀ t, 0 ≤ t → ∀ i, 0 ≤ v t i) ∧
      AntitoneOn (fun t => ∑ i, v t i) (Ici 0) ∧
      (∀ t, 0 ≤ t → (∑ i, v t i) ≤ ∑ i, x i) ∧
      (∀ t, 0 ≤ t → (∑ i, x i) * Real.exp (-(∫ s in (0 : ℝ)..t, c s)) ≤ ∑ i, v t i) := by
  obtain ⟨v, hv0, hvc, hvac, hvaci, hvi, hve, hn, hm, hupper⟩ :=
    exists_integrable_subgenerator_solution Q hQi hQ hrows x hx
  refine ⟨v, hv0, hvc, hvac, hvaci, hvi, hve, hn, hm, hupper, ?_⟩
  intro t ht
  simpa only [hv0] using integrable_finiteRowODE_mass_clock_lower_bound Q v c
    (fun t _ i => hvaci 0 t i) (hve.mono (fun _ hs _ => hs)) hn hc hlower ht

end Rhone.Statistics.Identifiability
