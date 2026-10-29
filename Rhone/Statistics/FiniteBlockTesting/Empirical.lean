/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ThreeSiteRobustness.FiniteWeights
public import Rhone.Statistics.Identifiability.FinitePanelConcentration

/-! # Finite-alphabet empirical-frequency tests -/

@[expose] public section

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Rhone.Statistics.FiniteBlockTesting
open ThreeSiteRobustness Identifiability.FinitePanelSampling
variable {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]

open scoped Classical in
def atom (a x : X) : ℝ := if x = a then 1 else 0

omit [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X] in
theorem atom_bound (a x : X) : |atom a x| ≤ 1 := by
  unfold atom
  split_ifs <;> norm_num

omit [Fintype X] in
theorem atom_integral [Finite X] (μ : Measure X) [IsProbabilityMeasure μ] (a : X) :
    (∫ x, atom a x ∂μ) = μ.real {a} := by
  classical
  let := Fintype.ofFinite X
  rw [integral_fintype (by fun_prop)]
  simp [atom]

def frequencyRejects {N : ℕ} (P : Measure X) (r : ℝ) (x : Fin N → X) : Prop :=
  ∀ a, |sampleMean (atom a) x - P.real {a}| ≤ r

omit [MeasurableSingletonClass X] in
theorem close_frequencies_tv {N : ℕ} (P Q : Measure X) (r : ℝ) (x : Fin N → X)
    (hP : frequencyRejects P r x)
    (hQ : ∀ a, |sampleMean (atom a) x - Q.real {a}| ≤ r) :
    finiteTV P Q ≤ Fintype.card X * r := by
  have h (a : X) : |P.real {a} - Q.real {a}| ≤ 2 * r := by
    have ht := abs_add_le (P.real {a} - sampleMean (atom a) x)
      (sampleMean (atom a) x - Q.real {a})
    rw [sub_add_sub_cancel] at ht
    have hp : |P.real {a} - sampleMean (atom a) x| ≤ r := by
      rw [abs_sub_comm]
      exact hP a
    exact ht.trans (by have hq := hQ a; linarith)
  have hs := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) => h a)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
  unfold finiteTV
  linarith

theorem frequency_source_failure {N : ℕ} (P : Measure X) [IsProbabilityMeasure P]
    (hN : 0 < N) {r : ℝ} (hr : 0 ≤ r) :
    (iidLaw P N).real {x | ¬ frequencyRejects P r x} ≤
      2 * Fintype.card X * Real.exp (-(N : ℝ) * r ^ 2 / 2) := by
  have ht := iid_finite_scores_abs_ge P atom (fun _ => by fun_prop) atom_bound hN hr
  simp_rw [atom_integral] at ht
  apply le_trans (measureReal_mono ?_ (measure_ne_top _ _)) ht
  intro x hx
  change ¬ ∀ a, |sampleMean (atom a) x - P.real {a}| ≤ r at hx
  push Not at hx
  obtain ⟨a, ha⟩ := hx
  exact ⟨a, ha.le⟩

theorem frequency_null_size {N : ℕ} (P Q : Measure X) [IsProbabilityMeasure Q]
    (hN : 0 < N) {r δ : ℝ} (hr : 0 ≤ r)
    (hgap : δ ≤ finiteTV P Q) (hsmall : (Fintype.card X : ℝ) * r < δ) :
    (iidLaw Q N).real {x | frequencyRejects P r x} ≤
      2 * Fintype.card X * Real.exp (-(N : ℝ) * r ^ 2 / 2) := by
  have ht := iid_finite_scores_abs_ge Q atom (fun _ => by fun_prop) atom_bound hN hr
  simp_rw [atom_integral] at ht
  apply le_trans (measureReal_mono ?_ (measure_ne_top _ _)) ht
  intro x hx
  change ∃ a, r ≤ |sampleMean (atom a) x - Q.real {a}|
  by_contra hn
  push Not at hn
  have hv := close_frequencies_tv P Q r x hx (fun a => (hn a).le)
  linarith

end Rhone.Statistics.FiniteBlockTesting
