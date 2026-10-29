/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.Witness

/-! # A universal panmictic event-flux constraint -/

@[expose] public section

namespace Rhone.Statistics.Identifiability

abbrev PanState := Fin 3

def panShape : PanState → MarkovChain.Identifiability.Shape :=
    ![MarkovChain.Identifiability.shape 0, MarkovChain.Identifiability.shape 2,
    MarkovChain.Identifiability.shape 7]

theorem pan_event_counts :
    (∀ i, MarkovChain.Identifiability.firstACount (panShape i) = (![0, 1, 1] : PanState → Nat) i) ∧
    (∀ i, MarkovChain.Identifiability.firstAThenBCount (panShape i) = (![0, 1, 1] : PanState → Nat)
        i) := by
  constructor <;> intro i <;> fin_cases i <;> decide

noncomputable def panFirstA (rate : ℝ) (mass : PanState → ℝ) : ℝ :=
  rate * ∑ i, mass i * (MarkovChain.Identifiability.firstACount (panShape i) : ℝ)

noncomputable def panNextB (rate : ℝ) (mass : PanState → ℝ) : ℝ :=
  rate^2 * ∑ i, mass i * (MarkovChain.Identifiability.firstAThenBCount (panShape i) : ℝ)

noncomputable def panPairDensity (rate survival : ℝ) : ℝ := rate * survival

theorem pan_flux_factorization (rate : ℝ) (mass : PanState → ℝ) :
    panNextB rate mass = rate * panFirstA rate mass := by
  simp only [panNextB, panFirstA, pan_event_counts.1, pan_event_counts.2]
  ring

theorem pan_witness_zero (rate survival : ℝ) (mass : PanState → ℝ) :
    survival * panNextB rate mass - panPairDensity rate survival * panFirstA rate mass = 0 := by
  rw [pan_flux_factorization]
  unfold panPairDensity
  ring

theorem no_matching_pan_forward_observables (k : Nat) {c q r : ℝ}
    (hc : 0 < c) (hq : 0 < q) (hr : 0 < r) :
    ¬ ∃ (rate survival : ℝ → ℝ) (mass : ℝ → PanState → ℝ),
      ∀ t, 0 ≤ t →
        survivalJet k c q 0 t = survival t ∧
        densityJet k c q 0 t = panPairDensity (rate t) (survival t) ∧
        firstAJet k c q r 0 t = panFirstA (rate t) (mass t) ∧
        postBJet k c q r 0 t = panNextB (rate t) (mass t) := by
  rintro ⟨rate, survival, mass, hmatch⟩
  apply island_witness_not_identically_zero k hc hq hr
  intro t ht
  rcases hmatch t ht with ⟨hs, hf, hb, hj⟩
  unfold witness
  rw [hs, hf, hb, hj]
  exact pan_witness_zero (rate t) (survival t) (mass t)

end Rhone.Statistics.Identifiability
