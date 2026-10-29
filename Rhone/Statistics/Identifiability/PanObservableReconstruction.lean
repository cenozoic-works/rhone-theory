/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.PanReconstructionODE
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Reconstruct the three pre-merger coordinates from the observable invariants -/

@[expose] public section

namespace Rhone.Statistics.Identifiability

set_option backward.isDefEq.respectTransparency false

noncomputable def reconstructedR (D Z : ℝ → ℝ) : ℝ → ℝ :=
  fun t => Z t * Real.sqrt (D t) - 2 * D t

noncomputable def reconstructedU (D G Z : ℝ → ℝ) : ℝ → ℝ :=
  fun t => G t + D t - Z t * Real.sqrt (D t)

theorem reconstructedR_continuous (D Z : ℝ → ℝ)
    (hD : Continuous D) (hZ : Continuous Z) : Continuous (reconstructedR D Z) := by
  unfold reconstructedR
  fun_prop

theorem reconstructedU_continuous (D G Z : ℝ → ℝ)
    (hD : Continuous D) (hG : Continuous G) (hZ : Continuous Z) :
    Continuous (reconstructedU D G Z) := by
  unfold reconstructedU
  fun_prop

theorem reconstructed_masses_initial (D G Z : ℝ → ℝ)
    (hD : D 0 = 1) (hG : G 0 = 1) (hZ : Z 0 = 2) :
    D 0 = 1 ∧ reconstructedR D Z 0 = 0 ∧ reconstructedU D G Z 0 = 0 := by
  norm_num [reconstructedR, reconstructedU, hD, hG, hZ]

theorem reconstructed_masses_total (D G Z : ℝ → ℝ) (t : ℝ) :
    D t + reconstructedR D Z t + reconstructedU D G Z t = G t := by
  simp only [reconstructedR, reconstructedU]
  ring

theorem reconstructed_masses_invariant (D Z : ℝ → ℝ) {t : ℝ} (hD : 0 < D t) :
    (reconstructedR D Z t + 2 * D t) / Real.sqrt (D t) = Z t := by
  have hs : Real.sqrt (D t) ≠ 0 := (Real.sqrt_pos.2 hD).ne'
  simp [reconstructedR, hs]

theorem pan_observables_reconstruct_at (rate recomb D G Z : ℝ → ℝ) {t : ℝ}
    (hD : 0 < D t)
    (hd : HasDerivAt D ((rate t / Real.sqrt (D t) * Z t - 3 * rate t - 2 * recomb t) * D t) t)
    (hg : HasDerivAt G (rate t * D t - 2 * rate t * G t) t)
    (hz : HasDerivAt Z (-(7 / 2 : ℝ) * rate t * Z t +
      4 * (rate t / Real.sqrt (D t)) * G t + 4 * (rate t * Real.sqrt (D t)) -
      (1 / 2 : ℝ) * (rate t / Real.sqrt (D t)) * (Z t) ^ 2) t) :
    HasDerivAt D (-(rate t + 2 * recomb t) * D t + rate t * reconstructedR D Z t) t ∧
    HasDerivAt (reconstructedR D Z)
      (2 * recomb t * D t - (3 * rate t + recomb t) * reconstructedR D Z t +
        4 * rate t * reconstructedU D G Z t) t ∧
    HasDerivAt (reconstructedU D G Z)
      (recomb t * reconstructedR D Z t - 6 * rate t * reconstructedU D G Z t) t := by
  have hs : Real.sqrt (D t) ≠ 0 := (Real.sqrt_pos.2 hD).ne'
  have hs2 := Real.sq_sqrt hD.le
  refine ⟨?_, ?_, ?_⟩
  · convert! hd using 1
    dsimp [reconstructedR]
    generalize hsdef : Real.sqrt (D t) = s at *
    rw [← hs2]
    field_simp
    ring
  · convert! (hz.mul (hd.sqrt hD.ne')).sub (hd.const_mul 2) using 1
    dsimp [reconstructedR, reconstructedU]
    generalize hsdef : Real.sqrt (D t) = s at *
    rw [← hs2]
    field_simp
    ring
  · convert! (hg.add hd).sub (hz.mul (hd.sqrt hD.ne')) using 1
    dsimp [reconstructedR, reconstructedU]
    generalize hsdef : Real.sqrt (D t) = s at *
    rw [← hs2]
    field_simp
    ring

theorem pan_observables_reconstruct_equations (rate recomb D G Z : ℝ → ℝ)
    (hD : ∀ t, 0 ≤ t → 0 < D t)
    (hd : ∀ t, 0 ≤ t → HasDerivAt D
      ((rate t / Real.sqrt (D t) * Z t - 3 * rate t - 2 * recomb t) * D t) t)
    (hg : ∀ t, 0 ≤ t → HasDerivAt G (rate t * D t - 2 * rate t * G t) t)
    (hz : ∀ t, 0 ≤ t → HasDerivAt Z (-(7 / 2 : ℝ) * rate t * Z t +
      4 * (rate t / Real.sqrt (D t)) * G t + 4 * (rate t * Real.sqrt (D t)) -
      (1 / 2 : ℝ) * (rate t / Real.sqrt (D t)) * (Z t) ^ 2) t) :
    PanPreEquations rate recomb D (reconstructedR D Z) (reconstructedU D G Z) := by
  intro t ht
  exact pan_observables_reconstruct_at rate recomb D G Z (hD t ht) (hd t ht) (hg t ht) (hz t ht)

end Rhone.Statistics.Identifiability
