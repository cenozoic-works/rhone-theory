/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.HittingTime
public import Rhone.MarkovChain.CoreBridge
public import Rhone.MarkovChain.FixationHarmonic

/-! # Fixation probabilities as probabilities of trajectories -/

@[expose] public section

namespace Rhone.MarkovChain

open Finset MeasureTheory

variable {N : ℕ}

theorem fixation_real_eq_of_harmonic_unique (hN : 0 < N) (P : CountKernel N)
    (hP : P.IsStochastic) (h0 : (P.toFinChain hP).IsAbsorbing 0)
    (hlast : (P.toFinChain hP).IsAbsorbing (Fin.last N)) {φ : Fin (N + 1) → ℝ}
    (huniq : ∀ h : Fin (N + 1) → ℝ, P.IsHarmonic h → h 0 = 0 → h (Fin.last N) = 1 →
      ∀ i, h i = φ i) (i : Fin (N + 1)) :
    ((P.toFinChain hP).pathLaw i).real {ω | ∃ n, ω n = Fin.last N} = φ i := by
  have hne : (0 : Fin (N + 1)) ≠ Fin.last N := fun h => by
    have := congrArg Fin.val h
    simp only [Fin.val_zero, Fin.val_last] at this
    omega
  rw [FinChain.pathLaw_hit_eq_absorbProb hlast]
  refine huniq _ ((CountKernel.toFinChain_isHarmonic P hP _).1
    (FinChain.absorbProb_isHarmonic hlast)) ?_ ?_ i
  · rw [FinChain.absorbProb_of_isAbsorbing h0, ite_eq_right hne]
  · rw [FinChain.absorbProb_of_isAbsorbing hlast, ite_eq_left rfl]

theorem wf_fixation_real (hN : 0 < N) (i : Fin (N + 1)) :
    ((wfChain N).pathLaw i).real {ω | ∃ n, ω n = Fin.last N} = (i : ℝ) / N :=
  fixation_real_eq_of_harmonic_unique hN (wf N) (wf_isStochastic N)
    (wfChain_isAbsorbing_zero N) (wfChain_isAbsorbing_last hN)
    (fun h hh h0 h1 j => wf_harmonic_unique hN h hh h0 h1 j) i

theorem wf_fixation_real_eventually (hN : 0 < N) (i : Fin (N + 1)) :
    ((wfChain N).pathLaw i).real {ω | ∃ n, ∀ m, n ≤ m → ω m = Fin.last N} = (i : ℝ) / N := by
  rw [FinChain.pathLaw_absorbed_eq_hit (wfChain_isAbsorbing_last hN), wf_fixation_real hN]

theorem wf_ae_absorbed (hN : 0 < N) (i : Fin (N + 1)) :
    ∀ᵐ ω ∂(wfChain N).pathLaw i, ∃ n, ω n = 0 ∨ ω n = Fin.last N := by
  filter_upwards [FinChain.ae_exists_mem (wfChain_isAbsorbingSet hN) (wfChain_reaches N) i]
    with ω ⟨n, hn⟩
  exact ⟨n, mem_fixationBoundary.1 hn⟩

theorem wf_lintegral_hitTime (hN : 0 < N) (i : Fin (N + 1)) :
    ∫⁻ ω, (hitTime (fixationBoundary N) ω : ENNReal) ∂(wfChain N).pathLaw i =
      ENNReal.ofReal ((wfChain N).absorbTime (fixationBoundary N) i) :=
  FinChain.lintegral_hitTime (wfChain_isAbsorbingSet hN) (wfChain_reaches N) i

variable {r : ℝ}

theorem moran_fixation_real (hN : 0 < N) (hr : 0 < r) (i : Fin (N + 1)) :
    ((moranChain N r hr).pathLaw i).real {ω | ∃ n, ω n = Fin.last N} = moranFixProb N r i :=
  fixation_real_eq_of_harmonic_unique hN (moran N r) (moran_isStochastic hr N)
    (moranChain_isAbsorbing_zero N hr) (moranChain_isAbsorbing_last N hr)
    (φ := fun j => moranFixProb N r j)
    (fun h hh h0 h1 j => moran_harmonic_unique hN hr h hh h0 h1 j) i

theorem moran_fixation_real_neutral (hN : 0 < N) (i : Fin (N + 1)) :
    ((moranChain N 1 one_pos).pathLaw i).real {ω | ∃ n, ω n = Fin.last N} = (i : ℝ) / N := by
  rw [moran_fixation_real hN one_pos, moranFixProb_one]

theorem moran_fixation_real_selection (hN : 0 < N) (hr : 0 < r) (hr1 : r ≠ 1)
    (i : Fin (N + 1)) :
    ((moranChain N r hr).pathLaw i).real {ω | ∃ n, ω n = Fin.last N} =
      (1 - (r⁻¹) ^ (i : ℕ)) / (1 - (r⁻¹) ^ N) := by
  rw [moran_fixation_real hN hr, moranFixProb_of_ne_one hr1]

theorem moran_fixation_real_eventually (hN : 0 < N) (hr : 0 < r) (i : Fin (N + 1)) :
    ((moranChain N r hr).pathLaw i).real {ω | ∃ n, ∀ m, n ≤ m → ω m = Fin.last N} =
      moranFixProb N r i := by
  rw [FinChain.pathLaw_absorbed_eq_hit (moranChain_isAbsorbing_last N hr),
    moran_fixation_real hN hr]

theorem moran_ae_absorbed (hr : 0 < r) (i : Fin (N + 1)) :
    ∀ᵐ ω ∂(moranChain N r hr).pathLaw i, ∃ n, ω n = 0 ∨ ω n = Fin.last N := by
  filter_upwards [FinChain.ae_exists_mem (moranChain_isAbsorbingSet N hr)
    (moranChain_reaches N hr) i] with ω ⟨n, hn⟩
  exact ⟨n, mem_fixationBoundary.1 hn⟩

end Rhone.MarkovChain
