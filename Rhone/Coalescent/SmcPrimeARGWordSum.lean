/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.SmcPrimeARGWordSectors

/-! # The one-split sector as a sum over finite event words -/

@[expose] public section

namespace Rhone.Coalescent.SmcPrime
open IntervalProcess SmcSupport MeasureTheory
open scoped ENNReal
attribute [local instance] Classical.propDecidable

def argPrefixFinalOne (n : ℕ) : Set (ARGPrefix n) :=
  {h | (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩).1.2.2.1 = 1}

theorem argPrefixFinalOne_measurable (n : ℕ) : MeasurableSet (argPrefixFinalOne n) :=
  measurableSet_eq_fun (IntervalProcess.liveCount_measurable.comp
    (measurable_pi_apply (⟨n, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic n)).fst) measurable_const

theorem argOneSector_indicator_sum (N : ℕ) (f : ARGPrefix (N + 1) → ℝ≥0∞)
    (h : ARGPrefix (N + 1)) :
    (oneSplitPrefixSector N).indicator f h =
      ∑' w : Fin (N + 1) → Action, if argFlatWordOneSplit w then
        (argWordSet (N + 1) (argFiniteWord w)).indicator
          ((argPrefixFinalOne (N + 1)).indicator f) h else 0 := by
  classical
  by_cases hs : h ∈ oneSplitPrefixSector N
  · obtain ⟨hw, hh⟩ := argPrefixSector_decoded N h hs
    have hc : h ∈ argPrefixFinalOne (N + 1) := hs.2
    rw [tsum_eq_single (argDecodedWord h)]
    · simp only [ite_eq_left hw, Set.indicator_of_mem hh, Set.indicator_of_mem hc,
        Set.indicator_of_mem hs]
    · intro w hneq
      by_cases hwo : argFlatWordOneSplit w
      · rw [ite_eq_left hwo, Set.indicator_of_notMem]
        intro hh'
        exact hneq (argDecodedWord_eq h w hh').symm
      · exact ite_eq_right hwo
  · rw [Set.indicator_of_notMem hs]
    symm
    apply ENNReal.tsum_eq_zero.mpr
    intro w
    by_cases hw : argFlatWordOneSplit w
    · rw [ite_eq_left hw]
      by_cases hh : h ∈ argWordSet (N + 1) (argFiniteWord w)
      · rw [Set.indicator_of_mem hh]
        apply Set.indicator_of_notMem
        intro hc
        exact hs (argWordSector_implies_prefix N h w hw hh hc)
      · exact Set.indicator_of_notMem hh _
    · exact ite_eq_right hw

theorem argOneSector_lintegral_sum (N : ℕ) (R : ℝ)
    (f : ARGPrefix (N + 1) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ h, f h ∂oneSplitARGPrefixLaw N R) =
      ∑' w : Fin (N + 1) → Action, if argFlatWordOneSplit w then
        ∫⁻ h, (argPrefixFinalOne (N + 1)).indicator f h
          ∂argWordPrefixLaw R (initialState N, (0, .inl ())) (N + 1) (argFiniteWord w)
      else 0 := by
  classical
  rw [oneSplitARGPrefixLaw, ← lintegral_indicator (oneSplitPrefixSector_measurable N)]
  rw [lintegral_congr (argOneSector_indicator_sum N f)]
  rw [lintegral_tsum]
  · apply tsum_congr
    intro w
    by_cases hw : argFlatWordOneSplit w
    · simp only [ite_eq_left hw]
      rw [lintegral_indicator (argWordSet_measurable (N + 1) (argFiniteWord w))]
      rfl
    · simp only [ite_eq_right hw, lintegral_zero]
  · intro w
    by_cases hw : argFlatWordOneSplit w
    · simp only [ite_eq_left hw]
      exact ((hf.indicator (argPrefixFinalOne_measurable (N + 1))).indicator
        (argWordSet_measurable (N + 1) (argFiniteWord w))).aemeasurable
    · simp only [ite_eq_right hw]
      exact measurable_const.aemeasurable
end Rhone.Coalescent.SmcPrime
