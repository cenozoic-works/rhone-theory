/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.HittingTime
public import Rhone.MarkovChain.CoreBridge
public import Rhone.MarkovChain.MoranSelection

/-!
# Moran trajectory mean absorption times

Source: ewens2004, sec. 3.4; altrock_traulsen2009, eq. (14). -/

@[expose] public section
namespace Rhone.MarkovChain

open MeasureTheory

/-- Source: ewens2004, sec. 3.4; altrock_traulsen2009, eq. (14). -/
theorem moranSelectionTime_eq_absorbTime (N : ℕ) {r : ℝ} (hr : 0 < r) :
    (fun i : Fin (N + 1) => moranSelectionTime N r i) =
      (moranChain N r hr).absorbTime (fixationBoundary N) := by
  apply FinChain.eq_absorbTime_of_step (moranChain_isAbsorbingSet N hr)
    (moranChain_reaches N hr)
  · intro a ha
    rcases mem_fixationBoundary.mp ha with rfl | rfl
    · exact moranSelectionTime_zero N r
    · exact moranSelectionTime_self N r
  · intro i hi
    have hint := pos_and_lt_of_notMem_fixationBoundary hi
    have hp := moranSelectionTime_poisson N hr i
    rw [ite_eq_left hint] at hp
    change (∑ j, moran N r i j * moranSelectionTime N r j) =
      moranSelectionTime N r i - 1 at hp
    change moranSelectionTime N r i =
      1 + ∑ j, moran N r i j * moranSelectionTime N r j
    linarith

/-- Source: ewens2004, sec. 3.4; altrock_traulsen2009, eq. (14). -/
theorem moranSelectionTime_lintegral_hitTime (N : ℕ) {r : ℝ} (hr : 0 < r)
    (i : Fin (N + 1)) :
    ∫⁻ ω, (Rhone.MarkovChain.hitTime (fixationBoundary N) ω : ENNReal)
      ∂(moranChain N r hr).pathLaw i =
      ENNReal.ofReal (moranSelectionTime N r i) := by
  rw [FinChain.lintegral_hitTime (moranChain_isAbsorbingSet N hr)
    (moranChain_reaches N hr)]
  exact congrArg ENNReal.ofReal (congrFun (moranSelectionTime_eq_absorbTime N hr) i).symm

/-- Source: ewens2004, sec. 3.4. -/
theorem moranAbsorptionTime_eq_absorbTime (N : ℕ) :
    (fun i : Fin (N + 1) => moranAbsorptionTime N i) =
      (moranChain N 1 (by norm_num)).absorbTime (fixationBoundary N) := by
  calc
    _ = (fun i : Fin (N + 1) => moranSelectionTime N 1 i) := by
      funext i
      exact (moranSelectionTime_one N i).symm
    _ = _ := moranSelectionTime_eq_absorbTime N (by norm_num)

/-- Source: ewens2004, sec. 3.4. -/
theorem moranAbsorptionTime_lintegral_hitTime (N : ℕ) (i : Fin (N + 1)) :
    ∫⁻ ω, (Rhone.MarkovChain.hitTime (fixationBoundary N) ω : ENNReal)
      ∂(moranChain N 1 (by norm_num)).pathLaw i =
      ENNReal.ofReal (moranAbsorptionTime N i) := by
  rw [moranSelectionTime_lintegral_hitTime N (by norm_num)]
  rw [moranSelectionTime_one]

end Rhone.MarkovChain
