/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.CommonClockIslandPhase

/-! # Pre and post blocks of the common-clock island phase generator and reward -/

@[expose] public section

open scoped Matrix Matrix.Norms.Operator
namespace Rhone.Statistics.Identifiability

@[simp] theorem commonClockIslandPhase_pre_pre (k : ℕ) (c q r : ℝ) (i j : Fin 16) :
    commonClockIslandPhase k c q r (Fin.castAdd 2 i) (Fin.castAdd 2 j) =
      MarkovChain.Identifiability.generator k c q r i j := by
  simp [commonClockIslandPhase]

@[simp] theorem commonClockIslandPhase_pre_post (k : ℕ) (c q r : ℝ)
    (i : Fin 16) (j : Fin 2) :
    commonClockIslandPhase k c q r (Fin.castAdd 2 i) (Fin.natAdd 16 j) =
      commonClockFirstRate c i j := by
  simp [commonClockIslandPhase]

@[simp] theorem commonClockIslandPhase_post_pre (k : ℕ) (c q r : ℝ)
    (i : Fin 2) (j : Fin 16) :
    commonClockIslandPhase k c q r (Fin.natAdd 16 i) (Fin.castAdd 2 j) = 0 := by
  simp [commonClockIslandPhase]

@[simp] theorem commonClockIslandPhase_post_post (k : ℕ) (c q r : ℝ) (i j : Fin 2) :
    commonClockIslandPhase k c q r (Fin.natAdd 16 i) (Fin.natAdd 16 j) =
      2 * MarkovChain.Identifiability.pairGenerator k c q i j := by
  simp [commonClockIslandPhase]

@[simp] theorem commonClockIslandReward_pre (c : ℝ) (i : Fin 16) :
    commonClockIslandReward c (Fin.castAdd 2 i) = markRates c i 0 / 2 := by
  simp [commonClockIslandReward]

@[simp] theorem commonClockIslandReward_post (c : ℝ) (i : Fin 2) :
    commonClockIslandReward c (Fin.natAdd 16 i) = MarkovChain.Identifiability.pairDensity c i := by
  simp [commonClockIslandReward]

end Rhone.Statistics.Identifiability
