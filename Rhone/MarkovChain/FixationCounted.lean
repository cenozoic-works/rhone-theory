/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.CountedBridge
public import Rhone.MarkovChain.FixationHarmonic

/-! # Neutral fixation for Wright–Fisher and Moran from the general theorem -/

@[expose] public section

namespace Rhone.MarkovChain

open Finset MeasureTheory

variable {N : ℕ}

theorem wfCounted_isNeutral (N : ℕ) : (wfCounted N).IsNeutral :=
  (CountKernel.toFinChain_isHarmonic (wf N) (wf_isStochastic N) _).2 (wf_isHarmonic_freq N)

theorem moranCounted_isNeutral (N : ℕ) : (moranCounted N 1 one_pos).IsNeutral :=
  (CountKernel.toFinChain_isHarmonic (moran N 1) (moran_isStochastic one_pos N) _).2
    (moran_isHarmonic_freq N)

theorem wf_fixation_real_of_counted (hN : 0 < N) (i : Fin (N + 1)) :
    ((wfChain N).pathLaw i).real {ω | ∃ n, ω n = Fin.last N} = (i : ℝ) / N :=
  CountedChain.fixation_real hN (wfCounted_isNeutral N) (wfCounted_hasAbsorbingBoundary hN)
    (wfCounted_reaches N) i

theorem wf_loss_real (hN : 0 < N) (i : Fin (N + 1)) :
    ((wfChain N).pathLaw i).real {ω | ∃ n, ω n = 0} = 1 - (i : ℝ) / N :=
  CountedChain.loss_real hN (wfCounted_isNeutral N) (wfCounted_hasAbsorbingBoundary hN)
    (wfCounted_reaches N) i

theorem moran_fixation_real_neutral_of_counted (hN : 0 < N) (i : Fin (N + 1)) :
    ((moranChain N 1 one_pos).pathLaw i).real {ω | ∃ n, ω n = Fin.last N} = (i : ℝ) / N :=
  CountedChain.fixation_real hN (moranCounted_isNeutral N)
    (moranCounted_hasAbsorbingBoundary N one_pos) (moranCounted_reaches N one_pos) i

theorem moran_loss_real_neutral (hN : 0 < N) (i : Fin (N + 1)) :
    ((moranChain N 1 one_pos).pathLaw i).real {ω | ∃ n, ω n = 0} = 1 - (i : ℝ) / N :=
  CountedChain.loss_real hN (moranCounted_isNeutral N)
    (moranCounted_hasAbsorbingBoundary N one_pos) (moranCounted_reaches N one_pos) i

end Rhone.MarkovChain
