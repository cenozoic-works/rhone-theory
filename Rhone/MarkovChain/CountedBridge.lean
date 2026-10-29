/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.CountedChain
public import Rhone.MarkovChain.CoreBridge

/-! # The Wright–Fisher and Moran chains as chains with an allele count -/

@[expose] public section

namespace Rhone.MarkovChain

open Finset

variable {N : ℕ}

theorem countedChain_id_boundary (C : FinChain (Fin (N + 1))) :
    (CountedChain.mk C id).boundary = fixationBoundary N := by
  ext i
  rw [CountedChain.mem_boundary, mem_fixationBoundary]
  exact or_comm

noncomputable def wfCounted (N : ℕ) : CountedChain (Fin (N + 1)) N where
  toFinChain := wfChain N
  count := id

theorem wfCounted_boundary (N : ℕ) : (wfCounted N).boundary = fixationBoundary N :=
  countedChain_id_boundary _

theorem wfCounted_hasAbsorbingBoundary (hN : 0 < N) : (wfCounted N).HasAbsorbingBoundary :=
  CountedChain.hasAbsorbingBoundary_of_isAbsorbing fun s hs =>
    wfChain_isAbsorbingSet hN s (mem_fixationBoundary.2 hs)

theorem wfCounted_reaches (N : ℕ) : (wfCounted N).toFinChain.Reaches (wfCounted N).boundary := by
  rw [wfCounted_boundary]
  exact wfChain_reaches N

variable {r : ℝ}

noncomputable def moranCounted (N : ℕ) (r : ℝ) (hr : 0 < r) : CountedChain (Fin (N + 1)) N where
  toFinChain := moranChain N r hr
  count := id

theorem moranCounted_boundary (N : ℕ) (hr : 0 < r) :
    (moranCounted N r hr).boundary = fixationBoundary N :=
  countedChain_id_boundary _

theorem moranCounted_hasAbsorbingBoundary (N : ℕ) (hr : 0 < r) :
    (moranCounted N r hr).HasAbsorbingBoundary :=
  CountedChain.hasAbsorbingBoundary_of_isAbsorbing fun s hs =>
    moranChain_isAbsorbingSet N hr s (mem_fixationBoundary.2 hs)

theorem moranCounted_reaches (N : ℕ) (hr : 0 < r) :
    (moranCounted N r hr).toFinChain.Reaches (moranCounted N r hr).boundary := by
  rw [moranCounted_boundary]
  exact moranChain_reaches N hr

end Rhone.MarkovChain
