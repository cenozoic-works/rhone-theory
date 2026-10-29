/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.Coverage
public import Rhone.MarkovChain.CanningsReachability

/-! # Coverage instances for Wright–Fisher, Moran, and Cannings -/

@[expose] public section

namespace Rhone.MarkovChain

open MeasureTheory

instance (N : ℕ) : IsNeutralCounted (wfCounted N) := ⟨wfCounted_isNeutral N⟩

instance (N : ℕ) [hN : PositiveSize N] : HasClosedBoundary (wfCounted N) :=
  ⟨wfCounted_hasAbsorbingBoundary hN.pos⟩

instance (N : ℕ) : ReachesBoundary (wfCounted N) := ⟨wfCounted_reaches N⟩

theorem wf_fixation_via_classes (N : ℕ) [PositiveSize N] (i : Fin (N + 1)) :
    ((wfChain N).pathLaw i).real {ω | ∃ n, ω n = Fin.last N} = (i : ℝ) / N :=
  fixation_real_of_coverage (wfCounted N) i

instance (N : ℕ) : IsNeutralCounted (moranCounted N 1 one_pos) :=
  ⟨moranCounted_isNeutral N⟩

instance (N : ℕ) : HasClosedBoundary (moranCounted N 1 one_pos) :=
  ⟨moranCounted_hasAbsorbingBoundary N one_pos⟩

instance (N : ℕ) : ReachesBoundary (moranCounted N 1 one_pos) :=
  ⟨moranCounted_reaches N one_pos⟩

theorem moran_fixation_via_classes (N : ℕ) [PositiveSize N] (i : Fin (N + 1)) :
    ((moranChain N 1 one_pos).pathLaw i).real {ω | ∃ n, ω n = Fin.last N} = (i : ℝ) / N :=
  fixation_real_of_coverage (moranCounted N 1 one_pos) i

instance {N : ℕ} (C : FinChain (Fin (N + 1))) [hm : HasMartingaleCount C] :
    IsNeutralCounted (CountedChain.mk C id) :=
  ⟨countedId_isNeutral C hm.martingale⟩

instance {N : ℕ} (C : FinChain (Fin (N + 1))) [hm : HasMartingaleCount C] :
    HasClosedBoundary (CountedChain.mk C id) :=
  ⟨countedId_hasAbsorbingBoundary C hm.martingale⟩

instance {N : ℕ} {Ω : Type*} [Fintype Ω] (M : CanningsModel N Ω) :
    HasMartingaleCount M.countChain :=
  ⟨M.countChain_expect_count⟩

instance {N : ℕ} {Ω : Type*} [Fintype Ω] (M : CanningsModel N Ω)
    [hM : Fact (CanningsModel.NonDegenerate M)] :
    ReachesBoundary (CountedChain.mk M.countChain id) :=
  ⟨by rw [countedChain_id_boundary]; exact CanningsModel.countChain_reaches M hM.out⟩

theorem cannings_fixation_via_classes {N : ℕ} {Ω : Type*} [Fintype Ω] [PositiveSize N]
    (M : CanningsModel N Ω) [Fact (CanningsModel.NonDegenerate M)] (i : Fin (N + 1)) :
    (M.countChain.pathLaw i).real {ω | ∃ n, ω n = Fin.last N} = (i : ℝ) / N :=
  fixation_real_of_coverage (CountedChain.mk M.countChain id) i

theorem cannings_loss_via_classes {N : ℕ} {Ω : Type*} [Fintype Ω] [PositiveSize N]
    (M : CanningsModel N Ω) [Fact (CanningsModel.NonDegenerate M)] (i : Fin (N + 1)) :
    (M.countChain.pathLaw i).real {ω | ∃ n, ω n = 0} = 1 - (i : ℝ) / N :=
  loss_real_of_coverage (CountedChain.mk M.countChain id) i

theorem wfModel_fixation_via_classes (N : ℕ) (hN : 2 ≤ N) (i : Fin (N + 1)) :
    ((wfModel N).countChain.pathLaw i).real {ω | ∃ n, ω n = Fin.last N} = (i : ℝ) / N := by
  have : PositiveSize N := ⟨by omega⟩
  have : Fact (CanningsModel.NonDegenerate (wfModel N)) := ⟨wfModel_nonDegenerate hN⟩
  exact cannings_fixation_via_classes (wfModel N) i

end Rhone.MarkovChain
