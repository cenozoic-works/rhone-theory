module

public import Rhone.MarkovChain.CanningsReachability

@[expose] public section

namespace Rhone.Palomar.NeutralFixation

open Finset MeasureTheory MarkovChain

theorem fixation_real_of_nonDegenerate {N : ℕ} {Ω : Type*} [Fintype Ω] (hN : 0 < N)
    (M : CanningsModel N Ω) (hM : CanningsModel.NonDegenerate M) (i : Fin (N + 1)) :
    (M.countChain.pathLaw i).real {ω | ∃ n, ω n = Fin.last N} = (i : ℝ) / N :=
  Rhone.MarkovChain.CanningsModel.fixation_real_of_nonDegenerate hN M hM i

theorem fixation_real_eventually_of_nonDegenerate {N : ℕ} {Ω : Type*} [Fintype Ω] (hN : 0 < N)
    (M : CanningsModel N Ω) (hM : CanningsModel.NonDegenerate M) (i : Fin (N + 1)) :
    (M.countChain.pathLaw i).real {ω | ∃ n, ∀ m, n ≤ m → ω m = Fin.last N} = (i : ℝ) / N :=
  Rhone.MarkovChain.CanningsModel.fixation_real_eventually_of_nonDegenerate hN M hM i

theorem loss_real_of_nonDegenerate {N : ℕ} {Ω : Type*} [Fintype Ω] (hN : 0 < N)
    (M : CanningsModel N Ω) (hM : CanningsModel.NonDegenerate M) (i : Fin (N + 1)) :
    (M.countChain.pathLaw i).real {ω | ∃ n, ω n = 0} = 1 - (i : ℝ) / N :=
  Rhone.MarkovChain.CanningsModel.loss_real_of_nonDegenerate hN M hM i

theorem fixation_real_of_not_nonDegenerate {N : ℕ} {Ω : Type*} [Fintype Ω]
    (M : CanningsModel N Ω) (hM : ¬ CanningsModel.NonDegenerate M) {i : Fin (N + 1)}
    (hi : i ≠ Fin.last N) :
    (M.countChain.pathLaw i).real {ω | ∃ n, ω n = Fin.last N} = 0 :=
  Rhone.MarkovChain.CanningsModel.fixation_real_of_not_nonDegenerate M hM hi

theorem cannings_fixation_ne_freq_without_reaches :
    ∃ M : CanningsModel 2 Unit,
      (M.countChain.pathLaw 1).real {ω | ∃ n, ω n = Fin.last 2} ≠ (1 : ℝ) / 2 :=
  Rhone.MarkovChain.cannings_fixation_ne_freq_without_reaches

theorem countChain_reaches_iff {N : ℕ} {Ω : Type*} [Fintype Ω] (M : CanningsModel N Ω)
    (hN : 2 ≤ N) :
    M.countChain.Reaches (fixationBoundary N) ↔ CanningsModel.NonDegenerate M :=
  Rhone.MarkovChain.CanningsModel.countChain_reaches_iff M hN

theorem nonDegenerate_iff_offspringProb_zero_pos {N : ℕ} {Ω : Type*} [Fintype Ω]
    (M : CanningsModel N Ω) (k : Fin N) :
    CanningsModel.NonDegenerate M ↔ 0 < CanningsModel.offspringProb M k 0 :=
  Rhone.MarkovChain.CanningsModel.nonDegenerate_iff_offspringProb_zero_pos M k

theorem nonDegenerate_iff_offspringProb_one_lt_one {N : ℕ} {Ω : Type*} [Fintype Ω]
    (M : CanningsModel N Ω) (k : Fin N) :
    CanningsModel.NonDegenerate M ↔ CanningsModel.offspringProb M k 1 < 1 :=
  Rhone.MarkovChain.CanningsModel.nonDegenerate_iff_offspringProb_one_lt_one M k

theorem nonDegenerate_iff_offspringVariance_pos {N : ℕ} {Ω : Type*} [Fintype Ω]
    (M : CanningsModel N Ω) (k : Fin N) :
    CanningsModel.NonDegenerate M ↔ 0 < CanningsModel.offspringSqDeviation M k :=
  Rhone.MarkovChain.CanningsModel.nonDegenerate_iff_offspringVariance_pos M k

theorem fixation_real_of_martingale {N : ℕ} (hN : 0 < N) (C : FinChain (Fin (N + 1)))
    (hm : ∀ i, C.expect (fun j => (j : ℝ)) i = i) (hR : C.Reaches (fixationBoundary N))
    (i : Fin (N + 1)) :
    (C.pathLaw i).real {ω | ∃ n, ω n = Fin.last N} = (i : ℝ) / N :=
  Rhone.MarkovChain.fixation_real_of_martingale hN C hm hR i

theorem moranModel_nonDegenerate {N : ℕ} (hN : 2 ≤ N) (h : 0 < N) :
    CanningsModel.NonDegenerate (moranModel N h) :=
  Rhone.MarkovChain.moranModel_nonDegenerate hN h

theorem moranModel_fixation_real {N : ℕ} (hN : 2 ≤ N) (h : 0 < N) (i : Fin (N + 1)) :
    ((moranModel N h).countChain.pathLaw i).real {ω | ∃ n, ω n = Fin.last N} = (i : ℝ) / N :=
  Rhone.MarkovChain.moranModel_fixation_real hN h i

end Rhone.Palomar.NeutralFixation
