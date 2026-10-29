/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.DriftProof
public import Rhone.MarkovChain.FixationTrajectory

/-! # Executable drift values equal the mathematical trajectory quantities -/

@[expose] public section
namespace Rhone.Computation.Drift
open MeasureTheory

theorem wf_fixation_real (n : Nat) (hn : 0 < n) (i : Fin (n + 1)) :
    (neutralFixation n i : Real) =
      ((Rhone.MarkovChain.wfChain n).pathLaw i).real {ω | ∃ t, ω t = Fin.last n} := by
  rw [Rhone.MarkovChain.wf_fixation_real hn, neutralFixation_cast]

theorem moran_neutral_fixation_real (n : Nat) (hn : 0 < n) (i : Fin (n + 1)) :
    (neutralFixation n i : Real) =
      ((Rhone.MarkovChain.moranChain n 1 one_pos).pathLaw i).real
        {ω | ∃ t, ω t = Fin.last n} := by
  rw [Rhone.MarkovChain.moran_fixation_real_neutral hn, neutralFixation_cast]

theorem moran_fixation_real (n : Nat) (hn : 0 < n) (r : Rat)
    (hr : 0 < (r : Real)) (i : Fin (n + 1)) :
    (moranFixation n r i : Real) =
      ((Rhone.MarkovChain.moranChain n (r : Real) hr).pathLaw i).real
        {ω | ∃ t, ω t = Fin.last n} := by
  rw [Rhone.MarkovChain.moran_fixation_real hn hr, moranFixation_cast]

theorem wf_heterozygosity_integral (n t : Nat) (i : Fin (n + 1)) :
    (wfHeterozygosity n i t : Real) =
      ∫ ω, Rhone.MarkovChain.het n (ω t) ∂(Rhone.MarkovChain.wfChain n).pathLaw i := by
  rw [Rhone.MarkovChain.FinChain.integral_eval (Rhone.MarkovChain.wfChain n) t
    (fun j : Fin (n + 1) => Rhone.MarkovChain.het n j) i]
  rw [Rhone.MarkovChain.wfChain, Rhone.MarkovChain.CountKernel.toFinChain_expectN]
  exact wfHeterozygosity_cast n t i

theorem moran_heterozygosity_integral (n t : Nat) (i : Fin (n + 1)) :
    (moranHeterozygosity n i t : Real) =
      ∫ ω, Rhone.MarkovChain.het n (ω t)
        ∂(Rhone.MarkovChain.moranChain n 1 one_pos).pathLaw i := by
  rw [Rhone.MarkovChain.FinChain.integral_eval (Rhone.MarkovChain.moranChain n 1 one_pos) t
    (fun j : Fin (n + 1) => Rhone.MarkovChain.het n j) i]
  rw [Rhone.MarkovChain.moranChain, Rhone.MarkovChain.CountKernel.toFinChain_expectN]
  exact moranHeterozygosity_cast n t i

end Rhone.Computation.Drift
