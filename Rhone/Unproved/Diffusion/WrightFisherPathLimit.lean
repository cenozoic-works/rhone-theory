/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Diffusion.InterpolatedPath
public import Rhone.MarkovChain.Trajectory
public import Rhone.Diffusion.MartingaleProblem
public import Rhone.Diffusion.WrightFisherUniqueness
public import Rhone.Diffusion.WrightFisherGeneratorLimit
public import Rhone.Diffusion.CanningsGeneratorLimit
public import Rhone.Diffusion.CanningsPathLimit

/-!
# Convergence in law of the paths to the Wright–Fisher diffusion

Source: ethier_kurtz1986, ch. 10, sec. 1, ch. 4, ch. 1, sec. 6. -/

@[expose] public section

namespace Rhone.Unproved

open MeasureTheory Filter Topology Diffusion MarkovChain Analysis
open scoped NNReal BoundedContinuousFunction

/-- Source: ethier_kurtz1986, ch. 8, ch. 10, sec. 1. -/
theorem wrightFisherDiffusionLaw_exists {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ∃ P : Measure C(ℝ≥0, ℝ), IsWrightFisherDiffusionLaw x P :=
  Rhone.Diffusion.wrightFisherDiffusionLaw_exists hx

/-- Source: ethier_kurtz1986, ch. 8, ch. 10, sec. 1. -/
theorem wrightFisherDiffusionLaw_existsUnique {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ∃! P : Measure C(ℝ≥0, ℝ), IsWrightFisherDiffusionLaw x P := by
  obtain ⟨P, hP⟩ := wrightFisherDiffusionLaw_exists hx
  exact ⟨P, hP, fun Q hQ => hQ.unique hP⟩

/-- Source: ethier_kurtz1986, ch. 10, sec. 1. -/
theorem wfChain_pathLaw_tendsto_wrightFisherDiffusion (i : ∀ N : ℕ, Fin (N + 1)) {x : ℝ}
    (hx : Tendsto (fun N : ℕ => ((i N : ℕ) : ℝ) / N) atTop (𝓝 x))
    {P : Measure C(ℝ≥0, ℝ)} (hP : IsWrightFisherDiffusionLaw x P) (F : C(ℝ≥0, ℝ) →ᵇ ℝ) :
    Tendsto (fun N : ℕ => ∫ ω, F (rescaledPath (N : ℝ) fun m => ((ω m : ℕ) : ℝ) / N)
        ∂((wfChain N).pathLaw (i N)))
      atTop (𝓝 (∫ w, F w ∂P)) :=
  Rhone.Diffusion.wfChain_pathLaw_tendsto_wrightFisherDiffusion i hx hP F

/-- Source: mohle2001, Thm 3.3, p. 143; ethier_kurtz1986, ch. 1, sec. 6, ch. 4, sec. 2. -/
theorem cannings_pathLaw_tendsto_wrightFisherDiffusion {Ω : ℕ → Type*} [∀ n, Fintype (Ω n)]
    (N : ℕ → ℕ) (M : ∀ n, CanningsModel (N n) (Ω n)) (k : ∀ n, Fin (N n))
    (hvar : ∀ᶠ n in atTop, 0 < (M n).offspringVariance (k n))
    (h3 : Tendsto (fun n => (M n).offspringAbsThirdMoment (k n) /
      ((N n : ℝ) * (M n).offspringVariance (k n))) atTop (𝓝 0))
    (i : ∀ n, Fin (N n + 1)) {x : ℝ}
    (hx : Tendsto (fun n => ((i n : ℕ) : ℝ) / N n) atTop (𝓝 x))
    {P : Measure C(ℝ≥0, ℝ)} (hP : IsWrightFisherDiffusionLaw x P) (F : C(ℝ≥0, ℝ) →ᵇ ℝ) :
    Tendsto (fun n => ∫ ω, F (rescaledPath (((N n : ℝ) - 1) / (M n).offspringVariance (k n))
        fun m => ((ω m : ℕ) : ℝ) / N n) ∂((M n).countChain.pathLaw (i n)))
      atTop (𝓝 (∫ w, F w ∂P)) :=
  Rhone.Diffusion.cannings_pathLaw_tendsto_wrightFisherDiffusion N M k hvar h3 i hx hP F

end Rhone.Unproved
