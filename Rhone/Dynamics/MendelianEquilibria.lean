/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Dynamics.MendelianLaws
/-!
# Equilibrium limits of fair Mendelian founder-copy generation laws

Source: wright1931, pp. 109–110. -/
@[expose] public section
namespace Rhone.Dynamics.MendelianIBD
open Finset
/-- Source: wright1931, pp. 109–110. -/
theorem tendsto_selfing_generation_ibd
    {A : Type*} [Fintype A] [DecidableEq A]
    (p : (Fin 2 → A) → ℝ) (hp0 : ∀ d, 0 ≤ p d) (hp : ∑ d, p d = 1) :
    Filter.Tendsto (fun t => founderIbd ((selfingLaw^[t]) p) id)
      Filter.atTop (nhds 1) := by
  have he : (fun t => founderIbd ((selfingLaw^[t]) p) id) =
      (fun t => ((Inbreeding.partialSelfingStep 1)^[t]) (founderIbd p id)) := by
    funext t
    rw [selfing_generation_ibd p hp0 hp, Inbreeding.selfing_iterate]
  rw [he]
  exact Inbreeding.tendsto_selfing _
/-- Source: wright1931, pp. 109–110. -/
theorem tendsto_sibling_generation_ibd
    {A : Type*} [Fintype A] [DecidableEq A]
    (p : ((Fin 2 → A) × (Fin 2 → A)) → ℝ)
    (hp0 : ∀ d, 0 ≤ p d) (hp : ∑ d, p d = 1)
    (hequal : founderIbd p Prod.fst = founderIbd p Prod.snd) :
    Filter.Tendsto (fun t => ibdPair ((sibLaw^[t]) p))
      Filter.atTop (nhds (1, 1)) := by
  have he : (fun t => ibdPair ((sibLaw^[t]) p)) =
      (fun t => ((Inbreeding.fullSibStep)^[t]) (ibdPair p)) := by
    funext t
    exact sibling_generation_ibd p hp0 hp hequal t
  rw [he]
  exact Inbreeding.tendsto_full_sib _
end Rhone.Dynamics.MendelianIBD
