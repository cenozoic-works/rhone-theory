/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcSupport.SamplerKernel
public import Mathlib.Probability.Kernel.Composition.MeasureComp

/-! # The good-state invariant holds almost surely along sampler paths -/
@[expose] public section
namespace Rhone.Coalescent.SmcSupport
open IntervalProcess MeasureTheory ProbabilityTheory

private theorem process_good {S : Type*} [MeasurableSpace S]
    (P : Rhone.MarkovChain.DiscreteProcess S) (G : S → Prop)
    (hG : MeasurableSet {z | G z}) (x : S) (hx : G x)
    (hstep : ∀ z, G z → ∀ᵐ y ∂P.step z, G y) (k : ℕ) :
    ∀ᵐ ω ∂P.pathLaw x, G (ω k) := by
  have hm : ∀ j, ∀ᵐ z ∂(P.pathLaw x).map
      (fun ω => ω j), G z := by
    intro j
    induction j with
    | zero =>
      rw [P.map_eval_zero]
      exact (ae_dirac_iff hG).mpr hx
    | succ j ih =>
      rw [P.map_eval_succ]
      let μ : Measure S := (P.pathLaw x).map (fun ω => ω j)
      have hs : ∀ᵐ z ∂μ, ∀ᵐ y ∂P.step z, G y :=
        ih.mono (fun z hz => hstep z hz)
      exact Measure.ae_comp_of_ae_ae (μ := μ) (κ := P.step) (p := G) hG hs
  exact ae_of_ae_map
    (μ := P.pathLaw x) (f := fun ω : ℕ → S => ω k)
    (p := G) (measurable_pi_apply k).aemeasurable (hm k)

theorem samplerProcess_good (mode : Mode) (R : ℝ) (hR : 0 ≤ R)
    (n : ℕ) (hn : 0 < n) (k : ℕ) :
    ∀ᵐ ω ∂(samplerProcess mode R).pathLaw (trackedInitial n), Good (ω k) := by
  exact process_good (samplerProcess mode R) Good good_measurable (trackedInitial n)
    (trackedInitial_good n hn) (samplerKernel_good mode R hR) k

end Rhone.Coalescent.SmcSupport
