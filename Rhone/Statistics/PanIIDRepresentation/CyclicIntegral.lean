/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.PanIIDRepresentation.CubeSymmetry

/-! # Integration of the cyclic order-statistic identity under an iid law -/

@[expose] public section

noncomputable section
open Set MeasureTheory
namespace Rhone.Statistics.PanIIDRepresentation
open AtomicRank

lemma integral_cyclic_average (μ : Measure ℝ) [SFinite μ] (F : LeftCube → ℝ)
    (hF : Integrable F ((μ.prod μ).prod μ)) :
    (∫ p, (F p + F (cycle p) + F (cycle (cycle p))) / 2 ∂(μ.prod μ).prod μ) =
      (3 / 2 : ℝ) * ∫ p, F p ∂(μ.prod μ).prod μ := by
  have h1 : Integrable (fun p => F (cycle p)) ((μ.prod μ).prod μ) :=
    (cycle_preserving μ).integrable_comp_of_integrable hF
  have h2 : Integrable (fun p => F (cycle (cycle p))) ((μ.prod μ).prod μ) :=
    (cycle_preserving μ).integrable_comp_of_integrable h1
  have hs : Integrable (fun p => F p + F (cycle p)) ((μ.prod μ).prod μ) := hF.add h1
  rw [integral_div, integral_add hs h2, integral_add hF h1,
    (cycle_preserving μ).integral_comp' (fun p => F (cycle p)),
    (cycle_preserving μ).integral_comp' F]
  ring

theorem integral_sorted_eq_selected (μ : Measure ℝ) [SFinite μ] [NullSingletonClass μ]
    (f : Coefficients) (g : ℝ → ℝ) (hg : Antitone g)
    (hF : Integrable (fun p : LeftCube =>
      selectedKernel (fun x y => value f (g x) (g y)) p.1.1 p.1.2 p.2)
      ((μ.prod μ).prod μ)) :
    (∫ p : LeftCube, sortedKernel f (g p.1.1) (g p.1.2) (g p.2)
      ∂(μ.prod μ).prod μ) =
      (3 / 2 : ℝ) * ∫ p : LeftCube,
        selectedKernel (fun x y => value f (g x) (g y)) p.1.1 p.1.2 p.2
        ∂(μ.prod μ).prod μ := by
  rw [← integral_cyclic_average μ _ hF]
  apply integral_congr_ae
  filter_upwards [iid_triple_distinct μ] with p hp
  exact sortedKernel_cyclic f g hg hp.1 hp.2.1 hp.2.2

end Rhone.Statistics.PanIIDRepresentation
