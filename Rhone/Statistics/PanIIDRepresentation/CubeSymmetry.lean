/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.PanIIDRepresentation.PairMinimum
public import Rhone.Statistics.PanIIDRepresentation.CyclicKernel

/-! # Cyclic invariance and distinctness for three iid atomless real draws -/

@[expose] public section

noncomputable section
open Set MeasureTheory
namespace Rhone.Statistics.PanIIDRepresentation

abbrev LeftCube := (ℝ × ℝ) × ℝ

def cycle : LeftCube ≃ᵐ LeftCube :=
  MeasurableEquiv.prodAssoc.trans MeasurableEquiv.prodComm

lemma cycle_apply (p : LeftCube) : cycle p = ((p.1.2, p.2), p.1.1) := rfl

lemma cycle_preserving (μ : Measure ℝ) [SFinite μ] :
    MeasurePreserving cycle ((μ.prod μ).prod μ) ((μ.prod μ).prod μ) :=
  Measure.measurePreserving_swap.comp (measurePreserving_prodAssoc μ μ μ)

lemma integral_cycle (μ : Measure ℝ) [SFinite μ] (F : LeftCube → ℝ) :
    (∫ p, F ((p.1.2, p.2), p.1.1) ∂(μ.prod μ).prod μ) =
      ∫ p, F p ∂(μ.prod μ).prod μ :=
  (cycle_preserving μ).integral_comp' F

lemma iid_pair_distinct (μ : Measure ℝ) [SFinite μ] [NullSingletonClass μ] :
    ∀ᵐ p ∂μ.prod μ, p.1 ≠ p.2 := by
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
  exact Filter.Eventually.of_forall fun x => (Measure.ae_ne μ x).mono fun _ h => Ne.symm h

lemma iid_triple_distinct (μ : Measure ℝ) [SFinite μ] [NullSingletonClass μ] :
    ∀ᵐ p ∂(μ.prod μ).prod μ, p.1.1 ≠ p.1.2 ∧ p.1.2 ≠ p.2 ∧ p.1.1 ≠ p.2 := by
  have h : ∀ᵐ p ∂(μ.prod μ).prod μ, p.1.1 ≠ p.1.2 :=
    Measure.quasiMeasurePreserving_fst.ae (iid_pair_distinct μ)
  have h1 := (cycle_preserving μ).quasiMeasurePreserving.ae h
  have h2 := (cycle_preserving μ).quasiMeasurePreserving.ae h1
  filter_upwards [h, h1, h2] with p ha hb hc
  exact ⟨ha, hb, Ne.symm hc⟩

end Rhone.Statistics.PanIIDRepresentation
