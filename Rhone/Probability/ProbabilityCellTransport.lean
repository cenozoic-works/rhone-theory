/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.MeasureTheory.Measure.Count
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Constructions.Pi

/-! # Transport of a fixed discrete mark cell by a coordinate equivalence -/

@[expose] public section
namespace Rhone.Probability.MeasureTransport
open MeasureTheory

variable {α β X : Type*} [MeasurableSpace α] [MeasurableSpace β]
  [MeasurableSpace X] [MeasurableSingletonClass α] [MeasurableSingletonClass β]
  [Countable α] [Countable β]

theorem markCell_slice (μ : Measure X) [SFinite μ] (a : α) (C : Set (α × X))
    (ha : ∀ z ∈ C, z.1 = a) :
    ((Measure.count : Measure α).prod μ).restrict C =
      (μ.restrict ((Prod.mk a) ⁻¹' C)).map (Prod.mk a) := by
  have hC : C = {a} ×ˢ ((Prod.mk a) ⁻¹' C) := by
    ext z
    constructor
    · intro hz
      refine ⟨ha z hz, ?_⟩
      change (a, z.2) ∈ C
      simpa only [← ha z hz, Prod.eta] using hz
    · rintro ⟨hz, hx⟩
      have hz' : z.1 = a := hz
      change (a, z.2) ∈ C at hx
      simpa only [← hz', Prod.eta] using hx
  rw [hC, ← Measure.prod_restrict, Measure.restrict_singleton, Measure.count_singleton,
    one_smul, Measure.dirac_prod]
  congr 2
  ext x
  simp

theorem markCell_transport (μ : Measure X) [SFinite μ] (a : α) (b : β)
    (C : Set (α × X)) (hC : MeasurableSet C) (ha : ∀ z ∈ C, z.1 = a)
    (F : α × X → β × X) (hF : Measurable F) (e : X ≃ᵐ X)
    (he : MeasurePreserving e μ μ) (hFe : ∀ z ∈ C, F z = (b, e z.2)) :
    MeasurableSet (F '' C) ∧
      (((Measure.count : Measure α).prod μ).restrict C).map F =
        ((Measure.count : Measure β).prod μ).restrict (F '' C) := by
  let D : Set X := (Prod.mk a) ⁻¹' C
  have hD : MeasurableSet D := hC.preimage measurable_prodMk_left
  have him : F '' C = {b} ×ˢ (e '' D) := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [hFe w hw]
      refine ⟨rfl, ⟨w.2, ?_, rfl⟩⟩
      change (a, w.2) ∈ C
      simpa only [← ha w hw, Prod.eta] using hw
    · rintro ⟨hz, x, hx, hex⟩
      refine ⟨(a, x), hx, ?_⟩
      rw [hFe (a, x) hx]
      exact Prod.ext hz.symm hex
  have hmeas : MeasurableSet (F '' C) := by
    rw [him]
    exact (measurableSet_singleton b).prod (e.measurableSet_image.mpr hD)
  refine ⟨hmeas, ?_⟩
  rw [markCell_slice μ a C ha, Measure.map_map hF measurable_prodMk_left]
  have hfg : (fun x => F (a, x)) =ᵐ[μ.restrict D] (fun x => (b, e x)) := by
    filter_upwards [ae_restrict_mem hD] with x hx
    exact hFe (a, x) hx
  change (μ.restrict D).map (fun x => F (a, x)) = _
  rw [Measure.map_congr hfg]
  have heD : (μ.restrict D).map e = μ.restrict (e '' D) := by
    have h := e.restrict_map μ (e '' D)
    rw [he.map_eq, e.injective.preimage_image] at h
    exact h.symm
  change (μ.restrict D).map ((Prod.mk b) ∘ e) = _
  rw [← Measure.map_map measurable_prodMk_left e.measurable, heD, him,
    ← Measure.dirac_prod, ← Measure.prod_restrict, Measure.restrict_singleton,
    Measure.count_singleton, one_smul]

end Rhone.Probability.MeasureTransport
