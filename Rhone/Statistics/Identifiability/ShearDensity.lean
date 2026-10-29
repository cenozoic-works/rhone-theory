/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.JointLaw
public import Mathlib.MeasureTheory.Group.Prod

/-! # The upper shear map on the plane and its action on densities -/

@[expose] public section

open scoped ENNReal
open Set MeasureTheory
namespace Rhone.Statistics.Identifiability

theorem equiv_map_withDensity {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (e : α ≃ᵐ β) (f : α → ℝ≥0∞) (hf : Measurable f) :
    (μ.withDensity f).map e = (μ.map e).withDensity (fun y => f (e.symm y)) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs, withDensity_apply _ (e.measurable hs),
    withDensity_apply _ hs]
  have h := setLIntegral_map (μ := μ) (f := fun y => f (e.symm y))
    hs (hf.comp e.symm.measurable) e.measurable
  simpa using h.symm

noncomputable abbrev upperShear : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) := MeasurableEquiv.shearAddRight ℝ
noncomputable abbrev planeVolume : Measure (ℝ × ℝ) :=
  (volume : Measure ℝ).prod (volume : Measure ℝ)

theorem upperShear_apply (p : ℝ × ℝ) : upperShear p = (p.1, p.1+p.2) := rfl

theorem upperShear_symm_apply (p : ℝ × ℝ) : upperShear.symm p = (p.1, -p.1+p.2) := rfl

theorem upperShear_preserving : MeasurePreserving upperShear planeVolume planeVolume :=
  measurePreserving_prod_add volume volume

theorem upperShear_preimage : upperShear ⁻¹' upperWedge = Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ) := by
  ext p
  simp [upperWedge, upperShear_apply]

theorem upperShear_map_quadrant :
    (planeVolume.restrict (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ))).map upperShear =
      planeVolume.restrict upperWedge := by
  rw [← upperShear_preimage,
    ← Measure.restrict_map upperShear.measurable upperWedge_open.measurableSet,
    upperShear_preserving.map_eq]

theorem shear_product_density (f g : ℝ → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g) :
    (((volume.restrict (Ioi (0 : ℝ))).withDensity f).prod
      ((volume.restrict (Ioi (0 : ℝ))).withDensity g)).map upperShear =
    (planeVolume.restrict upperWedge).withDensity (fun p => f p.1 * g (p.2-p.1)) := by
  rw [prod_withDensity hf hg, Measure.prod_restrict,
    equiv_map_withDensity _ upperShear (fun z : ℝ × ℝ => f z.1 * g z.2)
      ((hf.comp measurable_fst).mul (hg.comp measurable_snd)),
    upperShear_map_quadrant]
  congr 1
  funext p
  simp only [upperShear_symm_apply]
  congr 2
  ring

end Rhone.Statistics.Identifiability
