/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.AEDensityMarginals

/-! # Construct the ordered two-event law from event fluxes -/

@[expose] public section

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace Rhone.Statistics.Identifiability.TwoEventFluxLaw

noncomputable def law (δ : ℝ → ℝ) (jA jB : ℝ × ℝ → ℝ) : Measure (ℝ × ℝ) :=
  diagonalDensityLaw δ + triangularDensityLaw jA +
    (triangularDensityLaw jB).map Prod.swap

def positiveQuadrant : Set (ℝ × ℝ) := Ioi 0 ×ˢ Ioi 0

def square (T : ℝ) : Set (ℝ × ℝ) := Ioc 0 T ×ˢ Ioc 0 T

noncomputable def finiteMass (δ : ℝ → ℝ) (jA jB : ℝ × ℝ → ℝ) (T : ℝ) : ℝ≥0∞ :=
  (∫⁻ t in Ioc 0 T, ENNReal.ofReal (δ t)) +
  (∫⁻ t in Ioc 0 T, ∫⁻ s in Ioo 0 t, ENNReal.ofReal (jA (s, t))) +
  (∫⁻ t in Ioc 0 T, ∫⁻ s in Ioo 0 t, ENNReal.ofReal (jB (s, t)))

theorem square_measurable (T : ℝ) : MeasurableSet (square T) :=
  measurableSet_Ioc.prod measurableSet_Ioc

theorem positiveQuadrant_measurable : MeasurableSet positiveQuadrant :=
  measurableSet_Ioi.prod measurableSet_Ioi

theorem law_restrict_upper (δ : ℝ → ℝ) (jA jB : ℝ × ℝ → ℝ) :
    (law δ jA jB).restrict upperWedge = triangularDensityLaw jA := by
  rw [law, Measure.restrict_add, Measure.restrict_add,
    diagonal_restrict_upper, triangular_restrict_upper, swapped_triangular_restrict_upper]
  simp

theorem law_restrict_diagonal (δ : ℝ → ℝ) (jA jB : ℝ × ℝ → ℝ) :
    (law δ jA jB).restrict timeDiagonal = diagonalDensityLaw δ := by
  rw [law, Measure.restrict_add, Measure.restrict_add,
    diagonal_restrict_diagonal, triangular_restrict_diagonal,
    swapped_triangular_restrict_diagonal]
  simp

theorem diagonal_restrict_positiveQuadrant (δ : ℝ → ℝ) :
    (diagonalDensityLaw δ).restrict positiveQuadrant = diagonalDensityLaw δ := by
  rw [diagonalDensityLaw, Measure.restrict_map (f := fun t : ℝ => (t, t))
    (measurable_id.prodMk measurable_id)
    positiveQuadrant_measurable]
  have he : (fun t : ℝ => (t, t)) ⁻¹' positiveQuadrant = Ioi 0 := by
    ext t
    simp [positiveQuadrant]
  rw [he, restrict_withDensity measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi, inter_self]

theorem triangular_restrict_positiveQuadrant (j : ℝ × ℝ → ℝ) :
    (triangularDensityLaw j).restrict positiveQuadrant = triangularDensityLaw j := by
  rw [triangularDensityLaw, restrict_withDensity positiveQuadrant_measurable,
    Measure.restrict_restrict positiveQuadrant_measurable]
  have he : positiveQuadrant ∩ upperWedge = upperWedge := by
    apply inter_eq_right.mpr
    intro p hp
    exact ⟨hp.1, hp.1.trans hp.2⟩
  rw [he]

theorem swapped_triangular_restrict_positiveQuadrant (j : ℝ × ℝ → ℝ) :
    ((triangularDensityLaw j).map Prod.swap).restrict positiveQuadrant =
      (triangularDensityLaw j).map Prod.swap := by
  rw [Measure.restrict_map (f := Prod.swap) (measurable_snd.prodMk measurable_fst)
    positiveQuadrant_measurable]
  have he : Prod.swap ⁻¹' positiveQuadrant = positiveQuadrant := by
    ext p
    simp [positiveQuadrant]
  rw [he, triangular_restrict_positiveQuadrant]

theorem law_restrict_positiveQuadrant (δ : ℝ → ℝ) (jA jB : ℝ × ℝ → ℝ) :
    (law δ jA jB).restrict positiveQuadrant = law δ jA jB := by
  rw [law, Measure.restrict_add, Measure.restrict_add,
    diagonal_restrict_positiveQuadrant, triangular_restrict_positiveQuadrant,
    swapped_triangular_restrict_positiveQuadrant]

theorem law_positive_ae (δ : ℝ → ℝ) (jA jB : ℝ × ℝ → ℝ) :
    ∀ᵐ p ∂law δ jA jB, 0 < p.1 ∧ 0 < p.2 := by
  rw [← law_restrict_positiveQuadrant δ jA jB]
  exact ae_restrict_mem positiveQuadrant_measurable

theorem diagonal_square (δ : ℝ → ℝ) (T : ℝ) :
    diagonalDensityLaw δ (square T) = ∫⁻ t in Ioc 0 T, ENNReal.ofReal (δ t) := by
  rw [diagonalDensityLaw, Measure.map_apply (f := fun t : ℝ => (t, t))
    (measurable_id.prodMk measurable_id)
    (square_measurable T)]
  have he : (fun t : ℝ => (t, t)) ⁻¹' square T = Ioc 0 T := by
    ext t
    simp [square]
  rw [he, withDensity_apply _ measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc]
  congr 2
  ext t
  simp only [mem_inter_iff, mem_Ioc, mem_Ioi]
  tauto

theorem triangular_square (j : ℝ × ℝ → ℝ)
    (hj : AEMeasurable j (planeVolume.restrict upperWedge)) (T : ℝ) :
    triangularDensityLaw j (square T) =
      ∫⁻ t in Ioc 0 T, ∫⁻ s in Ioo 0 t, ENNReal.ofReal (j (s, t)) := by
  have he : (triangularDensityLaw j).map Prod.snd (Ioc 0 T) =
      ∫⁻ t in Ioc 0 T, ∫⁻ s in Ioo 0 t, ENNReal.ofReal (j (s, t)) := by
    rw [triangular_map_snd_ae j hj, withDensity_apply _ measurableSet_Ioc]
  rw [← he, Measure.map_apply measurable_snd measurableSet_Ioc,
    triangularDensityLaw, withDensity_apply _ (square_measurable T),
    withDensity_apply _ (measurable_snd measurableSet_Ioc),
    Measure.restrict_restrict (square_measurable T),
    Measure.restrict_restrict (measurable_snd measurableSet_Ioc)]
  congr 2
  ext p
  simp only [square, mem_inter_iff, mem_prod, mem_Ioc, mem_preimage]
  change ((0 < p.1 ∧ p.1 ≤ T) ∧ 0 < p.2 ∧ p.2 ≤ T) ∧ (0 < p.1 ∧ p.1 < p.2) ↔
    (0 < p.2 ∧ p.2 ≤ T) ∧ (0 < p.1 ∧ p.1 < p.2)
  constructor
  · tauto
  · rintro ⟨⟨hp2, hpT⟩, hp1, hlt⟩
    exact ⟨⟨⟨hp1, hlt.le.trans hpT⟩, hp2, hpT⟩, hp1, hlt⟩

theorem law_square (δ : ℝ → ℝ) (jA jB : ℝ × ℝ → ℝ)
    (hjA : AEMeasurable jA (planeVolume.restrict upperWedge))
    (hjB : AEMeasurable jB (planeVolume.restrict upperWedge)) (T : ℝ) :
    law δ jA jB (square T) = finiteMass δ jA jB T := by
  rw [law, Measure.add_apply, Measure.add_apply,
    Measure.map_apply (f := Prod.swap) (measurable_snd.prodMk measurable_fst) (square_measurable T)]
  have he : Prod.swap ⁻¹' square T = square T := by
    ext p
    simp [square, and_comm]
  rw [he, diagonal_square, triangular_square jA hjA, triangular_square jB hjB]
  rfl

theorem iUnion_square_nat : (⋃ n : ℕ, square n) = positiveQuadrant := by
  ext p
  simp only [mem_iUnion, square, positiveQuadrant, mem_prod, mem_Ioc, mem_Ioi]
  constructor
  · rintro ⟨n, ⟨hp1, _⟩, hp2, _⟩
    exact ⟨hp1, hp2⟩
  · rintro ⟨hp1, hp2⟩
    obtain ⟨n, hn⟩ := exists_nat_gt (max p.1 p.2)
    exact ⟨n, ⟨hp1, (le_max_left _ _).trans hn.le⟩,
      hp2, (le_max_right _ _).trans hn.le⟩

theorem square_mono : Monotone square := by
  intro S T hST p hp
  exact ⟨⟨hp.1.1, hp.1.2.trans hST⟩, hp.2.1, hp.2.2.trans hST⟩

theorem probability_of_finiteMass (δ : ℝ → ℝ) (jA jB : ℝ × ℝ → ℝ)
    (hjA : AEMeasurable jA (planeVolume.restrict upperWedge))
    (hjB : AEMeasurable jB (planeVolume.restrict upperWedge))
    (F : ℝ → ℝ) (hfinite : ∀ T, 0 ≤ T → finiteMass δ jA jB T = ENNReal.ofReal (F T))
    (hF : Tendsto F atTop (𝓝 1)) : IsProbabilityMeasure (law δ jA jB) := by
  have hlim : Tendsto (fun n : ℕ => law δ jA jB (square n)) atTop
      (𝓝 (law δ jA jB positiveQuadrant)) := by
    rw [← iUnion_square_nat]
    exact tendsto_measure_iUnion_atTop (square_mono.comp Nat.mono_cast)
  have hlim1 : Tendsto (fun n : ℕ => law δ jA jB (square n)) atTop (𝓝 1) := by
    have ht := (ENNReal.continuous_ofReal.tendsto 1).comp (hF.comp tendsto_natCast_atTop_atTop)
    simpa only [Function.comp_def, ENNReal.ofReal_one, law_square δ jA jB hjA hjB,
      hfinite _ (Nat.cast_nonneg _)] using ht
  have hmass : law δ jA jB positiveQuadrant = 1 := tendsto_nhds_unique hlim hlim1
  have hs := congrArg (fun μ : Measure (ℝ × ℝ) => μ univ)
    (law_restrict_positiveQuadrant δ jA jB)
  simp only [Measure.restrict_apply MeasurableSet.univ, univ_inter] at hs
  exact ⟨hs.symm.trans hmass⟩

theorem lintegral_law (δ : ℝ → ℝ) (jA jB : ℝ × ℝ → ℝ)
    (hδ : AEMeasurable δ (volume.restrict (Ioi 0)))
    (hjA : AEMeasurable jA (planeVolume.restrict upperWedge))
    (hjB : AEMeasurable jB (planeVolume.restrict upperWedge))
    (φ : ℝ × ℝ → ℝ≥0∞) (hφ : Measurable φ) :
    (∫⁻ p, φ p ∂law δ jA jB) =
      (∫⁻ t in Ioi 0, ENNReal.ofReal (δ t) * φ (t, t)) +
      (∫⁻ p in upperWedge, ENNReal.ofReal (jA p) * φ p ∂planeVolume) +
      (∫⁻ p in upperWedge, ENNReal.ofReal (jB p) * φ p.swap ∂planeVolume) := by
  rw [law, lintegral_add_measure, lintegral_add_measure, diagonalDensityLaw,
    lintegral_map (g := fun t : ℝ => (t, t)) hφ (measurable_id.prodMk measurable_id),
    lintegral_map (g := Prod.swap) hφ (measurable_snd.prodMk measurable_fst), triangularDensityLaw,
    triangularDensityLaw,
    lintegral_withDensity_eq_lintegral_mul₀ (g := fun t => φ (t, t)) hδ.ennreal_ofReal
      (hφ.comp (measurable_id.prodMk measurable_id)).aemeasurable,
    lintegral_withDensity_eq_lintegral_mul₀ hjA.ennreal_ofReal hφ.aemeasurable,
    lintegral_withDensity_eq_lintegral_mul₀ (g := fun p => φ p.swap) hjB.ennreal_ofReal
      (hφ.comp (measurable_snd.prodMk measurable_fst)).aemeasurable]
  rfl

theorem integral_ofReal_density {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (d g : α → ℝ) (hd : AEMeasurable d μ)
    (hn : ∀ᵐ x ∂μ, 0 ≤ d x) :
    (∫ x, g x ∂μ.withDensity (fun x => ENNReal.ofReal (d x))) =
      ∫ x, d x * g x ∂μ := by
  rw [integral_withDensity_eq_integral_toReal_smul₀ hd.ennreal_ofReal
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [hn] with x hx
  simp [ENNReal.toReal_ofReal hx]

theorem integral_law (δ : ℝ → ℝ) (jA jB : ℝ × ℝ → ℝ)
    (hδ : AEMeasurable δ (volume.restrict (Ioi 0)))
    (hjA : AEMeasurable jA (planeVolume.restrict upperWedge))
    (hjB : AEMeasurable jB (planeVolume.restrict upperWedge))
    (hδn : ∀ᵐ t ∂volume.restrict (Ioi 0), 0 ≤ δ t)
    (hjAn : ∀ᵐ p ∂planeVolume.restrict upperWedge, 0 ≤ jA p)
    (hjBn : ∀ᵐ p ∂planeVolume.restrict upperWedge, 0 ≤ jB p)
    (φ : ℝ × ℝ → ℝ) (hφ : Measurable φ) (hi : Integrable φ (law δ jA jB)) :
    (∫ p, φ p ∂law δ jA jB) =
      (∫ t in Ioi 0, δ t * φ (t, t)) +
      (∫ p in upperWedge, jA p * φ p ∂planeVolume) +
      (∫ p in upperWedge, jB p * φ p.swap ∂planeVolume) := by
  have hd := hi.left_of_add_measure.left_of_add_measure
  have hA := hi.left_of_add_measure.right_of_add_measure
  have hB := hi.right_of_add_measure
  rw [law, integral_add_measure (hd.add_measure hA) hB,
    integral_add_measure hd hA, diagonalDensityLaw,
    integral_map_of_stronglyMeasurable (φ := fun t : ℝ => (t, t))
      (measurable_id.prodMk measurable_id)
      hφ.stronglyMeasurable,
    integral_map_of_stronglyMeasurable (φ := Prod.swap)
      (measurable_snd.prodMk measurable_fst)
      hφ.stronglyMeasurable,
    triangularDensityLaw, triangularDensityLaw,
    integral_ofReal_density _ _ _ hδ hδn,
    integral_ofReal_density _ _ _ hjA hjAn,
    integral_ofReal_density _ _ _ hjB hjBn]

theorem ofReal_intervalIntegral {f : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hi : IntervalIntegrable f volume 0 T)
    (hn : ∀ᵐ t ∂volume.restrict (Ioc 0 T), 0 ≤ f t) :
    ENNReal.ofReal (∫ t in (0 : ℝ)..T, f t) =
      ∫⁻ t in Ioc 0 T, ENNReal.ofReal (f t) := by
  rw [intervalIntegral.integral_of_le hT]
  exact ofReal_integral_eq_lintegral_ofReal hi.1 hn

theorem ofReal_columnIntegral (j : ℝ × ℝ → ℝ) {t : ℝ} (ht : 0 ≤ t)
    (hi : IntervalIntegrable (fun s => j (s, t)) volume 0 t)
    (hn : ∀ᵐ s ∂volume.restrict (Ioo 0 t), 0 ≤ j (s, t)) :
    ENNReal.ofReal (∫ s in (0 : ℝ)..t, j (s, t)) =
      ∫⁻ s in Ioo 0 t, ENNReal.ofReal (j (s, t)) := by
  rw [intervalIntegral.integral_of_le ht, integral_Ioc_eq_integral_Ioo]
  exact ofReal_integral_eq_lintegral_ofReal (hi.1.mono_set Ioo_subset_Ioc_self) hn

theorem finiteMass_of_real_columns (δ a b : ℝ → ℝ) (jA jB : ℝ × ℝ → ℝ)
    {T : ℝ} (hT : 0 ≤ T)
    (hδi : IntervalIntegrable δ volume 0 T)
    (hai : IntervalIntegrable a volume 0 T) (hbi : IntervalIntegrable b volume 0 T)
    (hδn : ∀ᵐ t ∂volume.restrict (Ioc 0 T), 0 ≤ δ t)
    (han : ∀ᵐ t ∂volume.restrict (Ioc 0 T), 0 ≤ a t)
    (hbn : ∀ᵐ t ∂volume.restrict (Ioc 0 T), 0 ≤ b t)
    (hA : ∀ᵐ t ∂volume.restrict (Ioc 0 T),
      (∫⁻ s in Ioo 0 t, ENNReal.ofReal (jA (s, t))) = ENNReal.ofReal (a t))
    (hB : ∀ᵐ t ∂volume.restrict (Ioc 0 T),
      (∫⁻ s in Ioo 0 t, ENNReal.ofReal (jB (s, t))) = ENNReal.ofReal (b t)) :
    finiteMass δ jA jB T = ENNReal.ofReal
      ((∫ t in (0 : ℝ)..T, δ t) + (∫ t in (0 : ℝ)..T, a t) +
        (∫ t in (0 : ℝ)..T, b t)) := by
  have hd : 0 ≤ ∫ t in (0 : ℝ)..T, δ t := by
    rw [intervalIntegral.integral_of_le hT]
    exact integral_nonneg_of_ae hδn
  have ha : 0 ≤ ∫ t in (0 : ℝ)..T, a t := by
    rw [intervalIntegral.integral_of_le hT]
    exact integral_nonneg_of_ae han
  have hb : 0 ≤ ∫ t in (0 : ℝ)..T, b t := by
    rw [intervalIntegral.integral_of_le hT]
    exact integral_nonneg_of_ae hbn
  rw [finiteMass, lintegral_congr_ae hA, lintegral_congr_ae hB,
    ← ofReal_intervalIntegral hT hδi hδn,
    ← ofReal_intervalIntegral hT hai han, ← ofReal_intervalIntegral hT hbi hbn,
    ENNReal.ofReal_add (add_nonneg hd ha) hb, ENNReal.ofReal_add hd ha]

theorem probability_of_real_columns (δ a b F : ℝ → ℝ) (jA jB : ℝ × ℝ → ℝ)
    (hjA : AEMeasurable jA (planeVolume.restrict upperWedge))
    (hjB : AEMeasurable jB (planeVolume.restrict upperWedge))
    (hδi : ∀ T, 0 ≤ T → IntervalIntegrable δ volume 0 T)
    (hai : ∀ T, 0 ≤ T → IntervalIntegrable a volume 0 T)
    (hbi : ∀ T, 0 ≤ T → IntervalIntegrable b volume 0 T)
    (hδn : ∀ᵐ t ∂volume.restrict (Ioi 0), 0 ≤ δ t)
    (han : ∀ᵐ t ∂volume.restrict (Ioi 0), 0 ≤ a t)
    (hbn : ∀ᵐ t ∂volume.restrict (Ioi 0), 0 ≤ b t)
    (hA : ∀ᵐ t ∂volume.restrict (Ioi 0),
      (∫⁻ s in Ioo 0 t, ENNReal.ofReal (jA (s, t))) = ENNReal.ofReal (a t))
    (hB : ∀ᵐ t ∂volume.restrict (Ioi 0),
      (∫⁻ s in Ioo 0 t, ENNReal.ofReal (jB (s, t))) = ENNReal.ofReal (b t))
    (hfinite : ∀ T, 0 ≤ T → F T =
      (∫ t in (0 : ℝ)..T, δ t) + (∫ t in (0 : ℝ)..T, a t) +
        (∫ t in (0 : ℝ)..T, b t))
    (hF : Tendsto F atTop (𝓝 1)) : IsProbabilityMeasure (law δ jA jB) := by
  apply probability_of_finiteMass δ jA jB hjA hjB F _ hF
  intro T hT
  have hm : volume.restrict (Ioc 0 T) ≤ volume.restrict (Ioi (0 : ℝ)) :=
    Measure.restrict_mono (fun _ hx => hx.1) le_rfl
  rw [hfinite T hT]
  exact finiteMass_of_real_columns δ a b jA jB hT (hδi T hT) (hai T hT) (hbi T hT)
    (hδn.filter_mono (ae_mono hm)) (han.filter_mono (ae_mono hm))
    (hbn.filter_mono (ae_mono hm)) (hA.filter_mono (ae_mono hm))
    (hB.filter_mono (ae_mono hm))

theorem law_square_eq_terminal (δ : ℝ → ℝ) (jA jB : ℝ × ℝ → ℝ)
    (hjA : AEMeasurable jA (planeVolume.restrict upperWedge))
    (hjB : AEMeasurable jB (planeVolume.restrict upperWedge))
    (F : ℝ → ℝ) (hfinite : ∀ T, 0 ≤ T → finiteMass δ jA jB T = ENNReal.ofReal (F T))
    {T : ℝ} (hT : 0 ≤ T) :
    law δ jA jB (square T) = ENNReal.ofReal (F T) := by
  rw [law_square δ jA jB hjA hjB, hfinite T hT]

theorem law_square_ne_top (δ : ℝ → ℝ) (jA jB : ℝ × ℝ → ℝ)
    (hjA : AEMeasurable jA (planeVolume.restrict upperWedge))
    (hjB : AEMeasurable jB (planeVolume.restrict upperWedge))
    (F : ℝ → ℝ) (hfinite : ∀ T, 0 ≤ T → finiteMass δ jA jB T = ENNReal.ofReal (F T))
    {T : ℝ} (hT : 0 ≤ T) : law δ jA jB (square T) ≠ ∞ := by
  rw [law_square_eq_terminal δ jA jB hjA hjB F hfinite hT]
  exact ENNReal.ofReal_ne_top

theorem law_square_pos_iff (δ : ℝ → ℝ) (jA jB : ℝ × ℝ → ℝ)
    (hjA : AEMeasurable jA (planeVolume.restrict upperWedge))
    (hjB : AEMeasurable jB (planeVolume.restrict upperWedge))
    (F : ℝ → ℝ) (hfinite : ∀ T, 0 ≤ T → finiteMass δ jA jB T = ENNReal.ofReal (F T))
    {T : ℝ} (hT : 0 ≤ T) : 0 < law δ jA jB (square T) ↔ 0 < F T := by
  rw [law_square_eq_terminal δ jA jB hjA hjB F hfinite hT, ENNReal.ofReal_pos]

end Rhone.Statistics.Identifiability.TwoEventFluxLaw
