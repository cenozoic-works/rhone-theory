/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeAttachmentLaw
public import Rhone.Coalescent.SmcPrimeKingmanActiveUnique
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# Flat law of the two-uniform attachment time and target

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 1–6. -/

@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open MeasureTheory IntervalProcess Set
open scoped ENNReal

theorem attachmentUniformLaw_flat {N : ℕ} (T : Tree N)
    (hT : TreeTemporalCover T) (t : ℝ) (ht : 0 ≤ t) :
    attachmentUniformLaw T t =
      (volume.prod (Measure.count : Measure (Finset (Fin N)))).withDensity
        (fun p => if t ≤ p.1 then ENNReal.ofReal
          (Real.exp (-attachmentHazard T t p.1) * attachmentTargetRate T p.1 p.2)
          else 0) := by
  classical
  let d : ℝ × Finset (Fin N) → ℝ≥0∞ := fun p => if t ≤ p.1 then
    ENNReal.ofReal (Real.exp (-attachmentHazard T t p.1) *
      attachmentTargetRate T p.1 p.2) else 0
  have hd : Measurable d := by
    apply measurable_from_prod_countable_left
    intro c
    exact (((Real.continuous_exp.comp (continuous_attachmentHazard T t).neg).measurable.mul
      (measurable_attachmentTargetRate T c)).ennreal_ofReal).piecewise
        measurableSet_Ici measurable_const
  ext S hS
  let A (c : Finset (Fin N)) := (fun s : ℝ => (s, c)) ⁻¹' S
  have hA (c) : MeasurableSet (A c) :=
    hS.preimage (measurable_id.prodMk measurable_const)
  have hcover : S = ⋃ c, A c ×ˢ {c} := by
    ext p
    simp [A]
  have hdis : Pairwise (fun c e => Disjoint (A c ×ˢ {c}) (A e ×ˢ {e})) := by
    intro c e hce
    apply Set.disjoint_left.mpr
    rintro p ⟨_, hc⟩ ⟨_, he⟩
    exact hce (hc.symm.trans he)
  have hfiber (c : Finset (Fin N)) :
      attachmentUniformLaw T t (A c ×ˢ {c}) =
        ∫⁻ s, (S.indicator d) (s, c) := by
    rw [show A c ×ˢ {c} = {p | p.1 ∈ A c ∧ p.2 = c} by rfl,
      attachment_target_joint_density T hT t ht (A c) (hA c) c]
    rw [← lintegral_indicator ((hA c).inter measurableSet_Ici)]
    apply lintegral_congr
    intro s
    by_cases hst : t ≤ s <;> by_cases hs : (s, c) ∈ S <;>
      simp [d, A, hst, hs, Set.indicator]
  change _ = ((volume.prod Measure.count).withDensity d) S
  rw [withDensity_apply d hS, ← lintegral_indicator hS,
    lintegral_prod_symm _ (hd.indicator hS).aemeasurable, lintegral_count]
  conv_lhs => rw [hcover, measure_iUnion hdis (fun c =>
    (hA c).prod (measurableSet_singleton c))]
  exact tsum_congr hfiber

theorem attachmentTargetRate_of_active_unique {N : ℕ} (T : Tree N)
    (hT : TreeActiveUnique T) (s : ℝ) (hs : 0 ≤ s) (c : Finset (Fin N)) :
    attachmentTargetRate T s c = if c ∈ timeClades T s then 1 else 0 := by
  classical
  by_cases hr : rootHeight T ≤ s
  · simp [attachmentTargetRate, timeClades, hr]
  · simp only [attachmentTargetRate, timeClades, ite_eq_right hr]
    by_cases hc : c ∈ (activeBranches T s).image (fun i => (T.2 i).1)
    · obtain ⟨i, hi, hci⟩ := Finset.mem_image.mp hc
      have he : (activeBranches T s).filter (fun i => (T.2 i).1 = c) = {i} := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · intro hj
          exact hT s hs j hj.1 i hi (hj.2.trans hci.symm)
        · rintro rfl
          exact ⟨hi, hci⟩
      simp [hc, he]
    · have he : (activeBranches T s).filter (fun i => (T.2 i).1 = c) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro i hi
        exact hc (Finset.mem_image.mpr ⟨i, (Finset.mem_filter.mp hi).1,
          (Finset.mem_filter.mp hi).2⟩)
      simp [hc, he]

end Rhone.Coalescent.SmcPrime
