/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.SmcPrimeExtractionLookupsMeas
/-! # Measurability of the state fields of the one-split extraction -/

@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess MeasureTheory

abbrev ExtractionCoordinates (N : ℕ) := AugmentedState × (Fin N → ℕ) × (Fin N → ℕ) ×
  Option ℕ × KingmanHistory N × ℕ × (Finset (Fin N) × ℝ × ℝ) × (ℝ × Finset (Fin N))

def extractionCoordinates (N : ℕ) (z : OneSplitExtractionState N) : ExtractionCoordinates N :=
  (z.old,z.oldLabels,z.argLabels,z.detached,z.oldHistory,z.mergers,z.cut,z.attachment)

instance (N : ℕ) : MeasurableSpace (OneSplitExtractionState N) :=
  MeasurableSpace.comap (extractionCoordinates N) inferInstance

theorem extractionCoordinates_measurable (N : ℕ) : Measurable (extractionCoordinates N) :=
  comap_measurable _

theorem extractionState_mk_measurable {α : Type*} [MeasurableSpace α] (N : ℕ)
    (a : α → AugmentedState) (l r : α → Fin N → ℕ) (d : α → Option ℕ)
    (h : α → KingmanHistory N) (m : α → ℕ)
    (c : α → Finset (Fin N) × ℝ × ℝ) (b : α → ℝ × Finset (Fin N))
    (ha : Measurable a) (hl : Measurable l) (hr : Measurable r) (hd : Measurable d)
    (hh : Measurable h) (hm : Measurable m) (hc : Measurable c) (hb : Measurable b) :
    Measurable (fun p => ({
          old := a p
          oldLabels := l p
          argLabels := r p
          detached := d p
          oldHistory := h p
          mergers := m p
          cut := c p
          attachment := b p } :
        OneSplitExtractionState N)) := by
  apply measurable_comap_iff.mpr
  exact ha.prodMk (hl.prodMk (hr.prodMk (hd.prodMk
    (hh.prodMk (hm.prodMk (hc.prodMk hb))))))

theorem extractionOld_measurable (N : ℕ) :
    Measurable (fun z : OneSplitExtractionState N => z.old) :=
  (extractionCoordinates_measurable N).fst

theorem extractionOldLabels_measurable (N : ℕ) :
    Measurable (fun z : OneSplitExtractionState N => z.oldLabels) :=
  (extractionCoordinates_measurable N).snd.fst

theorem extractionARGLabels_measurable (N : ℕ) :
    Measurable (fun z : OneSplitExtractionState N => z.argLabels) :=
  (extractionCoordinates_measurable N).snd.snd.fst

theorem extractionDetached_measurable (N : ℕ) :
    Measurable (fun z : OneSplitExtractionState N => z.detached) :=
  (extractionCoordinates_measurable N).snd.snd.snd.fst

theorem extractionOldHistory_measurable (N : ℕ) :
    Measurable (fun z : OneSplitExtractionState N => z.oldHistory) :=
  (extractionCoordinates_measurable N).snd.snd.snd.snd.fst

theorem extractionMergers_measurable (N : ℕ) :
    Measurable (fun z : OneSplitExtractionState N => z.mergers) :=
  (extractionCoordinates_measurable N).snd.snd.snd.snd.snd.fst

theorem extractionCut_measurable (N : ℕ) :
    Measurable (fun z : OneSplitExtractionState N => z.cut) :=
  (extractionCoordinates_measurable N).snd.snd.snd.snd.snd.snd.fst

theorem extractionAttachment_measurable (N : ℕ) :
    Measurable (fun z : OneSplitExtractionState N => z.attachment) :=
  (extractionCoordinates_measurable N).snd.snd.snd.snd.snd.snd.snd

theorem extractionHistoryUpdate_measurable (N : ℕ) :
    Measurable (fun p : (KingmanHistory N × ℕ) × AugmentedState =>
      if hj : p.1.2 + 1 < N then Function.update p.1.1 ⟨p.1.2 + 1,hj⟩ p.2 else p.1.1) := by
  classical
  apply measurable_countable_choice
    (fun p : (KingmanHistory N × ℕ) × AugmentedState => p.1.2) measurable_fst.snd
    (fun m p => if hj : m + 1 < N then Function.update p.1.1 ⟨m + 1,hj⟩ p.2 else p.1.1)
  intro m
  by_cases hm : m + 1 < N
  · simp only [dite_eq_left hm]
    apply measurable_pi_iff.mpr
    intro k
    by_cases hk : k = ⟨m+1,hm⟩
    · subst k
      simpa only [Function.update_self] using
        (measurable_snd : Measurable (fun p : (KingmanHistory N × ℕ) × AugmentedState => p.2))
    · simpa only [Function.update_of_ne hk, Function.comp_def] using
        (measurable_pi_apply k).comp measurable_fst.fst
  · simp only [dite_eq_right hm]
    exact measurable_fst.fst
end Rhone.Coalescent.SmcPrime
