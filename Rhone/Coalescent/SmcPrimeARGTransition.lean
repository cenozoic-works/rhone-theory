/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeKingmanSupport
public import Rhone.Coalescent.SmcSupport.ARGActionMixture

/-! # The ARG transition on index-coded lineage arrays and its relation to the sampler step -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess SmcSupport MeasureTheory

noncomputable def splitSuccessorNat (s : State) (i : ℕ) (x : ℝ) : State :=
  if hi : i < s.2.2.1 then splitSuccessor s ⟨i, hi⟩ x else s

theorem splitSuccessorNat_fixed_measurable (i : ℕ) :
    Measurable (fun p : State × ℝ => splitSuccessorNat p.1 i p.2) := by
  let f (p : LiveState × ((ℝ × ℕ) × ℝ)) :=
    splitSuccessorNat (p.2.1.1, p.2.1.2, p.1) i p.2.2
  have hf : Measurable f := by
    apply measurable_prod_sigma_of_fibers
    intro m
    by_cases hi : i < m
    · simpa only [f, splitSuccessorNat, stateOfFiber, Function.comp_def,
        dite_eq_left hi] using (splitSuccessorFiber_measurable m ⟨i, hi⟩).comp
        ((measurable_snd.fst.fst.prodMk
          (measurable_snd.fst.snd.prodMk measurable_fst)).prodMk measurable_snd.snd)
    · simpa only [f, splitSuccessorNat, stateOfFiber, Function.comp_def,
        dite_eq_right hi] using (stateOfFiber_measurable m).comp
        (measurable_snd.fst.fst.prodMk (measurable_snd.fst.snd.prodMk measurable_fst))
  exact hf.comp (measurable_fst.snd.snd.prodMk
    ((measurable_fst.fst.prodMk measurable_fst.snd.fst).prodMk measurable_snd))

noncomputable def lineageHullEndpoint (upper : Bool) (s : State) (i : ℕ) : ℝ :=
  if hi : i < s.2.2.1 then
    if upper then hullHi (s.2.2.2 ⟨i, hi⟩).2 else hullLo (s.2.2.2 ⟨i, hi⟩).2
  else 0

theorem lineageHullEndpoint_fixed_measurable (upper : Bool) (i : ℕ) :
    Measurable (fun s : State => lineageHullEndpoint upper s i) := by
  have hf : Measurable (fun z : LiveState => if hi : i < z.1 then
      if upper then hullHi (z.2 ⟨i, hi⟩).2 else hullLo (z.2 ⟨i, hi⟩).2 else 0) := by
    apply measurable_sigma_of_fibers
    intro m
    by_cases hi : i < m
    · cases upper
      · simpa only [Function.comp_def, dite_eq_left hi, Bool.false_eq_true, ite_false] using
          hullLo_measurable.comp
            (show Measurable (fun f : Fin m → ℕ × Material => (f ⟨i, hi⟩).2) from
              (measurable_pi_apply (⟨i, hi⟩ : Fin m)).snd)
      · simpa only [Function.comp_def, dite_eq_left hi, ite_true] using
          hullHi_measurable.comp
            (show Measurable (fun f : Fin m → ℕ × Material => (f ⟨i, hi⟩).2) from
              (measurable_pi_apply (⟨i, hi⟩ : Fin m)).snd)
    · simpa only [Function.comp_def, dite_eq_right hi] using
        (measurable_const : Measurable (fun _ : Fin m → ℕ × Material => (0 : ℝ)))
  exact hf.comp measurable_snd.snd

def ARGTransition (p : AugmentedState × AugmentedState) : Prop :=
  KingmanTransition p ∨
    (2 ≤ p.1.1.2.2.1 ∧ ∃ i : ℕ,
      i < p.1.1.2.2.1 ∧
      p.2.2.2 = .inr (.inr (i, (genealogyEventCode p.2.2.2).2.2.2)) ∧
      lineageHullEndpoint false p.1.1 i < (genealogyEventCode p.2.2.2).2.2.2 ∧
      (genealogyEventCode p.2.2.2).2.2.2 < lineageHullEndpoint true p.1.1 i ∧
      p.2.1 = atTime p.2.1.1
        (splitSuccessorNat p.1.1 i (genealogyEventCode p.2.2.2).2.2.2) ∧
      p.1.1.1 < p.2.1.1)

theorem ARGTransition_measurable : MeasurableSet {p | ARGTransition p} := by
  have hm : MeasurableSet {p : AugmentedState × AugmentedState | 2 ≤ p.1.1.2.2.1} :=
    measurableSet_le measurable_const (IntervalProcess.liveCount_measurable.comp measurable_fst.fst)
  have hs : MeasurableSet {p : AugmentedState × AugmentedState | ∃ i : ℕ,
      i < p.1.1.2.2.1 ∧
      p.2.2.2 = .inr (.inr (i, (genealogyEventCode p.2.2.2).2.2.2)) ∧
      lineageHullEndpoint false p.1.1 i < (genealogyEventCode p.2.2.2).2.2.2 ∧
      (genealogyEventCode p.2.2.2).2.2.2 < lineageHullEndpoint true p.1.1 i ∧
      p.2.1 = atTime p.2.1.1
        (splitSuccessorNat p.1.1 i (genealogyEventCode p.2.2.2).2.2.2) ∧
      p.1.1.1 < p.2.1.1} := by
    apply measurableSet_exists
    intro i
    have hx : Measurable (fun p : AugmentedState × AugmentedState =>
        (genealogyEventCode p.2.2.2).2.2.2) :=
      (genealogyEventCode_measurable.comp measurable_snd.snd.snd).snd.snd.snd
    have he : Measurable (fun p : AugmentedState × AugmentedState =>
        (.inr (.inr (i, (genealogyEventCode p.2.2.2).2.2.2)) : Event)) :=
      measurable_inr.comp (measurable_inr.comp (measurable_const.prodMk hx))
    have hu : Measurable (fun p : AugmentedState × AugmentedState =>
        splitSuccessorNat p.1.1 i (genealogyEventCode p.2.2.2).2.2.2) :=
      (splitSuccessorNat_fixed_measurable i).comp (measurable_fst.fst.prodMk hx)
    exact (measurableSet_lt measurable_const
      (IntervalProcess.liveCount_measurable.comp measurable_fst.fst)).inter
      ((measurableSet_eq_fun measurable_snd.snd.snd he).inter
        ((measurableSet_lt ((lineageHullEndpoint_fixed_measurable false i).comp
          measurable_fst.fst) hx).inter
          ((measurableSet_lt hx ((lineageHullEndpoint_fixed_measurable true i).comp
            measurable_fst.fst)).inter
            ((measurableSet_eq_fun measurable_snd.fst
              (measurable_snd.fst.fst.prodMk hu.snd)).inter
              (measurableSet_lt measurable_fst.fst.fst measurable_snd.fst.fst)))))
  exact KingmanTransition_measurable.union (hm.inter hs)

theorem sampleStep_ARGTransition (R : ℝ) (z : AugmentedState) (u : Noise)
    (hu : ∀ i, 0 < u i ∧ u i < 1) :
    ARGTransition (z, sampleStep false R z.1 u) := by
  classical
  by_cases hm : 2 ≤ z.1.2.2.1
  · have ht := unrestricted_totalRate_positive R z.1 hm
    have hz : totalRate false R z.1 ≠ 0 := ne_of_gt ht
    have hstop : ¬ (z.1.2.2.1 ≤ 1 ∨ totalRate false R z.1 = 0) := by
      intro h
      rcases h with hm' | hz'
      · omega
      · exact hz hz'
    obtain ⟨a, ha, hp⟩ := selectedAction_exists_positive false R z.1 u
      (hu 0).1.le (hu 0).2 ht
    have ht' : 0 < (totalRate false R z.1 : ℝ) := by exact_mod_cast ht
    have hlog : Real.log (u 1) / (totalRate false R z.1 : ℝ) < 0 :=
      div_neg_of_neg_of_pos (Real.log_neg (hu 1).1 (hu 1).2) ht'
    have htime : z.1.1 < z.1.1 - Real.log (u 1) / (totalRate false R z.1 : ℝ) := by
      linarith
    cases a with
    | inl ij =>
      have hij := positive_pair_order false R z.1 ij hp
      apply Or.inl
      unfold KingmanTransition
      rw [ite_eq_left hm]
      unfold sampleStep
      rw [ite_eq_right hstop, ha]
      refine ⟨(ij.1.val, ij.2.val), hij, ij.2.isLt, rfl, ?_, htime⟩
      simp only [coalSuccessorNat, dite_eq_left ij.1.isLt, dite_eq_left ij.2.isLt, atTime]
    | inr i =>
      have hlen : 0 < hullLength (z.1.2.2.2 i).2 := by
        by_contra hn
        have he : hullLength (z.1.2.2.2 i).2 = 0 :=
          le_antisymm (le_of_not_gt hn) (le_max_left _ _)
        simp only [candidateRate, he] at hp
        change 0 < R.toNNReal / 2 * 0 at hp
        simp only [mul_zero, lt_self_iff_false] at hp
      have hwidth : 0 < hullHi (z.1.2.2.2 i).2 - hullLo (z.1.2.2.2 i).2 := by
        exact (lt_max_iff.mp hlen).resolve_left (lt_irrefl 0)
      have hcut : hullLo (z.1.2.2.2 i).2 <
          hullLo (z.1.2.2.2 i).2 + hullLength (z.1.2.2.2 i).2 * u 2 ∧
          hullLo (z.1.2.2.2 i).2 + hullLength (z.1.2.2.2 i).2 * u 2 <
            hullHi (z.1.2.2.2 i).2 := by
        rw [hullLength, max_eq_right hwidth.le]
        have hlo := mul_pos hwidth (hu 2).1
        have hhi := mul_lt_mul_of_pos_left (hu 2).2 hwidth
        constructor <;> nlinarith
      apply Or.inr
      unfold sampleStep
      rw [ite_eq_right hstop, ha]
      refine ⟨hm, i.val, i.isLt, rfl, ?_, ?_, ?_, htime⟩
      · simpa only [lineageHullEndpoint, dite_eq_left i.isLt, Bool.false_eq_true,
          ite_false, genealogyEventCode] using hcut.1
      · simpa only [lineageHullEndpoint, dite_eq_left i.isLt, ite_true,
          genealogyEventCode] using hcut.2
      · simp only [splitSuccessorNat, dite_eq_left i.isLt, genealogyEventCode, atTime]
  · have hm' : z.1.2.2.1 ≤ 1 := by omega
    apply Or.inl
    simp [KingmanTransition, hm, sampleStep, hm']

theorem eventProcess_ARGTransition (R : ℝ) (x : AugmentedState) :
    ∀ᵐ ω ∂(eventProcess false R).pathLaw x,
      ∀ k, ARGTransition (ω k, ω (k + 1)) := by
  apply process_transition_relation (eventProcess false R) ARGTransition
    ARGTransition_measurable _ x
  intro z
  change ∀ᵐ y ∂eventKernel false R z, ARGTransition (z, y)
  rw [eventKernel_apply]
  apply (ae_map_iff
    ((sampleStep_measurable false R).comp (measurable_const.prodMk measurable_id)).aemeasurable
    (ARGTransition_measurable.preimage
      (measurable_const.prodMk measurable_id))).mpr
  exact noiseLaw_interior.mono (fun u hu => sampleStep_ARGTransition R z u hu)

end Rhone.Coalescent.SmcPrime
