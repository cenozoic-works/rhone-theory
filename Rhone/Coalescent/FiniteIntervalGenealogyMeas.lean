/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.FiniteIntervalGenealogy

/-! # Measurability of ancestor labels and the genealogy law of the full ARG -/
@[expose] public section

namespace Rhone.Coalescent.IntervalProcess
open MeasureTheory
open scoped ENNReal NNReal

theorem liveCount_measurable : Measurable (fun s : State => s.2.2.1) := by
  have h : Measurable (fun z : LiveState => z.1) := by
    apply measurable_sigma_of_fibers
    intro m
    exact measurable_const
  exact h.comp measurable_snd.snd

theorem liveLabelAt_fixed_measurable (i : ℕ) :
    Measurable (fun s : State => liveLabelAt s i) := by
  have h : Measurable (fun z : LiveState =>
      if hi : i < z.1 then (z.2 ⟨i, hi⟩).1 else 0) := by
    apply measurable_sigma_of_fibers
    intro m
    by_cases hi : i < m
    · simpa only [Function.comp_def, dite_eq_left hi] using
        (measurable_pi_apply (⟨i, hi⟩ : Fin m)).fst
    · simpa only [Function.comp_def, dite_eq_right hi] using
        (measurable_const : Measurable (fun _ : Fin m → ℕ × Material => (0 : ℕ)))
  exact h.comp measurable_snd.snd

theorem liveLabelAt_measurable :
    Measurable (fun p : State × ℕ => liveLabelAt p.1 p.2) := by
  exact measurable_countable_choice (fun p : State × ℕ => p.2) measurable_snd
    (fun i => fun p : State × ℕ => liveLabelAt p.1 i)
    (fun i => (liveLabelAt_fixed_measurable i).comp measurable_fst)

def genealogyEventCode : Event → ℕ × ℕ × ℕ × ℝ
  | .inl _ => (0, 0, 0, 0)
  | .inr (.inl ij) => (1, ij.1, ij.2, 0)
  | .inr (.inr ix) => (2, ix.1, 0, ix.2)

theorem genealogyEventCode_measurable : Measurable genealogyEventCode := by
  exact measurable_const.sumElim
    ((measurable_const.prodMk
      (measurable_fst.prodMk (measurable_snd.prodMk measurable_const))).sumElim
      (measurable_const.prodMk
        (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))))

theorem ancestorStep_measurable (q : GenomicProbe) :
    Measurable (fun p : State × Event × ℕ => ancestorStep p.1 p.2.1 q p.2.2) := by
  let c (p : State × Event × ℕ) := genealogyEventCode p.2.1
  have hc : Measurable c := genealogyEventCode_measurable.comp measurable_snd.fst
  have hm : Measurable (fun p : State × Event × ℕ => p.1.2.2.1) :=
    liveCount_measurable.comp measurable_fst
  have hn : Measurable (fun p : State × Event × ℕ => p.1.2.1) := measurable_fst.snd.fst
  have ha : Measurable (fun p : State × Event × ℕ => p.2.2) := measurable_snd.snd
  have hl : Measurable (fun p : State × Event × ℕ => liveLabelAt p.1 (c p).2.1) :=
    liveLabelAt_measurable.comp (measurable_fst.prodMk hc.snd.fst)
  have hr : Measurable (fun p : State × Event × ℕ => liveLabelAt p.1 (c p).2.2.1) :=
    liveLabelAt_measurable.comp (measurable_fst.prodMk hc.snd.snd.fst)
  have hpair : MeasurableSet {p : State × Event × ℕ |
      (c p).2.1 < (c p).2.2.1 ∧ (c p).2.2.1 < p.1.2.2.1} :=
    (measurableSet_lt hc.snd.fst hc.snd.snd.fst).inter
      (measurableSet_lt hc.snd.snd.fst hm)
  have hhit : MeasurableSet {p : State × Event × ℕ |
      p.2.2 = liveLabelAt p.1 (c p).2.1 ∨
      p.2.2 = liveLabelAt p.1 (c p).2.2.1} :=
    (measurableSet_eq_fun ha hl).union (measurableSet_eq_fun ha hr)
  have hsplit : MeasurableSet {p : State × Event × ℕ |
      (c p).2.1 < p.1.2.2.1 ∧ p.2.2 = liveLabelAt p.1 (c p).2.1} :=
    (measurableSet_lt hc.snd.fst hm).inter (measurableSet_eq_fun ha hl)
  have hcut : MeasurableSet {p : State × Event × ℕ | (q.val : ℝ) < (c p).2.2.2} :=
    measurableSet_lt measurable_const hc.snd.snd.snd
  have hnext : Measurable (fun p : State × Event × ℕ => p.1.2.1 + 1) := by fun_prop
  have hb : Measurable (fun p : State × Event × ℕ =>
      if (c p).1 = 1 then
        if (c p).2.1 < (c p).2.2.1 ∧ (c p).2.2.1 < p.1.2.2.1 then
          if p.2.2 = liveLabelAt p.1 (c p).2.1 ∨
            p.2.2 = liveLabelAt p.1 (c p).2.2.1 then p.1.2.1 else p.2.2
        else p.2.2
      else if (c p).1 = 2 then
        if (c p).2.1 < p.1.2.2.1 ∧ p.2.2 = liveLabelAt p.1 (c p).2.1 then
          if (q.val : ℝ) < (c p).2.2.2 then p.1.2.1 else p.1.2.1 + 1
        else p.2.2
      else p.2.2) :=
    ((hn.piecewise hhit ha).piecewise hpair ha).piecewise
      (measurableSet_eq_fun hc.fst measurable_const)
      (((hn.piecewise hcut hnext).piecewise hsplit ha).piecewise
        (measurableSet_eq_fun hc.fst measurable_const) ha)
  convert hb using 1
  funext p
  rcases p with ⟨s, e, a⟩
  cases e with
  | inl u => simp [ancestorStep, c, genealogyEventCode]
  | inr e => cases e <;> simp [ancestorStep, c, genealogyEventCode] <;> rfl

theorem ancestorLabel_measurable (N : ℕ) (q : GenomicProbe) (i : Fin N) (k : ℕ) :
    Measurable (fun ω : EventPath => ancestorLabel N ω q i k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
      exact (ancestorStep_measurable q).comp
        ((measurable_pi_apply k).fst.prodMk
          ((measurable_pi_apply (k + 1)).snd.snd.prodMk ih))

theorem genealogyObservation_measurable (N : ℕ) :
    Measurable (genealogyObservation N) := by
  apply measurable_pi_iff.mpr
  intro q
  apply measurable_pi_iff.mpr
  intro i
  apply measurable_pi_iff.mpr
  intro j
  apply Measurable.iInf
  intro k
  exact (ENNReal.measurable_ofReal.comp (measurable_pi_apply k).fst.fst).piecewise
    (measurableSet_eq_fun (ancestorLabel_measurable N q i k)
      (ancestorLabel_measurable N q j k)) measurable_const

noncomputable def fullARGGenealogyLaw (N : ℕ) (R : ℝ) : Measure (Genealogy N) :=
  ((eventProcess false R).pathLaw (initialState N, (0, .inl ()))).map
    (genealogyObservation N)

instance fullARGGenealogyLaw_probability (N : ℕ) (R : ℝ) :
    IsProbabilityMeasure (fullARGGenealogyLaw N R) := by
  unfold fullARGGenealogyLaw
  exact (Measure.isProbabilityMeasure_map_iff
    (genealogyObservation_measurable N).aemeasurable).mpr inferInstance

end Rhone.Coalescent.IntervalProcess
