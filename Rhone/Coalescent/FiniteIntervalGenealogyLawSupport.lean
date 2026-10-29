/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.FiniteIntervalGenealogyPath
public import Rhone.Coalescent.FiniteIntervalGenealogyMeas
public import Rhone.Coalescent.SmcSupport.JointSampler

/-! # Law support for chronological sample ancestry -/
@[expose] public section
namespace Rhone.Coalescent.IntervalProcess
open SmcSupport MeasureTheory

theorem materialContains_measurable (q : ℝ) :
    MeasurableSet {a : Material | materialContains a q} := by
  apply measurableSet_sigma_of_fibers
  intro k
  change MeasurableSet {a : Fin (k + 1) → ℝ × ℝ | ∃ i, (a i).1 ≤ q ∧ q < (a i).2}
  apply measurableSet_exists
  intro i
  have hi : Measurable (fun a : Fin (k + 1) → ℝ × ℝ => a i) := measurable_pi_apply i
  exact (measurableSet_le hi.fst measurable_const).inter
    (measurableSet_lt measurable_const hi.snd)

theorem ancestorCarried_fixed_measurable (q : ℝ) (a : ℕ) :
    MeasurableSet {s : State | ancestorCarried s q a} := by
  apply statePredicate_measurable
  intro m
  change MeasurableSet {p : FiberState m | ∃ i,
    (p.2.2 i).1 = a ∧ materialContains (p.2.2 i).2 q}
  apply measurableSet_exists
  intro i
  have hi : Measurable (fun p : FiberState m => p.2.2 i) :=
    (measurable_pi_apply i).comp measurable_snd.snd
  exact (measurableSet_eq_fun hi.fst measurable_const).inter
    ((materialContains_measurable q).preimage hi.snd)

theorem ancestorCarried_measurable (q : ℝ) :
    MeasurableSet {p : State × ℕ | ancestorCarried p.1 q p.2} := by
  classical
  have hf : Measurable (fun p : State × ℕ =>
      if ancestorCarried p.1 q p.2 then (1 : ℝ) else 0) := by
    exact measurable_countable_choice Prod.snd measurable_snd
      (fun a p => if ancestorCarried p.1 q a then (1 : ℝ) else 0)
      (fun a => measurable_const.piecewise
        ((ancestorCarried_fixed_measurable q a).preimage measurable_fst) measurable_const)
  convert (measurableSet_eq_fun hf (measurable_const :
    Measurable (fun _ : State × ℕ => (1 : ℝ)))) using 1
  ext p
  by_cases hp : ancestorCarried p.1 q p.2 <;> simp [hp]

def ancestryTransition (p : AugmentedState × AugmentedState) : Prop :=
  p.1.1.1 ≤ p.2.1.1 ∧ p.2.2.1 = p.2.1.1 ∧
    (Valid p.1.1 → Valid p.2.1) ∧
    ∀ (q : GenomicProbe) (a : ℕ), Valid p.1.1 → ancestorCarried p.1.1 (q.val : ℝ) a →
      ancestorCarried p.2.1 (q.val : ℝ) (ancestorStep p.1.1 p.2.2.2 q a)

theorem ancestryTransition_measurable :
    MeasurableSet {p : AugmentedState × AugmentedState | ancestryTransition p} := by
  have hpre : MeasurableSet {p : AugmentedState × AugmentedState | Valid p.1.1} :=
    validState_measurable.preimage measurable_fst.fst
  have hpost : MeasurableSet {p : AugmentedState × AugmentedState | Valid p.2.1} :=
    validState_measurable.preimage measurable_snd.fst
  have hv : MeasurableSet {p : AugmentedState × AugmentedState |
      Valid p.1.1 → Valid p.2.1} := by
    convert hpre.compl.union hpost using 1
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_compl_iff, imp_iff_not_or]
  refine (measurableSet_le measurable_fst.fst.fst measurable_snd.fst.fst).inter
    ((measurableSet_eq_fun measurable_snd.snd.fst measurable_snd.fst.fst).inter
      (hv.inter ?_))
  apply measurableSet_forall
  intro q
  apply measurableSet_forall
  intro a
  have hc : MeasurableSet {p : AugmentedState × AugmentedState |
      ancestorCarried p.1.1 (q.val : ℝ) a} :=
    (ancestorCarried_fixed_measurable _ a).preimage measurable_fst.fst
  have hn : MeasurableSet {p : AugmentedState × AugmentedState |
      ancestorCarried p.2.1 (q.val : ℝ) (ancestorStep p.1.1 p.2.2.2 q a)} :=
    (ancestorCarried_measurable _).preimage
      (measurable_snd.fst.prodMk ((ancestorStep_measurable q).comp
        (measurable_fst.fst.prodMk (measurable_snd.snd.snd.prodMk measurable_const))))
  convert hpre.compl.union (hc.compl.union hn) using 1
  ext p
  simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_compl_iff, imp_iff_not_or]

theorem eventProcess_ancestryTransition (mode : Mode) (R : ℝ) (x : AugmentedState) :
    ∀ᵐ ω ∂(eventProcess mode R).pathLaw x,
      ∀ k, ancestryTransition (ω k, ω (k + 1)) := by
  apply process_transition_relation (eventProcess mode R) ancestryTransition
    ancestryTransition_measurable _ x
  intro z
  change ∀ᵐ y ∂eventKernel mode R z, ancestryTransition (z, y)
  rw [eventKernel_apply]
  apply (ae_map_iff
    ((sampleStep_measurable mode R).comp (measurable_const.prodMk measurable_id)).aemeasurable
    (ancestryTransition_measurable.preimage
      (measurable_const.prodMk measurable_id))).mpr
  filter_upwards [noiseLaw_interior] with u hu
  refine ⟨sampleStep_time_le mode R z.1 u (hu 1).1.le (hu 1).2.le,
    sampleStep_record_time mode R z.1 u, ?_, ?_⟩
  · intro hz
    exact sampleStep_valid mode R z.1 hz u (hu 1).1.le (hu 1).2.le (hu 2).1 (hu 2).2
  · intro q a hz ha
    exact sampleStep_ancestorCarried mode R z.1 hz q a ha u (hu 0).1.le (hu 0).2

def ChronologicalAncestryPath (N : ℕ) (ω : EventPath) : Prop :=
  ω 0 = (initialState N, (0, .inl ())) ∧ ∀ k, ancestryTransition (ω k, ω (k + 1))

theorem eventProcess_chronologicalAncestryPath (N : ℕ) (mode : Mode) (R : ℝ) :
    ∀ᵐ ω ∂(eventProcess mode R).pathLaw (initialState N, (0, .inl ())),
      ChronologicalAncestryPath N ω := by
  let x : AugmentedState := (initialState N, (0, .inl ()))
  have hzero : ∀ᵐ ω ∂(eventProcess mode R).pathLaw x, ω 0 = x := by
    apply ae_of_ae_map
      (μ := (eventProcess mode R).pathLaw x)
      (f := fun ω : EventPath => ω 0) (p := fun y => y = x)
      (measurable_pi_apply 0).aemeasurable
    rw [(eventProcess mode R).map_eval_zero]
    exact (ae_dirac_iff (measurableSet_singleton x)).mpr rfl
  filter_upwards [hzero, eventProcess_ancestryTransition mode R x] with ω h0 hs
  exact ⟨h0, hs⟩

theorem ChronologicalAncestryPath.valid {N : ℕ} {ω : EventPath}
    (h : ChronologicalAncestryPath N ω) (k : ℕ) : Valid (ω k).1 := by
  induction k with
  | zero => rw [h.1]; exact initialState_valid N
  | succ k ih => exact (h.2 k).2.2.1 ih

theorem ChronologicalAncestryPath.ancestorCarried {N : ℕ} {ω : EventPath}
    (h : ChronologicalAncestryPath N ω) (q : GenomicProbe) (i : Fin N) (k : ℕ) :
    ancestorCarried (ω k).1 (q.val : ℝ) (ancestorLabel N ω q i k) := by
  induction k with
  | zero => simp only [ancestorLabel, h.1]; exact initial_ancestorCarried N q i
  | succ k ih => exact (h.2 k).2.2.2 q _ (h.valid k) ih

theorem ChronologicalAncestryPath.time_monotone {N : ℕ} {ω : EventPath}
    (h : ChronologicalAncestryPath N ω) : Monotone (fun k => (ω k).1.1) :=
  monotone_nat_of_le_succ (fun k => (h.2 k).1)

theorem ChronologicalAncestryPath.completed_of_coverage {N : ℕ} {ω : EventPath}
    (h : ChronologicalAncestryPath N ω) (K : ℕ) (hk : CompletedCoverage (ω K).1) :
    ∀ q i j, ancestorLabel N ω q i K = ancestorLabel N ω q j K := by
  intro q i j
  obtain ⟨a, ha, haq⟩ := h.ancestorCarried q i K
  obtain ⟨b, hb, hbq⟩ := h.ancestorCarried q j K
  exact ha.symm.trans (hk q a b haq hbq ▸ hb)

theorem ChronologicalAncestryPath.observation_eq_prefix_of_coverage {N : ℕ}
    {ω : EventPath} (h : ChronologicalAncestryPath N ω) (K : ℕ)
    (hk : CompletedCoverage (ω K).1) :
    genealogyObservation N ω = prefixGenealogyObservation N K ω :=
  genealogyObservation_eq_prefix N K ω h.time_monotone (h.completed_of_coverage K hk)

end Rhone.Coalescent.IntervalProcess
