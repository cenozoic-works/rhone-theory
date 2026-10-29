/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeKingmanHistory
public import Rhone.Coalescent.SmcSupport.StateMeasurable

/-! # Support of the zero-recombination Kingman initialization -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess SmcSupport MeasureTheory
open scoped NNReal ENNReal

noncomputable def coalSuccessorNat (s : State) (ij : ℕ × ℕ) : State :=
  if hi : ij.1 < s.2.2.1 then
    if hj : ij.2 < s.2.2.1 then coalSuccessor s ⟨ij.1, hi⟩ ⟨ij.2, hj⟩ else s
  else s

theorem coalSuccessorNat_fixed_measurable (ij : ℕ × ℕ) :
    Measurable (fun s : State => coalSuccessorNat s ij) := by
  let f (p : LiveState × (ℝ × ℕ)) := coalSuccessorNat (p.2.1, p.2.2, p.1) ij
  have hf : Measurable f := by
    apply measurable_prod_sigma_of_fibers
    intro m
    by_cases hi : ij.1 < m
    · by_cases hj : ij.2 < m
      · simpa only [f, coalSuccessorNat, stateOfFiber, Function.comp_def,
          dite_eq_left hi, dite_eq_left hj] using
          (coalSuccessorFiber_measurable m ⟨ij.1, hi⟩ ⟨ij.2, hj⟩).comp
            (measurable_snd.fst.prodMk (measurable_snd.snd.prodMk measurable_fst))
      · simpa only [f, coalSuccessorNat, stateOfFiber, Function.comp_def,
          dite_eq_left hi, dite_eq_right hj] using
          (stateOfFiber_measurable m).comp
            (measurable_snd.fst.prodMk (measurable_snd.snd.prodMk measurable_fst))
    · simpa only [f, coalSuccessorNat, stateOfFiber, Function.comp_def, dite_eq_right hi] using
        (stateOfFiber_measurable m).comp
          (measurable_snd.fst.prodMk (measurable_snd.snd.prodMk measurable_fst))
  exact hf.comp (measurable_snd.snd.prodMk (measurable_fst.prodMk measurable_snd.fst))

theorem coalSuccessorNat_measurable :
    Measurable (fun p : State × (ℕ × ℕ) => coalSuccessorNat p.1 p.2) :=
  measurable_countable_choice Prod.snd measurable_snd
    (fun ij p => coalSuccessorNat p.1 ij)
    (fun ij => (coalSuccessorNat_fixed_measurable ij).comp measurable_fst)

def KingmanTransition (p : AugmentedState × AugmentedState) : Prop :=
  if 2 ≤ p.1.1.2.2.1 then
    ∃ ij : ℕ × ℕ, ij.1 < ij.2 ∧ ij.2 < p.1.1.2.2.1 ∧
      p.2.2.2 = .inr (.inl ij) ∧
      p.2.1 = atTime p.2.1.1 (coalSuccessorNat p.1.1 ij) ∧ p.1.1.1 < p.2.1.1
  else p.2.1 = p.1.1 ∧ p.2.2.2 = .inl ()

theorem KingmanTransition_measurable : MeasurableSet {p | KingmanTransition p} := by
  classical
  have hc : MeasurableSet {p : AugmentedState × AugmentedState | 2 ≤ p.1.1.2.2.1} :=
    measurableSet_le measurable_const (IntervalProcess.liveCount_measurable.comp measurable_fst.fst)
  have hp : MeasurableSet {p : AugmentedState × AugmentedState |
      ∃ ij : ℕ × ℕ, ij.1 < ij.2 ∧ ij.2 < p.1.1.2.2.1 ∧
        p.2.2.2 = .inr (.inl ij) ∧
        p.2.1 = atTime p.2.1.1 (coalSuccessorNat p.1.1 ij) ∧ p.1.1.1 < p.2.1.1} := by
    apply measurableSet_exists
    intro ij
    by_cases hij : ij.1 < ij.2
    · simp only [hij, true_and]
      have hu : Measurable (fun p : AugmentedState × AugmentedState =>
          atTime p.2.1.1 (coalSuccessorNat p.1.1 ij)) :=
        measurable_snd.fst.fst.prodMk
          (((coalSuccessorNat_fixed_measurable ij).comp measurable_fst.fst).snd)
      exact (measurableSet_lt measurable_const
        (IntervalProcess.liveCount_measurable.comp measurable_fst.fst)).inter
          ((measurableSet_eq_fun measurable_snd.snd.snd measurable_const).inter
            ((measurableSet_eq_fun measurable_snd.fst hu).inter
              (measurableSet_lt measurable_fst.fst.fst measurable_snd.fst.fst)))
    · simp [hij]
  have hs : MeasurableSet {p : AugmentedState × AugmentedState |
      p.2.1 = p.1.1 ∧ p.2.2.2 = .inl ()} :=
    (measurableSet_eq_fun measurable_snd.fst measurable_fst.fst).inter
      (measurableSet_eq_fun measurable_snd.snd.snd measurable_const)
  convert (hc.inter hp).union (hc.compl.inter hs) using 1
  ext p
  by_cases h : 2 ≤ p.1.1.2.2.1 <;> simp [KingmanTransition, h]

theorem sampleStep_kingmanTransition (z : AugmentedState) (u : Noise)
    (hu : ∀ i, 0 < u i ∧ u i < 1) :
    KingmanTransition (z, sampleStep false 0 z.1 u) := by
  classical
  by_cases hm : 2 ≤ z.1.2.2.1
  · have ht := unrestricted_totalRate_positive 0 z.1 hm
    have hz : totalRate false 0 z.1 ≠ 0 := ne_of_gt ht
    have hstop : ¬ (z.1.2.2.1 ≤ 1 ∨ totalRate false 0 z.1 = 0) := by
      intro h
      rcases h with hm' | hz'
      · omega
      · exact hz hz'
    obtain ⟨a, ha, hp⟩ := selectedAction_exists_positive false 0 z.1 u
      (hu 0).1.le (hu 0).2 ht
    cases a with
    | inr i =>
      have hc : candidateRate false 0 z.1 (.inr i) = 0 := by
        simp only [candidateRate, Real.toNNReal_zero, zero_div]
        exact zero_mul _
      rw [hc] at hp
      exact False.elim ((lt_irrefl (0 : ℝ≥0)) hp)
    | inl ij =>
      have hij := positive_pair_order false 0 z.1 ij hp
      have ht' : 0 < (totalRate false 0 z.1 : ℝ) := by exact_mod_cast ht
      have hlog : Real.log (u 1) / (totalRate false 0 z.1 : ℝ) < 0 :=
        div_neg_of_neg_of_pos (Real.log_neg (hu 1).1 (hu 1).2) ht'
      have htime : z.1.1 < z.1.1 - Real.log (u 1) / (totalRate false 0 z.1 : ℝ) := by
        linarith
      unfold KingmanTransition
      rw [ite_eq_left hm]
      unfold sampleStep
      rw [ite_eq_right hstop, ha]
      refine ⟨(ij.1.val, ij.2.val), hij, ij.2.isLt, rfl, ?_, htime⟩
      simp only [coalSuccessorNat, dite_eq_left ij.1.isLt, dite_eq_left ij.2.isLt, atTime]
  · have hm' : z.1.2.2.1 ≤ 1 := by omega
    simp [KingmanTransition, hm, sampleStep, hm']

theorem eventProcess_kingmanTransition (x : AugmentedState) :
    ∀ᵐ ω ∂(eventProcess false 0).pathLaw x,
      ∀ k, KingmanTransition (ω k, ω (k + 1)) := by
  apply process_transition_relation (eventProcess false 0) KingmanTransition
    KingmanTransition_measurable _ x
  intro z
  change ∀ᵐ y ∂eventKernel false 0 z, KingmanTransition (z, y)
  rw [eventKernel_apply]
  apply (ae_map_iff
    ((sampleStep_measurable false 0).comp (measurable_const.prodMk measurable_id)).aemeasurable
    (KingmanTransition_measurable.preimage
      (measurable_const.prodMk measurable_id))).mpr
  exact noiseLaw_interior.mono (fun u hu => sampleStep_kingmanTransition z u hu)

theorem KingmanTransition.count {p : AugmentedState × AugmentedState}
    (h : KingmanTransition p) :
    p.2.1.2.2.1 = if 2 ≤ p.1.1.2.2.1 then p.1.1.2.2.1 - 1 else p.1.1.2.2.1 := by
  classical
  by_cases hm : 2 ≤ p.1.1.2.2.1
  · obtain ⟨ij, hij, hj, _, he, _⟩ := (ite_eq_left hm).mp h
    have hi : ij.1 < p.1.1.2.2.1 := lt_trans hij hj
    have hc := coalSuccessor_count p.1.1 ⟨ij.1, hi⟩ ⟨ij.2, hj⟩ hij
    rw [he, ite_eq_left hm]
    simp only [atTime, coalSuccessorNat, dite_eq_left hi, dite_eq_left hj]
    omega
  · obtain ⟨he, _⟩ := (ite_eq_right hm).mp h
    rw [he, ite_eq_right hm]

theorem KingmanTransition.fresh {p : AugmentedState × AugmentedState}
    (h : KingmanTransition p) (hm : 2 ≤ p.1.1.2.2.1) :
    p.2.1.2.1 = p.1.1.2.1 + 1 := by
  classical
  obtain ⟨ij, hij, hj, _, he, _⟩ := (ite_eq_left hm).mp h
  have hi : ij.1 < p.1.1.2.2.1 := lt_trans hij hj
  rw [he]
  simp only [atTime, coalSuccessorNat, dite_eq_left hi, dite_eq_left hj,
    coalSuccessor, ite_eq_left hij]

theorem kingman_path_count (N : ℕ) (ω : EventPath)
    (hinit : (ω 0).1 = initialState N)
    (hstep : ∀ k, KingmanTransition (ω k, ω (k + 1))) (k : ℕ) (hk : k < N) :
    (ω k).1.2.2.1 = N - k := by
  induction k with
  | zero => simp [hinit, initialState]
  | succ k ih =>
    have hk' : k < N := by omega
    have hc := (hstep k).count
    have hi := ih hk'
    have hm : 2 ≤ (ω k).1.2.2.1 := by omega
    rw [ite_eq_left hm, hi] at hc
    omega

theorem kingman_path_fresh (N : ℕ) (ω : EventPath)
    (hinit : (ω 0).1 = initialState N)
    (hstep : ∀ k, KingmanTransition (ω k, ω (k + 1))) (k : ℕ) (hk : k < N) :
    (ω k).1.2.1 = N + k := by
  induction k with
  | zero => simp [hinit, initialState]
  | succ k ih =>
    have hk' : k < N := by omega
    have hc := kingman_path_count N ω hinit hstep k hk'
    have hm : 2 ≤ (ω k).1.2.2.1 := by omega
    have hf := (hstep k).fresh hm
    rw [ih hk'] at hf
    omega

end Rhone.Coalescent.SmcPrime
