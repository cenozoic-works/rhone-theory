/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module
public import Rhone.Coalescent.SmcPrimeARGNoSplitHistory

/-!
# The zero-split sector of the ARG genealogy law equals the zero-proposal sector

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 1–7. -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open MeasureTheory ProbabilityTheory IntervalProcess SmcSupport

def argNoSplitPathSet : Set EventPath := {ω | ∀ k, ω k ∈ argNoSplitEvent}

theorem argNoSplitPathSet_measurable : MeasurableSet argNoSplitPathSet := by
  apply measurableSet_forall
  intro k
  exact argNoSplitEvent_measurable.preimage (measurable_pi_apply k)

noncomputable def zeroSplitARGGenealogySector (N : ℕ) (R : ℝ) : Measure (Genealogy N) :=
  (((eventProcess false R).pathLaw (initialState N, (0, .inl ()))).restrict
    argNoSplitPathSet).map (genealogyObservation N)

theorem KingmanTransition.noSplit {p : AugmentedState × AugmentedState}
    (hp : KingmanTransition p) : p.2 ∈ argNoSplitEvent := by
  by_cases hm : 2 ≤ p.1.1.2.2.1
  · obtain ⟨ij, _, _, he, _, _⟩ := (ite_eq_left hm).mp hp
    simp [argNoSplitEvent, he, genealogyEventCode]
  · obtain ⟨_, he⟩ := (ite_eq_right hm).mp hp
    simp [argNoSplitEvent, he, genealogyEventCode]

theorem argNoSplitPathSet_prefix_ae (N : ℕ) (hN : 0 < N) (R : ℝ) :
    argNoSplitPathSet =ᵐ[(eventProcess false R).pathLaw (initialState N, (0, .inl ()))]
      (fun ω : EventPath => fun k : Finset.Iic (N - 1) => ω k.val) ⁻¹'
        argNoSplitPrefixSet (N - 1) := by
  filter_upwards [eventProcess_chronologicalAncestryPath N false R,
    eventProcess_kingman_of_noSplit R (initialState N, (0, .inl ()))] with ω hc hl
  apply propext
  constructor
  · intro hn j
    exact hn (j.val + 1)
  · intro hp
    have hs := noSplit_prefix_kingman N hN ω (congrArg Prod.fst hc.1) hl
      (fun k hk => hp ⟨k, hk⟩)
    intro k
    cases k with
    | zero => simp [hc.1, argNoSplitEvent, genealogyEventCode]
    | succ k => exact (hs k).noSplit

theorem argNoSplitHistorySource_genealogy (N : ℕ) (hN : 0 < N) (R : ℝ) :
    (argNoSplitHistorySource N R).map (zeroHistoryGenealogy N) =
      zeroSplitARGGenealogySector N R := by
  let F (ω : EventPath) : ARGPrefix (N - 1) := fun k => ω k.val
  have hF : Measurable F := measurable_pi_iff.mpr (fun k => measurable_pi_apply k.val)
  have hS := (argNoSplitPrefixSet_measurable (N - 1)).preimage hF
  have ho : (fun ω => zeroHistoryGenealogy N (argPrefixKingmanHistory N (F ω))) =ᵐ[
      ((eventProcess false R).pathLaw (initialState N, (0, .inl ()))).restrict
        (F ⁻¹' argNoSplitPrefixSet (N - 1))] genealogyObservation N := by
    filter_upwards [ae_restrict_mem hS,
      ae_restrict_of_ae (eventProcess_chronologicalAncestryPath N false R),
      ae_restrict_of_ae (eventProcess_kingman_of_noSplit R (initialState N, (0, .inl ())))]
      with ω hp hc hl
    have hs := noSplit_prefix_kingman N hN ω (congrArg Prod.fst hc.1) hl
      (fun k hk => hp ⟨k, hk⟩)
    funext q i j
    exact metric_tree_pair_mrca N ω (congrArg Prod.fst hc.1) hc.valid hs hN q i j
  rw [argNoSplitHistorySource, Measure.map_map (zeroHistoryGenealogy_measurable N)
    (argPrefixKingmanHistory_measurable N), argNoSplitPrefixLaw, argPrefixLaw,
    Measure.restrict_map hF (argNoSplitPrefixSet_measurable (N - 1)),
    Measure.map_map ((zeroHistoryGenealogy_measurable N).comp
      (argPrefixKingmanHistory_measurable N)) hF,
    zeroSplitARGGenealogySector,
    Measure.restrict_congr_set (argNoSplitPathSet_prefix_ae N hN R)]
  exact Measure.map_congr ho

theorem zeroSplitARGGenealogySector_eq_of_pos (N : ℕ) (hN : 0 < N) (R : ℝ) (hR : 0 ≤ R) :
    zeroSplitARGGenealogySector N R = zeroProposalGenealogySector N R := by
  rw [← argNoSplitHistorySource_genealogy N hN R,
    argNoSplitHistorySource_density N (by omega) R hR,
    zeroProposalGenealogySector_density N R hR]
theorem eventProcess_noSplit_zero_samples (R : ℝ) :
    ∀ᵐ ω ∂(eventProcess false R).pathLaw (initialState 0, (0, .inl ())),
      ω ∈ argNoSplitPathSet := by
  filter_upwards [eventProcess_chronologicalAncestryPath 0 false R,
    eventProcess_kingman_of_noSplit R (initialState 0, (0, .inl ()))] with ω hc hl
  have hk : ∀ k, (ω k).1.2.2.1 = 0 ∧ KingmanTransition (ω k, ω (k + 1)) := by
    intro k
    induction k with
    | zero =>
      have he : (ω 0).1.2.2.1 = 0 := by rw [hc.1]; rfl
      exact ⟨he, hl 0 (Or.inr (by omega))⟩
    | succ k ih =>
      have he := ih.2.count
      change (ω (k + 1)).1.2.2.1 =
        if 2 ≤ (ω k).1.2.2.1 then (ω k).1.2.2.1 - 1 else (ω k).1.2.2.1 at he
      simp only [ih.1, show ¬ (2 : ℕ) ≤ 0 by omega, ite_false] at he
      exact ⟨he, hl (k + 1) (Or.inr (by omega))⟩
  intro k
  cases k with
  | zero => simp [hc.1, argNoSplitEvent, genealogyEventCode]
  | succ k => exact (hk k).2.noSplit

theorem zeroSplitARGGenealogySector_eq (N : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    zeroSplitARGGenealogySector N R = zeroProposalGenealogySector N R := by
  by_cases hN : 0 < N
  · exact zeroSplitARGGenealogySector_eq_of_pos N hN R hR
  · have hn : N = 0 := by omega
    subst N
    have hARG : IsProbabilityMeasure (zeroSplitARGGenealogySector 0 R) := by
      unfold zeroSplitARGGenealogySector
      rw [Measure.restrict_eq_self_of_ae_mem (eventProcess_noSplit_zero_samples R)]
      infer_instance
    have hSMC : IsProbabilityMeasure (zeroProposalGenealogySector 0 R) := by
      rw [zeroProposalGenealogySector_density 0 R hR]
      have hw : (fun h : KingmanHistory 0 => ENNReal.ofReal
          (Real.exp (-(R / 2 * treeLength (metricTreeFromHistory 0 h))))) = 1 := by
        funext h
        have hL : treeLength (metricTreeFromHistory 0 h) = 0 := by
          change treeLength (treeOfList ([] : List (Branch 0))) = 0
          unfold treeLength treeOfList
          exact Finset.sum_eq_zero (fun i _ => Fin.elim0 i)
        simp [hL]
      rw [hw, withDensity_one]
      infer_instance
    apply Measure.ext_of_lintegral
    intro g _
    let a : Genealogy 0 := zeroHistoryGenealogy 0 (fun i => Fin.elim0 i)
    have he : g = fun _ => g a := by
      funext b
      exact congrArg g (Subsingleton.elim b a)
    rw [he, lintegral_const, lintegral_const, measure_univ, measure_univ]
theorem zeroSplitARGGenealogySector_le (N : ℕ) (R : ℝ) :
    zeroSplitARGGenealogySector N R ≤ fullARGGenealogyLaw N R := by
  exact Measure.map_mono Measure.restrict_le_self (genealogyObservation_measurable N)

theorem zeroProposalGenealogySector_le_fullARG (N : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    zeroProposalGenealogySector N R ≤ fullARGGenealogyLaw N R := by
  rw [← zeroSplitARGGenealogySector_eq N R hR]
  exact zeroSplitARGGenealogySector_le N R
end Rhone.Coalescent.SmcPrime
