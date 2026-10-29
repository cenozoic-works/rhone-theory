/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module
public import Rhone.Coalescent.SmcPrimeARGNoSplitKernel
public import Rhone.Coalescent.SmcPrimeKingmanObservation
public import Rhone.Coalescent.SmcPrimeARGNoSplitPrefixDensity
public import Rhone.Coalescent.SmcPrimeKingmanLength
public import Rhone.Coalescent.SmcPrimeSectorDensityLaw

/-!
# Density of the no-split Kingman history and the observation of supported paths

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 1–7. -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open MeasureTheory ProbabilityTheory IntervalProcess SmcSupport

theorem sampleStep_kingman_of_noSplit (R : ℝ) (z : AugmentedState) (u : Noise)
    (hu : ∀ i, 0 < u i ∧ u i < 1)
    (hn : sampleStep false R z.1 u ∈ argNoSplitEvent ∨ z.1.2.2.1 ≤ 1) :
    KingmanTransition (z, sampleStep false R z.1 u) := by
  classical
  by_cases hm : 2 ≤ z.1.2.2.1
  · have ht := unrestricted_totalRate_positive R z.1 hm
    have hz : totalRate false R z.1 ≠ 0 := ne_of_gt ht
    have hstop : ¬ (z.1.2.2.1 ≤ 1 ∨ totalRate false R z.1 = 0) := by
      intro h
      rcases h with hm' | hz'
      · omega
      · exact hz hz'
    have hns : sampleStep false R z.1 u ∈ argNoSplitEvent := hn.resolve_right (by omega)
    obtain ⟨a, ha, hp⟩ := selectedAction_exists_positive false R z.1 u
      (hu 0).1.le (hu 0).2 ht
    cases a with
    | inr i =>
      unfold sampleStep at hns
      rw [ite_eq_right hstop, ha] at hns
      simp [argNoSplitEvent, genealogyEventCode] at hns
    | inl ij =>
      have hij := positive_pair_order false R z.1 ij hp
      have ht' : 0 < (totalRate false R z.1 : ℝ) := by exact_mod_cast ht
      have hlog : Real.log (u 1) / (totalRate false R z.1 : ℝ) < 0 :=
        div_neg_of_neg_of_pos (Real.log_neg (hu 1).1 (hu 1).2) ht'
      have htime : z.1.1 < z.1.1 - Real.log (u 1) / (totalRate false R z.1 : ℝ) := by
        linarith
      unfold KingmanTransition
      rw [ite_eq_left hm]
      unfold sampleStep
      rw [ite_eq_right hstop, ha]
      refine ⟨(ij.1.val, ij.2.val), hij, ij.2.isLt, rfl, ?_, htime⟩
      simp only [coalSuccessorNat, dite_eq_left ij.1.isLt, dite_eq_left ij.2.isLt, atTime]
  · have hm' : z.1.2.2.1 ≤ 1 := by omega
    simp [KingmanTransition, hm, sampleStep, hm']

theorem eventProcess_kingman_of_noSplit (R : ℝ) (z : AugmentedState) :
    ∀ᵐ ω ∂(eventProcess false R).pathLaw z,
      ∀ k, ω (k + 1) ∈ argNoSplitEvent ∨ (ω k).1.2.2.1 ≤ 1 →
        KingmanTransition (ω k, ω (k + 1)) := by
  let A (p : AugmentedState × AugmentedState) :=
    p.2 ∈ argNoSplitEvent ∨ p.1.1.2.2.1 ≤ 1 → KingmanTransition p
  have hA : MeasurableSet {p | A p} := by
    have hpre : MeasurableSet {p : AugmentedState × AugmentedState |
        p.2 ∈ argNoSplitEvent ∨ p.1.1.2.2.1 ≤ 1} :=
      (argNoSplitEvent_measurable.preimage measurable_snd).union
        (measurableSet_le
          (IntervalProcess.liveCount_measurable.comp measurable_fst.fst) measurable_const)
    convert hpre.compl.union KingmanTransition_measurable using 1
    ext p
    simp only [A, Set.mem_union, Set.mem_compl_iff, Set.mem_ofPred_eq, imp_iff_not_or]
  apply process_transition_relation (eventProcess false R) A hA _ z
  intro w
  change ∀ᵐ y ∂eventKernel false R w, A (w, y)
  rw [eventKernel_apply]
  apply (ae_map_iff
    ((sampleStep_measurable false R).comp (measurable_const.prodMk measurable_id)).aemeasurable
    (hA.preimage (measurable_const.prodMk measurable_id))).mpr
  exact noiseLaw_interior.mono (fun u hu hn => sampleStep_kingman_of_noSplit R w u hu hn)

theorem noSplit_prefix_kingman (N : ℕ) (hN : 0 < N) (ω : EventPath)
    (hinit : (ω 0).1 = initialState N)
    (hlocal : ∀ k, ω (k + 1) ∈ argNoSplitEvent ∨ (ω k).1.2.2.1 ≤ 1 →
      KingmanTransition (ω k, ω (k + 1)))
    (hprefix : ∀ k < N - 1, ω (k + 1) ∈ argNoSplitEvent) :
    ∀ k, KingmanTransition (ω k, ω (k + 1)) := by
  have hc : ∀ k, (ω k).1.2.2.1 = max 1 (N - k) ∧
      KingmanTransition (ω k, ω (k + 1)) := by
    intro k
    induction k with
    | zero =>
      have hcount : (ω 0).1.2.2.1 = max 1 N := by rw [hinit]; simp [initialState]; omega
      refine ⟨by simpa using hcount, hlocal 0 ?_⟩
      by_cases hz : 0 < N - 1
      · exact Or.inl (hprefix 0 hz)
      · exact Or.inr (by rw [hcount]; omega)
    | succ k ih =>
      have hcount := ih.2.count
      have he : (ω (k + 1)).1.2.2.1 = max 1 (N - (k + 1)) := by
        change (ω (k + 1)).1.2.2.1 =
          if 2 ≤ (ω k).1.2.2.1 then (ω k).1.2.2.1 - 1 else (ω k).1.2.2.1 at hcount
        rw [ih.1] at hcount
        apply hcount.trans
        split_ifs <;> omega
      refine ⟨he, hlocal (k + 1) ?_⟩
      by_cases hk : k + 1 < N - 1
      · exact Or.inl (hprefix (k + 1) hk)
      · exact Or.inr (by rw [he]; omega)
  exact fun k => (hc k).2
end Rhone.Coalescent.SmcPrime

namespace Rhone.Coalescent.SmcPrime
open MeasureTheory ProbabilityTheory IntervalProcess SmcSupport
open scoped ENNReal

theorem kingman_path_zeroSplitReachable (N : ℕ) (ω : EventPath)
    (hinit : (ω 0).1 = initialState N)
    (hstep : ∀ k, KingmanTransition (ω k, ω (k + 1))) (k : ℕ) :
    ZeroSplitReachable (ω k).1 := by
  induction k with
  | zero => rw [hinit]; exact .initial N
  | succ k ih =>
    by_cases hm : 2 ≤ (ω k).1.2.2.1
    · obtain ⟨ij, hij, hj, _, he, _⟩ := (ite_eq_left hm).mp (hstep k)
      have hi := hij.trans hj
      rw [he]
      have hc := ZeroSplitReachable.coal ih (⟨ij.1, hi⟩ : Fin (ω k).1.2.2.1)
        (⟨ij.2, hj⟩ : Fin (ω k).1.2.2.1)
      simpa only [atTime, coalSuccessorNat, dite_eq_left hi, dite_eq_left hj] using
        ZeroSplitReachable.clock hc (ω (k + 1)).1.1
    · obtain ⟨he, _⟩ := (ite_eq_right hm).mp (hstep k)
      rw [he]
      exact ih

theorem kingman_history_extra_rate (N : ℕ) (h : KingmanHistory N)
    (hs : KingmanHistorySupported N h) (R : ℝ) (hR : 0 ≤ R) (k : Fin N) :
    (totalRate false R (h k).1 : ℝ) - (totalRate false 0 (h k).1 : ℝ) =
      R / 2 * ((h k).1.2.2.1 : ℝ) := by
  have hr := kingman_path_zeroSplitReachable N (kingmanCompletion N h)
    hs.completion_init hs.completion_step k.val
  rw [kingmanCompletion_prefix N h k.val k.isLt] at hr
  rw [totalRate_unrestricted_real R hR, totalRate_unrestricted_real 0 (by positivity),
    zeroSplit_recombinationRate R hr, zeroSplit_recombinationRate 0 hr]
  ring

def argPrefixKingmanHistory (N : ℕ) (p : ARGPrefix (N - 1)) : KingmanHistory N :=
  fun k => p ⟨k.val, Finset.mem_Iic.mpr (by omega)⟩

theorem argPrefixKingmanHistory_measurable (N : ℕ) : Measurable (argPrefixKingmanHistory N) :=
  measurable_pi_iff.mpr (fun _ => measurable_pi_apply _)

noncomputable def argNoSplitHistorySource (N : ℕ) (R : ℝ) : Measure (KingmanHistory N) :=
  (argNoSplitPrefixLaw R (initialState N, (0, .inl ())) (N - 1)).map
    (argPrefixKingmanHistory N)

theorem argPrefixKingmanHistory_zero_law (N : ℕ) :
    (argPrefixLaw 0 (initialState N, (0, .inl ())) (N - 1)).map
      (argPrefixKingmanHistory N) = kingmanHistoryLaw N := by
  rw [argPrefixLaw, Measure.map_map (argPrefixKingmanHistory_measurable N) (by fun_prop)]
  rfl

theorem argNoSplitPrefixWeight_kingman (N : ℕ) (hN : 1 ≤ N) (R : ℝ) (hR : 0 ≤ R)
    (p : ARGPrefix (N - 1)) (hs : KingmanHistorySupported N (argPrefixKingmanHistory N p)) :
    argNoSplitPrefixWeight R (N - 1) p = ENNReal.ofReal
      (Real.exp (-(R / 2 *
        treeLength (metricTreeFromHistory N (argPrefixKingmanHistory N p))))) := by
  let h := argPrefixKingmanHistory N p
  have he := metric_tree_from_history_length N h hN hs
  unfold argNoSplitPrefixWeight argNoSplitFactor
  rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => Real.exp_nonneg _), ← Real.exp_sum]
  congr 1
  rw [he, Finset.mul_sum, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  have hk := kingman_history_extra_rate N h hs R hR (⟨k.val, by omega⟩ : Fin N)
  change (totalRate false R (p ⟨k.val, Finset.mem_Iic.mpr (by omega)⟩).1 : ℝ) -
    (totalRate false 0 (p ⟨k.val, Finset.mem_Iic.mpr (by omega)⟩).1 : ℝ) =
      R / 2 * ((p ⟨k.val, Finset.mem_Iic.mpr (by omega)⟩).1.2.2.1 : ℝ) at hk
  rw [hk]
  change -(R / 2 * ((p ⟨k.val, Finset.mem_Iic.mpr (by omega)⟩).1.2.2.1 : ℝ)) *
    ((p ⟨k.val + 1, Finset.mem_Iic.mpr (by omega)⟩).1.1 -
      (p ⟨k.val, Finset.mem_Iic.mpr (by omega)⟩).1.1) = _
  dsimp only [h, argPrefixKingmanHistory]
  ring

theorem argNoSplitHistorySource_density (N : ℕ) (hN : 1 ≤ N) (R : ℝ) (hR : 0 ≤ R) :
    argNoSplitHistorySource N R = (kingmanHistoryLaw N).withDensity (fun h =>
      ENNReal.ofReal (Real.exp (-(R / 2 * treeLength (metricTreeFromHistory N h))))) := by
  let f (h : KingmanHistory N) :=
    ENNReal.ofReal (Real.exp (-(R / 2 * treeLength (metricTreeFromHistory N h))))
  have hf : Measurable f := (Real.measurable_exp.comp
    (measurable_const.mul ((treeLength_joint_measurable N).comp
      (metricTreeFromHistory_measurable N))).neg).ennreal_ofReal
  have hp : ∀ᵐ p ∂argPrefixLaw 0 (initialState N, (0, .inl ())) (N - 1),
      KingmanHistorySupported N (argPrefixKingmanHistory N p) := by
    apply ae_of_ae_map (argPrefixKingmanHistory_measurable N).aemeasurable
    rw [argPrefixKingmanHistory_zero_law]
    exact kingmanHistoryLaw_supported N
  rw [argNoSplitHistorySource, argNoSplitPrefixLaw_density R hR,
    ← argPrefixKingmanHistory_zero_law N]
  apply Measure.ext_of_lintegral
  intro g hg
  rw [lintegral_map hg (argPrefixKingmanHistory_measurable N),
    lintegral_withDensity_eq_lintegral_mul _ (argNoSplitPrefixWeight_measurable R (N - 1))
      (show Measurable (fun p => g (argPrefixKingmanHistory N p)) from
        hg.comp (argPrefixKingmanHistory_measurable N)),
    lintegral_withDensity_eq_lintegral_mul _ hf hg,
    lintegral_map (hf.mul hg) (argPrefixKingmanHistory_measurable N)]
  apply lintegral_congr_ae
  filter_upwards [hp] with p hs
  change argNoSplitPrefixWeight R (N - 1) p * g (argPrefixKingmanHistory N p) =
    f (argPrefixKingmanHistory N p) * g (argPrefixKingmanHistory N p)
  rw [argNoSplitPrefixWeight_kingman N hN R hR p hs]
end Rhone.Coalescent.SmcPrime
