/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeProposalSkeleton
public import Rhone.Coalescent.SmcPrimeProposalLengthMean

/-!
# Accepted-proposal densities and the stopping density of the one-split proposal source

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 1–7. -/

@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open MeasureTheory ProbabilityTheory IntervalProcess
open scoped ENNReal

theorem oneSplitReferenceSourceMap_density (N : ℕ) (h : KingmanHistory N)
    (b : OneSplitSkeleton N → ℝ≥0∞) (hb : Measurable b) :
    (((unitUniform.prod unitUniform).prod
      (unitUniform.prod (unitUniform.prod unitUniform))).withDensity
        (b ∘ oneSplitReferenceSourceMap N h)).map (oneSplitReferenceSourceMap N h) =
      (((unitUniform.prod unitUniform).prod
        (unitUniform.prod (unitUniform.prod unitUniform))).map
          (oneSplitReferenceSourceMap N h)).withDensity b := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (oneSplitReferenceSourceMap_measurable N h),
    lintegral_withDensity_eq_lintegral_mul _
      (hb.comp (oneSplitReferenceSourceMap_measurable N h))
      (show Measurable (fun p => f (oneSplitReferenceSourceMap N h p)) from
        hf.comp (oneSplitReferenceSourceMap_measurable N h)),
    lintegral_withDensity_eq_lintegral_mul _ hb hf,
    lintegral_map (hb.mul hf) (oneSplitReferenceSourceMap_measurable N h)]
  rfl

theorem groupedClock_accepted_density (q : ℝ) (hq : 0 < q) :
    ((unitUniform.prod unitUniform).prod
      ((unitUniform.map (fun u => -Real.log u / q)).prod
        (unitUniform.prod unitUniform))).restrict {p | p.2.1 < 1} =
    ((unitUniform.prod unitUniform).prod
      (unitUniform.prod (unitUniform.prod unitUniform))).withDensity
        (fun p => ENNReal.ofReal (q * Real.exp (-q * p.2.1))) := by
  have hs : {p : (ℝ × ℝ) × (ℝ × (ℝ × ℝ)) | p.2.1 < 1} =
      Set.univ ×ˢ (Set.Iio 1 ×ˢ Set.univ) := by ext p; simp
  rw [hs, ← Measure.prod_restrict, Measure.restrict_univ,
    ← Measure.prod_restrict, Measure.restrict_univ, spatialClock_accepted_density q hq]
  have hf : Measurable (fun x : ℝ => ENNReal.ofReal (q * Real.exp (-q * x))) :=
    by fun_prop
  rw [prod_withDensity_left hf, prod_withDensity_right
    (show Measurable (fun z : ℝ × (ℝ × ℝ) =>
      ENNReal.ofReal (q * Real.exp (-q * z.1))) from hf.comp measurable_fst)]

theorem indexedProposal_accepted_density (N : ℕ) (R : ℝ)
    (h : KingmanHistory N) (hR : 0 < R)
    (hL : 0 < treeLength (metricTreeFromHistory N h)) :
    (proposalNoiseLaw.restrict
      {u | (proposal R (metricTreeFromHistory N h) u).1 < 1}).map
        (indexedProposal N R h) =
      (oneSplitReferenceFiber N h).withDensity
        (fun s => ENNReal.ofReal (R / 2 * Real.exp
          (-(R / 2 * treeLength (metricTreeFromHistory N h)) * s.2.2.2.1))) := by
  let q := R / 2 * treeLength (metricTreeFromHistory N h)
  let G (u : ProposalNoise) := ((u 1, u 2), (-Real.log (u 0) / q, (u 3, u 4)))
  let F := oneSplitReferenceSourceMap N h
  have hG : Measurable G := by fun_prop
  have hF : Measurable F := oneSplitReferenceSourceMap_measurable N h
  have hq : 0 < q := mul_pos (by linarith) hL
  have he : indexedProposal N R h = F ∘ G := by
    funext u
    exact indexedProposal_source N R h u
  have hs : {u | (proposal R (metricTreeFromHistory N h) u).1 < 1} =
      G ⁻¹' {p | p.2.1 < 1} := by
    ext u
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, G, q, proposal_fst_eq]
  rw [he, hs, ← Measure.map_map hF hG, ← Measure.restrict_map hG
    (measurableSet_lt measurable_snd.fst measurable_const)]
  change (((proposalNoiseLaw.map G).restrict {p | p.2.1 < 1}).map F) = _
  rw [proposalNoiseLaw_cut_distance_attachment q, groupedClock_accepted_density q hq]
  let b (s : OneSplitSkeleton N) := ENNReal.ofReal (q * Real.exp (-q * s.2.2.2.1))
  have hb : Measurable b := by fun_prop
  change (((unitUniform.prod unitUniform).prod
    (unitUniform.prod (unitUniform.prod unitUniform))).withDensity (b ∘ F)).map F = _
  rw [oneSplitReferenceSourceMap_density N h b hb, oneSplitReferenceFiber_source,
    withDensity_smul_measure]
  have hf : Measurable (fun s : OneSplitSkeleton N => ENNReal.ofReal
      (R / 2 * Real.exp (-q * s.2.2.2.1))) := by fun_prop
  rw [← withDensity_smul _ hf]
  congr 1
  funext s
  simp only [b, Pi.smul_apply, smul_eq_mul, ← ENNReal.ofReal_mul hL.le]
  congr 1
  dsimp [q]
  ring
end Rhone.Coalescent.SmcPrime

@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open MeasureTheory ProbabilityTheory IntervalProcess

theorem indexedProposal_postTree (N : ℕ) (R : ℝ)
    (h : KingmanHistory N) (u : ProposalNoise)
    (hc : ∃ s t, cutPoint (metricTreeFromHistory N h) (u 1) (u 2) = some (s, t)) :
    oneSplitPostTree (indexedProposal N R h u) =
      (proposal R (metricTreeFromHistory N h) u).2.2 := by
  obtain ⟨s, t, hc⟩ := hc
  let T := metricTreeFromHistory N h
  have hb : forgetCutIndex T (indexedCutValue T (u 1, u 2)) = (s, t) := by
    rw [forgetCutIndex_indexedCutValue]
    simp [cutValue, T, hc]
  have ht : (indexedCutValue T (u 1, u 2)).2 = t := by
    have he : (indexedCutValue T (u 1, u 2)).2 = (cutValue T (u 1, u 2)).2 := by
      unfold indexedCutValue cutValue cutPoint
      cases chooseByRate
        (fun i => branchLength (T.2 i)) (List.finRange T.1) (u 1 * treeLength T) <;> rfl
    rw [he]
    simp [cutValue, T, hc]
  simp only [oneSplitPostTree, indexedProposal, proposal, hc]
  change regraft T (forgetCutIndex T (indexedCutValue T (u 1, u 2))).1
    (attachmentTarget T (attachmentTime T (indexedCutValue T (u 1, u 2)).2
      (-Real.log (u 3))) (u 4)) (indexedCutValue T (u 1, u 2)).2
    (attachmentTime T (indexedCutValue T (u 1, u 2)).2 (-Real.log (u 3))) = _
  rw [hb, ht]

theorem indexedProposal_postTree_ae (N : ℕ) (R : ℝ)
    (h : KingmanHistory N) (hL : 0 < treeLength (metricTreeFromHistory N h)) :
    ∀ᵐ u ∂proposalNoiseLaw,
      oneSplitPostTree (indexedProposal N R h u) =
        (proposal R (metricTreeFromHistory N h) u).2.2 := by
  filter_upwards [proposalNoiseLaw_ae_marks] with u hu
  obtain ⟨s, t, hc, _⟩ := cut_point_extant_clade (metricTreeFromHistory N h) hL
    (u 1) (u 2) ⟨(hu 1).1.le, (hu 1).2⟩ ⟨(hu 2).1.le, (hu 2).2⟩
  exact indexedProposal_postTree N R h u ⟨s, t, hc⟩

theorem spatialStep_initial_accepted {N : ℕ} (R : ℝ) (T : Tree N)
    (hR : 0 < R) (hL : 0 < treeLength T) (u : ProposalNoise) :
    (spatialStep N R (0, T) u).1 < 1 ↔ (proposal R T u).1 < 1 := by
  simp only [spatialStep, not_le.mpr hR, not_le.mpr hL, false_or,
    show ¬ (1 : ℝ) ≤ 0 by norm_num, zero_add, ite_false]
  split_ifs with hx
  · exact iff_of_true hx hx
  · simp [hx]
end Rhone.Coalescent.SmcPrime

@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open MeasureTheory ProbabilityTheory IntervalProcess
open scoped ENNReal

noncomputable def oneProposalSkeletonFiber (N : ℕ) (R : ℝ) (h : KingmanHistory N) :
    Measure (OneSplitSkeleton N) :=
  ((proposalNoiseLaw.prod proposalNoiseLaw).restrict
    {p | let z := spatialStep N R (0, metricTreeFromHistory N h) p.1
         z.1 < 1 ∧ (spatialStep N R z p.2).1 = 1}).map
    (fun p => indexedProposal N R h p.1)

noncomputable def oneSplitStopDensity (N : ℕ) (R : ℝ) (s : OneSplitSkeleton N) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(R / 2 * treeLength (oneSplitPostTree s) * (1 - s.2.2.2.1))))

theorem oneSplitStopDensity_measurable (N : ℕ) (R : ℝ) :
    Measurable (oneSplitStopDensity N R) :=
  (Real.measurable_exp.comp
    ((measurable_const.mul ((treeLength_joint_measurable N).comp
      (oneSplitPostTree_measurable N))).mul
        (measurable_const.sub measurable_snd.snd.snd.fst)).neg).ennreal_ofReal

theorem oneProposalSkeletonFiber_stop_factor (N : ℕ) (R : ℝ)
    (h : KingmanHistory N) (hR : 0 < R)
    (hL : 0 < treeLength (metricTreeFromHistory N h)) :
    oneProposalSkeletonFiber N R h =
      ((proposalNoiseLaw.restrict
        {u | (proposal R (metricTreeFromHistory N h) u).1 < 1}).map
          (indexedProposal N R h)).withDensity (oneSplitStopDensity N R) := by
  let T := metricTreeFromHistory N h
  let F := indexedProposal N R h
  let Z (u : ProposalNoise) := spatialStep N R (0, T) u
  have hF : Measurable F := (indexedProposal_measurable N R).comp
    (measurable_const.prodMk measurable_id)
  have hZ : Measurable Z := (spatialStep_measurable N R).comp
    (measurable_const.prodMk measurable_id)
  have hp : Measurable (fun u : ProposalNoise => proposal R T u) :=
    (proposal_measurable N R).comp (measurable_const.prodMk measurable_id)
  have ha : MeasurableSet {u : ProposalNoise | (proposal R T u).1 < 1} :=
    measurableSet_lt hp.fst measurable_const
  have hg : Measurable (fun p : ProposalNoise × ProposalNoise =>
      spatialStep N R (Z p.1) p.2) :=
    (spatialStep_measurable N R).comp ((hZ.comp measurable_fst).prodMk measurable_snd)
  have hevent : MeasurableSet {p : ProposalNoise × ProposalNoise |
      (Z p.1).1 < 1 ∧ (spatialStep N R (Z p.1) p.2).1 = 1} :=
    (measurableSet_lt (hZ.fst.comp measurable_fst) measurable_const).inter
      (measurableSet_eq_fun hg.fst measurable_const)
  ext s hs
  unfold oneProposalSkeletonFiber
  change (((proposalNoiseLaw.prod proposalNoiseLaw).restrict
    {p | (Z p.1).1 < 1 ∧ (spatialStep N R (Z p.1) p.2).1 = 1}).map
      (fun p => F p.1)) s =
    ((proposalNoiseLaw.restrict {u | (proposal R T u).1 < 1}).map F).withDensity
      (oneSplitStopDensity N R) s
  have hFp : Measurable (fun p : ProposalNoise × ProposalNoise => F p.1) :=
    hF.comp measurable_fst
  rw [Measure.map_apply hFp hs,
    Measure.restrict_apply (hs.preimage hFp),
    Measure.prod_apply ((hs.preimage hFp).inter hevent),
    withDensity_apply _ hs, ← lintegral_indicator hs,
    lintegral_map ((oneSplitStopDensity_measurable N R).indicator hs) hF,
    ← lintegral_indicator ha]
  apply lintegral_congr_ae
  filter_upwards [indexedProposal_postTree_ae N R h hL] with u hu
  change proposalNoiseLaw {v | F u ∈ s ∧ (Z u).1 < 1 ∧
    (spatialStep N R (Z u) v).1 = 1} =
      {u : ProposalNoise | (proposal R T u).1 < 1}.indicator
        (fun u => s.indicator (oneSplitStopDensity N R) (F u)) u
  by_cases hx : (proposal R T u).1 < 1
  · have hz : Z u = ((proposal R T u).1, (proposal R T u).2.2) := by
      simp only [Z, spatialStep, show ¬ (1 : ℝ) ≤ 0 by norm_num,
        not_le.mpr hR, not_le.mpr (show 0 < treeLength T from hL), false_or,
        ite_false, zero_add, ite_eq_left hx]
    have hzx : (Z u).1 < 1 := by rw [hz]; exact hx
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, hx, hzx, ite_true, true_and]
    by_cases hm : F u ∈ s
    · simp only [hm, true_and]
      have hind : s.indicator (oneSplitStopDensity N R) (F u) =
          oneSplitStopDensity N R (F u) := Set.indicator_of_mem hm _
      rw [hind]
      have he := spatial_kernel_stop_mass R hR.le (Z u) hzx.le
      rw [spatialKernel_apply, Measure.map_apply
        (show Measurable (fun v : ProposalNoise => spatialStep N R (Z u) v) from
          (spatialStep_measurable N R).comp (measurable_const.prodMk measurable_id))
        (show MeasurableSet {y : SpatialState N | y.1 = 1} from
          measurableSet_eq_fun measurable_fst measurable_const)] at he
      rw [show proposalNoiseLaw {v | (spatialStep N R (Z u) v).1 = 1} =
        ENNReal.ofReal (Real.exp (-(R / 2 * treeLength (Z u).2 * (1 - (Z u).1)))) from
          by simpa only [Set.preimage_ofPred_eq] using he]
      change ENNReal.ofReal (Real.exp (-(R / 2 * treeLength (Z u).2 * (1 - (Z u).1)))) =
        ENNReal.ofReal (Real.exp (-(R / 2 * treeLength (oneSplitPostTree (F u)) *
          (1 - (F u).2.2.2.1))))
      rw [hz, show oneSplitPostTree (F u) = (proposal R T u).2.2 from hu]
      rfl
    · simp [hm]
  · have hzx : ¬ (Z u).1 < 1 := by
      simpa only [Z] using (spatialStep_initial_accepted R T hR hL u).not.mpr hx
    simp [hx, hzx]
end Rhone.Coalescent.SmcPrime
