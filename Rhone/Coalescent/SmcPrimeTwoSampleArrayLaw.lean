/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeTwoSampleArray
public import Rhone.Coalescent.SmcPrimeFixedPositionTwoSampleLaw
public import Rhone.Coalescent.SmcPrimeCutLaw
public import Rhone.Coalescent.SmcPrimeProposalSkeleton
public import Rhone.Coalescent.SmcPrimeKingmanRootHeightLength

/-!
# Law of the root height after one SMC′ proposal on a reachable two-sample array

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 1–7. -/

@[expose] public section

namespace Rhone.Coalescent.SmcPrime
open MeasureTheory Set IntervalProcess
open scoped ENNReal

theorem lintegral_branchCutMeasure_twoSample (b : Branch 2)
    (F : Finset (Fin 2) × ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, F x ∂branchCutMeasure b =
      ∑ i : Fin 2, ∫⁻ t, (if b.1 = {i} then
        (Ioo b.2.1 b.2.2).indicator (fun t => F ({i}, t)) t else 0) := by
  classical
  have hm : Measurable (fun t : ℝ => (b.1, t)) := measurable_const.prodMk measurable_id
  by_cases hc : b.1 = ∅ ∨ b.1 = Finset.univ
  · have hne : ∀ i : Fin 2, ¬ b.1 = {i} := by
      intro i hi
      exact twoSample_singleton_proper i (hi ▸ hc)
    simp only [branchCutMeasure, hc, ↓reduceIte, lintegral_zero_measure, hne, lintegral_zero,
      Finset.sum_const_zero]
  · obtain ⟨j, hj⟩ : ∃ j : Fin 2, b.1 = {j} := by
      rcases twoSample_clade_cases b.1 with h | h | h | h
      · exact absurd (Or.inl h) hc
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
      · exact absurd (Or.inr h) hc
    simp only [branchCutMeasure, hc, ↓reduceIte]
    rw [lintegral_map hF hm, Finset.sum_eq_single j]
    · simp only [hj, ↓reduceIte]
      rw [lintegral_indicator measurableSet_Ioo]
    · intro i _ hij
      have hne : ¬ b.1 = {i} := fun hi => hij (Finset.singleton_injective (hi.symm.trans hj))
      simp only [hne, ↓reduceIte, lintegral_zero]
    · intro hj'
      exact absurd (Finset.mem_univ j) hj'

namespace TwoSampleArray

variable {T : Tree 2}

theorem lintegral_treeCutMeasure (hT : TwoSampleArray T)
    (F : Finset (Fin 2) × ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, F x ∂treeCutMeasure T =
      ∑ i : Fin 2, ∫⁻ t in Ioo 0 (rootHeight T), F ({i}, t) := by
  classical
  unfold treeCutMeasure
  rw [lintegral_finsetSum_measure]
  simp only [lintegral_branchCutMeasure_twoSample _ F hF]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hφ : Measurable (fun t : ℝ => F ({i}, t)) :=
    hF.comp (measurable_const.prodMk measurable_id)
  have hterm : ∀ b : Fin T.1, Measurable (fun t : ℝ => if (T.2 b).1 = {i} then
      (Ioo (T.2 b).2.1 (T.2 b).2.2).indicator (fun t => F ({i}, t)) t else 0) := by
    intro b
    by_cases hc : (T.2 b).1 = {i}
    · simp only [hc, ↓reduceIte]
      exact hφ.indicator measurableSet_Ioo
    · simp only [hc, ↓reduceIte]
      exact measurable_const
  rw [← lintegral_finsetSum _ (fun b _ => hterm b), ← lintegral_indicator measurableSet_Ioo]
  apply lintegral_congr_ae
  have hfin : ∀ᵐ t ∂(volume : Measure ℝ), ∀ b : Fin T.1, t ≠ (T.2 b).2.1 := by
    rw [ae_all_iff]
    intro b
    exact compl_mem_ae_iff.mpr (measure_singleton (T.2 b).2.1)
  filter_upwards [hfin] with t ht
  by_cases htin : t ∈ Ioo 0 (rootHeight T)
  · obtain ⟨b, hb, hbi⟩ := hT.exists_active htin.1.le htin.2 i
    have hbm := (mem_activeBranches T t b).mp hb
    rw [indicator_of_mem htin, Finset.sum_eq_single b]
    · simp only [hbi, ↓reduceIte]
      rw [indicator_of_mem
        (show t ∈ Ioo (T.2 b).2.1 (T.2 b).2.2 from
          ⟨lt_of_le_of_ne hbm.2.1 (Ne.symm (ht b)), hbm.2.2⟩)]
    · intro b' _ hne
      by_cases hc : (T.2 b').1 = {i}
      · simp only [hc, ↓reduceIte]
        apply indicator_of_notMem
        intro hmem
        exact hne (hT.activeUnique t htin.1.le b'
          ((mem_activeBranches T t b').mpr
            ⟨twoSample_branch_pos hc (hmem.1.trans hmem.2), hmem.1.le, hmem.2⟩)
          b hb (hc.trans hbi.symm))
      · simp only [hc, ↓reduceIte]
    · intro hb'
      exact absurd (Finset.mem_univ b) hb'
  · rw [indicator_of_notMem htin]
    apply Finset.sum_eq_zero
    intro b _
    by_cases hc : (T.2 b).1 = {i}
    · simp only [hc, ↓reduceIte]
      apply indicator_of_notMem
      intro hmem
      exact htin ⟨lt_of_le_of_lt (hT.nonnegative b) hmem.1,
        hmem.2.trans_le (branch_hi_le_root T b
          (twoSample_branch_pos hc (hmem.1.trans hmem.2)))⟩
    · simp only [hc, ↓reduceIte]

theorem treeLength_eq (hT : TwoSampleArray T) (hh : 0 < rootHeight T) :
    treeLength T = 2 * rootHeight T := by
  have hL := treeLength_pos_of_rootHeight_pos T hh
  have hmass := congrArg (fun μ => μ Set.univ) (cutPoint_uniform_law T hL)
  simp only [Measure.smul_apply, smul_eq_mul] at hmass
  have hcut : treeCutMeasure T Set.univ =
      ENNReal.ofReal (rootHeight T) + ENNReal.ofReal (rootHeight T) := by
    rw [← lintegral_one, hT.lintegral_treeCutMeasure _ measurable_const]
    simp only [lintegral_const, MeasurableSet.univ, Measure.restrict_apply, univ_inter,
      Real.volume_Ioo, sub_zero, one_mul, Fin.sum_univ_two]
  rw [Measure.map_apply (cutValue_measurable T) MeasurableSet.univ, preimage_univ,
    measure_univ, hcut] at hmass
  rw [← ENNReal.ofReal_add hh.le hh.le, ← ENNReal.ofReal_mul (inv_pos.mpr hL).le] at hmass
  have h1 := (ENNReal.ofReal_eq_one.mp hmass.symm)
  field_simp at h1
  linarith

end TwoSampleArray

theorem lintegral_attachmentUniformLaw {N : ℕ} (T : Tree N) (hT : TreeTemporalCover T)
    (t : ℝ) (ht : 0 ≤ t) (ψ : ℝ × Finset (Fin N) → ℝ≥0∞) (hψ : Measurable ψ) :
    ∫⁻ p, ψ p ∂attachmentUniformLaw T t =
      ∑ c : Finset (Fin N), ∫⁻ a in Ici t, ENNReal.ofReal
        (Real.exp (-attachmentHazard T t a) * attachmentTargetRate T a c) * ψ (a, c) := by
  classical
  have hS : ∀ c : Finset (Fin N), MeasurableSet {p : ℝ × Finset (Fin N) | p.2 = c} :=
    fun c => (measurableSet_singleton c).preimage measurable_snd
  have hpt : ∀ p : ℝ × Finset (Fin N), ψ p = ∑ c : Finset (Fin N),
      ({p : ℝ × Finset (Fin N) | p.2 = c}).indicator (fun p => ψ (p.1, c)) p := by
    intro p
    rw [Finset.sum_eq_single p.2]
    · rw [indicator_of_mem (show p ∈ {q : ℝ × Finset (Fin N) | q.2 = p.2} from rfl)]
    · intro c _ hc
      exact indicator_of_notMem (s := {q : ℝ × Finset (Fin N) | q.2 = c})
        (fun h => hc (Eq.symm h)) _
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hd : ∀ c : Finset (Fin N), Measurable (fun s => ENNReal.ofReal
      (Real.exp (-attachmentHazard T t s) * attachmentTargetRate T s c)) := fun c =>
    (((Real.continuous_exp.comp (continuous_attachmentHazard T t).neg).measurable).mul
      (measurable_attachmentTargetRate T c)).ennreal_ofReal
  have hψc : ∀ c : Finset (Fin N), Measurable (fun a : ℝ => ψ (a, c)) := fun c =>
    hψ.comp (measurable_id.prodMk measurable_const)
  have hmeas : ∀ c : Finset (Fin N),
      ((attachmentUniformLaw T t).restrict {p | p.2 = c}).map Prod.fst =
        (volume.restrict (Ici t)).withDensity (fun s => ENNReal.ofReal
          (Real.exp (-attachmentHazard T t s) * attachmentTargetRate T s c)) := by
    intro c
    ext A hA
    rw [Measure.map_apply measurable_fst hA, Measure.restrict_apply (hA.preimage measurable_fst),
      withDensity_apply _ hA, Measure.restrict_restrict hA]
    exact attachment_target_joint_density T hT t ht A hA c
  rw [lintegral_congr hpt, lintegral_finsetSum _
    (fun c _ => (show Measurable (fun p : ℝ × Finset (Fin N) => ψ (p.1, c)) from
      (hψc c).comp measurable_fst).indicator (hS c))]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [lintegral_indicator (hS c)]
  have hmap := lintegral_map (μ := (attachmentUniformLaw T t).restrict {p | p.2 = c})
    (hψc c) measurable_fst
  rw [hmeas c, lintegral_withDensity_eq_lintegral_mul _ (hd c) (hψc c)] at hmap
  exact hmap.symm

theorem twoSample_sum_clades {M : Type*} [AddCommMonoid M] (Φ : Finset (Fin 2) → M) :
    ∑ c, Φ c = Φ ∅ + (Φ {0} + (Φ {1} + Φ Finset.univ)) := by
  have huniv : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, Finset.univ} := by
    decide
  rw [huniv, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]

noncomputable def twoSampleAttachmentWeight (h : ℝ) (g : ℝ → ℝ≥0∞) (t a : ℝ) : ℝ≥0∞ :=
  if a < h then
    (if t < a then ENNReal.ofReal (Real.exp (-(2 * (a - t)))) * (g h + g a) else 0)
  else ENNReal.ofReal (Real.exp (-(2 * (h - t) + (a - h)))) * g a

theorem measurable_twoSampleAttachmentWeight (h : ℝ) (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    Measurable (fun q : ℝ × ℝ => twoSampleAttachmentWeight h g q.1 q.2) := by
  unfold twoSampleAttachmentWeight
  refine Measurable.ite (measurableSet_lt measurable_snd measurable_const)
    (Measurable.ite (measurableSet_lt measurable_fst measurable_snd) ?_ measurable_const) ?_
  · exact (by fun_prop : Measurable fun q : ℝ × ℝ =>
      ENNReal.ofReal (Real.exp (-(2 * (q.2 - q.1))))).mul
        (measurable_const.add (hg.comp measurable_snd))
  · exact (by fun_prop : Measurable fun q : ℝ × ℝ =>
      ENNReal.ofReal (Real.exp (-(2 * (h - q.1) + (q.2 - h))))).mul (hg.comp measurable_snd)

theorem TwoSampleArray.lintegral_attachment_rootHeight {T : Tree 2} (hT : TwoSampleArray T)
    (g : ℝ → ℝ≥0∞) (hg : Measurable g) {t : ℝ} (ht : 0 ≤ t) (hth : t < rootHeight T)
    (i : Fin 2) :
    ∫⁻ q : ℝ × ℝ, g (rootHeight (regraft T {i}
        (attachmentTarget T (attachmentTime T t (-Real.log q.1)) q.2) t
        (attachmentTime T t (-Real.log q.1)))) ∂(unitUniform.prod unitUniform) =
      ∫⁻ a, twoSampleAttachmentWeight (rootHeight T) g t a := by
  classical
  have hcover := tree_chronology_temporal_cover T (by norm_num) hT.chronology
  let ψ : ℝ × Finset (Fin 2) → ℝ≥0∞ := fun p => g (rootHeight (regraft T {i} p.2 t p.1))
  have hψ : Measurable ψ := hg.comp ((rootHeight_measurable 2).comp
    ((regraft_joint_measurable 2).comp (measurable_const.prodMk (measurable_const.prodMk
      (measurable_snd.prodMk (measurable_const.prodMk measurable_fst))))))
  have h1 : ∫⁻ q : ℝ × ℝ, g (rootHeight (regraft T {i}
        (attachmentTarget T (attachmentTime T t (-Real.log q.1)) q.2) t
        (attachmentTime T t (-Real.log q.1)))) ∂(unitUniform.prod unitUniform) =
      ∫⁻ p, ψ p ∂attachmentUniformLaw T t := by
    unfold attachmentUniformLaw
    rw [lintegral_map hψ (measurable_attachmentUniformMap T t)]
  have hterm : ∀ c : Finset (Fin 2), Measurable (fun a : ℝ => ENNReal.ofReal
      (Real.exp (-attachmentHazard T t a) * attachmentTargetRate T a c) * ψ (a, c)) :=
    fun c => ((((Real.continuous_exp.comp (continuous_attachmentHazard T t).neg).measurable).mul
      (measurable_attachmentTargetRate T c)).ennreal_ofReal).mul
        (hψ.comp (measurable_id.prodMk measurable_const))
  rw [h1, lintegral_attachmentUniformLaw T hcover t ht ψ hψ,
    ← lintegral_finsetSum _ (fun c _ => hterm c), ← setLIntegral_congr Ioi_ae_eq_Ici,
    ← lintegral_indicator measurableSet_Ioi]
  refine lintegral_congr fun a => ?_
  have hi : i = 0 ∨ i = 1 := 
    (Fin.forall_fin_two (p := fun i => i = 0 ∨ i = 1)).mpr ⟨Or.inl rfl, Or.inr rfl⟩ i
  by_cases hta : t < a
  · rw [indicator_of_mem (mem_Ioi.mpr hta), twoSample_sum_clades]
    by_cases hah : a < rootHeight T
    · have hhaz := hT.attachmentHazard_below ht hta.le hah.le
      simp only [twoSampleAttachmentWeight, hah, hta, ↓reduceIte, hhaz,
        attachmentTargetRate_below_improper hah (Or.inl rfl),
        attachmentTargetRate_below_improper hah (Or.inr rfl),
        hT.attachmentTargetRate_below (ht.trans hta.le) hah, mul_zero, mul_one,
        ENNReal.ofReal_zero, zero_mul, zero_add, add_zero, ψ]
      rcases hi with rfl | rfl
      · rw [twoSample_regraft_self_rootHeight T hT.normalized ht hta.le hah 0,
          twoSample_regraft_other_rootHeight T ht hta (by decide : (0 : Fin 2) ≠ 1), mul_add]
      · rw [twoSample_regraft_self_rootHeight T hT.normalized ht hta.le hah 1,
          twoSample_regraft_other_rootHeight T ht hta (by decide : (1 : Fin 2) ≠ 0), mul_add,
          add_comm]
    · have hah' : rootHeight T ≤ a := not_lt.mp hah
      have hhaz := hT.attachmentHazard_above ht hth.le hah'
      have he : ¬ ((∅ : Finset (Fin 2)) = Finset.univ) := by decide
      have h0 : ¬ (({0} : Finset (Fin 2)) = Finset.univ) := by decide
      have h1' : ¬ (({1} : Finset (Fin 2)) = Finset.univ) := by decide
      simp only [twoSampleAttachmentWeight, hah, ↓reduceIte, hhaz,
        attachmentTargetRate_above hah', he, h0, h1', mul_zero, mul_one,
        ENNReal.ofReal_zero, zero_mul, zero_add, ψ]
      rw [twoSample_regraft_above_rootHeight T hT.normalized hth.le hta hah' i Finset.univ]
  · rw [indicator_of_notMem (fun hc => hta (mem_Ioi.mp hc))]
    have hah : a < rootHeight T := (not_lt.mp hta).trans_lt hth
    simp only [twoSampleAttachmentWeight, hah, hta, ↓reduceIte]

noncomputable def proposalMarks (p q : ℝ × ℝ) : ProposalNoise := ![2⁻¹, p.1, p.2, q.1, q.2]

theorem measurable_proposalMarks :
    Measurable (fun pq : (ℝ × ℝ) × (ℝ × ℝ) => proposalMarks pq.1 pq.2) := by
  refine Measurable.of_eval fun k => ?_
  fin_cases k
  · exact measurable_const
  · exact measurable_fst.comp measurable_fst
  · exact measurable_snd.comp measurable_fst
  · exact measurable_fst.comp measurable_snd
  · exact measurable_snd.comp measurable_snd

theorem proposal_tree_proposalMarks {N : ℕ} (R : ℝ) (T : Tree N) (u : ProposalNoise) :
    (proposal R T (proposalMarks (u 1, u 2) (u 3, u 4))).2.2 = (proposal R T u).2.2 := by
  have h1 : proposalMarks (u 1, u 2) (u 3, u 4) 1 = u 1 := rfl
  have h2 : proposalMarks (u 1, u 2) (u 3, u 4) 2 = u 2 := rfl
  have h3 : proposalMarks (u 1, u 2) (u 3, u 4) 3 = u 3 := rfl
  have h4 : proposalMarks (u 1, u 2) (u 3, u 4) 4 = u 4 := rfl
  unfold proposal
  simp only [h1, h2, h3, h4]
  cases cutPoint T (u 1) (u 2) <;> rfl

theorem proposal_tree_proposalMarks_of_cut {N : ℕ} (R : ℝ) (T : Tree N) (p q : ℝ × ℝ)
    {s : Finset (Fin N)} {t : ℝ} (hcut : cutPoint T p.1 p.2 = some (s, t)) :
    (proposal R T (proposalMarks p q)).2.2 = regraft T s
      (attachmentTarget T (attachmentTime T t (-Real.log q.1)) q.2) t
      (attachmentTime T t (-Real.log q.1)) := by
  have h1 : proposalMarks p q 1 = p.1 := rfl
  have h2 : proposalMarks p q 2 = p.2 := rfl
  have h3 : proposalMarks p q 3 = q.1 := rfl
  have h4 : proposalMarks p q 4 = q.2 := rfl
  simp only [proposal, h1, h2, h3, h4, hcut]

namespace TwoSampleArray

variable {T : Tree 2}

theorem proposal_rootHeight_lintegral_weight (hT : TwoSampleArray T) (R : ℝ)
    (hh : 0 < rootHeight T) (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ u, g (rootHeight (SmcPrime.proposal R T u).2.2) ∂proposalNoiseLaw =
      ENNReal.ofReal ((2 * rootHeight T)⁻¹) * ∑ _i : Fin 2,
        ∫⁻ t in Ioo 0 (rootHeight T), ∫⁻ a, twoSampleAttachmentWeight (rootHeight T) g t a := by
  classical
  have hL := treeLength_pos_of_rootHeight_pos T hh
  let G : (ℝ × ℝ) × (ℝ × ℝ) → ℝ≥0∞ := fun pq =>
    g (rootHeight (SmcPrime.proposal R T (proposalMarks pq.1 pq.2)).2.2)
  have hG : Measurable G := hg.comp ((rootHeight_measurable 2).comp
    ((measurable_snd.comp measurable_snd).comp ((proposal_measurable 2 R).comp
      (measurable_const.prodMk measurable_proposalMarks))))
  have hmarks : proposalNoiseLaw.map (fun u => ((u 1, u 2), (u 3, u 4))) =
      (unitUniform.prod unitUniform).prod (unitUniform.prod unitUniform) := by
    have hgr := proposalNoiseLaw_grouped
    have hcomp : (fun u : ProposalNoise => ((u 1, u 2), (u 3, u 4))) =
        Prod.snd ∘ fun u : ProposalNoise => (u 0, ((u 1, u 2), (u 3, u 4))) := rfl
    rw [hcomp, ← Measure.map_map measurable_snd (by fun_prop), hgr, Measure.map_snd_prod]
    simp
  have hfun : (fun u : ProposalNoise => g (rootHeight (SmcPrime.proposal R T u).2.2)) =
      fun u => G ((u 1, u 2), (u 3, u 4)) := by
    funext u
    simp only [G, proposal_tree_proposalMarks]
  rw [hfun, ← lintegral_map hG (by fun_prop), hmarks, lintegral_prod _ hG.aemeasurable]
  let W : Finset (Fin 2) × ℝ → ℝ≥0∞ := fun x =>
    ∫⁻ a, twoSampleAttachmentWeight (rootHeight T) g x.2 a
  have hW : Measurable W :=
    (Measurable.lintegral_prod_right'
      (measurable_twoSampleAttachmentWeight (rootHeight T) g hg)).comp measurable_snd
  have hlaw := cutPoint_uniform_law T hL
  have hnull : ∀ᵐ p ∂unitUniform.prod unitUniform, (cutValue T p).2 ≠ rootHeight T := by
    have hS : MeasurableSet {x : Finset (Fin 2) × ℝ | x.2 = rootHeight T} :=
      (measurableSet_singleton _).preimage measurable_snd
    have h0 : ((unitUniform.prod unitUniform).map (cutValue T))
        {x | x.2 = rootHeight T} = 0 := by
      rw [hlaw, Measure.smul_apply, ← lintegral_indicator_one hS,
        hT.lintegral_treeCutMeasure _ (measurable_one.indicator hS), smul_eq_mul,
        mul_eq_zero]
      right
      refine Finset.sum_eq_zero fun i _ => ?_
      have hz : ∀ t ∈ Ioo 0 (rootHeight T),
          ({x : Finset (Fin 2) × ℝ | x.2 = rootHeight T}).indicator
            (1 : Finset (Fin 2) × ℝ → ℝ≥0∞)
            (({i} : Finset (Fin 2)), t) = (fun _ => 0) t :=
        fun t ht => indicator_of_notMem
          (s := {x : Finset (Fin 2) × ℝ | x.2 = rootHeight T})
          (fun hc => ht.2.ne hc) _
      rw [setLIntegral_congr_fun measurableSet_Ioo hz, lintegral_zero]
    rw [Measure.map_apply (cutValue_measurable T) hS] at h0
    exact measure_eq_zero_iff_ae_notMem.mp h0
  have hunit : ∀ᵐ p ∂unitUniform.prod unitUniform,
      p.1 ∈ Ioo (0 : ℝ) 1 ∧ p.2 ∈ Ioo (0 : ℝ) 1 := by
    have h2 : ∀ᵐ v ∂unitUniform, v ∈ Ioo (0 : ℝ) 1 := ae_restrict_mem measurableSet_Ioo
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := unitUniform)
      (ν := unitUniform)).ae h2, (Measure.quasiMeasurePreserving_snd (μ := unitUniform)
      (ν := unitUniform)).ae h2] with p hp1 hp2
    exact ⟨hp1, hp2⟩
  have hinner : ∀ᵐ p ∂unitUniform.prod unitUniform,
      ∫⁻ q, G (p, q) ∂unitUniform.prod unitUniform = W (cutValue T p) := by
    filter_upwards [hnull, hunit] with p hp hpu
    obtain ⟨hp1, hp2⟩ := hpu
    obtain ⟨s, t, hcut, -, -, -⟩ := cut_point_extant_clade T hL p.1 p.2
      ⟨hp1.1.le, hp1.2⟩ ⟨hp2.1.le, hp2.2⟩
    obtain ⟨b, hbs, hblo, -, hbpos, hth⟩ := cut_point_bounds T p.1 p.2 hp1.1.le
      ⟨hp2.1.le, hp2.2.le⟩ s t hcut
    have hcv : cutValue T p = (s, t) := by
      simp only [cutValue, hcut, Option.getD_some]
    rw [hcv] at hp ⊢
    have ht0 : 0 ≤ t := (hT.nonnegative b).trans hblo
    have htlt : t < rootHeight T := lt_of_le_of_ne hth hp
    obtain ⟨i, rfl⟩ : ∃ i : Fin 2, s = {i} := by
      rcases (twoSample_branch_of_pos hbpos).1 with h | h
      · exact ⟨0, hbs.symm.trans h⟩
      · exact ⟨1, hbs.symm.trans h⟩
    change _ = ∫⁻ a, twoSampleAttachmentWeight (rootHeight T) g t a
    rw [← hT.lintegral_attachment_rootHeight g hg ht0 htlt i]
    refine lintegral_congr fun q => ?_
    simp only [G, proposal_tree_proposalMarks_of_cut R T p q hcut]
  rw [lintegral_congr_ae hinner, ← lintegral_map hW (cutValue_measurable T), hlaw,
    lintegral_smul_measure, hT.lintegral_treeCutMeasure W hW, hT.treeLength_eq hh]
  rfl

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 3–7. -/
theorem proposal_rootHeight_lintegral (hT : TwoSampleArray T) (R : ℝ)
    (hh : 0 < rootHeight T) (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ u, g (rootHeight (SmcPrime.proposal R T u).2.2) ∂proposalNoiseLaw =
      ENNReal.ofReal (twoSampleSelfMass (rootHeight T)) * g (rootHeight T) +
        ∫⁻ a in Ioi 0, ENNReal.ofReal (twoSampleJumpDensity (rootHeight T) a) * g a := by
  have hr := twoSampleTree_rootHeight hh
  have htree := (twoSampleTree_twoSampleArray hh).proposal_rootHeight_lintegral_weight R
    (by rw [hr]; exact hh) g hg
  rw [hr] at htree
  rw [hT.proposal_rootHeight_lintegral_weight R hh g hg, ← htree,
    twoSampleTree_proposal_rootHeight_lintegral R hh g hg]

end TwoSampleArray

end Rhone.Coalescent.SmcPrime
