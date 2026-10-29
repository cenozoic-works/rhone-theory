/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.FullARGTwoSamplePath

/-!
# The time to the most recent common ancestor at a probe, on sampler paths

Source: hudson1983, sec. 5.2, pp. 199–200; griffiths1991_two_locus_graph, p. 103. -/

@[expose] public section

namespace Rhone.Coalescent.IntervalProcess
open SmcSupport MeasureTheory ProbabilityTheory
open scoped ENNReal

def labelMergeTransition (q : GenomicProbe) (p : AugmentedState × AugmentedState) : Prop :=
  ∀ a b c d : ℕ, Valid p.1.1 → ancestorCarried p.1.1 (q.val : ℝ) a →
    ancestorCarried p.1.1 (q.val : ℝ) b → ancestorCarried p.1.1 (q.val : ℝ) c →
    ancestorCarried p.1.1 (q.val : ℝ) d → a ≠ b → c ≠ d →
    ancestorStep p.1.1 p.2.2.2 q a = ancestorStep p.1.1 p.2.2.2 q b →
    ancestorStep p.1.1 p.2.2.2 q c = ancestorStep p.1.1 p.2.2.2 q d →
    (a = c ∧ b = d) ∨ (a = d ∧ b = c)

theorem labelMergeTransition_measurable (q : GenomicProbe) :
    MeasurableSet {p : AugmentedState × AugmentedState | labelMergeTransition q p} := by
  have hv : Measurable fun p : AugmentedState × AugmentedState => Valid p.1.1 :=
    measurableSet_setOfPred.1 (validState_measurable.preimage measurable_fst.fst)
  have hc : ∀ a : ℕ, Measurable fun p : AugmentedState × AugmentedState =>
      ancestorCarried p.1.1 (q.val : ℝ) a := fun a =>
    measurableSet_setOfPred.1 ((ancestorCarried_fixed_measurable _ a).preimage measurable_fst.fst)
  have hst : ∀ a b : ℕ, Measurable fun p : AugmentedState × AugmentedState =>
      ancestorStep p.1.1 p.2.2.2 q a = ancestorStep p.1.1 p.2.2.2 q b := fun a b =>
    measurableSet_setOfPred.1 (measurableSet_eq_fun
      ((ancestorStep_measurable q).comp
        (measurable_fst.fst.prodMk (measurable_snd.snd.snd.prodMk measurable_const)))
      ((ancestorStep_measurable q).comp
        (measurable_fst.fst.prodMk (measurable_snd.snd.snd.prodMk measurable_const))))
  refine measurableSet_setOfPred.2 ?_
  unfold labelMergeTransition
  refine Measurable.forall fun a => Measurable.forall fun b => Measurable.forall fun c =>
    Measurable.forall fun d => ?_
  exact hv.imp ((hc a).imp ((hc b).imp ((hc c).imp ((hc d).imp (measurable_const.imp
    (measurable_const.imp ((hst a b).imp ((hst c d).imp measurable_const))))))))

theorem sampleStep_labelMergeTransition (R : ℝ) (z : AugmentedState) (u : Noise)
    (hu : ∀ i, 0 < u i ∧ u i < 1) (q : GenomicProbe) :
    labelMergeTransition q (z, sampleStep false R z.1 u) := by
  classical
  by_cases hm : 2 ≤ z.1.2.2.1
  swap
  · have hstep : sampleStep false R z.1 u = (z.1, (z.1.1, .inl ())) := by
      unfold sampleStep
      rw [ite_eq_left (Or.inl (by omega))]
    rw [hstep]
    intro a b _ _ _ _ _ _ _ hab _ hst _
    exact absurd hst hab
  obtain ⟨t, -, hform⟩ := sampleStep_active_form R z.1 u hu hm
  rcases hform with ⟨i, j, hij, he⟩ | ⟨i, c, he⟩
  · rw [he]
    intro a b c d hv hca hcb hcc hcd hab hcd' hst1 hst2
    have hv' : Valid z.1 := hv
    change ancestorStep z.1 (.inr (.inl (i.val, j.val))) q a =
      ancestorStep z.1 (.inr (.inl (i.val, j.val))) q b at hst1
    change ancestorStep z.1 (.inr (.inl (i.val, j.val))) q c =
      ancestorStep z.1 (.inr (.inl (i.val, j.val))) q d at hst2
    rw [ancestorStep_coal z.1 q i j hij, ancestorStep_coal z.1 q i j hij] at hst1 hst2
    have key : ∀ a b : ℕ, a ≠ b → ancestorCarried z.1 (q.val : ℝ) a →
        ancestorCarried z.1 (q.val : ℝ) b →
        (if a = (z.1.2.2.2 i).1 ∨ a = (z.1.2.2.2 j).1 then z.1.2.1 else a) =
          (if b = (z.1.2.2.2 i).1 ∨ b = (z.1.2.2.2 j).1 then z.1.2.1 else b) →
        (a = (z.1.2.2.2 i).1 ∨ a = (z.1.2.2.2 j).1) ∧
          (b = (z.1.2.2.2 i).1 ∨ b = (z.1.2.2.2 j).1) := by
      intro a b hab ha hb hst
      obtain ⟨ka, hka, -⟩ := ha
      obtain ⟨kb, hkb, -⟩ := hb
      have hla := hv'.2.2.1 ka
      have hlb := hv'.2.2.1 kb
      split_ifs at hst with h1 h2 h2
      · exact ⟨h1, h2⟩
      · omega
      · omega
      · omega
    have k1 := key a b hab hca hcb hst1
    have k2 := key c d hcd' hcc hcd hst2
    omega
  · rw [he]
    intro a b _ _ hv hca hcb _ _ hab _ hst _
    exfalso
    change ancestorStep z.1 (.inr (.inr (i.val, c))) q a =
      ancestorStep z.1 (.inr (.inr (i.val, c))) q b at hst
    rw [ancestorStep_split, ancestorStep_split] at hst
    have hv' : Valid z.1 := hv
    have hca' : ancestorCarried z.1 (q.val : ℝ) a := hca
    have hcb' : ancestorCarried z.1 (q.val : ℝ) b := hcb
    obtain ⟨ka, hka, -⟩ := hca'
    obtain ⟨kb, hkb, -⟩ := hcb'
    have hla := hv'.2.2.1 ka
    have hlb := hv'.2.2.1 kb
    by_cases hha : a = (z.1.2.2.2 i).1
    · by_cases hhb : b = (z.1.2.2.2 i).1
      · exact hab (hha.trans hhb.symm)
      · rw [ite_eq_left hha, ite_eq_right hhb] at hst
        split_ifs at hst <;> omega
    · by_cases hhb : b = (z.1.2.2.2 i).1
      · rw [ite_eq_right hha, ite_eq_left hhb] at hst
        split_ifs at hst <;> omega
      · rw [ite_eq_right hha, ite_eq_right hhb] at hst
        exact hab hst

theorem eventProcess_labelMergeTransition (R : ℝ) (x : AugmentedState) (q : GenomicProbe) :
    ∀ᵐ ω ∂(eventProcess false R).pathLaw x,
      ∀ k, labelMergeTransition q (ω k, ω (k + 1)) := by
  apply process_transition_relation (eventProcess false R) (labelMergeTransition q)
    (labelMergeTransition_measurable q) _ x
  intro z
  change ∀ᵐ y ∂eventKernel false R z, labelMergeTransition q (z, y)
  rw [eventKernel_apply]
  apply (ae_map_iff
    ((sampleStep_measurable false R).comp (measurable_const.prodMk measurable_id)).aemeasurable
    ((labelMergeTransition_measurable q).preimage
      (measurable_const.prodMk measurable_id))).mpr
  filter_upwards [noiseLaw_interior] with u hu
  exact sampleStep_labelMergeTransition R z u hu q

theorem card_le_card_image_add_one {S : Finset ℕ} {f : ℕ → ℕ}
    (h : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S, a ≠ b → c ≠ d → f a = f b → f c = f d →
      (a = c ∧ b = d) ∨ (a = d ∧ b = c)) :
    S.card ≤ (S.image f).card + 1 := by
  classical
  by_cases hinj : Set.InjOn f S
  · rw [Finset.card_image_of_injOn hinj]
    omega
  · simp only [Set.InjOn, not_forall] at hinj
    obtain ⟨a, ha, b, hb, hfab, hab⟩ := hinj
    have hinj' : Set.InjOn f (S.erase a) := by
      intro c hc d hd hcd
      by_contra hne
      have hc' := Finset.mem_erase.1 hc
      have hd' := Finset.mem_erase.1 hd
      rcases h a ha b hb c hc'.2 d hd'.2 hab hne hfab hcd with h1 | h1
      · exact hc'.1 h1.1.symm
      · exact hd'.1 h1.1.symm
    have h1 := Finset.card_image_of_injOn hinj'
    have h2 : ((S.erase a).image f).card ≤ (S.image f).card :=
      Finset.card_le_card (Finset.image_subset_image (Finset.erase_subset a S))
    have h3 := Finset.card_erase_of_mem (show a ∈ S from ha)
    omega

noncomputable def ancestorLabelSet (N : ℕ) (ω : EventPath) (q : GenomicProbe) (k : ℕ) : Finset ℕ :=
  Finset.univ.image fun i : Fin N => ancestorLabel N ω q i k

theorem ancestorLabelSet_succ (N : ℕ) (ω : EventPath) (q : GenomicProbe) (k : ℕ) :
    ancestorLabelSet N ω q (k + 1) =
      (ancestorLabelSet N ω q k).image (ancestorStep (ω k).1 (ω (k + 1)).2.2 q) := by
  unfold ancestorLabelSet
  rw [Finset.image_image]
  rfl

theorem carrierCount_le_card_ancestorLabelSet {N : ℕ} {ω : EventPath}
    (h : ChronologicalAncestryPath N ω) (q : GenomicProbe)
    (hq : ∀ k, twoSampleTransition q (ω k, ω (k + 1)))
    (hl : ∀ k, labelMergeTransition q (ω k, ω (k + 1))) (k : ℕ) :
    carrierCount (q.val : ℝ) (ω k).1 ≤ (ancestorLabelSet N ω q k).card := by
  classical
  induction k with
  | zero =>
    have hc : carrierCount (q.val : ℝ) (ω 0).1 = N := by
      rw [h.1]
      exact carrierCount_initialState N _ (by exact_mod_cast q.property.1)
        (by exact_mod_cast q.property.2)
    have hs : (ancestorLabelSet N ω q 0).card = N := by
      unfold ancestorLabelSet
      simp only [ancestorLabel]
      rw [Finset.card_image_of_injective _ Fin.val_injective, Finset.card_univ,
        Fintype.card_fin]
    omega
  | succ k ih =>
    obtain ⟨_, hmono, hdrop⟩ := hq k
    have hcar : ∀ a ∈ ancestorLabelSet N ω q k, ancestorCarried (ω k).1 (q.val : ℝ) a := by
      intro a ha
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 ha
      exact h.ancestorCarried q i k
    rw [ancestorLabelSet_succ]
    by_cases hinj : Set.InjOn (ancestorStep (ω k).1 (ω (k + 1)).2.2 q) (ancestorLabelSet N ω q k)
    · rw [Finset.card_image_of_injOn hinj]
      exact hmono.trans ih
    · simp only [Set.InjOn, not_forall] at hinj
      obtain ⟨a, ha, b, hb, hfab, hab⟩ := hinj
      have hlt : carrierCount (q.val : ℝ) (ω (k + 1)).1 < carrierCount (q.val : ℝ) (ω k).1 :=
        hdrop a b (h.valid k) hab (hcar a ha) (hcar b hb) hfab
      have hcard := card_le_card_image_add_one (S := ancestorLabelSet N ω q k)
        (f := ancestorStep (ω k).1 (ω (k + 1)).2.2 q)
        (fun a ha b hb c hc d hd => hl k a b c d (h.valid k) (hcar a ha) (hcar b hb)
          (hcar c hc) (hcar d hd))
      omega

theorem ancestorLabel_eq_of_carrierCount_le_one {N : ℕ} {ω : EventPath}
    (h : ChronologicalAncestryPath N ω) (q : GenomicProbe) (k : ℕ)
    (hc : carrierCount (q.val : ℝ) (ω k).1 ≤ 1) (i j : Fin N) :
    ancestorLabel N ω q i k = ancestorLabel N ω q j k := by
  classical
  obtain ⟨a, ha, haq⟩ := h.ancestorCarried q i k
  obtain ⟨b, hb, hbq⟩ := h.ancestorCarried q j k
  unfold carrierCount materialCount at hc
  have hab : a = b := Finset.card_le_one.mp hc a
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, haq⟩) b
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbq⟩)
  exact ha.symm.trans (hab ▸ hb)

theorem iSup_genealogyObservation_eq_time {N : ℕ} {ω : EventPath}
    (h : ChronologicalAncestryPath N ω) (q : GenomicProbe)
    (hq : ∀ k, twoSampleTransition q (ω k, ω (k + 1)))
    (hl : ∀ k, labelMergeTransition q (ω k, ω (k + 1)))
    (hterm : ∃ K, ∀ k, K ≤ k → (ω k).1.2.2.1 ≤ 1) :
    ∃ K, (∀ k < K, 2 ≤ carrierCount (q.val : ℝ) (ω k).1) ∧
      carrierCount (q.val : ℝ) (ω K).1 ≤ 1 ∧
      ⨆ i, ⨆ j, genealogyObservation N ω q i j = ENNReal.ofReal (ω K).1.1 := by
  classical
  obtain ⟨K0, hK0⟩ := hterm
  have hex : ∃ k, carrierCount (q.val : ℝ) (ω k).1 ≤ 1 :=
    ⟨K0, (materialCount_le _ _).trans (hK0 K0 le_rfl)⟩
  have hK : carrierCount (q.val : ℝ) (ω (Nat.find hex)).1 ≤ 1 := Nat.find_spec hex
  have hbefore : ∀ k < Nat.find hex, 2 ≤ carrierCount (q.val : ℝ) (ω k).1 := fun k hk => by
    have := Nat.find_min hex hk
    omega
  have heqK := ancestorLabel_eq_of_carrierCount_le_one h q _ hK
  refine ⟨Nat.find hex, hbefore, hK, le_antisymm ?_ ?_⟩
  · refine iSup_le fun i => iSup_le fun j => ?_
    exact iInf_le_of_le (Nat.find hex) (by simp [heqK i j])
  · rcases Nat.eq_zero_or_pos (Nat.find hex) with hz | hpos
    · rw [hz, h.1]
      simp [initialState]
    · obtain ⟨K', hK'⟩ : ∃ K', Nat.find hex = K' + 1 := ⟨Nat.find hex - 1, by omega⟩
      have h2 := hbefore K' (by omega)
      have hcard := (carrierCount_le_card_ancestorLabelSet h q hq hl K').trans' h2
      obtain ⟨a, ha, b, hb, hab⟩ :=
        Finset.one_lt_card.1 (by omega : 1 < (ancestorLabelSet N ω q K').card)
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 ha
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hb
      refine le_iSup_of_le i (le_iSup_of_le j ?_)
      refine le_iInf fun k => ?_
      by_cases hk : k ≤ K'
      · have hne : ancestorLabel N ω q i k ≠ ancestorLabel N ω q j k := fun e =>
          hab (ancestorLabel_equal_later N ω q i j k K' hk e)
        simp [hne]
      · have hKk : Nat.find hex ≤ k := by omega
        have hek := ancestorLabel_equal_later N ω q i j _ k hKk (heqK i j)
        simp only [hek, ite_true]
        exact ENNReal.ofReal_le_ofReal (h.time_monotone hKk)

end Rhone.Coalescent.IntervalProcess
