/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.FullARGTwoSampleKernel
public import Rhone.Coalescent.FullARGTermination

/-! # Path translation for two samples -/
@[expose] public section

namespace Rhone.Coalescent.IntervalProcess
open SmcSupport MeasureTheory ProbabilityTheory
open scoped ENNReal

def twoSampleTransition (q : GenomicProbe) (p : AugmentedState × AugmentedState) : Prop :=
  (2 ≤ p.1.1.2.2.1 → p.1.1.1 < p.2.1.1) ∧
  carrierCount (q.val : ℝ) p.2.1 ≤ carrierCount (q.val : ℝ) p.1.1 ∧
  ∀ a b : ℕ, Valid p.1.1 → a ≠ b → ancestorCarried p.1.1 (q.val : ℝ) a →
    ancestorCarried p.1.1 (q.val : ℝ) b →
    ancestorStep p.1.1 p.2.2.2 q a = ancestorStep p.1.1 p.2.2.2 q b →
    carrierCount (q.val : ℝ) p.2.1 < carrierCount (q.val : ℝ) p.1.1

theorem twoSampleTransition_measurable (q : GenomicProbe) :
    MeasurableSet {p : AugmentedState × AugmentedState | twoSampleTransition q p} := by
  have hcm := carrierCount_measurable (q.val : ℝ)
  have h1 : MeasurableSet {p : AugmentedState × AugmentedState |
      2 ≤ p.1.1.2.2.1 → p.1.1.1 < p.2.1.1} := by
    have ha : MeasurableSet {p : AugmentedState × AugmentedState | 2 ≤ p.1.1.2.2.1} :=
      measurableSet_le measurable_const (liveCount_measurable.comp measurable_fst.fst)
    have hb : MeasurableSet {p : AugmentedState × AugmentedState | p.1.1.1 < p.2.1.1} :=
      measurableSet_lt measurable_fst.fst.fst measurable_snd.fst.fst
    convert ha.compl.union hb using 1
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_compl_iff, imp_iff_not_or]
  have hlt : MeasurableSet {p : AugmentedState × AugmentedState |
      carrierCount (q.val : ℝ) p.2.1 < carrierCount (q.val : ℝ) p.1.1} :=
    measurableSet_lt (hcm.comp measurable_snd.fst) (hcm.comp measurable_fst.fst)
  have h2 : MeasurableSet {p : AugmentedState × AugmentedState |
      carrierCount (q.val : ℝ) p.2.1 ≤ carrierCount (q.val : ℝ) p.1.1} :=
    measurableSet_le (hcm.comp measurable_snd.fst) (hcm.comp measurable_fst.fst)
  have hpre : MeasurableSet {p : AugmentedState × AugmentedState | Valid p.1.1} :=
    validState_measurable.preimage measurable_fst.fst
  refine h1.inter (h2.inter ?_)
  apply measurableSet_forall
  intro a
  apply measurableSet_forall
  intro b
  have hca : MeasurableSet {p : AugmentedState × AugmentedState |
      ancestorCarried p.1.1 (q.val : ℝ) a} :=
    (ancestorCarried_fixed_measurable _ a).preimage measurable_fst.fst
  have hcb : MeasurableSet {p : AugmentedState × AugmentedState |
      ancestorCarried p.1.1 (q.val : ℝ) b} :=
    (ancestorCarried_fixed_measurable _ b).preimage measurable_fst.fst
  have hst : MeasurableSet {p : AugmentedState × AugmentedState |
      ancestorStep p.1.1 p.2.2.2 q a = ancestorStep p.1.1 p.2.2.2 q b} :=
    measurableSet_eq_fun
      ((ancestorStep_measurable q).comp
        (measurable_fst.fst.prodMk (measurable_snd.snd.snd.prodMk measurable_const)))
      ((ancestorStep_measurable q).comp
        (measurable_fst.fst.prodMk (measurable_snd.snd.snd.prodMk measurable_const)))
  by_cases hab : a = b
  · convert MeasurableSet.univ using 1
    ext p
    simp [hab]
  · convert hpre.compl.union (hca.compl.union (hcb.compl.union (hst.compl.union hlt))) using 1
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_compl_iff, imp_iff_not_or, ne_eq, hab,
      not_false_eq_true, not_true_eq_false, false_or]

theorem sampleStep_active_form (R : ℝ) (s : State) (u : Noise)
    (hu : ∀ i, 0 < u i ∧ u i < 1) (hm : 2 ≤ s.2.2.1) :
    ∃ t, s.1 < t ∧
      ((∃ i j : Fin s.2.2.1, i.val < j.val ∧ sampleStep false R s u =
          (atTime t (coalSuccessor s i j), (t, .inr (.inl (i.val, j.val))))) ∨
        ∃ (i : Fin s.2.2.1) (c : ℝ), sampleStep false R s u =
          (atTime t (splitSuccessor s i c), (t, .inr (.inr (i.val, c))))) := by
  classical
  have ht := unrestricted_totalRate_positive R s hm
  have ht' : (0 : ℝ) < totalRate false R s := by exact_mod_cast ht
  obtain ⟨a, ha, hp⟩ := selectedAction_exists_positive false R s u (hu 0).1.le (hu 0).2 ht
  refine ⟨s.1 - Real.log (u 1) / (totalRate false R s : ℝ), ?_, ?_⟩
  · have h1 := Real.log_neg (hu 1).1 (hu 1).2
    have h2 := div_neg_of_neg_of_pos h1 ht'
    linarith
  · have hstop : ¬(s.2.2.1 ≤ 1 ∨ totalRate false R s = 0) := by
      rintro (h | h)
      · omega
      · exact ht.ne' h
    cases a with
    | inl ij =>
      left
      refine ⟨ij.1, ij.2, positive_pair_order false R s ij hp, ?_⟩
      unfold sampleStep
      rw [ite_eq_right hstop]
      simp only [ha]
    | inr i =>
      right
      refine ⟨i, hullLo (s.2.2.2 i).2 + hullLength (s.2.2.2 i).2 * u 2, ?_⟩
      unfold sampleStep
      rw [ite_eq_right hstop]
      simp only [ha]

theorem ancestorStep_coal (s : State) (q : GenomicProbe) (i j : Fin s.2.2.1)
    (hij : i.val < j.val) (a : ℕ) :
    ancestorStep s (.inr (.inl (i.val, j.val))) q a =
      if a = (s.2.2.2 i).1 ∨ a = (s.2.2.2 j).1 then s.2.1 else a := by
  have hli : liveLabelAt s i.val = (s.2.2.2 i).1 := by simp [liveLabelAt, i.isLt]
  have hlj : liveLabelAt s j.val = (s.2.2.2 j).1 := by simp [liveLabelAt, j.isLt]
  simp only [ancestorStep, hij, j.isLt, and_self, ite_true, hli, hlj]

theorem ancestorStep_split (s : State) (q : GenomicProbe) (i : Fin s.2.2.1) (c : ℝ) (a : ℕ) :
    ancestorStep s (.inr (.inr (i.val, c))) q a =
      if a = (s.2.2.2 i).1 then (if (q.val : ℝ) < c then s.2.1 else s.2.1 + 1) else a := by
  have hli : liveLabelAt s i.val = (s.2.2.2 i).1 := by simp [liveLabelAt, i.isLt]
  simp only [ancestorStep, i.isLt, true_and, hli]

theorem sampleStep_twoSampleTransition (R : ℝ) (z : AugmentedState) (u : Noise)
    (hu : ∀ i, 0 < u i ∧ u i < 1) (q : GenomicProbe) :
    twoSampleTransition q (z, sampleStep false R z.1 u) := by
  classical
  by_cases hm : 2 ≤ z.1.2.2.1
  swap
  · have hstep : sampleStep false R z.1 u = (z.1, (z.1.1, .inl ())) := by
      unfold sampleStep
      rw [ite_eq_left (Or.inl (by omega))]
    rw [hstep]
    exact ⟨fun h => absurd h hm, le_rfl, fun a b _ hab _ _ hst => absurd hst hab⟩
  obtain ⟨t, htlt, hform⟩ := sampleStep_active_form R z.1 u hu hm
  rcases hform with ⟨i, j, hij, he⟩ | ⟨i, c, he⟩
  · rw [he]
    have hc := carrierCount_coalSuccessor (q.val : ℝ) (q.val : ℝ) z.1 i j hij
    refine ⟨fun _ => htlt, ?_, ?_⟩
    · change carrierCount (q.val : ℝ) (coalSuccessor z.1 i j) ≤ carrierCount (q.val : ℝ) z.1
      omega
    · intro a b hv hab hca hcb hst
      change ancestorStep z.1 (.inr (.inl (i.val, j.val))) q a =
        ancestorStep z.1 (.inr (.inl (i.val, j.val))) q b at hst
      rw [ancestorStep_coal z.1 q i j hij, ancestorStep_coal z.1 q i j hij] at hst
      change carrierCount (q.val : ℝ) (coalSuccessor z.1 i j) < carrierCount (q.val : ℝ) z.1
      have hv' : Valid z.1 := hv
      have hca' : ancestorCarried z.1 (q.val : ℝ) a := hca
      have hcb' : ancestorCarried z.1 (q.val : ℝ) b := hcb
      obtain ⟨ka, hka, hkaq⟩ := hca'
      obtain ⟨kb, hkb, hkbq⟩ := hcb'
      have hla := hv'.2.2.1 ka
      have hlb := hv'.2.2.1 kb
      by_cases hha : a = (z.1.2.2.2 i).1 ∨ a = (z.1.2.2.2 j).1
      · by_cases hhb : b = (z.1.2.2.2 i).1 ∨ b = (z.1.2.2.2 j).1
        · have hboth : materialContains (z.1.2.2.2 i).2 (q.val : ℝ) ∧
              materialContains (z.1.2.2.2 j).2 (q.val : ℝ) := by
            rcases hha with ha1 | ha1 <;> rcases hhb with hb1 | hb1
            · exact absurd (ha1.trans hb1.symm) hab
            · have e1 : ka = i := hv'.2.2.2 (hka.trans ha1)
              have e2 : kb = j := hv'.2.2.2 (hkb.trans hb1)
              exact ⟨e1 ▸ hkaq, e2 ▸ hkbq⟩
            · have e1 : ka = j := hv'.2.2.2 (hka.trans ha1)
              have e2 : kb = i := hv'.2.2.2 (hkb.trans hb1)
              exact ⟨e2 ▸ hkbq, e1 ▸ hkaq⟩
            · exact absurd (ha1.trans hb1.symm) hab
          simp only [carrierType, hboth.1, hboth.2, decide_true, Bool.and_self,
            Bool.toNat_true] at hc
          omega
        · rw [ite_eq_left hha, ite_eq_right hhb] at hst
          omega
      · by_cases hhb : b = (z.1.2.2.2 i).1 ∨ b = (z.1.2.2.2 j).1
        · rw [ite_eq_right hha, ite_eq_left hhb] at hst
          omega
        · rw [ite_eq_right hha, ite_eq_right hhb] at hst
          exact absurd hst hab
  · rw [he]
    refine ⟨fun _ => htlt, ?_, ?_⟩
    · exact (carrierCount_splitSuccessor (q.val : ℝ) z.1 i c).le
    · intro a b hv hab hca hcb hst
      change ancestorStep z.1 (.inr (.inr (i.val, c))) q a =
        ancestorStep z.1 (.inr (.inr (i.val, c))) q b at hst
      rw [ancestorStep_split, ancestorStep_split] at hst
      have hv' : Valid z.1 := hv
      have hca' : ancestorCarried z.1 (q.val : ℝ) a := hca
      have hcb' : ancestorCarried z.1 (q.val : ℝ) b := hcb
      obtain ⟨ka, hka, hkaq⟩ := hca'
      obtain ⟨kb, hkb, hkbq⟩ := hcb'
      have hla := hv'.2.2.1 ka
      have hlb := hv'.2.2.1 kb
      exfalso
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

theorem eventProcess_twoSampleTransition (R : ℝ) (x : AugmentedState) (q : GenomicProbe) :
    ∀ᵐ ω ∂(eventProcess false R).pathLaw x,
      ∀ k, twoSampleTransition q (ω k, ω (k + 1)) := by
  apply process_transition_relation (eventProcess false R) (twoSampleTransition q)
    (twoSampleTransition_measurable q) _ x
  intro z
  change ∀ᵐ y ∂eventKernel false R z, twoSampleTransition q (z, y)
  rw [eventKernel_apply]
  apply (ae_map_iff
    ((sampleStep_measurable false R).comp (measurable_const.prodMk measurable_id)).aemeasurable
    ((twoSampleTransition_measurable q).preimage
      (measurable_const.prodMk measurable_id))).mpr
  filter_upwards [noiseLaw_interior] with u hu
  exact sampleStep_twoSampleTransition R z u hu q

theorem materialCount_eq_of_forall (P : Material → Prop) (s : State)
    (h : ∀ i : Fin s.2.2.1, P (s.2.2.2 i).2) : materialCount P s = s.2.2.1 := by
  classical
  unfold materialCount
  rw [Finset.filter_true_of_mem (by intro i _; exact h i), Finset.card_univ, Fintype.card_fin]

theorem carrierCount_initialState (N : ℕ) (q : ℝ) (h0 : 0 ≤ q) (h1 : q < 1) :
    carrierCount q (initialState N) = N := by
  classical
  unfold carrierCount materialCount
  have hall : ∀ i : Fin (initialState N).2.2.1,
      materialContains ((initialState N).2.2.2 i).2 q :=
    fun i => (initial_materialContains N i q).mpr ⟨h0, h1⟩
  rw [Finset.filter_true_of_mem (by intro i _; exact hall i), Finset.card_univ]
  exact Fintype.card_fin N

theorem jointCarrierCount_initialState (N : ℕ) (x y : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1)
    (hy0 : 0 ≤ y) (hy1 : y < 1) : jointCarrierCount x y (initialState N) = N := by
  unfold jointCarrierCount
  have hall : ∀ i : Fin (initialState N).2.2.1,
      materialContains ((initialState N).2.2.2 i).2 x ∧
        materialContains ((initialState N).2.2.2 i).2 y :=
    fun i => ⟨(initial_materialContains N i x).mpr ⟨hx0, hx1⟩,
      (initial_materialContains N i y).mpr ⟨hy0, hy1⟩⟩
  exact materialCount_eq_of_forall _ _ hall

theorem carrierCount_le_of_labels {ω : EventPath} (h : ChronologicalAncestryPath 2 ω)
    (q : GenomicProbe) (hq : ∀ k, twoSampleTransition q (ω k, ω (k + 1))) (k : ℕ) :
    carrierCount (q.val : ℝ) (ω k).1 ≤ 2 ∧
      (ancestorLabel 2 ω q 0 k = ancestorLabel 2 ω q 1 k →
        carrierCount (q.val : ℝ) (ω k).1 ≤ 1) := by
  induction k with
  | zero =>
    have hc : carrierCount (q.val : ℝ) (ω 0).1 = 2 := by
      rw [h.1]
      exact carrierCount_initialState 2 _ (by exact_mod_cast q.property.1)
        (by exact_mod_cast q.property.2)
    refine ⟨hc.le, fun heq => ?_⟩
    simp [ancestorLabel] at heq
  | succ k ih =>
    obtain ⟨_, hmono, hdrop⟩ := hq k
    refine ⟨hmono.trans ih.1, fun heq => ?_⟩
    by_cases hprev : ancestorLabel 2 ω q 0 k = ancestorLabel 2 ω q 1 k
    · exact hmono.trans (ih.2 hprev)
    · have hlt : carrierCount (q.val : ℝ) (ω (k + 1)).1 < carrierCount (q.val : ℝ) (ω k).1 :=
        hdrop _ _ (h.valid k) hprev (h.ancestorCarried q 0 k) (h.ancestorCarried q 1 k) heq
      have := ih.1
      omega

theorem labels_eq_of_carrierCount_le_one {ω : EventPath} (h : ChronologicalAncestryPath 2 ω)
    (q : GenomicProbe) (k : ℕ) (hc : carrierCount (q.val : ℝ) (ω k).1 ≤ 1) :
    ancestorLabel 2 ω q 0 k = ancestorLabel 2 ω q 1 k := by
  classical
  obtain ⟨i, hi, hiq⟩ := h.ancestorCarried q 0 k
  obtain ⟨j, hj, hjq⟩ := h.ancestorCarried q 1 k
  unfold carrierCount materialCount at hc
  have hij : i = j := Finset.card_le_one.mp hc i
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hiq⟩) j
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjq⟩)
  exact hi.symm.trans (hij ▸ hj)

theorem genealogyObservation_eq_time_of_carrierCount {ω : EventPath}
    (h : ChronologicalAncestryPath 2 ω) (q : GenomicProbe)
    (hq : ∀ k, twoSampleTransition q (ω k, ω (k + 1)))
    (hterm : ∃ K, ∀ k, K ≤ k → (ω k).1.2.2.1 ≤ 1) :
    ∃ K, (∀ k < K, carrierCount (q.val : ℝ) (ω k).1 = 2) ∧
      carrierCount (q.val : ℝ) (ω K).1 ≤ 1 ∧
      genealogyObservation 2 ω q 0 1 = ENNReal.ofReal (ω K).1.1 := by
  classical
  obtain ⟨K0, hK0⟩ := hterm
  have hex : ∃ k, carrierCount (q.val : ℝ) (ω k).1 ≤ 1 :=
    ⟨K0, (materialCount_le _ _).trans (hK0 K0 le_rfl)⟩
  have hbefore : ∀ k < Nat.find hex, ¬carrierCount (q.val : ℝ) (ω k).1 ≤ 1 :=
    fun k hk => Nat.find_min hex hk
  have hK := Nat.find_spec hex
  have heq := labels_eq_of_carrierCount_le_one h q _ hK
  refine ⟨Nat.find hex, fun k hk => ?_, hK, ?_⟩
  · have h1 := hbefore k hk
    have h2 := (carrierCount_le_of_labels h q hq k).1
    omega
  · apply le_antisymm
    · exact iInf_le_of_le (Nat.find hex) (by simp [heq])
    · apply le_iInf
      intro k
      by_cases hk : k < Nat.find hex
      · have hne : ancestorLabel 2 ω q 0 k ≠ ancestorLabel 2 ω q 1 k :=
          fun e => hbefore k hk ((carrierCount_le_of_labels h q hq k).2 e)
        simp [hne]
      · have hkl : Nat.find hex ≤ k := Nat.le_of_not_gt hk
        have hek := ancestorLabel_equal_later 2 ω q 0 1 _ k hkl heq
        simp only [hek, ite_true]
        exact ENNReal.ofReal_le_ofReal (h.time_monotone hkl)

theorem genealogyObservation_agreement_iff {ω : EventPath}
    (h : ChronologicalAncestryPath 2 ω) (x y : GenomicProbe)
    (hx : ∀ k, twoSampleTransition x (ω k, ω (k + 1)))
    (hy : ∀ k, twoSampleTransition y (ω k, ω (k + 1)))
    (hterm : ∃ K, ∀ k, K ≤ k → (ω k).1.2.2.1 ≤ 1) :
    genealogyObservation 2 ω x 0 1 = genealogyObservation 2 ω y 0 1 ↔
      ∃ n, (∀ k ≤ n, ω k ∈ twoLocusPre (x.val : ℝ) (y.val : ℝ)) ∧
        ω (n + 1) ∈ twoLocusDone (x.val : ℝ) (y.val : ℝ) := by
  obtain ⟨Kx, hbx, hdx, hGx⟩ := genealogyObservation_eq_time_of_carrierCount h x hx hterm
  obtain ⟨Ky, hby, hdy, hGy⟩ := genealogyObservation_eq_time_of_carrierCount h y hy hterm
  have hstrict : ∀ (q : GenomicProbe), (∀ k, twoSampleTransition q (ω k, ω (k + 1))) →
      ∀ K K' : ℕ, K < K' → carrierCount (q.val : ℝ) (ω (K' - 1)).1 = 2 →
        (ω K).1.1 < (ω K').1.1 := by
    intro q hq K K' hlt hc
    have hcount : 2 ≤ (ω (K' - 1)).1.2.2.1 := by
      have := materialCount_le (fun a => materialContains a (q.val : ℝ)) (ω (K' - 1)).1
      unfold carrierCount at hc
      omega
    have h1 : (ω (K' - 1)).1.1 < (ω (K' - 1 + 1)).1.1 := (hq (K' - 1)).1 hcount
    have h2 : (ω K).1.1 ≤ (ω (K' - 1)).1.1 := h.time_monotone (by omega)
    have e : K' - 1 + 1 = K' := by omega
    rw [e] at h1
    exact lt_of_le_of_lt h2 h1
  have hinit : carrierCount (x.val : ℝ) (ω 0).1 = 2 := by
    rw [h.1]
    exact carrierCount_initialState 2 _ (by exact_mod_cast x.property.1)
      (by exact_mod_cast x.property.2)
  rw [hGx, hGy, ENNReal.ofReal_eq_ofReal_iff (h.valid Kx).1 (h.valid Ky).1]
  constructor
  · intro ht
    have hK : Kx = Ky := by
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · exact (hstrict y hy Kx Ky hlt (hby _ (by omega))).ne ht
      · exact (hstrict x hx Ky Kx hgt (hbx _ (by omega))).ne ht.symm
    have hpos : 1 ≤ Kx := by
      by_contra hzero
      have e : Kx = 0 := by omega
      rw [e] at hdx
      omega
    refine ⟨Kx - 1, fun k hk => ⟨hbx k (by omega), hby k (by omega)⟩, ?_⟩
    have e : Kx - 1 + 1 = Kx := by omega
    rw [e]
    exact ⟨hdx, hK ▸ hdy⟩
  · rintro ⟨n, hpre, hdone⟩
    have hKx : Kx = n + 1 := by
      rcases Nat.lt_trichotomy Kx (n + 1) with hlt | heq | hgt
      · have := (hpre Kx (by omega)).1
        omega
      · exact heq
      · have := hbx (n + 1) hgt
        have := hdone.1
        omega
    have hKy : Ky = n + 1 := by
      rcases Nat.lt_trichotomy Ky (n + 1) with hlt | heq | hgt
      · have := (hpre Ky (by omega)).2
        omega
      · exact heq
      · have := hby (n + 1) hgt
        have := hdone.2
        omega
    rw [hKx, hKy]

theorem eventProcess_agreement_ae_iff (R : ℝ) (hR : 0 ≤ R) (x y : GenomicProbe) :
    ∀ᵐ ω ∂(eventProcess false R).pathLaw (initialState 2, (0, .inl ())),
      (genealogyObservation 2 ω x 0 1 = genealogyObservation 2 ω y 0 1 ↔
        ∃ n, (∀ k ≤ n, ω k ∈ twoLocusPre (x.val : ℝ) (y.val : ℝ)) ∧
          ω (n + 1) ∈ twoLocusDone (x.val : ℝ) (y.val : ℝ)) := by
  filter_upwards [eventProcess_chronologicalAncestryPath 2 false R,
    eventProcess_twoSampleTransition R (initialState 2, (0, .inl ())) x,
    eventProcess_twoSampleTransition R (initialState 2, (0, .inl ())) y,
    eventProcess_liveCount_reaches_one 2 R hR] with ω h hx hy hterm
  exact genealogyObservation_agreement_iff h x y hx hy hterm

end Rhone.Coalescent.IntervalProcess
