/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeFixedPositionTwoSampleProposal
public import Rhone.Coalescent.SmcPrimeRegraftActiveUnique
public import Rhone.Coalescent.SmcPrimeSpatialGeometry
public import Rhone.Coalescent.SmcPrimeGenealogyLaw
public import Rhone.Coalescent.SmcPrimeAttachmentLaw

/-!
# Branch arrays of two samples that the SMC′ chain can reach

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 1–7. -/

@[expose] public section

namespace Rhone.Coalescent.SmcPrime
open IntervalProcess MeasureTheory
open scoped ENNReal

theorem twoSample_clade_cases (c : Finset (Fin 2)) :
    c = ∅ ∨ c = {0} ∨ c = {1} ∨ c = Finset.univ := by
  revert c
  decide

theorem twoSample_branch_of_pos {b : Branch 2} (hb : 0 < branchLength b) :
    (b.1 = {0} ∨ b.1 = {1}) ∧ b.2.1 < b.2.2 := by
  classical
  have hc : ¬ (b.1 = ∅ ∨ b.1 = Finset.univ) := by
    intro hc
    simp [branchLength, hc] at hb
  have hl : b.2.1 < b.2.2 := by
    by_contra hn
    simp [branchLength, hc, max_eq_left (sub_nonpos.mpr (le_of_not_gt hn))] at hb
  refine ⟨?_, hl⟩
  rcases twoSample_clade_cases b.1 with h | h | h | h
  · exact absurd (Or.inl h) hc
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd (Or.inr h) hc

theorem twoSample_branch_pos {b : Branch 2} {i : Fin 2} (hc : b.1 = {i})
    (hl : b.2.1 < b.2.2) : 0 < branchLength b := by
  classical
  have hp := twoSample_singleton_proper i
  rw [← hc] at hp
  simp [branchLength, hp, hl]

theorem mem_activeBranches {N : ℕ} (T : Tree N) (q : ℝ) (b : Fin T.1) :
    b ∈ activeBranches T q ↔
      0 < branchLength (T.2 b) ∧ (T.2 b).2.1 ≤ q ∧ q < (T.2 b).2.2 := by
  classical
  simp [activeBranches]

theorem foldr_max_mem (l : List ℝ) (h : 0 < l.foldr max 0) : l.foldr max 0 ∈ l := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    simp only [List.foldr_cons] at h ⊢
    rcases le_total (l.foldr max 0) a with hle | hle
    · rw [max_eq_left hle]
      simp
    · rw [max_eq_right hle] at h ⊢
      exact List.mem_cons_of_mem _ (ih h)

theorem exists_branch_hi_eq_rootHeight {N : ℕ} (T : Tree N) (h : 0 < rootHeight T) :
    ∃ i, 0 < branchLength (T.2 i) ∧ (T.2 i).2.2 = rootHeight T := by
  have hm := foldr_max_mem _ h
  obtain ⟨i, -, hi⟩ := List.mem_map.mp hm
  by_cases hp : 0 < branchLength (T.2 i)
  · refine ⟨i, hp, ?_⟩
    rw [rootHeight]
    simpa only [hp, ↓reduceIte] using hi
  · simp only [hp, ↓reduceIte] at hi
    exact absurd h (by rw [rootHeight, ← hi]; exact lt_irrefl 0)

theorem treeLength_pos_of_rootHeight_pos {N : ℕ} (T : Tree N) (h : 0 < rootHeight T) :
    0 < treeLength T := by
  obtain ⟨i, hi, -⟩ := exists_branch_hi_eq_rootHeight T h
  exact hi.trans_le (Finset.single_le_sum (f := fun j => branchLength (T.2 j))
    (fun j _ => branchLength_nonneg _) (Finset.mem_univ i))

theorem twoSample_treePairMRCA (T : Tree 2) :
    treePairMRCA T 0 1 = ENNReal.ofReal (rootHeight T) := by
  classical
  have h01 : ¬ ((0 : Fin 2) = 1) := by decide
  have hb : ∀ b : Fin T.1, ¬ ((0 : Fin 2) ∈ (T.2 b).1 ∧ (1 : Fin 2) ∈ (T.2 b).1 ∧
      0 < branchLength (T.2 b)) := by
    rintro b ⟨h0, h1, hp⟩
    rcases (twoSample_branch_of_pos hp).1 with h | h
    · rw [h] at h1
      exact absurd h1 (by decide)
    · rw [h] at h0
      exact absurd h0 (by decide)
  simp only [treePairMRCA, h01, ↓reduceIte, hb, iInf_top, le_top, inf_of_le_left]

structure TwoSampleArray (T : Tree 2) : Prop where
  normalized : TreeNormalized T
  nonnegative : TreeNonnegative T
  chronology : TreeChronology T
  activeUnique : TreeActiveUnique T

namespace TwoSampleArray

variable {T : Tree 2}

theorem exists_active (hT : TwoSampleArray T) {q : ℝ} (hq0 : 0 ≤ q)
    (hq : q < rootHeight T) (i : Fin 2) :
    ∃ b ∈ activeBranches T q, (T.2 b).1 = {i} := by
  classical
  obtain ⟨c, hc, hic⟩ := (hT.chronology.1 q hq0).2.1 i
  simp only [timeClades, not_le.mpr hq, ↓reduceIte, Finset.mem_image] at hc
  obtain ⟨b, hb, rfl⟩ := hc
  refine ⟨b, hb, ?_⟩
  have hpos := ((mem_activeBranches T q b).mp hb).1
  rcases (twoSample_branch_of_pos hpos).1 with h | h <;> rw [h] at hic ⊢ <;>
    fin_cases i <;> first | rfl | exact absurd hic (by decide)

theorem image_active (hT : TwoSampleArray T) {q : ℝ} (hq0 : 0 ≤ q)
    (hq : q < rootHeight T) :
    (activeBranches T q).image (fun b => (T.2 b).1) =
      ({{0}, {1}} : Finset (Finset (Fin 2))) := by
  classical
  ext c
  simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact (twoSample_branch_of_pos ((mem_activeBranches T q b).mp hb).1).1
  · rintro (rfl | rfl)
    · exact hT.exists_active hq0 hq 0
    · exact hT.exists_active hq0 hq 1

theorem attachmentRate_below (hT : TwoSampleArray T) {q : ℝ} (hq0 : 0 ≤ q)
    (hq : q < rootHeight T) : attachmentRate T q = 2 := by
  classical
  have hinj : Set.InjOn (fun b => (T.2 b).1) (activeBranches T q : Set (Fin T.1)) :=
    fun b hb b' hb' hbb => hT.activeUnique q hq0 b hb b' hb' hbb
  have hcard : (activeBranches T q).card = 2 := by
    rw [← Finset.card_image_of_injOn hinj, hT.image_active hq0 hq]
    decide
  simp only [attachmentRate, not_le.mpr hq, ↓reduceIte, hcard]
  norm_num

theorem attachmentTargetRate_below (hT : TwoSampleArray T) {q : ℝ} (hq0 : 0 ≤ q)
    (hq : q < rootHeight T) (i : Fin 2) : attachmentTargetRate T q {i} = 1 := by
  classical
  obtain ⟨b, hb, hbi⟩ := hT.exists_active hq0 hq i
  have hfilter : (activeBranches T q).filter (fun b => (T.2 b).1 = {i}) = {b} := by
    ext b'
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hb', hbi'⟩
      exact hT.activeUnique q hq0 b' hb' b hb (hbi'.trans hbi.symm)
    · rintro rfl
      exact ⟨hb, hbi⟩
  simp only [attachmentTargetRate, not_le.mpr hq, ↓reduceIte, hfilter,
    Finset.card_singleton, Nat.cast_one]

theorem attachmentTargetRate_below_improper {q : ℝ} (hq : q < rootHeight T)
    {c : Finset (Fin 2)} (hc : c = ∅ ∨ c = Finset.univ) : attachmentTargetRate T q c = 0 := by
  classical
  have hfilter : (activeBranches T q).filter (fun b => (T.2 b).1 = c) = ∅ := by
    ext b
    simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
    intro hb hbc
    rcases (twoSample_branch_of_pos ((mem_activeBranches T q b).mp hb).1).1 with h | h <;>
      rw [h] at hbc <;> rcases hc with hc | hc <;> rw [hc] at hbc <;>
      exact absurd hbc (by decide)
  simp only [attachmentTargetRate, not_le.mpr hq, ↓reduceIte, hfilter, Finset.card_empty,
    Nat.cast_zero]

theorem attachmentTargetRate_above {q : ℝ} (hq : rootHeight T ≤ q) (c : Finset (Fin 2)) :
    attachmentTargetRate T q c = if c = Finset.univ then 1 else 0 := by
  classical
  simp only [attachmentTargetRate, hq, ↓reduceIte]

theorem attachmentHazard_below (hT : TwoSampleArray T) {t s : ℝ} (ht : 0 ≤ t)
    (hts : t ≤ s) (hs : s ≤ rootHeight T) : attachmentHazard T t s = 2 * (s - t) := by
  unfold attachmentHazard
  rw [intervalIntegral.integral_of_le hts, integral_Ioc_eq_integral_Ioo,
    setIntegral_congr_fun measurableSet_Ioo (g := fun _ => (2 : ℝ))
      (fun x hx => hT.attachmentRate_below (ht.trans hx.1.le) (hx.2.trans_le hs)),
    setIntegral_const]
  simp [hts, mul_comm]

theorem attachmentHazard_above (hT : TwoSampleArray T) {t s : ℝ} (ht : 0 ≤ t)
    (hth : t ≤ rootHeight T) (hs : rootHeight T ≤ s) :
    attachmentHazard T t s = 2 * (rootHeight T - t) + (s - rootHeight T) := by
  rw [← attachmentHazard_add T t (rootHeight T) s, hT.attachmentHazard_below ht hth le_rfl,
    attachmentHazard_above_root T (rootHeight T) s le_rfl hs]

end TwoSampleArray

theorem twoSample_regraft_attachment_le_rootHeight (T : Tree 2) {t a : ℝ} (hta : t < a)
    (i : Fin 2) (target : Finset (Fin 2)) :
    a ≤ rootHeight (regraft T {i} target t a) := by
  obtain ⟨hpos, hhi⟩ := finiteBranch_pos (twoSample_singleton_proper i) hta
  have hmem := treeOfList_branch_hi_le_rootHeight
    (((List.finRange T.1).map (fun k => belowCut (T.2 k) t)) ++
      ((List.finRange T.1).map (fun k => betweenCutAttachment (T.2 k) {i} t a)) ++
      ((List.finRange T.1).map (fun k => aboveAttachment (T.2 k) {i} target a)) ++
      [finiteBranch ({i} : Finset (Fin 2)) t a,
        finiteBranch (Finset.univ \ {i}) (rootHeight T) a])
    (finiteBranch ({i} : Finset (Fin 2)) t a) (by simp) hpos
  rwa [hhi] at hmem

theorem twoSample_above_self_clade (i j : Fin 2) :
    ((({j} : Finset (Fin 2)) \ {i}) ∪
      if (({j} : Finset (Fin 2)) ∩ {i}).Nonempty then {i} else ∅) = {j} := by
  revert i j
  decide

theorem twoSample_above_other_clade (c : Finset (Fin 2)) {i j : Fin 2} (hij : i ≠ j) :
    (((c \ {i}) ∪ if (c ∩ {j}).Nonempty then {i} else ∅) = ∅) ∨
      (((c \ {i}) ∪ if (c ∩ {j}).Nonempty then {i} else ∅) = Finset.univ) := by
  revert c i j
  decide

theorem twoSample_regraft_self_rootHeight (T : Tree 2) (hT : TreeNormalized T) {t a : ℝ}
    (ht0 : 0 ≤ t) (hta : t ≤ a) (hah : a < rootHeight T) (i : Fin 2) :
    rootHeight (regraft T {i} {i} t a) = rootHeight T := by
  classical
  have hh : 0 < rootHeight T := (ht0.trans hta).trans_lt hah
  apply le_antisymm
  · have hle := regraft_root_height_le T {i} {i} t a hT (hta.trans hah.le) hta
    rwa [max_eq_left hah.le] at hle
  · obtain ⟨k, hk, hkh⟩ := exists_branch_hi_eq_rootHeight T hh
    obtain ⟨hkc, hkl⟩ := twoSample_branch_of_pos hk
    obtain ⟨j, hj⟩ : ∃ j : Fin 2, (T.2 k).1 = {j} := by
      rcases hkc with h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
    have hb : aboveAttachment (T.2 k) {i} {i} a =
        finiteBranch {j} (max (T.2 k).2.1 a) (T.2 k).2.2 := by
      unfold aboveAttachment
      rw [hj]
      congr 1
      convert twoSample_above_self_clade i j
    have hlt : max (T.2 k).2.1 a < (T.2 k).2.2 := max_lt hkl (hkh ▸ hah)
    obtain ⟨hpos, hhi⟩ := finiteBranch_pos (twoSample_singleton_proper j) hlt
    have hmem := treeOfList_branch_hi_le_rootHeight
      (((List.finRange T.1).map (fun k => belowCut (T.2 k) t)) ++
        ((List.finRange T.1).map (fun k => betweenCutAttachment (T.2 k) {i} t a)) ++
        ((List.finRange T.1).map (fun k => aboveAttachment (T.2 k) {i} {i} a)) ++
        [finiteBranch ({i} : Finset (Fin 2)) t a,
          finiteBranch (Finset.univ \ {i}) (rootHeight T) a])
      (finiteBranch {j} (max (T.2 k).2.1 a) (T.2 k).2.2)
      (by
        simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false]
        exact Or.inl (Or.inr ⟨k, List.mem_finRange k, hb⟩)) hpos
    rw [hhi, hkh] at hmem
    exact hmem

theorem twoSample_regraft_other_rootHeight (T : Tree 2) {t a : ℝ} (ht0 : 0 ≤ t)
    (hta : t < a) {i j : Fin 2} (hij : i ≠ j) :
    rootHeight (regraft T {i} {j} t a) = a := by
  classical
  apply le_antisymm
  · unfold regraft
    apply treeOfList_rootHeight_le _ a (ht0.trans hta.le)
    intro b hb hp
    simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with ((⟨k, _, rfl⟩ | ⟨k, _, rfl⟩) | ⟨k, _, rfl⟩) | (rfl | rfl)
    · unfold belowCut at hp ⊢
      rw [(finiteBranch_of_pos hp).2.2]
      exact (min_le_right _ _).trans hta.le
    · unfold betweenCutAttachment at hp ⊢
      rw [(finiteBranch_of_pos hp).2.2]
      exact min_le_right _ _
    · unfold aboveAttachment at hp
      exact absurd (by convert twoSample_above_other_clade (T.2 k).1 hij)
        (finiteBranch_of_pos hp).1
    · rw [(finiteBranch_of_pos hp).2.2]
    · rw [(finiteBranch_of_pos hp).2.2]
  · exact twoSample_regraft_attachment_le_rootHeight T hta i {j}

theorem twoSample_regraft_above_rootHeight (T : Tree 2) (hT : TreeNormalized T) {t a : ℝ}
    (hth : t ≤ rootHeight T) (hta : t < a) (hha : rootHeight T ≤ a) (i : Fin 2)
    (target : Finset (Fin 2)) :
    rootHeight (regraft T {i} target t a) = a := by
  apply le_antisymm
  · have hle := regraft_root_height_le T {i} target t a hT hth hta.le
    rwa [max_eq_right hha] at hle
  · exact twoSample_regraft_attachment_le_rootHeight T hta i target

theorem TwoSampleArray.proposal {T : Tree 2} (hT : TwoSampleArray T) (R : ℝ)
    (hL : 0 < treeLength T) (u : ProposalNoise) (hu : ∀ i, u i ∈ Set.Ioo 0 1) :
    TwoSampleArray (proposal R T u).2.2 := by
  have hu1 : u 1 ∈ Set.Ico 0 1 := ⟨(hu 1).1.le, (hu 1).2⟩
  have hu2 : u 2 ∈ Set.Ico 0 1 := ⟨(hu 2).1.le, (hu 2).2⟩
  have hu4 : u 4 ∈ Set.Ico 0 1 := ⟨(hu 4).1.le, (hu 4).2⟩
  have hg := proposal_geometry R T u (by norm_num) hL hT.normalized hT.nonnegative
    hT.chronology hu1 hu2 (hu 3) hu4
  have hc := proposal_chronology R T u hL hT.normalized hT.nonnegative hT.chronology
    hu1 hu2 (hu 3) hu4
  refine ⟨hg.1, hg.2.1, hc, ?_⟩
  obtain ⟨s, t, hcut, hs, hs0, hs1⟩ := cut_point_extant_clade T hL (u 1) (u 2) hu1 hu2
  obtain ⟨i, _, hilo, _, _, _⟩ :=
    cut_point_bounds T (u 1) (u 2) hu1.1 ⟨hu2.1, hu2.2.le⟩ s t hcut
  have ht : 0 ≤ t := (hT.nonnegative i).trans hilo
  have hcover := tree_chronology_temporal_cover T (by norm_num) hT.chronology
  have he : 0 ≤ -Real.log (u 3) :=
    neg_nonneg.mpr (Real.log_nonpos (hu 3).1.le (hu 3).2.le)
  have hbudget := attachment_time_budget_bound T hcover t (-Real.log (u 3)) ht he
  have hat := attachment_target_extant T hcover
    (attachmentTime T t (-Real.log (u 3))) (u 4) (ht.trans hbudget.1) hu4
  simp only [Rhone.Coalescent.SmcPrime.proposal, hcut]
  exact regraft_active_unique _ _ _ _ _ hT.normalized hT.chronology hT.activeUnique ht
    hbudget.1 hs hs0 hs1 hat

theorem TwoSampleArray.spatialStep {z : SpatialState 2} (hT : TwoSampleArray z.2) (R : ℝ)
    (u : ProposalNoise) (hu : ∀ i, u i ∈ Set.Ioo 0 1) :
    TwoSampleArray (spatialStep 2 R z u).2 := by
  by_cases hstop : 1 ≤ z.1 ∨ R ≤ 0 ∨ treeLength z.2 ≤ 0
  · simpa only [Rhone.Coalescent.SmcPrime.spatialStep, hstop, ↓reduceIte] using hT
  · have hL : 0 < treeLength z.2 := by
      push Not at hstop
      exact hstop.2.2
    by_cases hin : z.1 + (Rhone.Coalescent.SmcPrime.proposal R z.2 u).1 < 1
    · simpa only [Rhone.Coalescent.SmcPrime.spatialStep, hstop, ↓reduceIte, hin]
        using hT.proposal R hL u hu
    · simpa only [Rhone.Coalescent.SmcPrime.spatialStep, hstop, ↓reduceIte, hin]
        using hT

theorem twoSampleTree_twoSampleArray {h : ℝ} (hh : 0 < h) :
    TwoSampleArray (twoSampleTree h) := by
  classical
  have hr := twoSampleTree_rootHeight hh
  have hclades : ∀ q, 0 ≤ q → timeClades (twoSampleTree h) q =
      if h ≤ q then {Finset.univ} else ({{0}, {1}} : Finset (Finset (Fin 2))) := by
    intro q hq
    by_cases hqh : h ≤ q
    · simp only [timeClades, hr, hqh, ↓reduceIte]
    · simp only [timeClades, hr, hqh, ↓reduceIte,
        twoSampleTree_activeBranches hq (lt_of_not_ge hqh)]
      rfl
  refine ⟨twoSampleTree_normalized hh.le, fun i => le_rfl, ⟨?_, ?_⟩, ?_⟩
  · intro q hq
    rw [hclades q hq]
    by_cases hqh : h ≤ q
    · simp only [hqh, ↓reduceIte]
      decide
    · simp only [hqh, ↓reduceIte]
      decide
  · intro q r hq hqr c hc
    rw [hclades q hq] at hc
    rw [hclades r (hq.trans hqr)]
    by_cases hrh : h ≤ r
    · simp only [hrh, ↓reduceIte]
      exact ⟨Finset.univ, by simp, Finset.subset_univ c⟩
    · have hqh : ¬ h ≤ q := fun hc => hrh (hc.trans hqr)
      simp only [hqh, ↓reduceIte] at hc
      simp only [hrh, ↓reduceIte]
      exact ⟨c, hc, subset_rfl⟩
  · intro q _ i _ j _ hij
    have : ({i} : Finset (Fin 2)) = {j} := hij
    exact Finset.singleton_injective this

end Rhone.Coalescent.SmcPrime
