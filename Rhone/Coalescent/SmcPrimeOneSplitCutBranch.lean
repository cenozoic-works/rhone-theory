/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeOneSplitActiveOldCount
public import Rhone.Coalescent.SmcPrimeOneSplitNextOldRecord
public import Rhone.Coalescent.SmcPrimeOneSplitCutFields

/-! # The cut branch of the extraction: successor and other coalescences -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess

theorem OneSplitPrefixSupported.cut_successor {N : ℕ}
    {h : Rhone.Coalescent.SmcSupport.ARGPrefix (N + 1)} (hs : OneSplitPrefixSupported N h)
    (c : Fin (N + 1))
    (i : Fin (h ⟨c.val, Finset.mem_Iic.mpr (by have := c.isLt; omega)⟩).1.2.2.1)
    (x : ℝ)
    (hev : (h ⟨c.val + 1, Finset.mem_Iic.mpr c.isLt⟩).2.2 = .inr (.inr (i.val, x))) :
    0 < x ∧ x < 1 ∧ c.val < N ∧
      (h ⟨c.val + 1, Finset.mem_Iic.mpr c.isLt⟩).1 =
        atTime (h ⟨c.val + 1, Finset.mem_Iic.mpr c.isLt⟩).1.1
          (splitSuccessor (h ⟨c.val, Finset.mem_Iic.mpr (by have := c.isLt; omega)⟩).1 i x) := by
  have he : (h ⟨c.val + 1, Finset.mem_Iic.mpr c.isLt⟩).2.2 ∈ splitSet := by
    rw [hev]
    exact True.intro
  obtain ⟨j, y, hx, hy, hev', hnxt, _⟩ := (hs.2.2.1 c).split_case (hs.2.1 _) he
  have hp : (j.val, y) = (i.val, x) := Sum.inr.inj (Sum.inr.inj (hev'.symm.trans hev))
  have hj : j = i := Fin.ext (congrArg Prod.fst hp)
  have hxy : y = x := congrArg Prod.snd hp
  subst j
  subst y
  refine ⟨hx, hy, ?_, hnxt⟩
  have hm := (hs.2.2.1 c).split_active_count he
  by_contra hc
  have hcv : c.val = N := by have := c.isLt; omega
  have hcount := SmcSupport.splitSuccessor_count
    (h ⟨c.val, Finset.mem_Iic.mpr (by have := c.isLt; omega)⟩).1 i x
  have hfinal := hs.2.2.2.2.2
  have hnxtcount := congrArg (fun s : State => s.2.2.1) hnxt
  dsimp only [atTime] at hnxtcount
  have hcfin : (⟨c.val + 1, Finset.mem_Iic.mpr c.isLt⟩ : Finset.Iic (N + 1)) =
      ⟨N + 1, Finset.mem_Iic.mpr le_rfl⟩ := Subtype.ext (by change c.val + 1 = N + 1; omega)
  rw [hcfin] at hnxtcount
  omega

theorem OneSplitPrefixSupported.detached_before_cut {N : ℕ}
    {h : Rhone.Coalescent.SmcSupport.ARGPrefix (N + 1)} (hs : OneSplitPrefixSupported N h)
    (c : Fin (N + 1))
    (he : (h ⟨c.val + 1, Finset.mem_Iic.mpr c.isLt⟩).2.2 ∈ splitSet) :
    (extractionRun N h c.val).detached = none := by
  obtain ⟨s, _, hcoal⟩ := hs.2.2.2.2.1
  have hcs : c = s := by
    by_contra hn
    have hc := hcoal c hn
    cases hev : (h ⟨c.val + 1, Finset.mem_Iic.mpr c.isLt⟩).2.2 with
    | inl u => rw [hev] at he; cases he
    | inr a =>
      cases a with
      | inl ij => rw [hev] at he; cases he
      | inr ix => rw [hev] at hc; cases hc
  apply extractionRun_detached_before_split N h s hcoal c.val
  exact le_of_eq (congrArg Fin.val hcs)

theorem extraction_cut_branch (N : ℕ)
    (h : Rhone.Coalescent.SmcSupport.ARGPrefix (N + 1)) (hs : OneSplitPrefixSupported N h)
    (c : Fin (N + 1))
    (i : Fin (h ⟨c.val, Finset.mem_Iic.mpr (by have := c.isLt; omega)⟩).1.2.2.1)
    (x : ℝ)
    (hev : (h ⟨c.val + 1, Finset.mem_Iic.mpr c.isLt⟩).2.2 = .inr (.inr (i.val, x))) :
    ∃ b : Fin (metricTreeFromHistory N (extractOneSplitSkeleton N h).1).1,
      b ∈ activeBranches (metricTreeFromHistory N (extractOneSplitSkeleton N h).1)
        (h ⟨c.val + 1, Finset.mem_Iic.mpr c.isLt⟩).1.1 ∧
      ((metricTreeFromHistory N (extractOneSplitSkeleton N h).1).2 b).1 =
        extractionClade (extractionRun N h c.val).argLabels
          ((h ⟨c.val, Finset.mem_Iic.mpr (by have := c.isLt; omega)⟩).1.2.2.2 i).1 := by
  classical
  let z := extractionRun N h c.val
  let η := extractOneSplitSkeleton N h
  let ω := kingmanCompletion N η.1
  have he : (h ⟨c.val + 1, Finset.mem_Iic.mpr c.isLt⟩).2.2 ∈ splitSet := by
    rw [hev]
    exact True.intro
  have hd : z.detached = none := hs.detached_before_cut c he
  have hi : z.detached ≠ some ((h
      ⟨c.val, Finset.mem_Iic.mpr (by have := c.isLt; omega)⟩).1.2.2.2 i).1 := by
    rw [hd]
    exact nofun
  have hinv := extractionRun_inventory N h hs c.val (by have := c.isLt; omega)
  obtain ⟨a, u, haf, hag, _⟩ := hinv.parent_lookup i hi
  have hp := extractionRun_history_prefix N h hs c.val (by have := c.isLt; omega)
  have hmcount := (hp.records ⟨z.mergers, hp.bound⟩ le_rfl).2
  rw [hp.current] at hmcount
  change z.old.1.2.2.1 = N - z.mergers at hmcount
  have htwo : 2 ≤ z.old.1.2.2.1 := hinv.active_old_count (hs.2.1 _) hd
    ((hs.2.2.1 c).split_active_count he)
  have hm : z.mergers < N - 1 := by omega
  have hcN := (hs.cut_successor c i x hev).2.2.1
  have hpost : (extractionRun N h (c.val + 1)).mergers = z.mergers := by
    rw [extractionRun_succ N h c.val c.isLt]
    simp only [extractionStep, hev]
    rfl
  have hbounds := extractionRun_old_clock_interval N h hs (c.val + 1) (by omega)
    (by rw [hpost]; exact hm) (h ⟨c.val + 1, Finset.mem_Iic.mpr c.isLt⟩).1.1 le_rfl
    (hs.clock_lt ⟨c.val + 1, by omega⟩)
  have hbounds' : (η.1 ⟨z.mergers, hp.bound⟩).1.1 ≤
      (h ⟨c.val + 1, Finset.mem_Iic.mpr c.isLt⟩).1.1 ∧
      (h ⟨c.val + 1, Finset.mem_Iic.mpr c.isLt⟩).1.1 <
        (η.1 ⟨z.mergers + 1, by omega⟩).1.1 := by
    simpa only [hpost] using hbounds
  have hsη := extractOneSplitSkeleton_history_supported N h hs
  have hhist : (fun j : Fin N => ω j.val) = η.1 := by
    funext j
    exact kingmanCompletion_prefix N η.1 j.val j.isLt
  have hlive : ∃ v, ((ω z.mergers).1.2.2.2 v).1 = (z.old.1.2.2.2 u).1 := by
    dsimp only [ω]
    rw [kingmanCompletion_prefix N η.1 z.mergers hp.bound,
      extractionRun_final_old_record N h hs c.val (by have := c.isLt; omega)]
    exact ⟨u, rfl⟩
  have hlow : (ω z.mergers).1.1 ≤
      (h ⟨c.val + 1, Finset.mem_Iic.mpr c.isLt⟩).1.1 := by
    simpa only [ω, kingmanCompletion_prefix N η.1 z.mergers hp.bound] using hbounds'.1
  have hhigh : (h ⟨c.val + 1, Finset.mem_Iic.mpr c.isLt⟩).1.1 <
      (ω (z.mergers + 1)).1.1 := by
    simpa only [ω, kingmanCompletion_prefix N η.1 (z.mergers + 1) (by omega)]
      using hbounds'.2
  have hresult := kingman_live_active N ω hsη.completion_init hsη.completion_valid
    hsη.completion_step z.mergers (z.old.1.2.2.2 u).1 hm hlive
    (h ⟨c.val + 1, Finset.mem_Iic.mpr c.isLt⟩).1.1 hlow hhigh
  rw [hhist] at hresult
  obtain ⟨b, hb, hcl⟩ := hresult
  refine ⟨b, hb, ?_⟩
  rw [hcl, extractionRun_final_history_clade N h hs c.val (by have := c.isLt; omega)]
  exact hinv.parent_clade a i u haf hag

theorem OneSplitPrefixSupported.cut_other_coal {N : ℕ}
    {h : Rhone.Coalescent.SmcSupport.ARGPrefix (N + 1)} (hs : OneSplitPrefixSupported N h)
    (c : Fin (N + 1))
    (he : (h ⟨c.val + 1, Finset.mem_Iic.mpr c.isLt⟩).2.2 ∈ splitSet) :
    ∀ k : Fin (N + 1), k ≠ c →
      (h ⟨k.val + 1, Finset.mem_Iic.mpr k.isLt⟩).2.2 ∈ coalSet := by
  obtain ⟨s, _, hcoal⟩ := hs.2.2.2.2.1
  have hcs : c = s := by
    by_contra hn
    have hc := hcoal c hn
    cases hev : (h ⟨c.val + 1, Finset.mem_Iic.mpr c.isLt⟩).2.2 with
    | inl u => rw [hev] at he; cases he
    | inr a =>
      cases a with
      | inl ij => rw [hev] at he; cases he
      | inr ix => rw [hev] at hc; cases hc
  intro k hk
  exact hcoal k (fun he => hk (he.trans hcs.symm))

theorem extractOneSplitSkeleton_cut_branch (N : ℕ)
    (h : Rhone.Coalescent.SmcSupport.ARGPrefix (N + 1)) (hs : OneSplitPrefixSupported N h)
    (c : Fin (N + 1))
    (i : Fin (h ⟨c.val, Finset.mem_Iic.mpr (by have := c.isLt; omega)⟩).1.2.2.1)
    (x : ℝ)
    (hev : (h ⟨c.val + 1, Finset.mem_Iic.mpr c.isLt⟩).2.2 = .inr (.inr (i.val, x))) :
    ∃ b : Fin (metricTreeFromHistory N (extractOneSplitSkeleton N h).1).1,
      b ∈ activeBranches (metricTreeFromHistory N (extractOneSplitSkeleton N h).1)
        (extractOneSplitSkeleton N h).2.2.1 ∧
      (extractOneSplitSkeleton N h).2.1 = b.val ∧
      rebuildCutClade (extractOneSplitSkeleton N h) =
        extractionClade (extractionRun N h c.val).argLabels
          ((h ⟨c.val, Finset.mem_Iic.mpr (by have := c.isLt; omega)⟩).1.2.2.2 i).1 := by
  classical
  have he : (h ⟨c.val + 1, Finset.mem_Iic.mpr c.isLt⟩).2.2 ∈ splitSet := by
    rw [hev]
    exact True.intro
  have hother := extractionPrefixExtension_no_other_split N h c (hs.cut_other_coal c he)
  have hevω : (extractionPrefixExtension N h (c.val + 1)).2.2 =
      .inr (.inr (i.val, x)) := by
    rw [extractionPrefixExtension_prefix N h (c.val + 1) c.isLt]
    exact hev
  have hcut := extractionRun_cut_after_split N h c i.val x hevω hother
    (N + 1) le_rfl c.isLt
  have hf : (fun a => ancestorLabel N (extractionPrefixExtension N h)
      leftBoundaryProbe a c.val) = (extractionRun N h c.val).argLabels := by
    funext a
    exact (extractionRun_argLabels N h c.val c.isLt.le a).symm
  rw [hf, extractionPrefixExtension_prefix N h c.val c.isLt.le,
    extractionPrefixExtension_prefix N h (c.val + 1) c.isLt] at hcut
  simp only [liveLabelAt, dite_eq_left i.isLt] at hcut
  obtain ⟨b, hb, hcl⟩ := extraction_cut_branch N h hs c i x hev
  have ht : (extractOneSplitSkeleton N h).2.2.1 =
      (h ⟨c.val + 1, Finset.mem_Iic.mpr c.isLt⟩).1.1 := by
    change (extractionRun N h (N + 1)).cut.2.1 = _
    rw [hcut]
  have hidx : (extractOneSplitSkeleton N h).2.1 = b.val := by
    change extractionCutIndex _ (extractionRun N h (N + 1)).cut.1
      (extractionRun N h (N + 1)).cut.2.1 = _
    rw [hcut, ← hcl]
    exact extractionCutIndex_active _
      (metric_tree_from_history_active_unique N _ hs.sample_pos
        (extractOneSplitSkeleton_history_supported N h hs)) _
      (hs.clock_nonneg _) b hb
  refine ⟨b, by rwa [ht], hidx, ?_⟩
  have hvalid : (extractOneSplitSkeleton N h).2.1 <
      (metricTreeFromHistory N (extractOneSplitSkeleton N h).1).1 := by
    rw [hidx]
    exact b.isLt
  simp only [rebuildCutClade, dite_eq_left hvalid]
  have hi : (⟨(extractOneSplitSkeleton N h).2.1, hvalid⟩ :
      Fin (metricTreeFromHistory N (extractOneSplitSkeleton N h).1).1) = b := Fin.ext hidx
  rw [hi]
  exact hcl

end Rhone.Coalescent.SmcPrime
