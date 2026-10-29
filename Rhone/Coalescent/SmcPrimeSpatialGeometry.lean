/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.SmcPrimeProposalGeometry
public import Rhone.Coalescent.SmcPrimeRegraftChronology
public import Rhone.Coalescent.SmcPrimeSpatialProcess

/-!
# Proposal and spatial update preserve concrete chronological tree geometry

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 1–7. -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 1–7. -/
theorem proposal_chronology {N : ℕ} (R : ℝ) (T : Tree N) (u : ProposalNoise)
    (hL : 0 < treeLength T)
    (hnorm : TreeNormalized T) (hnonneg : TreeNonnegative T) (hchron : TreeChronology T)
    (hu1 : u 1 ∈ Set.Ico 0 1) (hu2 : u 2 ∈ Set.Ico 0 1)
    (hu3 : u 3 ∈ Set.Ioo 0 1) (hu4 : u 4 ∈ Set.Ico 0 1) :
    TreeChronology (proposal R T u).2.2 := by
  obtain ⟨s, t, hcut, hs, hs0, hs1⟩ := cut_point_extant_clade T hL (u 1) (u 2) hu1 hu2
  obtain ⟨i, _, hilo, _, _, _⟩ :=
    cut_point_bounds T (u 1) (u 2) hu1.1 ⟨hu2.1, hu2.2.le⟩ s t hcut
  have ht : 0 ≤ t := (hnonneg i).trans hilo
  have hN : 0 < N := by
    obtain ⟨i, _⟩ := Finset.nonempty_iff_ne_empty.mpr hs0
    exact Nat.zero_lt_of_lt i.isLt
  have hcover := tree_chronology_temporal_cover T hN hchron
  have he : 0 ≤ -Real.log (u 3) :=
    neg_nonneg.mpr (Real.log_nonpos hu3.1.le hu3.2.le)
  have hbudget := attachment_time_budget_bound T hcover t (-Real.log (u 3)) ht he
  have hat := attachment_target_extant T hcover
    (attachmentTime T t (-Real.log (u 3))) (u 4) (ht.trans hbudget.1) hu4
  simp only [proposal, hcut]
  exact regraft_chronology _ _ _ _ _ hnorm hchron ht hbudget.1 hs hs0 hs1 hat

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 1–7. -/
theorem spatial_step_tree_geometry {N : ℕ} (R : ℝ) (z : SpatialState N) (u : ProposalNoise)
    (hN : 0 < N) (hnorm : TreeNormalized z.2) (hnonneg : TreeNonnegative z.2)
    (hchron : TreeChronology z.2) (hu : ∀ i, u i ∈ Set.Ioo 0 1) :
    TreeNormalized (spatialStep N R z u).2 ∧ TreeNonnegative (spatialStep N R z u).2 ∧
      TreeChronology (spatialStep N R z u).2 ∧ TreeTemporalCover (spatialStep N R z u).2 ∧
      treeLength (spatialStep N R z u).2 ≤ treeLength z.2 + 2 * (-Real.log (u 3)) := by
  have he : 0 ≤ -Real.log (u 3) :=
    neg_nonneg.mpr (Real.log_nonpos (hu 3).1.le (hu 3).2.le)
  have hfreeze : TreeNormalized z.2 ∧ TreeNonnegative z.2 ∧ TreeChronology z.2 ∧
      TreeTemporalCover z.2 ∧ treeLength z.2 ≤ treeLength z.2 + 2 * (-Real.log (u 3)) :=
    ⟨hnorm, hnonneg, hchron, tree_chronology_temporal_cover z.2 hN hchron,
      by linarith⟩
  by_cases hstop : 1 ≤ z.1 ∨ R ≤ 0 ∨ treeLength z.2 ≤ 0
  · simpa only [spatialStep, hstop, ↓reduceIte] using hfreeze
  · have hL : 0 < treeLength z.2 := by
      push Not at hstop
      exact hstop.2.2
    by_cases hin : z.1 + (proposal R z.2 u).1 < 1
    · have hg := proposal_geometry R z.2 u hN hL hnorm hnonneg hchron
        ⟨(hu 1).1.le, (hu 1).2⟩ ⟨(hu 2).1.le, (hu 2).2⟩ (hu 3)
        ⟨(hu 4).1.le, (hu 4).2⟩
      have hc := proposal_chronology R z.2 u hL hnorm hnonneg hchron
        ⟨(hu 1).1.le, (hu 1).2⟩ ⟨(hu 2).1.le, (hu 2).2⟩ (hu 3)
        ⟨(hu 4).1.le, (hu 4).2⟩
      simpa only [spatialStep, hstop, ↓reduceIte, hin] using
        And.intro hg.1 (And.intro hg.2.1 (And.intro hc (And.intro hg.2.2.1 hg.2.2.2)))
    · simpa only [spatialStep, hstop, ↓reduceIte, hin] using hfreeze

end Rhone.Coalescent.SmcPrime
