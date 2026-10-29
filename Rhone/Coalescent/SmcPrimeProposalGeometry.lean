/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.SmcPrimeProposalSupport
public import Rhone.Coalescent.SmcPrimeRegraftCover

/-!
# Geometric bounds for an SMC′ proposal

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 1–7. -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
def TreeNonnegative {N : ℕ} (T : Tree N) : Prop := ∀ i, 0 ≤ (T.2 i).2.1

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
theorem regraft_nonnegative {N : ℕ} (T : Tree N)
    (s target : Finset (Fin N)) (t a : ℝ) (hT : TreeNonnegative T) (ht : 0 ≤ t) :
    TreeNonnegative (regraft T s target t a) := by
  intro i
  have hbranch : ∀ b ∈
      (((List.finRange T.1).map (fun j => belowCut (T.2 j) t)) ++
        ((List.finRange T.1).map (fun j => betweenCutAttachment (T.2 j) s t a)) ++
        ((List.finRange T.1).map (fun j => aboveAttachment (T.2 j) s target a)) ++
        [finiteBranch s t a, finiteBranch (Finset.univ \ s) (rootHeight T) a]),
      0 ≤ b.2.1 := by
    intro b hb
    simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with ((⟨j, _, rfl⟩ | ⟨j, _, rfl⟩) | ⟨j, _, rfl⟩) | (rfl | rfl)
    · exact hT j
    · exact (hT j).trans (le_max_left _ _)
    · exact (hT j).trans (le_max_left _ _)
    · exact ht
    · exact root_height_nonneg T
  exact hbranch _ (List.get_mem _ i)

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 1–7. -/
theorem proposal_geometry {N : ℕ} (R : ℝ) (T : Tree N) (u : ProposalNoise)
    (hN : 0 < N) (hL : 0 < treeLength T)
    (hnorm : TreeNormalized T) (hnonneg : TreeNonnegative T) (hchron : TreeChronology T)
    (hu1 : u 1 ∈ Set.Ico 0 1) (hu2 : u 2 ∈ Set.Ico 0 1)
    (hu3 : u 3 ∈ Set.Ioo 0 1) (hu4 : u 4 ∈ Set.Ico 0 1) :
    TreeNormalized (proposal R T u).2.2 ∧ TreeNonnegative (proposal R T u).2.2 ∧
      TreeTemporalCover (proposal R T u).2.2 ∧
      treeLength (proposal R T u).2.2 ≤ treeLength T + 2 * (-Real.log (u 3)) := by
  obtain ⟨s, t, hcut, hs, hs0, hs1⟩ := cut_point_extant_clade T hL (u 1) (u 2) hu1 hu2
  have hbounds := cut_point_bounds T (u 1) (u 2) hu1.1 ⟨hu2.1, hu2.2.le⟩ s t hcut
  obtain ⟨i, _, hilo, _, _, htroot⟩ := hbounds
  have ht : 0 ≤ t := (hnonneg i).trans hilo
  have hcover := tree_chronology_temporal_cover T hN hchron
  have he : 0 ≤ -Real.log (u 3) :=
    neg_nonneg.mpr (Real.log_nonpos hu3.1.le hu3.2.le)
  have hbudget := attachment_time_budget_bound T hcover t (-Real.log (u 3)) ht he
  have hat := attachment_target_extant T hcover
    (attachmentTime T t (-Real.log (u 3))) (u 4) (ht.trans hbudget.1) hu4
  simp only [proposal, hcut]
  refine ⟨regraft_normalized _ _ _ _ _, regraft_nonnegative _ _ _ _ _ hnonneg ht,
    regraft_temporal_cover _ _ _ _ _ hnorm hchron ht hbudget.1 hs hs0 hs1 hat, ?_⟩
  exact (regraft_length_le T _ _ _ _ hnorm htroot hbudget.1).trans (by linarith [hbudget.2])

end Rhone.Coalescent.SmcPrime
