/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.SmcPrimeTreeChronology
public import Rhone.Coalescent.SmcSupport.Selector

/-!
# Cut point and attachment target of an SMC′ proposal lie on extant clades

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 1–7. -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
theorem cut_point_extant_clade {N : ℕ} (T : Tree N) (hL : 0 < treeLength T)
    (u v : ℝ) (hu : u ∈ Set.Ico 0 1) (hv : v ∈ Set.Ico 0 1) :
    ∃ s t, cutPoint T u v = some (s, t) ∧ s ∈ timeClades T t ∧
      s ≠ ∅ ∧ s ≠ Finset.univ := by
  classical
  have hsum : ((List.finRange T.1).map (fun i => branchLength (T.2 i))).sum =
      treeLength T := by
    rw [← List.sum_toFinset _ (List.nodup_finRange _), List.toFinset_finRange]
    rfl
  obtain ⟨i, hi, hp⟩ := SmcSupport.chooseByRate_exists_positive
    (fun i => branchLength (T.2 i)) (List.finRange T.1)
    (fun _ _ => branchLength_nonneg _) (u * treeLength T) (mul_nonneg hu.1 hL.le)
    (by rw [hsum]; nlinarith [hu.2])
  have hproper : ¬ ((T.2 i).1 = ∅ ∨ (T.2 i).1 = Finset.univ) := by
    intro hc
    simp [branchLength, hc] at hp
  have hd : 0 < (T.2 i).2.2 - (T.2 i).2.1 := by
    by_contra hn
    simp [branchLength, hproper, max_eq_left (le_of_not_gt hn)] at hp
  let t := (T.2 i).2.1 + ((T.2 i).2.2 - (T.2 i).2.1) * v
  have htlo : (T.2 i).2.1 ≤ t := by
    dsimp [t]
    nlinarith [mul_nonneg hd.le hv.1]
  have hthi : t < (T.2 i).2.2 := by
    dsimp [t]
    nlinarith [mul_lt_mul_of_pos_left hv.2 hd]
  have htroot : t < rootHeight T := hthi.trans_le (branch_hi_le_root T i hp)
  refine ⟨(T.2 i).1, t, by simp [cutPoint, hi, t], ?_, (not_or.mp hproper).1,
    (not_or.mp hproper).2⟩
  simp only [timeClades, not_le.mpr htroot, ↓reduceIte, Finset.mem_image]
  exact ⟨i, by simp [activeBranches, hp, htlo, hthi], rfl⟩

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
theorem attachment_target_extant {N : ℕ} (T : Tree N)
    (hT : TreeTemporalCover T) (a u : ℝ) (ha : 0 ≤ a) (hu : u ∈ Set.Ico 0 1) :
    attachmentTarget T a u ∈ timeClades T a := by
  classical
  by_cases hr : rootHeight T ≤ a
  · simp [attachmentTarget, timeClades, hr]
  · have hactive := hT a ha (lt_of_not_ge hr)
    have hc : 0 < ((activeBranches T a).card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr hactive
    have hsum : ((activeBranches T a).toList.map (fun _ => (1 : ℝ))).sum =
        (activeBranches T a).card := by simp
    obtain ⟨i, hi, _⟩ := SmcSupport.chooseByRate_exists_positive
      (fun _ : Fin T.1 => (1 : ℝ)) (activeBranches T a).toList
      (fun _ _ => by norm_num) (u * (activeBranches T a).card)
      (mul_nonneg hu.1 hc.le) (by rw [hsum]; nlinarith [hu.2])
    have himem : i ∈ activeBranches T a := by
      exact Finset.mem_toList.mp (chooseByRate_mem _ _ _ _ hi)
    simp only [attachmentTarget, timeClades, hr, ↓reduceIte, hi, Finset.mem_image]
    exact ⟨i, himem, rfl⟩

end Rhone.Coalescent.SmcPrime
