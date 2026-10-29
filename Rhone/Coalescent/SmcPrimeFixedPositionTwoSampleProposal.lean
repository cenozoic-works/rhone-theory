/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeRootGeometry

/-!
# One SMC′ proposal on the two-branch tree of two samples

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 1–7. -/

@[expose] public section

namespace Rhone.Coalescent.SmcPrime
open IntervalProcess

def twoSampleTree (h : ℝ) : Tree 2 := ⟨2, fun i => ({i}, 0, h)⟩

theorem twoSample_singleton_proper (i : Fin 2) :
    ¬ (({i} : Finset (Fin 2)) = ∅ ∨ ({i} : Finset (Fin 2)) = Finset.univ) := by
  fin_cases i <;> decide

theorem twoSampleTree_branchLength {h : ℝ} (hh : 0 < h) (i : Fin 2) :
    branchLength ((twoSampleTree h).2 i) = h := by
  change branchLength (({i} : Finset (Fin 2)), (0 : ℝ), h) = h
  simp [branchLength, hh.le]

theorem twoSampleTree_treeLength {h : ℝ} (hh : 0 < h) :
    treeLength (twoSampleTree h) = 2 * h := by
  change ∑ i : Fin 2, branchLength ((twoSampleTree h).2 i) = 2 * h
  simp only [twoSampleTree_branchLength hh, Fin.sum_univ_two]
  ring

theorem twoSampleTree_normalized {h : ℝ} (hh : 0 ≤ h) : TreeNormalized (twoSampleTree h) := by
  intro i
  exact ⟨hh, fun hc => absurd hc (twoSample_singleton_proper i)⟩

theorem twoSampleTree_rootHeight {h : ℝ} (hh : 0 < h) :
    rootHeight (twoSampleTree h) = h := by
  apply le_antisymm
  · exact root_height_le_of_branch_bounds _ h hh.le fun i _ => le_rfl
  · exact branch_hi_le_root (twoSampleTree h) (0 : Fin 2)
      (by rw [twoSampleTree_branchLength hh]; exact hh)

theorem twoSampleTree_activeBranches {h t : ℝ} (ht0 : 0 ≤ t) (hth : t < h) :
    activeBranches (twoSampleTree h) t = Finset.univ := by
  classical
  ext i
  have hb := twoSampleTree_branchLength (ht0.trans_lt hth) i
  simp only [activeBranches, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
  exact ⟨by rw [hb]; exact ht0.trans_lt hth, ht0, hth⟩

theorem twoSampleTree_cutPoint {h : ℝ} (hh : 0 < h) {u : ℝ} (hu1 : u < 1)
    (v : ℝ) :
    cutPoint (twoSampleTree h) u v =
      some ({if u < 1 / 2 then (0 : Fin 2) else 1}, h * v) := by
  have hl : List.finRange (twoSampleTree h).1 = [(0 : Fin 2), 1] := by
    change List.finRange 2 = _
    decide
  have hb0 : branchLength (({0} : Finset (Fin 2)), (0 : ℝ), h) = h :=
    twoSampleTree_branchLength hh 0
  have hb1 : branchLength (({1} : Finset (Fin 2)), (0 : ℝ), h) = h :=
    twoSampleTree_branchLength hh 1
  unfold cutPoint
  rw [hl, twoSampleTree_treeLength hh]
  by_cases hu : u < 1 / 2
  · have h1 : u * (2 * h) < h := by nlinarith
    have hu' : u < 2⁻¹ := by simpa using hu
    simp [chooseByRate, hb0, h1, hu', twoSampleTree]
  · have h1 : ¬ u * (2 * h) < h := by
      rw [not_lt] at hu ⊢
      nlinarith
    have h2 : u * (2 * h) - h < h := by nlinarith
    have hu' : ¬ u < 2⁻¹ := by simpa using hu
    simp [chooseByRate, hb0, hb1, h1, h2, hu', twoSampleTree]

theorem twoSampleTree_nextBoundary {h t : ℝ} (ht0 : 0 ≤ t) (hth : t < h) :
    nextBoundary (twoSampleTree h) t = h := by
  have hl : List.finRange (twoSampleTree h).1 = [(0 : Fin 2), 1] := by
    change List.finRange 2 = _
    decide
  unfold nextBoundary
  rw [hl, twoSampleTree_rootHeight (ht0.trans_lt hth)]
  simp [twoSampleTree, hth, not_lt.mpr ht0]

theorem twoSampleTree_attachmentTime {h t : ℝ} (ht0 : 0 ≤ t) (hth : t < h) (e : ℝ) :
    attachmentTime (twoSampleTree h) t e =
      if e < 2 * (h - t) then t + e / 2 else h + (e - 2 * (h - t)) := by
  have hr := twoSampleTree_rootHeight (ht0.trans_lt hth)
  have hrate : attachmentRate (twoSampleTree h) t = 2 := by
    simp [attachmentRate, hr, not_le.mpr hth, twoSampleTree_activeBranches ht0 hth]
    norm_num [twoSampleTree]
  have hstep : attachmentTime (twoSampleTree h) t e =
      if e < 2 * (h - t) then t + e / 2
      else attachmentAux (twoSampleTree h) 4 h (e - 2 * (h - t)) := by
    change attachmentAux (twoSampleTree h) (4 + 1) t e = _
    rw [attachmentAux]
    simp only [hr, not_le.mpr hth, ↓reduceIte, twoSampleTree_nextBoundary ht0 hth, hrate]
  rw [hstep]
  split_ifs
  · rfl
  · rw [attachmentAux]
    simp [hr]

noncomputable def twoSampleTargetClade (u : ℝ) : Finset (Fin 2) :=
  ((chooseByRate (fun _ : Fin 2 => (1 : ℝ)) (Finset.univ : Finset (Fin 2)).toList
      (u * 2)).map fun i => ({i} : Finset (Fin 2))).getD Finset.univ

theorem twoSampleTree_attachmentTarget_below {h a : ℝ} (ha0 : 0 ≤ a) (hah : a < h) (u : ℝ) :
    attachmentTarget (twoSampleTree h) a u = twoSampleTargetClade u := by
  have hr := twoSampleTree_rootHeight (ha0.trans_lt hah)
  unfold attachmentTarget twoSampleTargetClade
  have hc : ((Finset.univ : Finset (Fin (twoSampleTree h).1)).card : ℝ) = 2 := by
    change (((Finset.univ : Finset (Fin 2)).card : ℝ)) = 2
    simp
  simp only [hr, not_le.mpr hah, ↓reduceIte, twoSampleTree_activeBranches ha0 hah, hc]
  split <;> rename_i hx
  · have hx' : chooseByRate (fun _ : Fin 2 => (1 : ℝ)) (Finset.univ : Finset (Fin 2)).toList
        (u * 2) = none := hx
    rw [hx']
    rfl
  · have hx' : chooseByRate (fun _ : Fin 2 => (1 : ℝ)) (Finset.univ : Finset (Fin 2)).toList
        (u * 2) = some _ := hx
    rw [hx']
    rfl

theorem twoSampleTree_attachmentTarget_above {h a : ℝ} (hh : 0 < h) (hha : h ≤ a) (u : ℝ) :
    attachmentTarget (twoSampleTree h) a u = Finset.univ := by
  unfold attachmentTarget
  simp only [twoSampleTree_rootHeight hh, hha, ↓reduceIte]

theorem twoSampleTargetClade_singleton {u : ℝ} (hu1 : u < 1) :
    ∃ j : Fin 2, twoSampleTargetClade u = {j} := by
  have hlen : (Finset.univ : Finset (Fin 2)).toList.length = 2 := by
    rw [Finset.length_toList]
    rfl
  unfold twoSampleTargetClade
  match hl : (Finset.univ : Finset (Fin 2)).toList, hlen with
  | [x, y], _ =>
    by_cases h1 : u * 2 < 1
    · exact ⟨x, by simp [chooseByRate, h1]⟩
    · have h2 : u * 2 - 1 < 1 := by linarith
      exact ⟨y, by simp [chooseByRate, h1, h2]⟩

theorem treeOfList_branch_hi_le_rootHeight {N : ℕ} (l : List (Branch N)) (b : Branch N)
    (hb : b ∈ l) (hp : 0 < branchLength b) : b.2.2 ≤ rootHeight (treeOfList l) := by
  obtain ⟨i, rfl⟩ := List.get_of_mem hb
  exact branch_hi_le_root (treeOfList l) i hp

theorem treeOfList_rootHeight_le {N : ℕ} (l : List (Branch N)) (M : ℝ) (hM : 0 ≤ M)
    (h : ∀ b ∈ l, 0 < branchLength b → b.2.2 ≤ M) : rootHeight (treeOfList l) ≤ M :=
  root_height_le_of_branch_bounds _ M hM fun i hi => h _ (List.get_mem l i) hi

theorem finiteBranch_of_pos {N : ℕ} {c : Finset (Fin N)} {lo hi : ℝ}
    (hp : 0 < branchLength (finiteBranch c lo hi)) :
    ¬ (c = ∅ ∨ c = Finset.univ) ∧ lo < hi ∧ (finiteBranch c lo hi).2.2 = hi := by
  classical
  by_cases hc : c = ∅ ∨ c = Finset.univ
  · simp [branchLength, finiteBranch, hc] at hp
  · have hl : lo < hi := by
      by_contra hn
      simp [branchLength, finiteBranch, hc, max_eq_left (le_of_not_gt hn)] at hp
    exact ⟨hc, hl, by simp [finiteBranch, hc, max_eq_right hl.le]⟩

theorem finiteBranch_pos {N : ℕ} {c : Finset (Fin N)} {lo hi : ℝ}
    (hc : ¬ (c = ∅ ∨ c = Finset.univ)) (hl : lo < hi) :
    0 < branchLength (finiteBranch c lo hi) ∧ (finiteBranch c lo hi).2.2 = hi := by
  classical
  constructor
  · simp [branchLength, finiteBranch, hc, max_eq_right hl.le, hl]
  · simp [finiteBranch, hc, max_eq_right hl.le]

theorem twoSampleTree_regraft_self_rootHeight {h t a : ℝ} (ht0 : 0 ≤ t) (hta : t ≤ a)
    (hah : a < h) (i : Fin 2) :
    rootHeight (regraft (twoSampleTree h) {i} {i} t a) = h := by
  have hh : 0 < h := (ht0.trans hta).trans_lt hah
  have hr := twoSampleTree_rootHeight hh
  apply le_antisymm
  · have hle := regraft_root_height_le (twoSampleTree h) {i} {i} t a
      (twoSampleTree_normalized hh.le) (by rw [hr]; exact (hta.trans hah.le)) hta
    rwa [hr, max_eq_left hah.le] at hle
  · have hb : aboveAttachment ((twoSampleTree h).2 i) {i} {i} a = finiteBranch {i} a h := by
      simp [aboveAttachment, twoSampleTree, max_eq_right (ht0.trans hta)]
    obtain ⟨hpos, hhi⟩ := finiteBranch_pos (twoSample_singleton_proper i) hah
    have hmem := treeOfList_branch_hi_le_rootHeight _ _
      (List.mem_append_left
        [finiteBranch ({i} : Finset (Fin 2)) t a,
          finiteBranch (Finset.univ \ {i}) (rootHeight (twoSampleTree h)) a]
        (List.mem_append_right
          (((List.finRange (twoSampleTree h).1).map
              (fun k => belowCut ((twoSampleTree h).2 k) t)) ++
            ((List.finRange (twoSampleTree h).1).map
              (fun k => betweenCutAttachment ((twoSampleTree h).2 k) {i} t a)))
          ((List.mem_map (f := fun k =>
            aboveAttachment ((twoSampleTree h).2 k) {i} {i} a)).mpr
            ⟨i, List.mem_finRange i, hb⟩))) hpos
    rwa [hhi] at hmem

theorem twoSampleTree_regraft_attachment_le_rootHeight {h t a : ℝ} (hta : t < a)
    (i : Fin 2) (target : Finset (Fin 2)) :
    a ≤ rootHeight (regraft (twoSampleTree h) {i} target t a) := by
  obtain ⟨hpos, hhi⟩ := finiteBranch_pos (twoSample_singleton_proper i) hta
  have hmem := treeOfList_branch_hi_le_rootHeight _ _
    (List.mem_append_right
      ((((List.finRange (twoSampleTree h).1).map
          (fun k => belowCut ((twoSampleTree h).2 k) t)) ++
        ((List.finRange (twoSampleTree h).1).map
          (fun k => betweenCutAttachment ((twoSampleTree h).2 k) {i} t a))) ++
        ((List.finRange (twoSampleTree h).1).map
          (fun k => aboveAttachment ((twoSampleTree h).2 k) {i} target a)))
      (List.mem_cons_self (a := finiteBranch ({i} : Finset (Fin 2)) t a)
        (l := [finiteBranch (Finset.univ \ {i}) (rootHeight (twoSampleTree h)) a]))) hpos
  rwa [hhi] at hmem

theorem twoSampleTree_aboveAttachment_other {h a : ℝ} {i j : Fin 2} (hij : i ≠ j)
    (k : Fin 2) :
    branchLength (aboveAttachment ((twoSampleTree h).2 k) {i} {j} a) = 0 := by
  have hall : ∀ i j k : Fin 2, i ≠ j →
      ((((({k} : Finset (Fin 2)) \ {i}) ∪
        if (({k} : Finset (Fin 2)) ∩ {j}).Nonempty then {i} else ∅) = ∅) ∨
      (((({k} : Finset (Fin 2)) \ {i}) ∪
        if (({k} : Finset (Fin 2)) ∩ {j}).Nonempty then {i} else ∅) = Finset.univ)) := by
    decide
  have hclade := hall i j k hij
  by_contra hne
  have hp : 0 < branchLength (aboveAttachment ((twoSampleTree h).2 k) {i} {j} a) :=
    lt_of_le_of_ne (branchLength_nonneg _) (Ne.symm hne)
  unfold aboveAttachment at hp
  exact (finiteBranch_of_pos hp).1 (by convert hclade <;> rfl)

theorem twoSampleTree_regraft_other_rootHeight {h t a : ℝ} (ht0 : 0 ≤ t) (hta : t < a)
    {i j : Fin 2} (hij : i ≠ j) :
    rootHeight (regraft (twoSampleTree h) {i} {j} t a) = a := by
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
    · rw [twoSampleTree_aboveAttachment_other hij k] at hp
      exact absurd hp (lt_irrefl _)
    · rw [(finiteBranch_of_pos hp).2.2]
    · rw [(finiteBranch_of_pos hp).2.2]
  · exact twoSampleTree_regraft_attachment_le_rootHeight hta i {j}

theorem twoSampleTree_regraft_above_rootHeight {h t a : ℝ} (ht0 : 0 ≤ t) (hth : t < h)
    (hha : h ≤ a) (i : Fin 2) (target : Finset (Fin 2)) :
    rootHeight (regraft (twoSampleTree h) {i} target t a) = a := by
  have hh : 0 < h := ht0.trans_lt hth
  have hr := twoSampleTree_rootHeight hh
  apply le_antisymm
  · have hle := regraft_root_height_le (twoSampleTree h) {i} target t a
      (twoSampleTree_normalized hh.le) (by rw [hr]; exact hth.le) (hth.le.trans hha)
    rwa [hr, max_eq_right hha] at hle
  · exact twoSampleTree_regraft_attachment_le_rootHeight (hth.trans_le hha) i target

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 3–7. -/
theorem twoSampleTree_proposal_rootHeight (R : ℝ) {h : ℝ} (hh : 0 < h) (u : ProposalNoise)
    (hu : ∀ i, 0 < u i ∧ u i < 1) :
    rootHeight (proposal R (twoSampleTree h) u).2.2 =
      if -Real.log (u 3) < 2 * (h - h * u 2) then
        (if twoSampleTargetClade (u 4) = {if u 1 < 1 / 2 then (0 : Fin 2) else 1} then h
          else h * u 2 + -Real.log (u 3) / 2)
      else h + (-Real.log (u 3) - 2 * (h - h * u 2)) := by
  have ht0 : 0 ≤ h * u 2 := mul_nonneg hh.le (hu 2).1.le
  have hth : h * u 2 < h := by nlinarith [(hu 2).2]
  have he0 : 0 < -Real.log (u 3) := neg_pos.mpr (Real.log_neg (hu 3).1 (hu 3).2)
  have hcut := twoSampleTree_cutPoint hh (hu 1).2 (u 2)
  simp only [proposal, hcut, twoSampleTree_attachmentTime ht0 hth]
  by_cases he : -Real.log (u 3) < 2 * (h - h * u 2)
  · have hta : h * u 2 < h * u 2 + -Real.log (u 3) / 2 := by linarith
    have hah : h * u 2 + -Real.log (u 3) / 2 < h := by linarith
    simp only [he, ↓reduceIte, twoSampleTree_attachmentTarget_below (ht0.trans hta.le) hah]
    by_cases hself : twoSampleTargetClade (u 4) = {if u 1 < 1 / 2 then (0 : Fin 2) else 1}
    · simp only [hself, ↓reduceIte]
      exact twoSampleTree_regraft_self_rootHeight ht0 hta.le hah _
    · obtain ⟨j, hj⟩ := twoSampleTargetClade_singleton (hu 4).2
      have hij : (if u 1 < 1 / 2 then (0 : Fin 2) else 1) ≠ j := by
        intro hc
        exact hself (by rw [hj, hc])
      rw [hj] at hself
      rw [hj]
      simp only [hself, ↓reduceIte]
      exact twoSampleTree_regraft_other_rootHeight ht0 hta hij
  · have hha : h ≤ h + (-Real.log (u 3) - 2 * (h - h * u 2)) := by linarith
    simp only [he, ↓reduceIte]
    exact twoSampleTree_regraft_above_rootHeight ht0 hth hha _ _

end Rhone.Coalescent.SmcPrime
