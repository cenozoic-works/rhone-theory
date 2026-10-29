/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.SmcPrimeRegraftActiveGroups
/-!
# Regraft preservation of uniqueness of active branch-array indices

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime

theorem regraft_active_unique {N : ℕ} (T : Tree N)
    (s target : Finset (Fin N)) (t a : ℝ)
    (hnorm : TreeNormalized T) (hchron : TreeChronology T)
    (hunique : TreeActiveUnique T) (ht : 0 ≤ t) (hta : t ≤ a)
    (hs : s ∈ timeClades T t) (hs0 : s ≠ ∅) (hs1 : s ≠ Finset.univ)
    (ha : target ∈ timeClades T a) :
    TreeActiveUnique (regraft T s target t a) := by
  classical
  have htr : t ≤ rootHeight T := by
    by_contra hn
    have hr : rootHeight T ≤ t := (lt_of_not_ge hn).le
    simp only [timeClades, hr, ↓reduceIte, Finset.mem_singleton] at hs
    exact hs1 hs
  let B := (List.finRange T.1).map (fun i => belowCut (T.2 i) t)
  let M := (List.finRange T.1).map (fun i => betweenCutAttachment (T.2 i) s t a)
  let A := (List.finRange T.1).map (fun i => aboveAttachment (T.2 i) s target a)
  let D := finiteBranch s t a
  let I := finiteBranch (Finset.univ \ s) (rootHeight T) a
  change TreeActiveUnique (treeOfList (((B ++ M) ++ A) ++ [D, I]))
  simp only [List.append_assoc]
  apply treeOfList_active_unique_of_pairwise
  intro q hq
  have hB := below_cut_pairwise T hnorm hunique t q hq
  have hM := between_cut_pairwise T hnorm hchron hunique s t a q hq
  have hA := above_attachment_pairwise T hnorm hchron hunique s target a q
    (ht.trans hta) hq ha
  have hstem : [D, I].Pairwise (ActiveCladeDistinct q) := by
    simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq]
    refine ⟨?_, by simp, List.Pairwise.nil⟩
    intro _ _ he
    change s = Finset.univ \ s at he
    obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hs0
    have hxI : x ∈ Finset.univ \ s := by rwa [← he]
    exact (Finset.mem_sdiff.mp hxI).2 hx
  have hAstem : ∀ b ∈ A, ∀ c ∈ [D, I], ActiveCladeDistinct q b c := by
    intro b hb c hc hbact hcact _
    rcases List.mem_map.mp hb with ⟨i, _, rfl⟩
    have hab := (above_attachment_active T hnorm s target a q i hbact).2.1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · have hh := (finite_branch_active_iff _ _ _ _).mp hcact
      linarith [hh.2.2.2]
    · have hh := (finite_branch_active_iff _ _ _ _).mp hcact
      linarith [hh.2.2.2]
  have hMrest : ∀ b ∈ M, ∀ c ∈ A ++ [D, I], ActiveCladeDistinct q b c := by
    intro b hb c hc hbact hcact he
    rcases List.mem_map.mp hb with ⟨i, _, rfl⟩
    have hm := between_cut_active T hnorm s t a q i hbact
    rcases List.mem_append.mp hc with hc | hc
    · rcases List.mem_map.mp hc with ⟨j, _, rfl⟩
      have hab := (above_attachment_active T hnorm s target a q j hcact).2.1
      linarith [hm.2.2.1]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · change (T.2 i).1 \ s = s at he
        obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hm.2.2.2
        have hxs : x ∈ s := by rwa [← he]
        exact (Finset.mem_sdiff.mp hx).2 hxs
      · have hh := (finite_branch_active_iff _ _ _ _).mp hcact
        have hqr := hm.1.2.2.trans_le (branch_hi_le_root T i hm.1.1)
        linarith [hh.2.2.1]
  have hBrest : ∀ b ∈ B, ∀ c ∈ M ++ (A ++ [D, I]), ActiveCladeDistinct q b c := by
    intro b hb c hc hbact hcact _
    rcases List.mem_map.mp hb with ⟨i, _, rfl⟩
    have hqt := (below_cut_active T hnorm t q i hbact).2
    rcases List.mem_append.mp hc with hc | hc
    · rcases List.mem_map.mp hc with ⟨j, _, rfl⟩
      have htq := (between_cut_active T hnorm s t a q j hcact).2.1
      linarith
    · rcases List.mem_append.mp hc with hc | hc
      · rcases List.mem_map.mp hc with ⟨j, _, rfl⟩
        have haq := (above_attachment_active T hnorm s target a q j hcact).2.1
        linarith
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl
        · have hh := (finite_branch_active_iff _ _ _ _).mp hcact
          linarith [hh.2.2.1]
        · have hh := (finite_branch_active_iff _ _ _ _).mp hcact
          linarith [hh.2.2.1]
  exact List.pairwise_append.mpr ⟨hB,
    List.pairwise_append.mpr ⟨hM, List.pairwise_append.mpr ⟨hA, hstem, hAstem⟩,
      hMrest⟩, hBrest⟩
end Rhone.Coalescent.SmcPrime
