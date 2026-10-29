/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.SmcPrimeRegraftCladeMap

/-!
# Classification of positive extant regraft branches into clade forms

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 1–7. -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
theorem regraft_active_clade_form {N : ℕ} (T : Tree N)
    (s target : Finset (Fin N)) (t a q : ℝ) (hnorm : TreeNormalized T)
    (ht : t ≤ rootHeight T) (_hta : t ≤ a)
    (i : Fin (regraft T s target t a).1)
    (hi : i ∈ activeBranches (regraft T s target t a) q) :
    (q < t ∧ ((regraft T s target t a).2 i).1 ∈ timeClades T q) ∨
    (t ≤ q ∧ q < a ∧
      (((regraft T s target t a).2 i).1 = s ∨
       ∃ c ∈ timeClades T q, ((regraft T s target t a).2 i).1 = c \ s)) ∨
    (a ≤ q ∧ ∃ c ∈ timeClades T q,
      ((regraft T s target t a).2 i).1 = regraftClade s target c) := by
  classical
  have hpos (c : Finset (Fin N)) (lo hi : ℝ)
      (hp : 0 < branchLength (finiteBranch c lo hi)) :
      lo < hi ∧ (finiteBranch c lo hi).2.2 = hi := by
    by_cases hc : c = ∅ ∨ c = Finset.univ
    · simp [branchLength, finiteBranch, hc] at hp
    · have hl : lo < hi := by
        by_contra hn
        simp [branchLength, finiteBranch, hc, max_eq_left (le_of_not_gt hn)] at hp
      exact ⟨hl, by simp [finiteBranch, hc, max_eq_right hl.le]⟩
  have hold (j : Fin T.1) (hlo : (T.2 j).2.1 ≤ q) (hhi : q < (T.2 j).2.2) :
      (T.2 j).1 ∈ timeClades T q := by
    have hd : (T.2 j).2.1 < (T.2 j).2.2 := hlo.trans_lt hhi
    have hc : ¬ ((T.2 j).1 = ∅ ∨ (T.2 j).1 = Finset.univ) := by
      intro hc
      linarith [(hnorm j).2 hc]
    have hp : 0 < branchLength (T.2 j) := by
      simp [branchLength, hc, max_eq_right (sub_nonneg.mpr hd.le), sub_pos.mpr hd]
    have hroot : q < rootHeight T := hhi.trans_le (branch_hi_le_root T j hp)
    simp only [timeClades, not_le.mpr hroot, ↓reduceIte, Finset.mem_image]
    exact ⟨j, by simp [activeBranches, hp, hlo, hhi], rfl⟩
  simp only [activeBranches, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  have himem := List.get_mem
    (((List.finRange T.1).map (fun j => belowCut (T.2 j) t)) ++
      ((List.finRange T.1).map (fun j => betweenCutAttachment (T.2 j) s t a)) ++
      ((List.finRange T.1).map (fun j => aboveAttachment (T.2 j) s target a)) ++
      [finiteBranch s t a, finiteBranch (Finset.univ \ s) (rootHeight T) a]) i
  change (regraft T s target t a).2 i ∈ _ at himem
  simp only [List.mem_append, List.mem_map, List.mem_cons,
    List.not_mem_nil, or_false] at himem
  rcases himem with ((⟨j, _, hj⟩ | ⟨j, _, hj⟩) | ⟨j, _, hj⟩) | (hj | hj)
  · rw [← hj] at hi ⊢
    have hh := (hpos _ _ _ hi.1).2
    have hqhi : q < min (T.2 j).2.2 t := by
      exact hi.2.2.trans_eq hh
    exact Or.inl ⟨(lt_min_iff.mp hqhi).2,
      hold j hi.2.1 (lt_min_iff.mp hqhi).1⟩
  · rw [← hj] at hi ⊢
    have hh := (hpos _ _ _ hi.1).2
    have hqhi : q < min (T.2 j).2.2 a := hi.2.2.trans_eq hh
    have hlo : (T.2 j).2.1 ≤ q := (le_max_left _ _).trans hi.2.1
    have htq : t ≤ q := (le_max_right _ _).trans hi.2.1
    exact Or.inr (Or.inl ⟨htq, (lt_min_iff.mp hqhi).2,
      Or.inr ⟨(T.2 j).1, hold j hlo (lt_min_iff.mp hqhi).1, rfl⟩⟩)
  · rw [← hj] at hi ⊢
    have hh := (hpos _ _ _ hi.1).2
    have hqhi : q < (T.2 j).2.2 := hi.2.2.trans_eq hh
    have hlo : (T.2 j).2.1 ≤ q := (le_max_left _ _).trans hi.2.1
    have haq : a ≤ q := (le_max_right _ _).trans hi.2.1
    exact Or.inr (Or.inr ⟨haq, (T.2 j).1, hold j hlo hqhi, rfl⟩)
  · rw [hj] at hi ⊢
    have hh := (hpos _ _ _ hi.1).2
    exact Or.inr (Or.inl ⟨hi.2.1, hi.2.2.trans_eq hh, Or.inl rfl⟩)
  · rw [hj] at hi ⊢
    have hh := (hpos _ _ _ hi.1).2
    have hqhi : q < a := hi.2.2.trans_eq hh
    have htq : t ≤ q := ht.trans hi.2.1
    have hfull : Finset.univ ∈ timeClades T q := by
      have hrq : rootHeight T ≤ q := hi.2.1
      simp [timeClades, hrq]
    exact Or.inr (Or.inl ⟨htq, hqhi, Or.inr ⟨Finset.univ, hfull, rfl⟩⟩)

end Rhone.Coalescent.SmcPrime
