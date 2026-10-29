/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.SmcPrimeTreeProposal
public import Mathlib.Data.List.OfFn
public import Mathlib.Tactic.Linarith

/-!
# Length bounds for the SMC′ regrafted tree

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 1–7. -/

@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess
open scoped BigOperators

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
def TreeNormalized {N : ℕ} (T : Tree N) : Prop :=
  ∀ i, (T.2 i).2.1 ≤ (T.2 i).2.2 ∧
    ((T.2 i).1 = ∅ ∨ (T.2 i).1 = Finset.univ → (T.2 i).2.2 = (T.2 i).2.1)

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
theorem finite_branch_length_le {N : ℕ} (c : Finset (Fin N)) (lo hi : ℝ) :
    branchLength (finiteBranch c lo hi) ≤ max 0 (hi - lo) := by
  classical
  by_cases hc : c = ∅ ∨ c = Finset.univ
  · simp [finiteBranch, branchLength, hc]
  · by_cases hh : lo ≤ hi
    · simp [finiteBranch, branchLength, hc, max_eq_right hh]
    · have hh' : hi ≤ lo := le_of_not_ge hh
      simp [finiteBranch, branchLength, hc, max_eq_left hh']

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
theorem finite_branch_normalized {N : ℕ} (c : Finset (Fin N)) (lo hi : ℝ) :
    (finiteBranch c lo hi).2.1 ≤ (finiteBranch c lo hi).2.2 ∧
    ((finiteBranch c lo hi).1 = ∅ ∨ (finiteBranch c lo hi).1 = Finset.univ →
      (finiteBranch c lo hi).2.2 = (finiteBranch c lo hi).2.1) := by
  classical
  by_cases hc : c = ∅ ∨ c = Finset.univ
  · simp [finiteBranch, hc]
  · simp [finiteBranch, hc]

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
theorem tree_of_list_length {N : ℕ} (l : List (Branch N)) :
    treeLength (treeOfList l) = (l.map branchLength).sum := by
  change (∑ i : Fin l.length, branchLength (l.get i)) = _
  rw [← List.sum_ofFn]
  congr 1
  change List.ofFn (branchLength ∘ l.get) = _
  rw [← List.map_ofFn, List.ofFn_get]

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
theorem regraft_normalized {N : ℕ} (T : Tree N)
    (s target : Finset (Fin N)) (t a : ℝ) : TreeNormalized (regraft T s target t a) := by
  intro i
  have hbranch : ∀ b ∈
      (((List.finRange T.1).map (fun j => belowCut (T.2 j) t)) ++
        ((List.finRange T.1).map (fun j => betweenCutAttachment (T.2 j) s t a)) ++
        ((List.finRange T.1).map (fun j => aboveAttachment (T.2 j) s target a)) ++
        [finiteBranch s t a, finiteBranch (Finset.univ \ s) (rootHeight T) a]),
      b.2.1 ≤ b.2.2 ∧ (b.1 = ∅ ∨ b.1 = Finset.univ → b.2.2 = b.2.1) := by
    intro b hb
    simp only [List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with ((⟨j, _, rfl⟩ | ⟨j, _, rfl⟩) | ⟨j, _, rfl⟩) | (rfl | rfl)
    · exact finite_branch_normalized _ _ _
    · exact finite_branch_normalized _ _ _
    · exact finite_branch_normalized _ _ _
    · exact finite_branch_normalized _ _ _
    · exact finite_branch_normalized _ _ _
  exact hbranch _ (List.get_mem _ i)

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
theorem clipped_branch_lengths_le {N : ℕ} (b : Branch N)
    (s target : Finset (Fin N)) (t a : ℝ) (hta : t ≤ a)
    (hb : b.2.1 ≤ b.2.2 ∧ (b.1 = ∅ ∨ b.1 = Finset.univ → b.2.2 = b.2.1)) :
    branchLength (belowCut b t) + branchLength (betweenCutAttachment b s t a) +
      branchLength (aboveAttachment b s target a) ≤ branchLength b := by
  classical
  have h1 := finite_branch_length_le b.1 b.2.1 (min b.2.2 t)
  have h2 := finite_branch_length_le (b.1 \ s) (max b.2.1 t) (min b.2.2 a)
  have h3 := finite_branch_length_le
    ((b.1 \ s) ∪ if (b.1 ∩ target).Nonempty then s else ∅) (max b.2.1 a) b.2.2
  change branchLength (belowCut b t) ≤ max 0 (min b.2.2 t - b.2.1) at h1
  change branchLength (betweenCutAttachment b s t a) ≤
    max 0 (min b.2.2 a - max b.2.1 t) at h2
  change branchLength (aboveAttachment b s target a) ≤ max 0 (b.2.2 - max b.2.1 a) at h3
  have hsum : max 0 (min b.2.2 t - b.2.1) + max 0 (min b.2.2 a - max b.2.1 t) +
      max 0 (b.2.2 - max b.2.1 a) = b.2.2 - b.2.1 := by
    simp only [max_def, min_def]
    split_ifs <;> linarith [hb.1]
  by_cases hc : b.1 = ∅ ∨ b.1 = Finset.univ
  · have hz := hb.2 hc
    have hbl : branchLength b = 0 := by simp [branchLength, hc]
    rw [hbl]
    linarith
  · have hbl : branchLength b = b.2.2 - b.2.1 := by
      simp [branchLength, hc, max_eq_right (sub_nonneg.mpr hb.1)]
    rw [hbl]
    linarith

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
theorem regraft_length_le {N : ℕ} (T : Tree N)
    (s target : Finset (Fin N)) (t a : ℝ) (hT : TreeNormalized T)
    (ht : t ≤ rootHeight T) (hta : t ≤ a) :
    treeLength (regraft T s target t a) ≤ treeLength T + 2 * (a - t) := by
  have hsum (f : Fin T.1 → ℝ) : ((List.finRange T.1).map f).sum = ∑ i, f i := by
    rw [← List.sum_toFinset _ (List.nodup_finRange _), List.toFinset_finRange]
  have hpieces := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => clipped_branch_lengths_le (T.2 i) s target t a hta (hT i))
  simp only [Finset.sum_add_distrib] at hpieces
  have hs : branchLength (finiteBranch s t a) ≤ a - t := by
    simpa only [max_eq_right (sub_nonneg.mpr hta)] using finite_branch_length_le s t a
  have hr : branchLength (finiteBranch (Finset.univ \ s) (rootHeight T) a) ≤ a - t := by
    apply (finite_branch_length_le _ _ _).trans
    exact max_le (sub_nonneg.mpr hta) (by linarith)
  unfold regraft
  rw [tree_of_list_length]
  simp only [List.map_append, List.sum_append, List.map_map, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, hsum, Function.comp_apply, add_zero]
  unfold treeLength
  linarith

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
theorem root_height_nonneg {N : ℕ} (T : Tree N) : 0 ≤ rootHeight T := by
  have h (l : List ℝ) : 0 ≤ l.foldr max 0 := by
    induction l with
    | nil => exact le_rfl
    | cons b rest ih => exact ih.trans (le_max_right _ _)
  exact h _

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
theorem branch_hi_le_root {N : ℕ} (T : Tree N) (i : Fin T.1)
    (hi : 0 < branchLength (T.2 i)) : (T.2 i).2.2 ≤ rootHeight T := by
  have h (l : List ℝ) : ∀ x ∈ l, x ≤ l.foldr max 0 := by
    induction l with
    | nil => simp
    | cons b rest ih =>
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact le_max_left _ _
      · exact (ih x hx).trans (le_max_right _ _)
  apply h
  exact List.mem_map.mpr ⟨i, by simp, by simp [hi]⟩

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/
theorem cut_point_bounds {N : ℕ} (T : Tree N) (u v : ℝ)
    (hu : 0 ≤ u) (hv : v ∈ Set.Icc 0 1) (s : Finset (Fin N)) (t : ℝ)
    (hcut : cutPoint T u v = some (s, t)) :
    ∃ i : Fin T.1, (T.2 i).1 = s ∧ (T.2 i).2.1 ≤ t ∧ t ≤ (T.2 i).2.2 ∧
      0 < branchLength (T.2 i) ∧ t ≤ rootHeight T := by
  have hpositive (rate : Fin T.1 → ℝ) (l : List (Fin T.1)) (x : ℝ) (a : Fin T.1)
      (hx : 0 ≤ x) (hsel : chooseByRate rate l x = some a) : 0 < rate a := by
    induction l generalizing x with
    | nil => simp [chooseByRate] at hsel
    | cons b rest ih =>
      by_cases hc : x < rate b
      · have he : b = a := by simpa [chooseByRate, hc] using hsel
        subst a
        linarith
      · have hr : chooseByRate rate rest (x - rate b) = some a := by
          simpa only [chooseByRate, ite_eq_right hc] using hsel
        exact ih (x - rate b) (by linarith) hr
  cases hsel : chooseByRate (fun i => branchLength (T.2 i))
      (List.finRange T.1) (u * treeLength T) with
  | none => simp [cutPoint, hsel] at hcut
  | some i =>
    have hi := hpositive (fun j => branchLength (T.2 j)) (List.finRange T.1)
      (u * treeLength T) i (mul_nonneg hu (treeLength_nonneg T)) hsel
    have he : (T.2 i).1 = s ∧
        (T.2 i).2.1 + ((T.2 i).2.2 - (T.2 i).2.1) * v = t := by
      simpa [cutPoint, hsel] using hcut
    have hd : 0 < (T.2 i).2.2 - (T.2 i).2.1 := by
      by_contra hn
      have hz : branchLength (T.2 i) = 0 := by
        simp [branchLength, max_eq_left (le_of_not_gt hn)]
      linarith
    have hlo : (T.2 i).2.1 ≤ t := by nlinarith [mul_nonneg hd.le hv.1, he.2]
    have hhi : t ≤ (T.2 i).2.2 := by
      nlinarith [mul_le_mul_of_nonneg_left hv.2 hd.le, he.2]
    exact ⟨i, he.1, hlo, hhi, hi, hhi.trans (branch_hi_le_root T i hi)⟩

end Rhone.Coalescent.SmcPrime
