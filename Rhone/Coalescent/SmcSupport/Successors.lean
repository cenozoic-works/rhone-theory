/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcSupport.Material
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.List.FinRange

/-! # Concrete interval-material support and finite race calculations -/
@[expose] public section

namespace Rhone.Coalescent.SmcSupport
open IntervalProcess

theorem initialState_valid (n : ℕ) : Valid (initialState n) := by
  constructor
  · norm_num [initialState]
  constructor
  · intro i
    change MaterialValid ⟨0, fun _ => (0, 1)⟩
    constructor
    · intro j
      norm_num [initialState]
    · exact ⟨0, by norm_num [initialState]⟩
  constructor
  · intro i
    exact i.isLt
  · intro i j hij
    exact Fin.ext hij

theorem filter_two_length {m : ℕ} (i j : Fin m) (hij : i ≠ j) :
    ((List.finRange m).filter (fun k => k ≠ i ∧ k ≠ j)).length = m - 2 := by
  have hne : j ∈ (List.finRange m).erase i := by simp [hij.symm]
  have he : (List.finRange m).filter (fun k => k ≠ i ∧ k ≠ j) =
      ((List.finRange m).erase i).erase j := by
    rw [(List.nodup_finRange m).erase i |>.erase_eq_filter j,
      (List.nodup_finRange m).erase_eq_filter i, List.filter_filter]
    congr 1
    funext k
    by_cases hki : k = i <;> by_cases hkj : k = j <;> simp [hki, hkj]
  rw [he, List.length_erase_of_mem hne,
    List.length_erase_of_mem (by simp), List.length_finRange]
  omega

theorem coalSuccessor_count (s : State) (i j : Fin s.2.2.1)
    (hij : i.val < j.val) : (coalSuccessor s i j).2.2.1 + 1 = s.2.2.1 := by
  have hne : i ≠ j := by intro h; subst j; omega
  have hm : 2 ≤ s.2.2.1 := by have := j.isLt; omega
  simp only [coalSuccessor, ite_eq_left hij, liveOfList, List.length_append,
    List.length_map, List.length_singleton]
  rw [filter_two_length i j hne]
  omega

theorem splitSuccessor_count (s : State) (i : Fin s.2.2.1) (x : ℝ) :
    (splitSuccessor s i x).2.2.1 = s.2.2.1 + 1 := by
  have hm : 1 ≤ s.2.2.1 := by have := i.isLt; omega
  have he : (List.finRange s.2.2.1).filter (fun k => k ≠ i) =
      (List.finRange s.2.2.1).erase i := by
    rw [(List.nodup_finRange _).erase_eq_filter]
    congr 1
  simp only [splitSuccessor, liveOfList, List.length_append, List.length_map,
    List.length_cons, List.length_nil]
  rw [he, List.length_erase_of_mem (by simp), List.length_finRange]
  omega

theorem valid_liveOfList (t : ℝ) (fresh : ℕ) (l : List (ℕ × Material))
    (ht : 0 ≤ t) (hm : ∀ p ∈ l, MaterialValid p.2)
    (hf : ∀ p ∈ l, p.1 < fresh) (hn : (l.map Prod.fst).Nodup) :
    Valid (t, fresh, liveOfList l) := by
  refine ⟨ht, ?_, ?_, ?_⟩
  · intro i
    exact hm (l.get i) (List.get_mem _ _)
  · intro i
    exact hf (l.get i) (List.get_mem _ _)
  · intro i j hij
    have hi : (l.map Prod.fst).get
        ⟨i.val, by rw [List.length_map]; exact i.isLt⟩ =
        (l.map Prod.fst).get ⟨j.val, by rw [List.length_map]; exact j.isLt⟩ := by
      simpa [liveOfList] using hij
    have he := hn.get_inj_iff.mp hi
    exact Fin.ext (congrArg (fun k : Fin (l.map Prod.fst).length => k.val) he)

theorem coalSuccessor_valid (s : State) (hs : Valid s)
    (i j : Fin s.2.2.1) : Valid (coalSuccessor s i j) := by
  classical
  unfold coalSuccessor
  split_ifs with hij
  · let survivors := (List.finRange s.2.2.1).filter (fun k => k ≠ i ∧ k ≠ j)
    let freshMaterial := mergeMaterial (s.2.2.2 i).2 (s.2.2.2 j).2
    apply valid_liveOfList s.1 (s.2.1 + 1)
      (survivors.map s.2.2.2 ++ [(s.2.1, freshMaterial)]) hs.1
    · intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
        exact hs.2.1 k
      · have he : p = (s.2.1, freshMaterial) := by simpa using hp
        rw [he]
        exact mergeMaterial_valid _ _ (hs.2.1 i) (hs.2.1 j)
    · intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
        exact lt_trans (hs.2.2.1 k) (Nat.lt_succ_self _)
      · have he : p = (s.2.1, freshMaterial) := by simpa using hp
        rw [he]
        exact Nat.lt_succ_self _
    · simp only [List.map_append, List.map_map, List.map_cons, List.map_nil]
      apply List.nodup_append.mpr
      refine ⟨?_, by simp, ?_⟩
      · exact (List.nodup_finRange s.2.2.1).filter _ |>.map hs.2.2.2
      · intro a ha b hb
        have hb' : b = s.2.1 := by simpa using hb
        obtain ⟨k, hk, hk'⟩ := List.mem_map.mp ha
        rw [hb', ← hk']
        exact (hs.2.2.1 k).ne
  · exact hs

theorem splitSuccessor_full_valid (s : State) (hs : Valid s)
    (hf : ∀ i, FullAtoms (s.2.2.2 i).2)
    (i : Fin s.2.2.1) (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    Valid (splitSuccessor s i x) := by
  classical
  let survivors := (List.finRange s.2.2.1).filter (fun k => k ≠ i)
  let daughters := splitMaterial (s.2.2.2 i).2 x
  obtain ⟨hl, hr⟩ := first_split_atoms _ (hf i) x hx0 hx1
  have hvl : MaterialValid daughters.1 := by
    constructor
    · intro j
      rw [hl j]
      exact ⟨le_rfl, hx0.le, hx1.le⟩
    · exact ⟨0, by rw [hl 0]; exact hx0⟩
  have hvr : MaterialValid daughters.2 := by
    constructor
    · intro j
      rw [hr j]
      exact ⟨hx0.le, hx1.le, le_rfl⟩
    · exact ⟨0, by rw [hr 0]; exact hx1⟩
  apply valid_liveOfList s.1 (s.2.1 + 2)
    (survivors.map s.2.2.2 ++ [(s.2.1, daughters.1), (s.2.1 + 1, daughters.2)]) hs.1
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
      exact hs.2.1 k
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl
      · exact hvl
      · exact hvr
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
      have := hs.2.2.1 k
      omega
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl <;> dsimp <;> omega
  · simp only [List.map_append, List.map_map, List.map_cons, List.map_nil]
    apply List.nodup_append.mpr
    refine ⟨?_, by simp, ?_⟩
    · exact (List.nodup_finRange s.2.2.1).filter _ |>.map hs.2.2.2
    · intro a ha b hb
      obtain ⟨k, hk, hk'⟩ := List.mem_map.mp ha
      have hka := hs.2.2.1 k
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
      rcases hb with rfl | rfl <;> rw [← hk'] <;> dsimp at * <;> omega

end Rhone.Coalescent.SmcSupport
