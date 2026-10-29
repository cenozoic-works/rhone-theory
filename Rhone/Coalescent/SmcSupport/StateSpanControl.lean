/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcSupport.SpanControl
public import Rhone.Coalescent.SmcSupport.Selector
public import Rhone.Coalescent.SmcSupport.StateMeasurable
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.List.Lemmas

/-! # Hull span control for the contact sampler -/
@[expose] public section
namespace Rhone.Coalescent.SmcSupport
open IntervalProcess MeasureTheory

noncomputable def totalHullSpan (s : State) : ℝ := ∑ i, hullLength (s.2.2.2 i).2

theorem totalHullSpan_measurable : Measurable totalHullSpan := by
  have h : Measurable (fun l : LiveState => ∑ i, hullLength (l.2 i).2) := by
    apply measurable_sigma_of_fibers
    intro m
    change Measurable (fun a : Fin m → ℕ × Material => ∑ i, hullLength (a i).2)
    exact Finset.measurable_sum _ (fun i _ =>
      hullLength_measurable.comp (measurable_pi_apply i).snd)
  exact h.comp measurable_snd.snd

theorem totalHullSpan_initial (n : ℕ) : totalHullSpan (initialState n) = n := by
  simp only [totalHullSpan, initialState, hullLength, hullLo, hullHi]
  norm_num
  change (Finset.univ : Finset (Fin n)).card = n
  simp

theorem totalHullSpan_liveOfList (t : ℝ) (fresh : ℕ) (l : List (ℕ × Material)) :
    totalHullSpan (t, fresh, liveOfList l) = (l.map (fun p => hullLength p.2)).sum := by
  exact Fin.sum_univ_fun_getElem l (fun p => hullLength p.2)

theorem totalHullSpan_coalSuccessor_le (s : State) (hs : Valid s)
    (i j : Fin s.2.2.1) (hc : touches (s.2.2.2 i).2 (s.2.2.2 j).2) :
    totalHullSpan (coalSuccessor s i j) ≤ totalHullSpan s := by
  classical
  by_cases hij : i.val < j.val
  · have hne : i ≠ j := by intro h; subst j; omega
    have he : (List.finRange s.2.2.1).filter (fun k => k ≠ i ∧ k ≠ j) =
        ((List.finRange s.2.2.1).erase i).erase j := by
      rw [(List.nodup_finRange _).erase i |>.erase_eq_filter j,
        (List.nodup_finRange _).erase_eq_filter i, List.filter_filter]
      congr 1
      funext k
      by_cases hki : k = i <;> by_cases hkj : k = j <;> simp [hki, hkj]
    have hi := List.sum_map_erase (fun k : Fin s.2.2.1 => hullLength (s.2.2.2 k).2)
      (l := List.finRange s.2.2.1) (a := i) (by simp)
    have hj := List.sum_map_erase (fun k : Fin s.2.2.1 => hullLength (s.2.2.2 k).2)
      (l := (List.finRange s.2.2.1).erase i) (a := j) (by simp [hne.symm])
    have hall : ((List.finRange s.2.2.1).map
        (fun k => hullLength (s.2.2.2 k).2)).sum = totalHullSpan s := by
      rw [← List.sum_toFinset _ (List.nodup_finRange _)]
      simp [totalHullSpan]
    have hm := hullLength_merge_le _ _ (hs.2.1 i) (hs.2.1 j) hc
    simp only [coalSuccessor, ite_eq_left hij]
    rw [totalHullSpan_liveOfList, List.map_append, List.sum_append]
    simp only [List.map_map, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Function.comp_def, add_zero]
    rw [he]
    linarith
  · simp only [coalSuccessor, ite_eq_right hij]
    exact le_rfl

theorem totalHullSpan_splitSuccessor_le (s : State) (hs : Valid s)
    (i : Fin s.2.2.1) (x : ℝ) (hlo : hullLo (s.2.2.2 i).2 < x)
    (hhi : x < hullHi (s.2.2.2 i).2) :
    totalHullSpan (splitSuccessor s i x) ≤ totalHullSpan s := by
  classical
  have he : (List.finRange s.2.2.1).filter (fun k => k ≠ i) =
      (List.finRange s.2.2.1).erase i := by
    rw [(List.nodup_finRange _).erase_eq_filter]
    congr 1
  have hi := List.sum_map_erase (fun k : Fin s.2.2.1 => hullLength (s.2.2.2 k).2)
    (l := List.finRange s.2.2.1) (a := i) (by simp)
  have hall : ((List.finRange s.2.2.1).map
      (fun k => hullLength (s.2.2.2 k).2)).sum = totalHullSpan s := by
    rw [← List.sum_toFinset _ (List.nodup_finRange _)]
    simp [totalHullSpan]
  have hm := hullLength_split_le _ (hs.2.1 i) x hlo hhi
  unfold splitSuccessor
  rw [totalHullSpan_liveOfList, List.map_append, List.sum_append]
  simp only [List.map_map, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Function.comp_def, add_zero]
  rw [he]
  linarith

theorem sampleStep_totalHullSpan_le (R : ℝ) (s : State) (hs : Valid s)
    (u : Noise) (hu0 : 0 ≤ u 0) (hu1 : u 0 < 1)
    (hc0 : 0 < u 2) (hc1 : u 2 < 1) :
    totalHullSpan (sampleStep true R s u).1 ≤ totalHullSpan s := by
  classical
  unfold sampleStep
  split_ifs with hstop
  · exact le_rfl
  · have ht : 0 < totalRate true R s :=
      lt_of_le_of_ne (by positivity) (Ne.symm (fun h => hstop (Or.inr h)))
    obtain ⟨a, ha, hp⟩ := selectedAction_exists_positive true R s u hu0 hu1 ht
    rw [ha]
    cases a with
    | inl ij =>
      have hc : touches (s.2.2.2 ij.1).2 (s.2.2.2 ij.2).2 := by
        by_contra hn
        simp [candidateRate, hn] at hp
      exact totalHullSpan_coalSuccessor_le s hs ij.1 ij.2 hc
    | inr i =>
      have hx := affine_cut_interior _ (hs.2.1 i) (u 2) hc0 hc1
      exact totalHullSpan_splitSuccessor_le s hs i _ hx.1 hx.2

end Rhone.Coalescent.SmcSupport
