/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.FiniteIntervalMaterialSelection
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Data.List.Nodup
public import Mathlib.Algebra.Order.BigOperators.Group.List

/-! # Probabilities of cumulative-rate selection intervals under a uniform mark -/
@[expose] public section

namespace Rhone.Coalescent.IntervalProcess
open MeasureTheory
open scoped ENNReal

theorem chooseByRate_mem {α : Type*} (rate : α → ℝ) (l : List α) (x : ℝ) (a : α)
    (h : chooseByRate rate l x = some a) : a ∈ l := by
  induction l generalizing x with
  | nil => simp [chooseByRate] at h
  | cons b rest ih =>
    by_cases hc : x < rate b
    · simp [chooseByRate, hc] at h
      simp [h]
    · simp only [chooseByRate, ite_eq_right hc] at h
      exact List.mem_cons_of_mem b (ih (x-rate b) h)

theorem chooseByRate_prefix_interval_general {α : Type*}
    (rate : α → ℝ) (before after : List α) (a : α)
    (hb : a ∉ before) (ha : a ∉ after)
    (hr : ∀ b ∈ before, 0 ≤ rate b) (x : ℝ) (hx : 0 ≤ x) :
    chooseByRate rate (before ++ a :: after) x = some a ↔
      (before.map rate).sum ≤ x ∧ x < (before.map rate).sum + rate a := by
  classical
  induction before generalizing x with
  | nil =>
    by_cases hc : x < rate a
    · simp [chooseByRate, hc, hx]
    · have hnone : chooseByRate rate after (x-rate a) ≠ some a := by
        intro he
        exact ha (chooseByRate_mem rate after (x-rate a) a he)
      simp [chooseByRate, hc, hnone]
  | cons b rest ih =>
    have hab : a ≠ b := fun he => hb (by simp [he])
    have hrest : a ∉ rest := fun he => hb (by simp [he])
    have hrb : 0 ≤ rate b := hr b (by simp)
    have hrr : ∀ c ∈ rest, 0 ≤ rate c := fun c hc => hr c (by simp [hc])
    have hs : 0 ≤ (rest.map rate).sum := List.sum_nonneg (by
      intro y hy
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hy
      exact hrr c hc)
    by_cases hc : x < rate b
    · simp only [List.cons_append, chooseByRate, ite_eq_left hc, Option.some.injEq,
        List.map_cons, List.sum_cons]
      constructor
      · intro he; exact (hab he.symm).elim
      · intro he; exfalso; linarith [he.1]
    · simp only [List.cons_append, chooseByRate, ite_eq_right hc,
        List.map_cons, List.sum_cons]
      rw [ih hrest hrr (x-rate b) (by linarith)]
      constructor <;> rintro ⟨hlo, hhi⟩ <;> constructor <;> linarith

theorem unitUniform_Ico (a b : ℝ) (ha : 0 ≤ a) (hb : b ≤ 1) :
    unitUniform (Set.Ico a b) = ENNReal.ofReal (b-a) := by
  rw [unitUniform, Measure.restrict_apply measurableSet_Ico]
  by_cases hz : a = 0
  · subst a
    have heq : Set.Ico 0 b ∩ Set.Ioo 0 1 = Set.Ioo 0 b := by
      ext u
      simp only [Set.mem_inter_iff, Set.mem_Ico, Set.mem_Ioo]
      constructor <;> rintro ⟨h1, h2⟩
      · exact ⟨h2.1, h1.2⟩
      · exact ⟨⟨h1.le, h2⟩, h1, lt_of_lt_of_le h2 hb⟩
    rw [heq, Real.volume_Ioo]
  · have heq : Set.Ico a b ∩ Set.Ioo 0 1 = Set.Ico a b := by
      apply Set.inter_eq_left.mpr
      intro u hu
      exact ⟨lt_of_lt_of_le (lt_of_le_of_ne ha (Ne.symm hz)) hu.1,
        lt_of_lt_of_le hu.2 hb⟩
    rw [heq, Real.volume_Ico]

theorem chooseByRate_uniform_mass_general {α : Type*}
    (rate : α → ℝ) (l : List α) (hn : l.Nodup)
    (hr : ∀ b ∈ l, 0 ≤ rate b) (ht : 0 < (l.map rate).sum)
    (a : α) (ha : a ∈ l) :
    unitUniform {u | chooseByRate rate l (u * (l.map rate).sum) = some a} =
      ENNReal.ofReal (rate a / (l.map rate).sum) := by
  classical
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace (Option α) := ⊤
  obtain ⟨before, after, rfl⟩ := List.mem_iff_append.mp ha
  have hbefore : a ∉ before := by
    intro ham
    exact (List.disjoint_left.mp hn.disjoint) ham (by simp)
  have hafter : a ∉ after := (List.nodup_cons.mp hn.of_append_right).1
  have hrb : ∀ b ∈ before, 0 ≤ rate b := fun b h => hr b (by simp [h])
  have hra : ∀ b ∈ after, 0 ≤ rate b := fun b h => hr b (by simp [h])
  let T := ((before ++ a :: after).map rate).sum
  let p := (before.map rate).sum
  let q := (after.map rate).sum
  have hp : 0 ≤ p := List.sum_nonneg (by
    intro y hy
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hy
    exact hrb b hb)
  have hq : 0 ≤ q := List.sum_nonneg (by
    intro y hy
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hy
    exact hra b hb)
  have hdecomp : T = p + rate a + q := by simp [T, p, q, List.sum_append]; ring
  have hl : 0 ≤ p/T := div_nonneg hp ht.le
  have hu : (p+rate a)/T ≤ 1 := (div_le_one ht).2 (by linarith)
  have hm : Measurable (fun u : ℝ =>
      chooseByRate rate (before ++ a :: after) (u*T)) :=
    chooseByRate_measurable (fun b _ => rate b) (fun _ => measurable_const)
      _ (fun u => u*T) (measurable_id.mul_const T)
  have hs : MeasurableSet {u : ℝ |
      chooseByRate rate (before ++ a :: after) (u*T) = some a} :=
    hm (show MeasurableSet ({some a} : Set (Option α)) from by trivial)
  have heq : {u : ℝ | chooseByRate rate (before ++ a :: after) (u*T) = some a} ∩
      Set.Ioo 0 1 = Set.Ico (p/T) ((p+rate a)/T) ∩ Set.Ioo 0 1 := by
    ext u
    by_cases hui : u ∈ Set.Ioo (0 : ℝ) 1
    · have hx : 0 ≤ u*T := mul_nonneg hui.1.le ht.le
      have hi := chooseByRate_prefix_interval_general rate before after a
        hbefore hafter hrb (u*T) hx
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, hui, and_true,
        Set.mem_Ico]
      rw [hi, div_le_iff₀ ht, lt_div_iff₀ ht]
    · simp [hui]
  calc
    _ = volume ({u : ℝ | chooseByRate rate (before ++ a :: after) (u*T) = some a} ∩
        Set.Ioo 0 1) := by rw [unitUniform, Measure.restrict_apply hs]
    _ = volume (Set.Ico (p/T) ((p+rate a)/T) ∩ Set.Ioo 0 1) := by rw [heq]
    _ = unitUniform (Set.Ico (p/T) ((p+rate a)/T)) := by
      rw [unitUniform, Measure.restrict_apply measurableSet_Ico]
    _ = ENNReal.ofReal ((p+rate a)/T-p/T) := unitUniform_Ico _ _ hl hu
    _ = ENNReal.ofReal (rate a/T) := by congr 1; ring

end Rhone.Coalescent.IntervalProcess
