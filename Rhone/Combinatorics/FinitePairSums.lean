/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-! # Finite sums over unordered pairs for Kingman merger rewards -/

@[expose] public section
namespace Rhone.Combinatorics
open Finset

theorem sum_powersetCard_two_cross_general {ι : Type*}
    (s : Finset ι) (f g : ι → ℝ) :
    ∑ t ∈ s.powersetCard 2,
      ((∑ i ∈ t, f i) * (∑ i ∈ t, g i) - ∑ i ∈ t, f i * g i) =
      (∑ i ∈ s, f i) * (∑ i ∈ s, g i) - ∑ i ∈ s, f i * g i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.powersetCard_eq_empty.mpr (by simp)]
    simp
  | @insert a s ha ih =>
    rw [powersetCard_succ_insert ha 1]
    have hd : Disjoint (s.powersetCard 2) ((s.powersetCard 1).image (insert a)) := by
      apply Finset.disjoint_left.mpr
      intro t ht hu
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hu
      exact ha ((Finset.mem_powersetCard.mp ht).1 (Finset.mem_insert_self a u))
    rw [Finset.sum_union hd, ih]
    have hinj : Set.InjOn (insert a) (↑(s.powersetCard 1) : Set (Finset ι)) := by
      intro t ht u hu he
      have hat : a ∉ t := fun h => ha ((Finset.mem_powersetCard.mp ht).1 h)
      have hau : a ∉ u := fun h => ha ((Finset.mem_powersetCard.mp hu).1 h)
      have h := congrArg (fun t : Finset ι => t.erase a) he
      simpa [hat, hau] using h
    rw [Finset.sum_image hinj, powersetCard_one]
    rw [Finset.sum_map]
    change _ + (∑ b ∈ s,
      ((∑ i ∈ insert a {b}, f i) * (∑ i ∈ insert a {b}, g i) -
        ∑ i ∈ insert a {b}, f i * g i)) = _
    have he (b : ι) (hb : b ∈ s) :
        ((∑ i ∈ insert a {b}, f i) * (∑ i ∈ insert a {b}, g i) -
          ∑ i ∈ insert a {b}, f i * g i) = f a * g b + f b * g a := by
      have hab : a ≠ b := fun h => ha (h ▸ hb)
      have hn : a ∉ ({b} : Finset ι) := by simp [hab]
      rw [Finset.sum_insert hn, Finset.sum_insert hn, Finset.sum_insert hn]
      simp only [Finset.sum_singleton]
      ring
    rw [Finset.sum_congr rfl he, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.sum_mul]
    simp only [Finset.sum_insert ha]
    ring

theorem sum_range_square_add_sq (T : ℕ) (g : ℕ → ℝ) :
    (∑ k ∈ Finset.range T, g k) ^ 2 + ∑ k ∈ Finset.range T, g k ^ 2 =
    2 * ∑ t ∈ Finset.range T, (∑ k ∈ Finset.range (t + 1), g k) * g t := by
  induction T with
  | zero => simp
  | succ T ih =>
    simp only [Finset.sum_range_succ] at ih ⊢
    nlinarith [ih]

theorem sum_range_prefix_mul_difference (T : ℕ) (g u : ℕ → ℝ) :
    ∑ t ∈ Finset.range T, (∑ k ∈ Finset.range (t + 1), g k) * (u t - u (t + 1)) =
    (∑ t ∈ Finset.range T, g t * u t) -
      (∑ k ∈ Finset.range T, g k) * u T := by
  induction T with
  | zero => simp
  | succ T ih =>
    simp only [Finset.sum_range_succ] at ih ⊢
    nlinarith [ih]

end Rhone.Combinatorics
