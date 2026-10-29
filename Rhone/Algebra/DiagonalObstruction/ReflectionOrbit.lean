/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic

/-! # Two nearby modular collision centres force a long orbit -/

@[expose] public section

namespace Rhone.Algebra.DiagonalObstruction

theorem reflection_translate {S : Finset ℕ} {c h x : ℕ}
    (hc : ∀ n ∈ S, n ≤ c → c - n ∈ S)
    (hch : ∀ n ∈ S, n ≤ c + h → c + h - n ∈ S)
    (hx : x ∈ S) (hxc : x ≤ c) : x + h ∈ S := by
  have hy := hc x hx hxc
  have hz := hch (c - x) hy (by omega)
  simpa only [show c + h - (c - x) = x + h by omega] using hz

theorem reflection_orbit_mem {S : Finset ℕ} {c h : ℕ}
    (hzero : 0 ∈ S)
    (hc : ∀ n ∈ S, n ≤ c → c - n ∈ S)
    (hch : ∀ n ∈ S, n ≤ c + h → c + h - n ∈ S) :
    ∀ k : ℕ, k * h ≤ c + h → k * h ∈ S := by
  intro k
  induction k with
  | zero => simpa using hzero
  | succ k ih =>
    intro hk
    rw [Nat.succ_mul] at hk
    have hkc : k * h ≤ c := by omega
    have hmem := ih (by omega)
    have hnext := reflection_translate hc hch hmem hkc
    simpa only [Nat.add_mul, one_mul] using hnext

theorem reflection_orbit_card {S : Finset ℕ} {c h N : ℕ}
    (hh : 0 < h) (hzero : 0 ∈ S)
    (hc : ∀ n ∈ S, n ≤ c → c - n ∈ S)
    (hch : ∀ n ∈ S, n ≤ c + h → c + h - n ∈ S)
    (hN : N * h ≤ c + h) : N + 1 ≤ S.card := by
  have hsubset : (Finset.range (N + 1)).image (fun k => k * h) ⊆ S := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
    have hkN : k ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    apply reflection_orbit_mem hzero hc hch k
    exact (Nat.mul_le_mul_right h hkN).trans hN
  have hinj : Function.Injective (fun k : ℕ => k * h) := by
    intro a b hab
    exact Nat.eq_of_mul_eq_mul_right hh hab
  simpa only [Finset.card_image_of_injective _ hinj, Finset.card_range] using
    Finset.card_le_card hsubset

end Rhone.Algebra.DiagonalObstruction
