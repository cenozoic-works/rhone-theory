/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.EsfPair.Defs

/-! # The one-step law of the partition-carrying chain -/

@[expose] public section

namespace Rhone.Coalescent.EsfPair

open Finset TwoLocusGenealogy TypedAncestralChain

variable {n : ℕ} {θA θB ρ : ℝ}

def stepP (θA θB ρ : ℝ) (g : PSt n → ℝ) (s : PSt n) : ℝ :=
  (∑ p ∈ s.1, ∑ q ∈ s.1.erase p, g (coalP s p q))
    + θA * (∑ p ∈ carA s.1, g (mutAP s p))
    + θB * (∑ p ∈ carB s.1, g (mutBP s p))
    + ρ * (∑ p ∈ carC s.1, g (recP s p))

theorem stepP_of_fst (f : Finset (Lin n) → ℝ) (s : PSt n) :
    stepP θA θB ρ (fun t => f t.1) s = stepU θA θB ρ f s.1 := rfl

theorem stepP_one (s : PSt n) : stepP θA θB ρ (fun _ => (1 : ℝ)) s = dtot θA θB ρ s.1 :=
  stepU_one s.1

theorem stepP_nonneg (hθA : 0 ≤ θA) (hθB : 0 ≤ θB) (hρ : 0 ≤ ρ) {g : PSt n → ℝ}
    (hg : ∀ t, 0 ≤ g t) (s : PSt n) : 0 ≤ stepP θA θB ρ g s := by
  refine add_nonneg (add_nonneg (add_nonneg ?_ ?_) ?_) ?_
  · exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => hg _
  · exact mul_nonneg hθA (Finset.sum_nonneg fun _ _ => hg _)
  · exact mul_nonneg hθB (Finset.sum_nonneg fun _ _ => hg _)
  · exact mul_nonneg hρ (Finset.sum_nonneg fun _ _ => hg _)

theorem stepP_mono (hθA : 0 ≤ θA) (hθB : 0 ≤ θB) (hρ : 0 ≤ ρ) {g₁ g₂ : PSt n → ℝ} (s : PSt n)
    (hcoal : ∀ p ∈ s.1, ∀ q ∈ s.1.erase p, g₁ (coalP s p q) ≤ g₂ (coalP s p q))
    (hmutA : ∀ p ∈ carA s.1, g₁ (mutAP s p) ≤ g₂ (mutAP s p))
    (hmutB : ∀ p ∈ carB s.1, g₁ (mutBP s p) ≤ g₂ (mutBP s p))
    (hrec : ∀ p ∈ carC s.1, g₁ (recP s p) ≤ g₂ (recP s p)) :
    stepP θA θB ρ g₁ s ≤ stepP θA θB ρ g₂ s := by
  refine add_le_add (add_le_add (add_le_add ?_ ?_) ?_) ?_
  · exact Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun q hq => hcoal p hp q hq
  · exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum hmutA) hθA
  · exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum hmutB) hθB
  · exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum hrec) hρ

theorem stepP_sum {ι : Type*} [Fintype ι] (c : ι → ℝ) (g : ι → PSt n → ℝ) (s : PSt n) :
    (∑ x, c x * stepP θA θB ρ (g x) s) = stepP θA θB ρ (fun t => ∑ x, c x * g x t) s := by
  have key : ∀ (θ : ℝ) (X : ι → ℝ), (∑ x, c x * (θ * X x)) = θ * ∑ x, c x * X x := by
    intro θ X
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  have hA : (∑ x, c x * ∑ p ∈ s.1, ∑ q ∈ s.1.erase p, g x (coalP s p q))
      = ∑ p ∈ s.1, ∑ q ∈ s.1.erase p, ∑ x, c x * g x (coalP s p q) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  have hB : (∑ x, c x * ∑ p ∈ carA s.1, g x (mutAP s p))
      = ∑ p ∈ carA s.1, ∑ x, c x * g x (mutAP s p) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
  have hC : (∑ x, c x * ∑ p ∈ carB s.1, g x (mutBP s p))
      = ∑ p ∈ carB s.1, ∑ x, c x * g x (mutBP s p) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
  have hD : (∑ x, c x * ∑ p ∈ carC s.1, g x (recP s p))
      = ∑ p ∈ carC s.1, ∑ x, c x * g x (recP s p) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
  simp only [stepP, mul_add, Finset.sum_add_distrib, key, hA, hB, hC, hD]

def hitAt (ζA ζB : Blocks n) (s : PSt n) : ℝ := if s.2.1 = ζA ∧ s.2.2 = ζB then 1 else 0

noncomputable def hitNP (ζA ζB : Blocks n) (θA θB ρ : ℝ) : ℕ → PSt n → ℝ
  | 0, s => if s.1 = ∅ then hitAt ζA ζB s else 0
  | N + 1, s =>
      if s.1 = ∅ then hitAt ζA ζB s
      else stepP θA θB ρ (hitNP ζA ζB θA θB ρ N) s / dtot θA θB ρ s.1

variable {ζA ζB : Blocks n}

@[simp] theorem hitNP_zero (s : PSt n) :
    hitNP ζA ζB θA θB ρ 0 s = if s.1 = ∅ then hitAt ζA ζB s else 0 := rfl

theorem hitNP_of_empty (N : ℕ) {s : PSt n} (h : s.1 = ∅) :
    hitNP ζA ζB θA θB ρ N s = hitAt ζA ζB s := by
  cases N <;> simp [hitNP, h]

theorem hitNP_succ_of_ne (N : ℕ) {s : PSt n} (h : s.1 ≠ ∅) :
    hitNP ζA ζB θA θB ρ (N + 1) s
      = stepP θA θB ρ (hitNP ζA ζB θA θB ρ N) s / dtot θA θB ρ s.1 := by
  rw [hitNP, ite_eq_right h]

theorem hitNP_nonneg (hθA : 0 ≤ θA) (hθB : 0 ≤ θB) (hρ : 0 ≤ ρ) (N : ℕ) (s : PSt n) :
    0 ≤ hitNP ζA ζB θA θB ρ N s := by
  induction N generalizing s with
  | zero =>
    rw [hitNP_zero, hitAt]
    split_ifs <;> norm_num
  | succ N ih =>
    by_cases h : s.1 = ∅
    · rw [hitNP_of_empty _ h, hitAt]
      split_ifs <;> norm_num
    · rw [hitNP_succ_of_ne N h]
      exact div_nonneg (stepP_nonneg hθA hθB hρ (fun t => ih t) s)
        (dtot_nonneg hθA hθB hρ s.1)

theorem hitNP_mono (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (N : ℕ) {s : PSt n}
    (hw : WF s.1) : hitNP ζA ζB θA θB ρ N s ≤ hitNP ζA ζB θA θB ρ (N + 1) s := by
  induction N generalizing s with
  | zero =>
    by_cases h : s.1 = ∅
    · rw [hitNP_of_empty _ h, hitNP_of_empty _ h]
    · rw [hitNP_zero, ite_eq_right h, hitNP_succ_of_ne 0 h]
      exact div_nonneg (stepP_nonneg hθA.le hθB.le hρ
        (fun t => hitNP_nonneg hθA.le hθB.le hρ 0 t) s) (dtot_nonneg hθA.le hθB.le hρ s.1)
  | succ N ih =>
    by_cases h : s.1 = ∅
    · rw [hitNP_of_empty _ h, hitNP_of_empty _ h]
    · have hd : 0 < dtot θA θB ρ s.1 :=
        dtot_pos hθA hθB hρ hw (Finset.nonempty_iff_ne_empty.2 h)
      rw [hitNP_succ_of_ne (N + 1) h, hitNP_succ_of_ne N h]
      refine div_le_div_of_nonneg_right ?_ hd.le
      refine stepP_mono hθA.le hθB.le hρ s ?_ ?_ ?_ ?_
      · exact fun p hp q hq => ih (hw.coal hp (Finset.mem_of_mem_erase hq))
      · exact fun p hp => ih (hw.mutA (carA_subset _ hp))
      · exact fun p hp => ih (hw.mutB (carB_subset _ hp))
      · exact fun p hp => ih (hw.recomb (mem_carC.1 hp).1 (mem_carC.1 hp).2.1
          (mem_carC.1 hp).2.2)

end Rhone.Coalescent.EsfPair
