/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.DiagonalChain.Cleared
public import Mathlib.Tactic.Positivity

/-! # Leading-form recursion of the cleared diagonal chain, vanishing for `k ≥ 3` -/

@[expose] public section

namespace Rhone.Probability.DiagonalChain

def Lam (A B : ℤ) (P x : ℕ) : ℤ := (P : ℤ) * A + (x : ℤ) * B

def topGstep (A B : ℤ) (P : ℕ) (w : ℕ → ℤ) (τ : ℕ) : ℤ :=
  (∏ x ∈ Finset.range τ, Lam A B P x)
    * ∑ u ∈ Finset.Icc (max τ 2) P,
        2 ^ (u - τ) * (∏ s ∈ Finset.Ico τ u, ((P : ℤ) - (s : ℤ)) ^ 2)
          * ((u : ℤ) * ((u : ℤ) - 1))
          * (∏ x ∈ Finset.Ico (u + 1) (P + 1), Lam A B P x)
          * w (u - 1)

def topG (A B : ℤ) : ℕ → ℕ → ℤ
  | 0 => fun _ => 0
  | 1 => fun τ => if τ = 1 then 1 else 0
  | (P + 2) => topGstep A B (P + 2) (topG A B (P + 1))

@[simp] theorem topG_one (A B : ℤ) (τ : ℕ) : topG A B 1 τ = if τ = 1 then 1 else 0 := rfl

@[simp] theorem topG_one_one (A B : ℤ) : topG A B 1 1 = 1 := rfl

@[simp] theorem topG_succ_succ (A B : ℤ) (P : ℕ) :
    topG A B (P + 2) = topGstep A B (P + 2) (topG A B (P + 1)) := rfl

theorem sum_Icc_succ (f : ℕ → ℤ) (a b : ℕ) (h : a ≤ b + 1) :
    ∑ u ∈ Finset.Icc a (b + 1), f u = (∑ u ∈ Finset.Icc a b, f u) + f (b + 1) :=
  Finset.sum_Icc_succ_top h f

theorem sum_Icc_succ_succ (f : ℕ → ℤ) (b : ℕ) (hb : 1 ≤ b) :
    ∑ u ∈ Finset.Icc 2 (b + 2), f u
      = (∑ u ∈ Finset.Icc 2 b, f u) + f (b + 1) + f (b + 2) := by
  have e : b + 1 + 1 = b + 2 := rfl
  have h1 := sum_Icc_succ f 2 (b + 1) (by omega)
  have h2 := sum_Icc_succ f 2 b (by omega)
  rw [e] at h1
  rw [h1, h2]

theorem prod_range_two (g : ℕ → ℤ) : (∏ x ∈ Finset.range 2, g x) = g 0 * g 1 := by
  have h := Finset.prod_range_succ g 1
  rw [Finset.prod_range_one] at h
  exact h

theorem topG_top (A B : ℤ) (P : ℕ) :
    topG A B (P + 2) (P + 2)
      = (∏ x ∈ Finset.range (P + 2), Lam A B (P + 2) x)
        * ((((P : ℤ) + 2) * ((P : ℤ) + 1)) * topG A B (P + 1) (P + 1)) := by
  rw [topG_succ_succ, topGstep, show max (P + 2) 2 = P + 2 from by omega, Finset.Icc_self,
    Finset.sum_singleton, Nat.sub_self, pow_zero, Finset.Ico_self, Finset.prod_empty,
    show P + 2 + 1 = P + 3 from by omega, Finset.Ico_self, Finset.prod_empty,
    show P + 2 - 1 = P + 1 from by omega]
  push_cast
  ring

theorem topG_sub (A B : ℤ) (P : ℕ) (hP : 1 ≤ P) :
    topG A B (P + 2) (P + 1)
      = (∏ x ∈ Finset.range (P + 1), Lam A B (P + 2) x)
        * ((((P : ℤ) + 1) * (P : ℤ)) * Lam A B (P + 2) (P + 2) * topG A B (P + 1) P
          + 2 * ((((P : ℤ) + 2) * ((P : ℤ) + 1))) * topG A B (P + 1) (P + 1)) := by
  have hIcc : Finset.Icc (P + 1) (P + 2) = {P + 1, P + 2} := by
    ext y
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hIco1 : Finset.Ico (P + 2) (P + 2 + 1) = {P + 2} := by
    ext y
    simp only [Finset.mem_Ico, Finset.mem_singleton]
    omega
  have hIcoA : (∏ s ∈ Finset.Ico (P + 1) (P + 2), (((P + 2 : ℕ) : ℤ) - (s : ℤ)) ^ 2) = 1 := by
    have hsing : Finset.Ico (P + 1) (P + 2) = {P + 1} := by
      ext y
      simp only [Finset.mem_Ico, Finset.mem_singleton]
      omega
    rw [hsing, Finset.prod_singleton]
    push_cast
    ring
  rw [topG_succ_succ, topGstep, show max (P + 1) 2 = P + 1 from by omega, hIcc,
    Finset.sum_pair (by omega : P + 1 ≠ P + 2)]
  rw [show P + 1 - (P + 1) = 0 from by omega, pow_zero, Finset.Ico_self, Finset.prod_empty,
    show P + 1 + 1 = P + 2 from by omega, show P + 1 - 1 = P from by omega,
    show P + 2 - (P + 1) = 1 from by omega, show P + 2 - 1 = P + 1 from by omega]
  rw [hIco1, Finset.prod_singleton, hIcoA, Finset.Ico_self, Finset.prod_empty]
  push_cast
  ring

theorem topG_zero (A B : ℤ) (P : ℕ) :
    topG A B (P + 2) 0
      = ∑ u ∈ Finset.Icc 2 (P + 2),
          2 ^ u * (∏ s ∈ Finset.Ico 0 u, (((P + 2 : ℕ) : ℤ) - (s : ℤ)) ^ 2)
            * ((u : ℤ) * ((u : ℤ) - 1))
            * (∏ x ∈ Finset.Ico (u + 1) (P + 3), Lam A B (P + 2) x)
            * topG A B (P + 1) (u - 1) := by
  rw [topG_succ_succ, topGstep, Finset.range_zero, Finset.prod_empty, one_mul,
    show max 0 2 = 2 from rfl]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Nat.sub_zero, show P + 2 + 1 = P + 3 from by omega]

theorem topG_two_one (A B : ℤ) : topG A B 2 1 = Lam A B 2 0 * 4 := by
  have h : topG A B 2 1 = topGstep A B 2 (topG A B 1) 1 := rfl
  have hIco : Finset.Ico (1 : ℕ) 2 = {1} := by
    ext y
    simp only [Finset.mem_Ico, Finset.mem_singleton]
    omega
  rw [h, topGstep, show max 1 2 = 2 from rfl, Finset.Icc_self, Finset.sum_singleton,
    Finset.prod_range_one, hIco, Finset.prod_singleton,
    show Finset.Ico (2 + 1 : ℕ) (2 + 1) = (∅ : Finset ℕ) from Finset.Ico_self _,
    Finset.prod_empty]
  norm_num

theorem topG_two_two (A B : ℤ) : topG A B 2 2 = Lam A B 2 0 * Lam A B 2 1 * 2 := by
  have h := topG_top A B 0
  simp only [Nat.zero_add] at h
  rw [h, topG_one_one, prod_range_two]
  push_cast
  ring

section VanishAtKm1

variable (k : ℕ)

def ptA : ℤ := (k : ℤ) - 1

def ptB : ℤ := -(k : ℤ)

variable {k}

theorem Lam_ptA (P x : ℕ) : Lam (ptA k) (ptB k) P x = (P : ℤ) * ((k : ℤ) - 1) - (x : ℤ) * k := by
  rw [Lam, ptA, ptB]
  ring

theorem two_mul_topG_eq_mul_topG_pred (k : ℕ) (P : ℕ) (hP : 2 ≤ P) :
    2 * topG (ptA k) (ptB k) P P = ((k : ℤ) - 2) * topG (ptA k) (ptB k) P (P - 1) := by
  induction P, hP using Nat.le_induction with
  | base =>
    rw [show (2 : ℕ) - 1 = 1 from rfl, topG_two_two, topG_two_one, Lam_ptA, Lam_ptA]
    push_cast
    ring
  | succ n hn ih =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    rw [show m + 2 + 1 = m + 1 + 2 from by omega, show m + 1 + 2 - 1 = m + 1 + 1 from by omega,
      topG_top, topG_sub _ _ (m + 1) (by omega), Finset.prod_range_succ,
      show m + 1 + 1 = m + 2 from by omega, show m + 1 + 2 = m + 3 from by omega]
    rw [show m + 2 - 1 = m + 1 from by omega] at ih
    rw [Lam_ptA, Lam_ptA]
    push_cast
    linear_combination
      ((∏ x ∈ Finset.range (m + 2), Lam (ptA k) (ptB k) (m + 3) x) * ((m : ℤ) + 2)
        * ((m : ℤ) + 1) * (-((m : ℤ) + 3))) * ih

theorem topG_vanishes_at_km1 {k : ℕ} (hk : 3 ≤ k) : topG (ptA k) (ptB k) k 0 = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
  set A := ptA (j + 3) with hA
  set B := ptB (j + 3) with hB
  set f : ℕ → ℤ := fun u =>
    2 ^ u * (∏ s ∈ Finset.Ico 0 u, (((j + 1 + 2 : ℕ) : ℤ) - (s : ℤ)) ^ 2)
      * ((u : ℤ) * ((u : ℤ) - 1))
      * (∏ x ∈ Finset.Ico (u + 1) (j + 1 + 3), Lam A B (j + 1 + 2) x)
      * topG A B (j + 1 + 1) (u - 1) with hf
  have hstart : topG A B (j + 3) 0 = ∑ u ∈ Finset.Icc 2 (j + 1 + 2), f u := by
    rw [hf]
    exact topG_zero A B (j + 1)
  have hzero : ∀ u ∈ Finset.Icc 2 (j + 1), f u = 0 := by
    intro u hu
    rw [Finset.mem_Icc] at hu
    have hmem : j + 2 ∈ Finset.Ico (u + 1) (j + 1 + 3) := by
      rw [Finset.mem_Ico]
      omega
    have hLam : Lam A B (j + 1 + 2) (j + 2) = 0 := by
      rw [hA, hB, Lam_ptA]
      push_cast
      ring
    rw [hf]
    simp only
    rw [Finset.prod_eq_zero hmem hLam]
    ring
  have hCk := two_mul_topG_eq_mul_topG_pred (j + 3) (j + 2) (by omega)
  rw [show j + 2 - 1 = j + 1 from rfl, ← hA, ← hB] at hCk
  have hsplit : (∏ s ∈ Finset.Ico 0 (j + 3), (((j + 1 + 2 : ℕ) : ℤ) - (s : ℤ)) ^ 2)
      = (∏ s ∈ Finset.Ico 0 (j + 2), (((j + 1 + 2 : ℕ) : ℤ) - (s : ℤ)) ^ 2)
        * ((((j + 1 + 2 : ℕ) : ℤ) - ((j + 2 : ℕ) : ℤ)) ^ 2) :=
    Finset.prod_Ico_succ_top (Nat.zero_le _) _
  have hg1 : ((((j + 1 + 2 : ℕ) : ℤ) - ((j + 2 : ℕ) : ℤ)) ^ 2) = 1 := by
    push_cast
    ring
  have hT1 : Finset.Ico (j + 3) (j + 4) = {j + 3} := by
    ext y
    simp only [Finset.mem_Ico, Finset.mem_singleton]
    omega
  have hL : Lam A B (j + 3) (j + 3) = -((j : ℤ) + 3) := by
    rw [hA, hB, Lam_ptA]
    push_cast
    ring
  rw [hstart, sum_Icc_succ_succ f (j + 1) (by omega), Finset.sum_eq_zero hzero, zero_add, hf]
  simp only
  rw [show j + 1 + 1 = j + 2 from rfl, show j + 1 + 2 = j + 3 from rfl,
    show j + 1 + 3 = j + 4 from rfl, show j + 2 + 1 = j + 3 from rfl,
    show j + 3 + 1 = j + 4 from rfl, show j + 2 - 1 = j + 1 from rfl,
    show j + 3 - 1 = j + 2 from rfl, hT1, Finset.prod_singleton, Finset.Ico_self,
    Finset.prod_empty, hsplit, hg1, mul_one, hL]
  generalize (∏ s ∈ Finset.Ico 0 (j + 2), (((j + 3 : ℕ) : ℤ) - (s : ℤ)) ^ 2) = Pi
  push_cast at hCk ⊢
  linear_combination (2 ^ (j + 2) * Pi * ((j : ℤ) + 3) * ((j : ℤ) + 2)) * hCk

end VanishAtKm1

section NonVanishAtK

def qtA (k : ℕ) : ℤ := (k : ℤ)

def qtB (k : ℕ) : ℤ := -(k : ℤ)

theorem Lam_qtA (k P x : ℕ) :
    Lam (qtA k) (qtB k) P x = (k : ℤ) * ((P : ℤ) - (x : ℤ)) := by
  rw [Lam, qtA, qtB]
  ring

theorem topG_top_pos {k : ℕ} (hk : 1 ≤ k) : ∀ P : ℕ, 1 ≤ P → 0 < topG (qtA k) (qtB k) P P := by
  intro P
  induction P with
  | zero => intro h; omega
  | succ n ih =>
    intro _
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rw [show m + 1 + 1 = m + 2 from rfl, topG_top]
      refine mul_pos (Finset.prod_pos fun x hx => ?_) (mul_pos ?_ ?_)
      · rw [Finset.mem_range] at hx
        rw [Lam_qtA]
        have hkz : (0 : ℤ) < (k : ℤ) := by exact_mod_cast hk
        have hxz : (x : ℤ) < ((m + 2 : ℕ) : ℤ) := by exact_mod_cast hx
        nlinarith
      · positivity
      · exact ih (by omega)

theorem topG_pos_at_k {k : ℕ} (hk : 2 ≤ k) : 0 < topG (qtA k) (qtB k) k 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  set A := qtA (j + 2) with hA
  set B := qtB (j + 2) with hB
  set f : ℕ → ℤ := fun u =>
    2 ^ u * (∏ s ∈ Finset.Ico 0 u, (((j + 2 : ℕ) : ℤ) - (s : ℤ)) ^ 2)
      * ((u : ℤ) * ((u : ℤ) - 1))
      * (∏ x ∈ Finset.Ico (u + 1) (j + 3), Lam A B (j + 2) x)
      * topG A B (j + 1) (u - 1) with hf
  have hstart : topG A B (j + 2) 0 = ∑ u ∈ Finset.Icc 2 (j + 2), f u := by
    rw [hf]
    exact topG_zero A B j
  have hzero : ∀ u ∈ Finset.Icc 2 (j + 1), f u = 0 := by
    intro u hu
    rw [Finset.mem_Icc] at hu
    have hmem : j + 2 ∈ Finset.Ico (u + 1) (j + 3) := by
      rw [Finset.mem_Ico]
      omega
    have hLam : Lam A B (j + 2) (j + 2) = 0 := by
      rw [hA, hB, Lam_qtA]
      push_cast
      ring
    rw [hf]
    simp only
    rw [Finset.prod_eq_zero hmem hLam]
    ring
  have hpos : 0 < ∏ s ∈ Finset.Ico 0 (j + 2), (((j + 2 : ℕ) : ℤ) - (s : ℤ)) ^ 2 := by
    refine Finset.prod_pos fun s hs => ?_
    rw [Finset.mem_Ico] at hs
    have hsz : (s : ℤ) < ((j + 2 : ℕ) : ℤ) := by exact_mod_cast hs.2
    positivity
  have htop : 0 < topG A B (j + 1) (j + 1) := by
    rw [hA, hB]
    exact topG_top_pos (by omega : 1 ≤ j + 2) (j + 1) (by omega)
  rw [hstart, sum_Icc_succ f 2 (j + 1) (by omega), Finset.sum_eq_zero hzero, zero_add, hf]
  simp only
  rw [show j + 1 + 1 = j + 2 from rfl, show j + 2 - 1 = j + 1 from rfl,
    show Finset.Ico (j + 2 + 1) (j + 3) = (∅ : Finset ℕ) from by
      rw [show j + 2 + 1 = j + 3 from rfl, Finset.Ico_self],
    Finset.prod_empty, mul_one]
  have h2 : (0 : ℤ) < 2 ^ (j + 2) := by positivity
  have h3 : (0 : ℤ) < ((j + 2 : ℕ) : ℤ) * (((j + 2 : ℕ) : ℤ) - 1) := by
    have : ((2 : ℕ) : ℤ) ≤ ((j + 2 : ℕ) : ℤ) := by exact_mod_cast (by omega : 2 ≤ j + 2)
    push_cast at this ⊢
    nlinarith
  positivity

theorem topG_ne_zero_at_k {k : ℕ} (hk : 2 ≤ k) : topG (qtA k) (qtB k) k 0 ≠ 0 :=
  (topG_pos_at_k hk).ne'

end NonVanishAtK

end Rhone.Probability.DiagonalChain
