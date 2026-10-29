/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib

/-! # The partial-fraction identity over the prefix sums of a permutation -/

@[expose] public section

namespace Rhone.Algebra.RhoZero

open Finset

variable {F : Type*} [Field F]

def prefixSum {N : ℕ} (x : Fin N → F) (σ : Equiv.Perm (Fin N)) (r : ℕ) : F :=
  ∑ s : Fin N, if (s : ℕ) < r then x (σ s) else 0

def sufSum {N : ℕ} (x : Fin N → F) (σ : Equiv.Perm (Fin N)) (r : ℕ) : F :=
  ∑ s : Fin N, if r ≤ (s : ℕ) then x (σ s) else 0

theorem sufSum_zero {N : ℕ} (x : Fin N → F) (σ : Equiv.Perm (Fin N)) :
    sufSum x σ 0 = ∑ i, x i := by
  simp only [sufSum, Nat.zero_le, ite_true]
  exact Equiv.sum_comp σ x

def sufWord {N : ℕ} (x : Fin N → F) (σ : Equiv.Perm (Fin N)) : F :=
  ∏ r ∈ Finset.range N, (sufSum x σ r)⁻¹

theorem sufSum_succ {n : ℕ} (x : Fin (n + 1) → F) (p : Fin (n + 1)) (e : Equiv.Perm (Fin n))
    (r : ℕ) :
    sufSum x (Equiv.Perm.decomposeFin.symm (p, e)) (r + 1)
      = sufSum (fun w : Fin n => x (Equiv.swap 0 p w.succ)) e r := by
  simp only [sufSum]
  rw [Fin.sum_univ_succ]
  have h0 : ¬ (r + 1 ≤ ((0 : Fin (n + 1)) : ℕ)) := by simp
  rw [ite_eq_right h0, zero_add]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hval : ((w.succ : Fin (n + 1)) : ℕ) = (w : ℕ) + 1 := rfl
  rw [hval]
  by_cases hc : r ≤ (w : ℕ)
  · rw [ite_eq_left (by omega), ite_eq_left hc, Equiv.Perm.decomposeFin_symm_apply_succ]
  · rw [ite_eq_right (by omega), ite_eq_right hc]

theorem sum_sufWord : ∀ (N : ℕ) (x : Fin N → F), (∀ i, x i ≠ 0) →
    (∀ (σ : Equiv.Perm (Fin N)) (r : ℕ), r < N → sufSum x σ r ≠ 0) →
    ∑ σ : Equiv.Perm (Fin N), sufWord x σ = ∏ i, (x i)⁻¹ := by
  intro N
  induction N with
  | zero => intro x _ _; simp [sufWord]
  | succ n IH =>
    intro x hx h
    have htot : (∑ i, x i) ≠ 0 := by
      have := h 1 0 (Nat.succ_pos n)
      rwa [sufSum_zero] at this
    have hyne : ∀ (p : Fin (n + 1)) (w : Fin n), x (Equiv.swap 0 p w.succ) ≠ 0 := fun p w => hx _
    have hword : ∀ (p : Fin (n + 1)) (e : Equiv.Perm (Fin n)),
        sufWord x (Equiv.Perm.decomposeFin.symm (p, e))
          = (∑ i, x i)⁻¹ * sufWord (fun w : Fin n => x (Equiv.swap 0 p w.succ)) e := by
      intro p e
      simp only [sufWord]
      rw [Finset.prod_range_succ']
      rw [sufSum_zero]
      rw [mul_comm]
      congr 1
      refine Finset.prod_congr rfl fun r _ => ?_
      rw [sufSum_succ x p e r]
    have hsuf : ∀ (p : Fin (n + 1)) (e : Equiv.Perm (Fin n)) (r : ℕ), r < n →
        sufSum (fun w : Fin n => x (Equiv.swap 0 p w.succ)) e r ≠ 0 := by
      intro p e r hr
      rw [← sufSum_succ x p e r]
      exact h _ _ (by omega)
    have hprod : ∀ p : Fin (n + 1),
        ∏ w : Fin n, (x (Equiv.swap 0 p w.succ))⁻¹ = x p * ∏ i, (x i)⁻¹ := by
      intro p
      have hswap : ∏ i : Fin (n + 1), (x i)⁻¹
          = ∏ i : Fin (n + 1), (x (Equiv.swap 0 p i))⁻¹ :=
        (Equiv.prod_comp (Equiv.swap (0 : Fin (n + 1)) p) fun i => (x i)⁻¹).symm
      rw [hswap, Fin.prod_univ_succ, Equiv.swap_apply_left, ← mul_assoc,
        mul_inv_cancel₀ (hx p), one_mul]
    calc ∑ σ : Equiv.Perm (Fin (n + 1)), sufWord x σ
        = ∑ pe : Fin (n + 1) × Equiv.Perm (Fin n),
            sufWord x (Equiv.Perm.decomposeFin.symm pe) :=
          (Equiv.sum_comp Equiv.Perm.decomposeFin.symm (sufWord x)).symm
      _ = ∑ p : Fin (n + 1), ∑ e : Equiv.Perm (Fin n),
            (∑ i, x i)⁻¹ * sufWord (fun w : Fin n => x (Equiv.swap 0 p w.succ)) e := by
          rw [Fintype.sum_prod_type]
          exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun e _ => hword p e
      _ = ∑ p : Fin (n + 1), (∑ i, x i)⁻¹ * ∏ w : Fin n, (x (Equiv.swap 0 p w.succ))⁻¹ := by
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [← Finset.mul_sum,
            IH (fun w : Fin n => x (Equiv.swap 0 p w.succ)) (hyne p) (hsuf p)]
      _ = (∑ i, x i)⁻¹ * ((∑ p : Fin (n + 1), x p) * ∏ i, (x i)⁻¹) := by
          rw [← Finset.mul_sum, Finset.sum_mul]
          refine congrArg _ (Finset.sum_congr rfl fun p _ => hprod p)
      _ = ∏ i, (x i)⁻¹ := by
          rw [← mul_assoc, inv_mul_cancel₀ htot, one_mul]

theorem prefixSum_mul_revPerm {N : ℕ} (x : Fin N → F) (σ : Equiv.Perm (Fin N)) {r : ℕ}
    (hr : r ≤ N) : prefixSum x (σ * Fin.revPerm) r = sufSum x σ (N - r) := by
  have key : sufSum x σ (N - r)
      = ∑ s : Fin N, if N - r ≤ ((Fin.rev s : Fin N) : ℕ) then x (σ (Fin.rev s)) else 0 :=
    (Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin N))
      (fun s => if N - r ≤ (s : ℕ) then x (σ s) else 0)).symm
  rw [key]
  simp only [prefixSum, Equiv.Perm.mul_apply, Fin.revPerm_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hs : (s : ℕ) < N := s.isLt
  rw [Fin.val_rev]
  by_cases hc : (s : ℕ) < r
  · rw [ite_eq_left hc, ite_eq_left (by omega)]
  · rw [ite_eq_right hc, ite_eq_right (by omega)]

theorem sum_perm_inv_prefix : ∀ (N : ℕ) (x : Fin N → F), N ≠ 0 → (∀ i, x i ≠ 0) →
    (∀ (σ : Equiv.Perm (Fin N)) (r : ℕ), 0 < r → r < N → prefixSum x σ r ≠ 0) →
    ∑ σ : Equiv.Perm (Fin N), ∏ r ∈ Finset.Ico 1 N, (prefixSum x σ r)⁻¹
      = (∑ i, x i) * ∏ i, (x i)⁻¹ := by
  rintro (_ | n) x hN hx hpre
  · exact absurd rfl hN
  clear hN
  have hsufne : ∀ (σ : Equiv.Perm (Fin (n + 1))) (s : ℕ), 0 < s → s < n + 1 →
      sufSum x σ s ≠ 0 := by
    intro σ s hs0 hsN
    have := prefixSum_mul_revPerm x σ (r := n + 1 - s) (by omega)
    rw [show n + 1 - (n + 1 - s) = s from by omega] at this
    rw [← this]
    exact hpre _ _ (by omega) (by omega)
  have step : ∀ σ : Equiv.Perm (Fin (n + 1)),
      ∏ r ∈ Finset.Ico 1 (n + 1), (prefixSum x (σ * Fin.revPerm) r)⁻¹
        = ∏ r ∈ Finset.range n, (sufSum x σ (r + 1))⁻¹ := by
    intro σ
    rw [Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel,
      ← Finset.prod_range_reflect (fun r => (sufSum x σ (r + 1))⁻¹) n]
    refine Finset.prod_congr rfl fun r hr => ?_
    rw [Finset.mem_range] at hr
    rw [prefixSum_mul_revPerm x σ (show 1 + r ≤ n + 1 by omega),
      show n + 1 - (1 + r) = n - 1 - r + 1 from by omega]
  have hrev : ∑ σ : Equiv.Perm (Fin (n + 1)),
      ∏ r ∈ Finset.Ico 1 (n + 1), (prefixSum x σ r)⁻¹
        = ∑ σ : Equiv.Perm (Fin (n + 1)),
            ∏ r ∈ Finset.Ico 1 (n + 1), (prefixSum x (σ * Fin.revPerm) r)⁻¹ :=
    (Equiv.sum_comp (Equiv.mulRight (Fin.revPerm : Equiv.Perm (Fin (n + 1))))
      (fun σ => ∏ r ∈ Finset.Ico 1 (n + 1), (prefixSum x σ r)⁻¹)).symm
  rw [hrev]
  have hyne : ∀ (p : Fin (n + 1)) (w : Fin n), x (Equiv.swap 0 p w.succ) ≠ 0 := fun p w => hx _
  have hsuf : ∀ (p : Fin (n + 1)) (e : Equiv.Perm (Fin n)) (r : ℕ), r < n →
      sufSum (fun w : Fin n => x (Equiv.swap 0 p w.succ)) e r ≠ 0 := by
    intro p e r hr
    rw [← sufSum_succ x p e r]
    exact hsufne _ _ (by omega) (by omega)
  have hprod : ∀ p : Fin (n + 1),
      ∏ w : Fin n, (x (Equiv.swap 0 p w.succ))⁻¹ = x p * ∏ i, (x i)⁻¹ := by
    intro p
    have hswap : ∏ i : Fin (n + 1), (x i)⁻¹
        = ∏ i : Fin (n + 1), (x (Equiv.swap 0 p i))⁻¹ :=
      (Equiv.prod_comp (Equiv.swap (0 : Fin (n + 1)) p) fun i => (x i)⁻¹).symm
    rw [hswap, Fin.prod_univ_succ, Equiv.swap_apply_left, ← mul_assoc,
      mul_inv_cancel₀ (hx p), one_mul]
  calc ∑ σ : Equiv.Perm (Fin (n + 1)),
        ∏ r ∈ Finset.Ico 1 (n + 1), (prefixSum x (σ * Fin.revPerm) r)⁻¹
      = ∑ σ : Equiv.Perm (Fin (n + 1)), ∏ r ∈ Finset.range n, (sufSum x σ (r + 1))⁻¹ :=
        Finset.sum_congr rfl fun σ _ => step σ
    _ = ∑ pe : Fin (n + 1) × Equiv.Perm (Fin n),
          ∏ r ∈ Finset.range n,
            (sufSum x (Equiv.Perm.decomposeFin.symm pe) (r + 1))⁻¹ :=
        (Equiv.sum_comp Equiv.Perm.decomposeFin.symm
          (fun σ => ∏ r ∈ Finset.range n, (sufSum x σ (r + 1))⁻¹)).symm
    _ = ∑ p : Fin (n + 1), ∑ e : Equiv.Perm (Fin n),
          sufWord (fun w : Fin n => x (Equiv.swap 0 p w.succ)) e := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun e _ => ?_
        simp only [sufWord]
        exact Finset.prod_congr rfl fun r _ => by rw [sufSum_succ x p e r]
    _ = ∑ p : Fin (n + 1), ∏ w : Fin n, (x (Equiv.swap 0 p w.succ))⁻¹ :=
        Finset.sum_congr rfl fun p _ =>
          sum_sufWord n (fun w : Fin n => x (Equiv.swap 0 p w.succ)) (hyne p) (hsuf p)
    _ = (∑ i, x i) * ∏ i, (x i)⁻¹ := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun p _ => hprod p

theorem sum_perm_inv_prefix_two {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) :
    x⁻¹ + y⁻¹ = (x + y) * (x * y)⁻¹ := by
  field_simp
  ring

theorem sum_perm_inv_prefix_three {x y z : F} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (hxy : x + y ≠ 0) (hxz : x + z ≠ 0) (hyz : y + z ≠ 0) :
    (x * (x + y))⁻¹ + (x * (x + z))⁻¹ + (y * (y + x))⁻¹ + (y * (y + z))⁻¹
        + (z * (z + x))⁻¹ + (z * (z + y))⁻¹
      = (x + y + z) * (x * y * z)⁻¹ := by
  have hyx : y + x ≠ 0 := by rwa [add_comm]
  have hzx : z + x ≠ 0 := by rwa [add_comm]
  have hzy : z + y ≠ 0 := by rwa [add_comm]
  field_simp
  ring

theorem sum_perm_inv_prefix_three_eq_zero {x y z : F} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (hxy : x + y ≠ 0) (hxz : x + z ≠ 0) (hyz : y + z ≠ 0) (hsum : x + y + z = 0) :
    (x * (x + y))⁻¹ + (x * (x + z))⁻¹ + (y * (y + x))⁻¹ + (y * (y + z))⁻¹
        + (z * (z + x))⁻¹ + (z * (z + y))⁻¹ = 0 := by
  rw [sum_perm_inv_prefix_three hx hy hz hxy hxz hyz, hsum, zero_mul]

end Rhone.Algebra.RhoZero
