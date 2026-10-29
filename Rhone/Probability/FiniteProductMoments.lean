/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.Ring

/-!
# Finite product-law moment identities, derived from the finite product-sum identity

Source: grinstead_snell1997, Thm 6.4. -/

@[expose] public section
namespace Rhone.Probability.FiniteProductMoments

/-- Source: grinstead_snell1997, Thm 6.4. -/
noncomputable def expect {κ Ω : Type*} [Fintype κ] [Fintype Ω]
    (q : κ → Ω → ℝ) (f : (κ → Ω) → ℝ) : ℝ :=
by
  classical
  exact ∑ ω, (∏ j, q j (ω j)) * f ω

/-- Source: grinstead_snell1997, Thm 6.4. -/
noncomputable def cov {κ Ω : Type*} [Fintype κ] [Fintype Ω]
    (q : κ → Ω → ℝ) (f g : (κ → Ω) → ℝ) : ℝ :=
  expect q (fun ω => f ω * g ω) - expect q f * expect q g

/-- Source: grinstead_snell1997, Thm 6.4. -/
theorem expect_product {κ Ω : Type*} [Fintype κ] [Fintype Ω]
    (q f : κ → Ω → ℝ) :
    expect q (fun ω => ∏ j, f j (ω j)) = ∏ j, ∑ a, q j a * f j a := by
  classical
  unfold expect
  rw [Fintype.prod_sum]
  simp only [Finset.prod_mul_distrib]

/-- Source: grinstead_snell1997, Thm 6.4. -/
theorem expect_coordinate {κ Ω : Type*} [Fintype κ] [Fintype Ω]
    (q : κ → Ω → ℝ) (hq : ∀ j, ∑ a, q j a = 1) (j : κ) (f : Ω → ℝ) :
    expect q (fun ω => f (ω j)) = ∑ a, q j a * f a := by
  classical
  have hprod (ω : κ → Ω) : (∏ k, if k=j then f (ω k) else 1) = f (ω j) := by
    simp
  calc
    expect q (fun ω => f (ω j)) =
        expect q (fun ω => ∏ k, (if k=j then f (ω k) else 1)) := by
      congr 1
      funext ω
      exact (hprod ω).symm
    _ = ∏ k, ∑ a, q k a * (if k=j then f a else 1) :=
      expect_product q (fun k a => if k=j then f a else 1)
    _ = ∑ a, q j a * f a := by
      have hs (k : κ) : (∑ a, q k a * (if k=j then f a else 1)) =
          if k=j then (∑ a, q j a * f a) else 1 := by
        by_cases h : k=j
        · subst k; simp
        · simp [h, hq]
      simp_rw [hs]
      simp

/-- Source: grinstead_snell1997, Thm 6.4. -/
theorem expect_distinct {κ Ω : Type*} [Fintype κ] [Fintype Ω]
    (q : κ → Ω → ℝ) (hq : ∀ j, ∑ a, q j a = 1)
    (j k : κ) (hjk : j ≠ k) (f g : Ω → ℝ) :
    expect q (fun ω => f (ω j) * g (ω k)) =
      (∑ a, q j a * f a) * (∑ a, q k a * g a) := by
  classical
  have hprod (ω : κ → Ω) :
      (∏ i, (if i=j then f (ω i) else 1) * (if i=k then g (ω i) else 1)) =
        f (ω j) * g (ω k) := by
    rw [Finset.prod_mul_distrib]
    simp
  calc
    expect q (fun ω => f (ω j) * g (ω k)) =
        expect q (fun ω => ∏ i,
          (if i=j then f (ω i) else 1) * (if i=k then g (ω i) else 1)) := by
      congr 1
      funext ω
      exact (hprod ω).symm
    _ = ∏ i, ∑ a, q i a * ((if i=j then f a else 1) *
        (if i=k then g a else 1)) := expect_product q (fun i a =>
          (if i=j then f a else 1) * (if i=k then g a else 1))
    _ = (∑ a, q j a * f a) * (∑ a, q k a * g a) := by
      have hs (i : κ) :
          (∑ a, q i a * ((if i=j then f a else 1) * (if i=k then g a else 1))) =
          (if i=j then (∑ a, q j a * f a) else 1) *
          (if i=k then (∑ a, q k a * g a) else 1) := by
        by_cases hij : i=j
        · subst i; simp [hjk]
        · by_cases hik : i=k
          · subst i; simp [Ne.symm hjk]
          · simp [hij, hik, hq]
      simp_rw [hs]
      rw [Finset.prod_mul_distrib]
      simp

/-- Source: grinstead_snell1997, Thm 6.4. -/
private theorem expect_sum {κ Ω η : Type*} [Fintype κ] [Fintype Ω] [Fintype η]
    (q : κ → Ω → ℝ) (f : η → (κ → Ω) → ℝ) :
    expect q (fun ω => ∑ j, f j ω) = ∑ j, expect q (f j) := by
  classical
  simp only [expect, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Source: grinstead_snell1997, Thms 6.4, 6.8. -/
theorem cov_additive {κ Ω : Type*} [Fintype κ] [Fintype Ω]
    (q f g : κ → Ω → ℝ) (hq : ∀ j, ∑ a, q j a = 1) :
    cov q (fun ω => ∑ j, f j (ω j)) (fun ω => ∑ j, g j (ω j)) =
      ∑ j, ((∑ a, q j a * (f j a * g j a)) -
        (∑ a, q j a * f j a) * (∑ a, q j a * g j a)) := by
  classical
  have hpair (j k : κ) :
      expect q (fun ω => f j (ω j) * g k (ω k)) -
        expect q (fun ω => f j (ω j)) * expect q (fun ω => g k (ω k)) =
        if j=k then ((∑ a, q j a * (f j a * g j a)) -
          (∑ a, q j a * f j a) * (∑ a, q j a * g j a)) else 0 := by
    by_cases h : j=k
    · subst k
      rw [expect_coordinate q hq j (fun a => f j a * g j a)]
      simp [expect_coordinate q hq]
    · rw [expect_distinct q hq j k h, expect_coordinate q hq,
        expect_coordinate q hq, sub_self, ite_eq_right h]
  unfold cov
  have hprod : (fun ω : κ → Ω => (∑ j, f j (ω j)) * (∑ k, g k (ω k))) =
      (fun ω => ∑ j, ∑ k, f j (ω j) * g k (ω k)) := by
    funext ω
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [hprod, expect_sum]
  simp only [expect_sum]
  have he : (∑ j, expect q (fun ω => f j (ω j))) *
      (∑ k, expect q (fun ω => g k (ω k))) =
      ∑ j, ∑ k, expect q (fun ω => f j (ω j)) * expect q (fun ω => g k (ω k)) := by
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum]
  rw [he, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.sum_sub_distrib]
  simp_rw [hpair]
  simp

end Rhone.Probability.FiniteProductMoments
