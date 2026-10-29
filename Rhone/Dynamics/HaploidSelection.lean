/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Haploid selection with several types

Source: fisher1930, ch. 2; crow_kimura1970, ch. 5; price1972, pp. 485–486, eq. (A 1)–(A 3), eq. (A
7); frank1995_price, p. 375. -/

@[expose] public section

namespace Rhone.Dynamics

variable {ι : Type*} [Fintype ι] {F : Type*} [Field F]

def wMean (p f : ι → F) : F := ∑ i, p i * f i

def wCov (p f g : ι → F) : F := wMean p (fun i => f i * g i) - wMean p f * wMean p g

def wVar (p f : ι → F) : F := wCov p f f

def haploidStep (p w : ι → F) : ι → F := fun i => p i * w i / wMean p w

theorem wVar_eq_mean_sq_sub (p f : ι → F) (hp : ∑ i, p i = 1) :
    wVar p f = wMean p (fun i => (f i - wMean p f) ^ 2) := by
  have h : ∑ i, p i * (f i - wMean p f) ^ 2
      = ∑ i, p i * (f i * f i) - 2 * wMean p f * ∑ i, p i * f i
        + wMean p f ^ 2 * ∑ i, p i := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [wMean, h, hp]
  simp only [wVar, wCov, wMean]
  ring

section Order

variable [LinearOrder F] [IsStrictOrderedRing F]

theorem haploidStep_nonneg (p w : ι → F) (hp : ∀ i, 0 ≤ p i) (hw : ∀ i, 0 ≤ w i)
    (hbar : 0 < wMean p w) (i : ι) : 0 ≤ haploidStep p w i :=
  div_nonneg (mul_nonneg (hp i) (hw i)) hbar.le

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem haploidStep_sum_eq_one (p w : ι → F) (hbar : wMean p w ≠ 0) :
    ∑ i, haploidStep p w i = 1 := by
  simp only [haploidStep, ← Finset.sum_div]
  exact div_self hbar

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem haploid_meanFitness_change (p w : ι → F) (hbar : wMean p w ≠ 0) :
    wMean (haploidStep p w) w - wMean p w = wVar p w / wMean p w := by
  have h : wMean (haploidStep p w) w = wMean p (fun i => w i * w i) / wMean p w := by
    simp only [wMean, haploidStep, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [h, wVar, wCov]
  field_simp

theorem haploid_meanFitness_mono (p w : ι → F) (hp0 : ∀ i, 0 ≤ p i) (hp : ∑ i, p i = 1)
    (hbar : 0 < wMean p w) : wMean p w ≤ wMean (haploidStep p w) w := by
  have h := haploid_meanFitness_change p w hbar.ne'
  have hv : 0 ≤ wVar p w := by
    rw [wVar_eq_mean_sq_sub p w hp]
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hp0 i) (sq_nonneg _)
  have : 0 ≤ wVar p w / wMean p w := div_nonneg hv hbar.le
  linarith

end Order

theorem haploid_traitMean_change (p w z : ι → F)
    (hbar : wMean p w ≠ 0) :
    wMean (haploidStep p w) z - wMean p z = wCov p w z / wMean p w := by
  have h : wMean (haploidStep p w) z = wMean p (fun i => w i * z i) / wMean p w := by
    simp only [wMean, haploidStep, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [h, wCov]
  field_simp

end Rhone.Dynamics
