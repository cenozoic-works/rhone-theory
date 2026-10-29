/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination

/-!
# The Price equation for a finite population

Source: price1970, p. 520, eq. (1), (4); frank1995_price, p. 376, eq. (3); price1972, p. 486, eq. (A
11)–(A 12); frank1995_price, pp. 375–376, eq. (2)–(3); robertson1966, p. 97, eq. (4), p. 99;
frank1995_price, p. 374, eq. (1). -/

@[expose] public section

namespace Rhone.Statistics

variable {ι : Type*} [Fintype ι] {F : Type*} [Field F]

def popMean (f : ι → F) : F := (∑ i, f i) / (Fintype.card ι : F)

def popCov (f g : ι → F) : F := popMean (fun i => f i * g i) - popMean f * popMean g

def nextMean (w z' : ι → F) : F := popMean (fun i => w i * z' i) / popMean w

theorem popMean_add (f g : ι → F) :
    popMean (fun i => f i + g i) = popMean f + popMean g := by
  simp [popMean, Finset.sum_add_distrib, add_div]

theorem popMean_sub (f g : ι → F) :
    popMean (fun i => f i - g i) = popMean f - popMean g := by
  simp [popMean, Finset.sum_sub_distrib, sub_div]

theorem popCov_comm (f g : ι → F) : popCov f g = popCov g f := by
  simp only [popCov, mul_comm (f _), mul_comm (popMean f)]

theorem popCov_eq_mean_centered [NeZero (Fintype.card ι : F)] (f g : ι → F) :
    popCov f g = popMean (fun i => (f i - popMean f) * (g i - popMean g)) := by
  have hc : (Fintype.card ι : F) ≠ 0 := NeZero.ne _
  simp only [popCov, popMean, mul_sub, sub_mul, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.sum_mul]
  field_simp
  ring

/-- Source: price1970, p. 520, eq. (4); frank1995_price, p. 376, eq. (3). -/
theorem price_equation (w z z' : ι → F) (hw : popMean w ≠ 0) :
    popMean w * (nextMean w z' - popMean z)
      = popCov w z + popMean (fun i => w i * (z' i - z i)) := by
  have h1 : popMean (fun i => w i * (z' i - z i))
      = popMean (fun i => w i * z' i) - popMean (fun i => w i * z i) := by
    rw [← popMean_sub]; congr 1; ext i; ring
  rw [h1, popCov, nextMean]
  field_simp
  ring

/--
Source: robertson1966, p. 97, eq. (4), p. 99; frank1995_price, p. 374, eq. (1); price1970, p. 520,
eq. (1). -/
theorem robertson_price (w z : ι → F) (hw : popMean w ≠ 0) :
    nextMean w z - popMean z = popCov w z / popMean w := by
  have h := price_equation w z z hw
  simp only [sub_self, mul_zero] at h
  have h0 : popMean (fun _ : ι => (0 : F)) = 0 := by simp [popMean]
  rw [h0, add_zero] at h
  field_simp
  linear_combination h

end Rhone.Statistics
