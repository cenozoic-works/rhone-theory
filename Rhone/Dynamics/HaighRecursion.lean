/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Probability.Distributions.Poisson.Basic

/-!
# Haigh's deterministic mutation-selection recursion

Source: haigh1978, eq. (1)–(6), pp. 252–253; etheridge_etal2007, sec. 2, eq. (2.2), Remark 4.2. -/

@[expose] public section

namespace Rhone.Dynamics.HaighRecursion

open Finset Filter
open scoped Nat Topology

noncomputable def poissonWeight (m : ℝ) (k : ℕ) : ℝ := Real.exp (-m) * m ^ k / k !

noncomputable def meanFitness (s : ℝ) (x : ℕ → ℝ) : ℝ := ∑' k, x k * (1 - s) ^ k

noncomputable def step (s U : ℝ) (x : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ range (k + 1), x j * (1 - s) ^ j / meanFitness s x * poissonWeight U (k - j)

def shift (j : ℕ) (x : ℕ → ℝ) (k : ℕ) : ℝ := if j ≤ k then x (k - j) else 0

/-- Source: etheridge_etal2007, sec. 2, eq. (2.2). -/
theorem poissonWeight_zero (m : ℝ) : poissonWeight m 0 = Real.exp (-m) := by
  simp [poissonWeight]

/-- Source: etheridge_etal2007, sec. 2, eq. (2.2). -/
theorem poissonWeight_nonneg {m : ℝ} (hm : 0 ≤ m) (k : ℕ) : 0 ≤ poissonWeight m k := by
  unfold poissonWeight
  positivity

/-- Source: etheridge_etal2007, sec. 2, eq. (2.2). -/
theorem poissonWeight_eq_poissonMeasure (r : NNReal) (k : ℕ) :
    poissonWeight r k = (ProbabilityTheory.poissonMeasure r).real {k} :=
  (ProbabilityTheory.poissonMeasure_real_singleton r k).symm

/-- Source: etheridge_etal2007, sec. 2, eq. (2.2). -/
theorem hasSum_poissonWeight_mul_pow (m c : ℝ) :
    HasSum (fun k => poissonWeight m k * c ^ k) (Real.exp (-m) * Real.exp (c * m)) := by
  have h := (NormedSpace.expSeries_div_hasSum_exp (c * m)).mul_left (Real.exp (-m))
  rw [← Real.exp_eq_exp_ℝ] at h
  convert h using 1
  funext k
  simp only [poissonWeight, mul_pow]
  ring

/-- Source: etheridge_etal2007, sec. 2, eq. (2.2). -/
theorem hasSum_poissonWeight (m : ℝ) : HasSum (poissonWeight m) 1 := by
  have h := hasSum_poissonWeight_mul_pow m 1
  simpa [← Real.exp_add] using h

/-- Source: etheridge_etal2007, sec. 2, eq. (2.2). -/
theorem meanFitness_poissonWeight (s m : ℝ) :
    meanFitness s (poissonWeight m) = Real.exp (-(s * m)) := by
  rw [meanFitness, (hasSum_poissonWeight_mul_pow m (1 - s)).tsum_eq, ← Real.exp_add]
  congr 1
  ring

/-- Source: etheridge_etal2007, sec. 2, eq. (2.2). -/
theorem step_poissonWeight (s U m : ℝ) :
    step s U (poissonWeight m) = poissonWeight ((1 - s) * m + U) := by
  funext k
  have hexp : Real.exp (-((1 - s) * m + U)) =
      Real.exp (-m) * Real.exp (s * m) * Real.exp (-U) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [step, meanFitness_poissonWeight]
  simp only [poissonWeight]
  rw [add_pow, hexp, Real.exp_neg (s * m), mul_sum, sum_div]
  refine sum_congr rfl fun j hj => ?_
  have hjk : j ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hj)
  rw [Nat.cast_choose ℝ hjk, mul_pow]
  have h1 : (j ! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
  have h2 : ((k - j)! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h3 : (k ! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have h4 : Real.exp (s * m) ≠ 0 := Real.exp_ne_zero _
  field_simp

/-- Source: haigh1978, eq. (6), p. 253; etheridge_etal2007, sec. 2, eq. (2.2). -/
theorem step_poissonWeight_fixed {s : ℝ} (hs : s ≠ 0) (U : ℝ) :
    step s U (poissonWeight (U / s)) = poissonWeight (U / s) := by
  rw [step_poissonWeight]
  congr 1
  field_simp
  ring

/-- Source: haigh1978, p. 252; etheridge_etal2007, sec. 2, eq. (2.2). -/
theorem meanFitness_poissonWeight_fixed {s : ℝ} (hs : s ≠ 0) (U : ℝ) :
    meanFitness s (poissonWeight (U / s)) = Real.exp (-U) := by
  rw [meanFitness_poissonWeight, mul_div_cancel₀ _ hs]

/-- Source: etheridge_etal2007, sec. 2, eq. (2.2). -/
theorem iterate_step_poissonWeight {s : ℝ} (hs : s ≠ 0) (U m : ℝ) (t : ℕ) :
    (step s U)^[t] (poissonWeight m) =
      poissonWeight (U / s + (1 - s) ^ t * (m - U / s)) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply', ih, step_poissonWeight]
    congr 1
    field_simp
    ring

private theorem continuous_poissonWeight (k : ℕ) :
    Continuous fun m : ℝ => poissonWeight m k := by
  unfold poissonWeight
  fun_prop

/-- Source: etheridge_etal2007, sec. 2, eq. (2.2). -/
theorem tendsto_iterate_step_poissonWeight {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (U m : ℝ)
    (k : ℕ) :
    Tendsto (fun t : ℕ => (step s U)^[t] (poissonWeight m) k) atTop
      (𝓝 (poissonWeight (U / s) k)) := by
  have hpow : Tendsto (fun t : ℕ => (1 - s) ^ t) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)
  have hmean : Tendsto (fun t : ℕ => U / s + (1 - s) ^ t * (m - U / s)) atTop (𝓝 (U / s)) := by
    simpa using (hpow.mul_const (m - U / s)).const_add (U / s)
  have h := ((continuous_poissonWeight k).tendsto (U / s)).comp hmean
  refine h.congr fun t => ?_
  simp only [Function.comp_apply]
  rw [iterate_step_poissonWeight hs0.ne']

/-- Source: etheridge_etal2007, sec. 2, eq. (2.2). -/
theorem meanFitness_pos {s : ℝ} (hs1 : s < 1) {x : ℕ → ℝ} (hx : ∀ k, 0 ≤ x k)
    (hsum : Summable fun k => x k * (1 - s) ^ k) {j : ℕ} (hj : 0 < x j) :
    0 < meanFitness s x := by
  have hpos : 0 < 1 - s := by linarith
  exact hsum.tsum_pos (fun k => mul_nonneg (hx k) (pow_nonneg hpos.le k)) j
    (mul_pos hj (pow_pos hpos j))

/-- Source: etheridge_etal2007, sec. 2, eq. (2.2). -/
theorem summable_mul_pow {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {x : ℕ → ℝ} (hx : ∀ k, 0 ≤ x k)
    (hsum : Summable x) : Summable fun k => x k * (1 - s) ^ k := by
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (hx k) (pow_nonneg (by linarith) k))
    (fun k => ?_) hsum
  exact mul_le_of_le_one_right (hx k) (pow_le_one₀ (by linarith) (by linarith))

/-- Source: etheridge_etal2007, sec. 2, eq. (2.2). -/
theorem step_nonneg {s U : ℝ} (hs1 : s ≤ 1) (hU : 0 ≤ U) {x : ℕ → ℝ} (hx : ∀ k, 0 ≤ x k)
    (hW : 0 ≤ meanFitness s x) (k : ℕ) : 0 ≤ step s U x k := by
  refine sum_nonneg fun j _ => mul_nonneg (div_nonneg (mul_nonneg (hx j) ?_) hW)
    (poissonWeight_nonneg hU _)
  exact pow_nonneg (by linarith) j

/-- Source: etheridge_etal2007, sec. 2, eq. (2.2). -/
theorem hasSum_step (s U : ℝ) {x : ℕ → ℝ} (hsum : Summable fun k => |x k * (1 - s) ^ k|)
    (hW : meanFitness s x ≠ 0) : HasSum (step s U x) 1 := by
  set f : ℕ → ℝ := fun j => x j * (1 - s) ^ j / meanFitness s x with hf
  have hfn : Summable fun j => ‖f j‖ := by
    have := hsum.div_const |meanFitness s x|
    refine this.congr fun j => ?_
    simp [hf]
  have hgn : Summable fun j => ‖poissonWeight U j‖ := (hasSum_poissonWeight U).summable.norm
  have hfsum : ∑' j, f j = 1 := by
    have hs : Summable fun k => x k * (1 - s) ^ k := hsum.of_abs
    rw [hf, tsum_div_const]
    exact div_self hW
  have hprod := tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hfn hgn
  rw [hfsum, (hasSum_poissonWeight U).tsum_eq, one_mul] at hprod
  have hsummable : Summable (step s U x) :=
    (summable_norm_sum_mul_range_of_summable_norm hfn hgn).of_norm
  have : (∑' n, step s U x n) = 1 := hprod.symm
  exact this ▸ hsummable.hasSum

/-- Source: etheridge_etal2007, sec. 2, eq. (2.2). -/
theorem shift_add (j : ℕ) (x : ℕ → ℝ) (i : ℕ) : shift j x (j + i) = x i := by
  simp [shift]

/-- Source: etheridge_etal2007, sec. 2, eq. (2.2). -/
theorem shift_of_lt {j k : ℕ} (x : ℕ → ℝ) (h : k < j) : shift j x k = 0 := by
  simp [shift, Nat.not_le.mpr h]

/-- Source: etheridge_etal2007, sec. 2, eq. (2.2). -/
theorem meanFitness_shift (s : ℝ) (j : ℕ) (x : ℕ → ℝ) :
    meanFitness s (shift j x) = (1 - s) ^ j * meanFitness s x := by
  unfold meanFitness
  have hinj : Function.Injective fun i : ℕ => j + i := fun a b h => Nat.add_left_cancel h
  have hsupp : Function.support (fun k => shift j x k * (1 - s) ^ k) ⊆
      Set.range fun i : ℕ => j + i := by
    intro k hk
    by_contra hnot
    have hlt : k < j := by
      by_contra hge
      exact hnot ⟨k - j, by simp only; omega⟩
    exact hk (by simp [shift_of_lt x hlt])
  rw [← hinj.tsum_eq hsupp, ← tsum_mul_left]
  refine tsum_congr fun i => ?_
  rw [shift_add, pow_add]
  ring

/-- Source: haigh1978, p. 253; etheridge_etal2007, sec. 2, eq. (2.2). -/
theorem step_shift {s : ℝ} (hs : s ≠ 1) (U : ℝ) (j : ℕ) (x : ℕ → ℝ) :
    step s U (shift j x) = shift j (step s U x) := by
  have hne : (1 - s) ^ j ≠ 0 := pow_ne_zero j (sub_ne_zero.mpr (Ne.symm hs))
  funext k
  rcases Nat.lt_or_ge k j with hlt | hge
  · rw [shift_of_lt _ hlt, step]
    refine sum_eq_zero fun i hi => ?_
    have : i < j := lt_of_le_of_lt (Nat.lt_succ_iff.mp (mem_range.mp hi)) hlt
    simp [shift_of_lt x this]
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hge
    rw [shift_add, step, step, meanFitness_shift, add_assoc, sum_range_add]
    have hzero : ∑ i ∈ range j, shift j x i * (1 - s) ^ i / ((1 - s) ^ j * meanFitness s x) *
        poissonWeight U (j + n - i) = 0 := by
      refine sum_eq_zero fun i hi => ?_
      simp [shift_of_lt x (mem_range.mp hi)]
    rw [hzero, zero_add]
    refine sum_congr rfl fun i _ => ?_
    rw [shift_add, pow_add, Nat.add_sub_add_left]
    field_simp

/-- Source: haigh1978, p. 253; etheridge_etal2007, sec. 2, eq. (2.2). -/
theorem step_shift_poissonWeight_fixed {s : ℝ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) (U : ℝ) (j : ℕ) :
    step s U (shift j (poissonWeight (U / s))) = shift j (poissonWeight (U / s)) := by
  rw [step_shift hs1, step_poissonWeight_fixed hs0]

/-- Source: etheridge_etal2007, sec. 2, eq. (2.2). -/
theorem meanFitness_shift_poissonWeight_fixed {s : ℝ} (hs0 : s ≠ 0) (U : ℝ) (j : ℕ) :
    meanFitness s (shift j (poissonWeight (U / s))) = (1 - s) ^ j * Real.exp (-U) := by
  rw [meanFitness_shift, meanFitness_poissonWeight_fixed hs0]

/-- Source: etheridge_etal2007, sec. 2, eq. (2.2). -/
theorem shift_poissonWeight_least (s U : ℝ) (j : ℕ) :
    shift j (poissonWeight (U / s)) j = Real.exp (-(U / s)) := by
  have h := shift_add j (poissonWeight (U / s)) 0
  rw [add_zero] at h
  rw [h, poissonWeight_zero]

/-- Source: haigh1978, eq. (1), p. 252; etheridge_etal2007, sec. 2, eq. (2.2). -/
theorem step_eq_sum_div (s U : ℝ) (x : ℕ → ℝ) (k : ℕ) :
    step s U x k =
      (∑ j ∈ range (k + 1), x j * (1 - s) ^ j * poissonWeight U (k - j)) / meanFitness s x := by
  rw [step, sum_div]
  exact sum_congr rfl fun j _ => by ring

/-- Source: etheridge_etal2007, sec. 2, eq. (2.2). -/
theorem meanFitness_eq_of_step_eq {s U : ℝ} {x : ℕ → ℝ} (hfix : step s U x = x)
    (h0 : x 0 ≠ 0) : meanFitness s x = Real.exp (-U) := by
  have h := congrFun hfix 0
  rw [step_eq_sum_div] at h
  simp only [zero_add, sum_range_one, pow_zero, mul_one, Nat.sub_self, poissonWeight_zero] at h
  have hW : meanFitness s x ≠ 0 := by
    intro hW
    rw [hW, div_zero] at h
    exact h0 h.symm
  rw [div_eq_iff hW] at h
  exact (mul_left_cancel₀ h0 h).symm

private theorem eq_of_linear_eq {s U : ℝ} (hs0 : 0 < s) (hs1 : s < 1) {x y : ℕ → ℝ}
    (hx : ∀ k, ∑ j ∈ range (k + 1), x j * (1 - s) ^ j * poissonWeight U (k - j) =
      Real.exp (-U) * x k)
    (hy : ∀ k, ∑ j ∈ range (k + 1), y j * (1 - s) ^ j * poissonWeight U (k - j) =
      Real.exp (-U) * y k)
    (h0 : x 0 = y 0) : x = y := by
  funext k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact h0
    · have hxk := hx k
      have hyk := hy k
      rw [sum_range_succ, Nat.sub_self, poissonWeight_zero] at hxk hyk
      have hsum : ∑ j ∈ range k, x j * (1 - s) ^ j * poissonWeight U (k - j) =
          ∑ j ∈ range k, y j * (1 - s) ^ j * poissonWeight U (k - j) :=
        sum_congr rfl fun j hj => by rw [ih j (mem_range.1 hj)]
      rw [hsum] at hxk
      have hpow : (1 - s) ^ k < 1 := pow_lt_one₀ (by linarith) (by linarith) hk.ne'
      have hE : 0 < Real.exp (-U) := Real.exp_pos _
      have hprod : (x k - y k) * (Real.exp (-U) * (1 - (1 - s) ^ k)) = 0 := by
        linear_combination hyk - hxk
      have hne : Real.exp (-U) * (1 - (1 - s) ^ k) ≠ 0 :=
        (mul_pos hE (by linarith)).ne'
      exact sub_eq_zero.1 ((mul_eq_zero.1 hprod).resolve_right hne)

/-- Source: haigh1978, eq. (3)–(6), pp. 252–253; etheridge_etal2007, sec. 2, Remark 4.2. -/
theorem eq_poissonWeight_of_step_eq {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (U : ℝ) {x : ℕ → ℝ}
    (hfix : step s U x = x) (h0 : x 0 ≠ 0) : x = poissonWeight (U / s) := by
  have hW : meanFitness s x = Real.exp (-U) := meanFitness_eq_of_step_eq hfix h0
  have hE : Real.exp (-U) ≠ 0 := Real.exp_ne_zero _
  set c : ℝ := x 0 * Real.exp (U / s) with hc
  have hx : ∀ k, ∑ j ∈ range (k + 1), x j * (1 - s) ^ j * poissonWeight U (k - j) =
      Real.exp (-U) * x k := by
    intro k
    have h := congrFun hfix k
    rw [step_eq_sum_div, hW, div_eq_iff hE] at h
    rw [h, mul_comm]
  have hy : ∀ k, ∑ j ∈ range (k + 1),
      (c * poissonWeight (U / s) j) * (1 - s) ^ j * poissonWeight U (k - j) =
      Real.exp (-U) * (c * poissonWeight (U / s) k) := by
    intro k
    have h := congrFun (step_poissonWeight_fixed hs0.ne' U) k
    rw [step_eq_sum_div, meanFitness_poissonWeight_fixed hs0.ne', div_eq_iff hE] at h
    calc ∑ j ∈ range (k + 1),
          (c * poissonWeight (U / s) j) * (1 - s) ^ j * poissonWeight U (k - j)
        = c * ∑ j ∈ range (k + 1),
            poissonWeight (U / s) j * (1 - s) ^ j * poissonWeight U (k - j) := by
          rw [mul_sum]
          exact sum_congr rfl fun j _ => by ring
      _ = Real.exp (-U) * (c * poissonWeight (U / s) k) := by
          rw [h]
          ring
  have hzero : x 0 = c * poissonWeight (U / s) 0 := by
    rw [poissonWeight_zero, hc, mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero,
      mul_one]
  have hxc : x = fun k => c * poissonWeight (U / s) k := eq_of_linear_eq hs0 hs1 hx hy hzero
  have hWc : meanFitness s x = c * Real.exp (-U) := by
    rw [hxc, meanFitness]
    simp only [mul_assoc]
    rw [tsum_mul_left]
    have h := meanFitness_poissonWeight_fixed hs0.ne' U
    rw [meanFitness] at h
    rw [h]
  have hc1 : c = 1 := by
    rw [hW] at hWc
    have : c * Real.exp (-U) = 1 * Real.exp (-U) := by rw [← hWc, one_mul]
    exact mul_right_cancel₀ hE this
  rw [hxc, hc1]
  funext k
  rw [one_mul]

/-- Source: haigh1978, p. 253; etheridge_etal2007, Remark 4.2. -/
theorem eq_shift_poissonWeight_of_step_eq {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (U : ℝ)
    {x : ℕ → ℝ} {j : ℕ} (hfix : step s U x = x) (hlt : ∀ i, i < j → x i = 0) (hj : x j ≠ 0) :
    x = shift j (poissonWeight (U / s)) := by
  have hxy : x = shift j fun k => x (j + k) := by
    funext k
    rcases Nat.lt_or_ge k j with h | h
    · rw [shift_of_lt _ h, hlt k h]
    · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h
      rw [shift_add]
  have hfixy : step s U (fun k => x (j + k)) = fun k => x (j + k) := by
    have h : shift j (step s U fun k => x (j + k)) = shift j fun k => x (j + k) := by
      rw [← step_shift hs1.ne, ← hxy, hfix]
    funext k
    have hk := congrFun h (j + k)
    rwa [shift_add, shift_add] at hk
  have hy := eq_poissonWeight_of_step_eq hs0 hs1 U hfixy (by simpa using hj)
  rw [hxy, hy]

end Rhone.Dynamics.HaighRecursion
