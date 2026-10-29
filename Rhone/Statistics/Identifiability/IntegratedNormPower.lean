/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Tactic

/-! # Integrals of a density times powers of its cumulative function -/

@[expose] public section

open MeasureTheory Set Filter

namespace Rhone.Statistics.Identifiability.IntegratedNormPower

theorem absolutelyContinuousOnInterval_pow {f : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (n : ℕ) :
    AbsolutelyContinuousOnInterval (fun x => f x ^ n) a b := by
  induction n with
  | zero =>
      simpa using (LipschitzWith.const (1 : ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval
  | succ n ih =>
      simpa only [pow_succ] using ih.fun_mul hf

theorem intervalIntegrable_mul_cumulative_pow {g : ℝ → ℝ}
    (hg : LocallyIntegrable g volume) (a b : ℝ) (n : ℕ) :
    IntervalIntegrable (fun s => g s * (∫ u in a..s, g u) ^ n) volume a b := by
  have hi : IntervalIntegrable g volume a b :=
    intervalIntegrable_iff.mpr <|
      (hg.integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc
  have hac : AbsolutelyContinuousOnInterval (fun s => ∫ u in a..s, g u) a b :=
    hi.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  exact hi.mul_continuousOn (hac.continuousOn.fun_pow n)

theorem integral_mul_cumulative_pow {g : ℝ → ℝ}
    (hg : LocallyIntegrable g volume) (a b : ℝ) (n : ℕ) :
    (∫ s in a..b, g s * (∫ u in a..s, g u) ^ n) =
      (∫ s in a..b, g s) ^ (n + 1) / (n + 1 : ℝ) := by
  let G : ℝ → ℝ := fun s => ∫ u in a..s, g u
  have hi : IntervalIntegrable g volume a b :=
    intervalIntegrable_iff.mpr <|
      (hg.integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc
  have hac : AbsolutelyContinuousOnInterval G a b :=
    hi.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hpac := absolutelyContinuousOnInterval_pow hac (n + 1)
  have hd : ∀ᵐ s, deriv (fun x => G x ^ (n + 1)) s =
      (n + 1 : ℝ) * (g s * G s ^ n) := by
    filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hg] with s hs
    have h := (hs a).fun_pow (n + 1)
    simpa only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one,
      mul_comm, mul_left_comm, G] using h.deriv
  have heq : (n + 1 : ℝ) * (∫ s in a..b, g s * G s ^ n) = G b ^ (n + 1) := by
    rw [← intervalIntegral.integral_const_mul]
    calc
      (∫ s in a..b, (n + 1 : ℝ) * (g s * G s ^ n)) =
          ∫ s in a..b, deriv (fun x => G x ^ (n + 1)) s := by
            apply intervalIntegral.integral_congr_ae
            filter_upwards [hd] with s hs _ using hs.symm
      _ = G b ^ (n + 1) - G a ^ (n + 1) := hpac.integral_deriv_eq_sub
      _ = G b ^ (n + 1) := by simp [G]
  apply (eq_div_iff (by positivity : (n + 1 : ℝ) ≠ 0)).mpr
  simpa [mul_comm, G] using heq

end Rhone.Statistics.Identifiability.IntegratedNormPower
