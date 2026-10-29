/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Diffusion.WrightStationaryDensitySelection
public import Rhone.Analysis.TruncationRemainder.Comparison
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # The uniform-beta Wright marginal as a worked example of weak-selection moments -/
@[expose] public section
namespace Rhone.Diffusion.WeakSelectionFinite
open Polynomial MeasureTheory Set Analysis.TruncationRemainder
open scoped Interval

noncomputable def numerator (s : ℝ) (n : ℕ) : ℝ :=
  ∫ x in (0 : ℝ)..1, x ^ n * Real.exp (s * x)
noncomputable def normalizer (s : ℝ) : ℝ := numerator s 0
noncomputable def moment (s : ℝ) (n : ℕ) : ℝ := numerator s n / normalizer s

theorem density_eq (s x : ℝ) : wrightDensitySel (s / 2) 1 1 x = Real.exp (s * x) := by
  unfold wrightDensitySel wrightDensity
  simp only [sub_self, Real.rpow_zero, mul_one]
  congr 1
  ring

theorem moment_eq (s : ℝ) (n : ℕ) : moment s n = numerator s n / normalizer s := by
  rfl

theorem numerator_integrable (s : ℝ) (n : ℕ) :
    IntervalIntegrable (fun x : ℝ => x ^ n * Real.exp (s * x)) volume 0 1 := by
  exact (by fun_prop : Continuous (fun x : ℝ => x ^ n * Real.exp (s * x))).intervalIntegrable _ _

theorem normalizer_pos (s : ℝ) : 0 < normalizer s := by
  have h := integral_wrightDensitySel_pos (s / 2) (show (0 : ℝ) < 1 by norm_num)
    (show (0 : ℝ) < 1 by norm_num)
  simpa [normalizer, numerator, density_eq] using h

theorem numerator_nonneg (s : ℝ) (n : ℕ) : 0 ≤ numerator s n := by
  apply intervalIntegral.integral_nonneg zero_le_one
  intro x hx
  exact mul_nonneg (pow_nonneg hx.1 _) (Real.exp_pos _).le

theorem numerator_le_normalizer (s : ℝ) (n : ℕ) : numerator s n ≤ normalizer s := by
  apply intervalIntegral.integral_mono_on zero_le_one (numerator_integrable s n)
    (numerator_integrable s 0)
  intro x hx
  simp only [pow_zero, one_mul]
  exact mul_le_of_le_one_left (Real.exp_pos _).le (pow_le_one₀ hx.1 hx.2)

theorem moment_mem_unit (s : ℝ) (n : ℕ) : 0 ≤ moment s n ∧ moment s n ≤ 1 := by
  rw [moment_eq]
  exact ⟨div_nonneg (numerator_nonneg s n) (normalizer_pos s).le,
    (div_le_one (normalizer_pos s)).2 (numerator_le_normalizer s n)⟩

theorem moment_zero (s : ℝ) : moment s 0 = 1 := by
  rw [moment_eq]
  exact div_self (normalizer_pos s).ne'

noncomputable def samplingDensity (s x : ℝ) : ℝ := Real.exp (s * x) / normalizer s

theorem samplingDensity_pos (s x : ℝ) : 0 < samplingDensity s x := by
  exact div_pos (Real.exp_pos _) (normalizer_pos s)

theorem samplingDensity_normalized (s : ℝ) :
    ∫ x in (0 : ℝ)..1, samplingDensity s x = 1 := by
  unfold samplingDensity
  rw [intervalIntegral.integral_div]
  have hn : (∫ x in (0 : ℝ)..1, Real.exp (s * x)) = normalizer s := by
    simp [normalizer, numerator]
  rw [hn, div_self (normalizer_pos s).ne']

theorem samplingDensity_stationary (s : ℝ) (p : ℝ[X]) :
    ∫ x in (0 : ℝ)..1,
      Rhone.Diffusion.wfGeneratorForces (s / 2) 1 1 (fun y => p.eval y) x *
        samplingDensity s x = 0 := by
  have h := integral_wfGeneratorForces_polynomial_mul_wrightDensitySel (s / 2)
    (show (0 : ℝ) < 1 by norm_num) (show (0 : ℝ) < 1 by norm_num) p
  simp only [density_eq] at h
  simp only [samplingDensity, ← mul_div_assoc]
  rw [intervalIntegral.integral_div, h, zero_div]

noncomputable def samplingLaw (s : ℝ) : Measure ℝ :=
  (volume.restrict (Ioc (0 : ℝ) 1)).withDensity (fun x => ENNReal.ofReal (samplingDensity s x))

theorem samplingLaw_isProbability (s : ℝ) : IsProbabilityMeasure (samplingLaw s) := by
  have hI : IntervalIntegrable (samplingDensity s) volume 0 1 := by
    have h : Continuous (samplingDensity s) := by unfold samplingDensity; fun_prop
    exact h.intervalIntegrable _ _
  have hOn := (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp hI
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] samplingDensity s :=
    Filter.Eventually.of_forall (fun x => (samplingDensity_pos s x).le)
  rw [isProbabilityMeasure_iff, samplingLaw, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, ← ofReal_integral_eq_lintegral_ofReal hOn hnn,
    ← intervalIntegral.integral_of_le zero_le_one, samplingDensity_normalized]
  norm_num

theorem samplingLaw_integral (s : ℝ) (f : ℝ → ℝ) :
    ∫ x, f x ∂samplingLaw s = ∫ x in (0 : ℝ)..1, f x * samplingDensity s x := by
  have hm : Measurable (fun x => ENNReal.ofReal (samplingDensity s x)) := by
    have h : Continuous (samplingDensity s) := by unfold samplingDensity; fun_prop
    exact h.measurable.ennreal_ofReal
  have ht : ∀ᵐ x ∂(volume.restrict (Ioc (0 : ℝ) 1)),
      ENNReal.ofReal (samplingDensity s x) < (⊤ : ENNReal) :=
    Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  rw [samplingLaw, integral_withDensity_eq_integral_toReal_smul hm ht,
    intervalIntegral.integral_of_le zero_le_one]
  apply integral_congr_ae
  filter_upwards with x
  rw [ENNReal.toReal_ofReal (samplingDensity_pos s x).le, smul_eq_mul, mul_comm]

theorem moment_is_law_moment (s : ℝ) (n : ℕ) : moment s n = ∫ x, x ^ n ∂samplingLaw s := by
  rw [samplingLaw_integral]
  have he : (fun x : ℝ => x ^ n * samplingDensity s x) =
      fun x => (x ^ n * Real.exp (s * x)) / normalizer s := by
    funext x; unfold samplingDensity; ring
  rw [he, intervalIntegral.integral_div]
  rfl

theorem samplingLaw_stationary (s : ℝ) (p : ℝ[X]) :
    ∫ x, Rhone.Diffusion.wfGeneratorForces (s / 2) 1 1
      (fun y => p.eval y) x ∂samplingLaw s = 0 := by
  rw [samplingLaw_integral]
  exact samplingDensity_stationary s p

noncomputable def T (w : ℕ → ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else (n : ℝ) / (n + 1) * w (n - 1)
noncomputable def U (w : ℕ → ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else (w n - w (n + 1)) / (n + 1)
noncomputable def v (n : ℕ) : ℝ := if n = 0 then 1 else 0
noncomputable def neutral (n : ℕ) : ℝ := 1 / (n + 1)
noncomputable def response (n : ℕ) : ℝ := (n : ℝ) / (2 * (n + 1) * (n + 2))
noncomputable def weight (n : ℕ) : ℝ := 2 ^ n

theorem T_linear : IsLinear T := by
  constructor
  · intro w z n; by_cases h : n = 0 <;> simp [T, h, mul_add]
  · intro a w n; by_cases h : n = 0 <;> simp [T, h]; ring

theorem U_linear : IsLinear U := by
  constructor
  · intro w z n; by_cases h : n = 0 <;> simp [U, h]; ring
  · intro a w n; by_cases h : n = 0 <;> simp [U, h]; ring

theorem neutral_fixed : ∀ n, neutral n = T neutral n + v n := by
  intro n
  cases n with
  | zero => norm_num [neutral, T, v]
  | succ n => simp only [neutral, T, v, Nat.succ_ne_zero, ite_false, Nat.succ_sub_one,
      Nat.cast_succ]; field_simp; ring

theorem response_fixed : ∀ n, response n = T response n + U neutral n := by
  intro n
  cases n with
  | zero => norm_num [response, T, U]
  | succ n =>
    simp only [response, neutral, T, U, Nat.succ_ne_zero, ite_false,
      Nat.succ_sub_one, Nat.cast_succ]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    field_simp
    ring

theorem weight_nonneg (n : ℕ) : 0 ≤ weight n := by unfold weight; positivity

theorem weight_ge_one (n : ℕ) : 1 ≤ weight n := by
  exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)

theorem moment_bounded (s : ℝ) : BoundBy weight 1 (moment s) := by
  intro n
  simpa [abs_of_nonneg (moment_mem_unit s n).1] using
    (moment_mem_unit s n).2.trans (weight_ge_one n)

theorem numerator_rec (s : ℝ) (n : ℕ) :
    (n + 2 : ℝ) * numerator s (n + 1) =
      (n + 1 : ℝ) * numerator s n + s * (numerator s (n + 1) - numerator s (n + 2)) := by
  let F : ℝ → ℝ := fun x => x ^ (n + 1) * (1 - x) * Real.exp (s * x)
  let G : ℝ → ℝ := fun x =>
    ((n + 1 : ℝ) * x ^ n - (n + 2 : ℝ) * x ^ (n + 1)
      + s * (x ^ (n + 1) - x ^ (n + 2))) * Real.exp (s * x)
  have hF : Continuous F := by unfold F; fun_prop
  have hG : Continuous G := by unfold G; fun_prop
  have hd : ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt F (G x) x := by
    intro x _
    have hp := (hasDerivAt_id x).pow (n + 1)
    have hl := (hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)
    have he := ((hasDerivAt_id x).const_mul s).exp
    have h := (hp.mul hl).mul he
    change HasDerivAt F _ x at h
    refine h.congr_deriv ?_
    dsimp [G]
    simp only [Nat.cast_add, Nat.cast_one, mul_one, zero_sub, pow_succ]
    ring
  have hi : ∫ x in (0 : ℝ)..1, G x = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
      hF.continuousOn hd (hG.intervalIntegrable _ _)]
    simp [F]
  have heq : G = fun x =>
      (n + 1 : ℝ) * (x ^ n * Real.exp (s * x))
      - (n + 2 : ℝ) * (x ^ (n + 1) * Real.exp (s * x))
      + s * (x ^ (n + 1) * Real.exp (s * x) - x ^ (n + 2) * Real.exp (s * x)) := by
    funext x; dsimp [G]; ring
  have he : (∫ x in (0 : ℝ)..1, G x) =
      (n + 1 : ℝ) * numerator s n - (n + 2 : ℝ) * numerator s (n + 1)
      + s * (numerator s (n + 1) - numerator s (n + 2)) := by
    rw [heq, intervalIntegral.integral_add, intervalIntegral.integral_sub,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_sub]
    · rfl
    all_goals first
      | exact (numerator_integrable s _).const_mul _
      | exact numerator_integrable s _
      | exact ((numerator_integrable s _).const_mul _).sub ((numerator_integrable s _).const_mul _)
      | exact ((numerator_integrable s _).sub (numerator_integrable s _)).const_mul _
  rw [he] at hi
  linarith

theorem moment_fixed (s : ℝ) : ∀ n, moment s n = T (moment s) n + s * U (moment s) n + v n := by
  intro n
  cases n with
  | zero => simp [T, U, v, moment_zero]
  | succ n =>
    have h := numerator_rec s n
    simp only [T, U, v, Nat.succ_ne_zero, ite_false, Nat.succ_sub_one, Nat.cast_succ]
    simp only [moment_eq]
    have hn : (n + 1 + 1 : ℝ) ≠ 0 := by positivity
    have hz := (normalizer_pos s).ne'
    field_simp
    nlinarith [h]

theorem T_dominates : Dominates weight T (1/2) := by
  intro w C hC hw n
  cases n with
  | zero => simp only [T, ite_true, abs_zero, weight, pow_zero, mul_one]; positivity
  | succ n =>
    have hn : (0 : ℝ) ≤ n + 1 := by positivity
    have hd : (0 : ℝ) < n + 1 + 1 := by positivity
    have hc : (n + 1 : ℝ) / (n + 1 + 1) ≤ 1 := (div_le_one hd).2 (by linarith)
    have hc0 : (0 : ℝ) ≤ (n + 1 : ℝ) / (n + 1 + 1) := div_nonneg hn hd.le
    simp only [T, Nat.succ_ne_zero, ite_false, Nat.succ_sub_one, Nat.cast_succ,
      abs_mul, abs_of_nonneg hc0]
    calc
      _ ≤ ((n + 1 : ℝ) / (n + 1 + 1)) * (C * weight n) :=
        mul_le_mul_of_nonneg_left (hw n) hc0
      _ ≤ C * weight n := mul_le_of_le_one_left (mul_nonneg hC (weight_nonneg n)) hc
      _ = C * (1 - 1/2) * weight (n + 1) := by simp [weight, pow_succ]; ring

theorem U_bounded : UBoundedBy weight U (3/2) := by
  intro w C hC hw n
  cases n with
  | zero => simp only [U, ite_true, abs_zero, weight, pow_zero, mul_one]; positivity
  | succ n =>
    have hd : (0 : ℝ) < n + 1 + 1 := by positivity
    have hnum : |w (n + 1) - w (n + 1 + 1)| ≤ C * (3 * weight (n + 1)) := by
      calc
        _ ≤ |w (n + 1)| + |w (n + 1 + 1)| := abs_sub _ _
        _ ≤ C * weight (n + 1) + C * weight (n + 1 + 1) := add_le_add (hw _) (hw _)
        _ = _ := by simp [weight, pow_succ]; ring
    simp only [U, Nat.succ_ne_zero, ite_false, Nat.cast_succ, abs_div, abs_of_pos hd]
    apply (div_le_iff₀ hd).2
    have hm := mul_nonneg hC (weight_nonneg (n + 1))
    nlinarith

theorem neutral_bounded : BoundBy weight 1 neutral := by
  intro n
  have h : (0 : ℝ) < n + 1 := by positivity
  have hn : (0 : ℝ) ≤ 1 / (n + 1) := by positivity
  have hle : (1 : ℝ) / (n + 1) ≤ 1 := (div_le_one h).2 (by exact_mod_cast Nat.le_add_left 1 n)
  change |1 / ((n : ℝ) + 1)| ≤ 1 * weight n
  rw [abs_of_nonneg hn, one_mul]
  exact hle.trans (weight_ge_one n)

theorem response_bounded : BoundBy weight 1 response := by
  intro n
  have hn : (0 : ℝ) ≤ response n := by unfold response; positivity
  have hle : response n ≤ 1 := by
    unfold response
    apply (div_le_one (by positivity)).2
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  simpa [abs_of_nonneg hn] using hle.trans (weight_ge_one n)

theorem d12_first_order (s : ℝ) (n : ℕ) :
    |moment s n - (neutral n + s * response n)| ≤ 9 * s ^ 2 * weight n := by
  let R0 : ℕ → ℝ := fun n => moment s n - neutral n
  let R1 : ℕ → ℝ := fun n => moment s n - (neutral n + s * response n)
  have hR0 : ∀ n, R0 n = T R0 n + s * U (moment s) n := by
    intro n
    have h := moment_fixed s n
    have hq := neutral_fixed n
    have ht := T_linear.map_sub (moment s) neutral n
    simp only [R0] at *
    linarith
  have bR0 : BoundBy weight 2 R0 := by
    have h := (moment_bounded s).sub neutral_bounded
    norm_num only at h
    exact h
  have fR0 : BoundBy weight (|s| * (3/2)) (fun n => s * U (moment s) n) := by
    simpa using (U_bounded (moment s) 1 zero_le_one (moment_bounded s)).const_mul
  have refined0 : BoundBy weight (3 * |s|) R0 := by
    have h := bound_of_fixedPoint (by norm_num : (0 : ℝ) < 1/2) (by norm_num) T_dominates
      (by positivity : (0 : ℝ) ≤ |s| * (3/2)) (by norm_num : (0 : ℝ) ≤ 2)
      hR0 bR0 fR0
    convert h using 1; ring
  have hR1 : ∀ n, R1 n = T R1 n + s * U R0 n := by
    intro n
    have hu := moment_fixed s n
    have hq := neutral_fixed n
    have hd := response_fixed n
    have ht1 := T_linear.map_add neutral (fun j => s * response j) n
    have ht2 := T_linear.map_smul s response n
    have ht3 := T_linear.map_sub (moment s) (fun j => neutral j + s * response j) n
    have hu1 := U_linear.map_sub (moment s) neutral n
    have hds := congrArg (fun x : ℝ => s * x) hd
    dsimp [R0, R1]
    rw [ht3, ht1, ht2, hu1]
    linarith
  have bR1 : BoundBy weight (2 + |s|) R1 := by
    have h := (moment_bounded s).sub (neutral_bounded.add (response_bounded.const_mul (a := s)))
    convert h using 1; ring
  have fR1 : BoundBy weight (|s| * ((3 * |s|) * (3/2))) (fun n => s * U R0 n) :=
    (U_bounded R0 (3 * |s|) (by positivity) refined0).const_mul
  have h := bound_of_fixedPoint (by norm_num : (0 : ℝ) < 1/2) (by norm_num) T_dominates
    (by positivity : (0 : ℝ) ≤ |s| * ((3 * |s|) * (3/2))) (by positivity : (0 : ℝ) ≤ 2 + |s|)
    hR1 bR1 fR1 n
  change |moment s n - (neutral n + s * response n)| ≤ _ at h
  convert h using 1
  rw [← sq_abs]
  ring

theorem moment_at_zero (n : ℕ) : moment 0 n = neutral n := by
  have h := d12_first_order 0 n
  norm_num only [zero_mul, zero_pow (by decide : 2 ≠ 0), add_zero] at h
  exact sub_eq_zero.mp (abs_nonpos_iff.mp h)

theorem response_is_derivative (n : ℕ) : HasDerivAt (fun s : ℝ => moment s n) (response n) 0 := by
  apply HasDerivAt.of_isLittleO
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have hC : 0 < 9 * weight n := by unfold weight; positivity
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (div_pos hc hC)] with s hs
  simp only [Metric.mem_ball, Real.dist_eq, sub_zero] at hs
  simp only [moment_at_zero, sub_zero, smul_eq_mul, Real.norm_eq_abs]
  have hbound := d12_first_order s n
  have he : moment s n - neutral n - s * response n =
      moment s n - (neutral n + s * response n) := by ring
  rw [he]
  have hm := mul_le_mul_of_nonneg_right ((lt_div_iff₀ hC).mp hs).le (abs_nonneg s)
  have habs : |s| ^ 2 = s ^ 2 := sq_abs s
  nlinarith

noncomputable def orderedSampling (s : ℝ) (a b : ℕ) : ℝ :=
  (∫ x in (0 : ℝ)..1, x ^ a * (1 - x) ^ b * Real.exp (s * x)) / normalizer s

theorem orderedSampling_is_law_moment (s : ℝ) (a b : ℕ) :
    orderedSampling s a b = ∫ x, x ^ a * (1 - x) ^ b ∂samplingLaw s := by
  rw [samplingLaw_integral]
  have he : (fun x : ℝ => x ^ a * (1 - x) ^ b * samplingDensity s x) =
      fun x => (x ^ a * (1 - x) ^ b * Real.exp (s * x)) / normalizer s := by
    funext x; unfold samplingDensity; ring
  rw [he, intervalIntegral.integral_div]
  rfl

theorem orderedSampling_favoured (s : ℝ) (a : ℕ) : orderedSampling s a 0 = moment s a := by
  simp [orderedSampling, moment, numerator]

theorem orderedSampling_mixed (s : ℝ) : orderedSampling s 1 1 = moment s 1 - moment s 2 := by
  have hf : (fun x : ℝ => x ^ 1 * (1 - x) ^ 1 * Real.exp (s * x)) =
      fun x => x ^ 1 * Real.exp (s * x) - x ^ 2 * Real.exp (s * x) := by
    funext x; ring
  rw [orderedSampling, hf, intervalIntegral.integral_sub (numerator_integrable s 1)
    (numerator_integrable s 2)]
  simp only [moment, numerator, sub_div]

theorem orderedSampling_disfavoured_one (s : ℝ) : orderedSampling s 0 1 = 1 - moment s 1 := by
  have hf : (fun x : ℝ => x ^ 0 * (1 - x) ^ 1 * Real.exp (s * x)) =
      fun x => x ^ 0 * Real.exp (s * x) - x ^ 1 * Real.exp (s * x) := by
    funext x; ring
  rw [orderedSampling, hf, intervalIntegral.integral_sub (numerator_integrable s 0)
    (numerator_integrable s 1), sub_div]
  change moment s 0 - moment s 1 = _
  rw [moment_zero]

theorem orderedSampling_disfavoured_two (s : ℝ) :
    orderedSampling s 0 2 = 1 - 2 * moment s 1 + moment s 2 := by
  have hf : (fun x : ℝ => x ^ 0 * (1 - x) ^ 2 * Real.exp (s * x)) =
      fun x => (x ^ 0 * Real.exp (s * x) - 2 * (x ^ 1 * Real.exp (s * x)))
        + x ^ 2 * Real.exp (s * x) := by
    funext x; ring
  rw [orderedSampling, hf, intervalIntegral.integral_add,
    intervalIntegral.integral_sub, intervalIntegral.integral_const_mul]
  · simp only [add_div, sub_div, mul_div_assoc]
    change moment s 0 - 2 * moment s 1 + moment s 2 = _
    rw [moment_zero]
  · exact numerator_integrable s 0
  · exact (numerator_integrable s 1).const_mul 2
  · exact (numerator_integrable s 0).sub ((numerator_integrable s 1).const_mul 2)
  · exact numerator_integrable s 2

theorem d12_mixed (s : ℝ) : |orderedSampling s 1 1 - 1/6| ≤ 54 * s ^ 2 := by
  have h1 := d12_first_order s 1
  have h2 := d12_first_order s 2
  norm_num [neutral, response, weight] at h1 h2
  rw [orderedSampling_mixed]
  have he : moment s 1 - moment s 2 - 1/6 =
      (moment s 1 - (1/2 + s * (1/12))) - (moment s 2 - (1/3 + s * (1/12))) := by ring
  rw [he]
  exact (abs_sub _ _).trans (by linarith)

theorem d12_disfavoured_one (s : ℝ) :
    |orderedSampling s 0 1 - (1/2 - s/12)| ≤ 18 * s ^ 2 := by
  have h := d12_first_order s 1
  norm_num [neutral, response, weight] at h
  rw [orderedSampling_disfavoured_one]
  have he : 1 - moment s 1 - (1/2 - s/12) = -(moment s 1 - (1/2 + s * (1/12))) := by ring
  rw [he, abs_neg]
  convert h using 1; ring

theorem d12_disfavoured_two (s : ℝ) :
    |orderedSampling s 0 2 - (1/3 - s/12)| ≤ 72 * s ^ 2 := by
  have h1 := d12_first_order s 1
  have h2 := d12_first_order s 2
  norm_num [neutral, response, weight] at h1 h2
  rw [orderedSampling_disfavoured_two]
  have he : 1 - 2 * moment s 1 + moment s 2 - (1/3 - s/12) =
      -2 * (moment s 1 - (1/2 + s * (1/12))) + (moment s 2 - (1/3 + s * (1/12))) := by ring
  rw [he]
  calc
    _ ≤ |-2 * (moment s 1 - (1/2 + s * (1/12)))| + |moment s 2 - (1/3 + s * (1/12))| :=
      abs_add_le _ _
    _ = 2 * |moment s 1 - (1/2 + s * (1/12))| + |moment s 2 - (1/3 + s * (1/12))| := by
      rw [abs_mul]; norm_num
    _ ≤ 72 * s ^ 2 := by linarith

theorem orderedSampling_mem_unit (s : ℝ) (a b : ℕ) :
    0 ≤ orderedSampling s a b ∧ orderedSampling s a b ≤ 1 := by
  have hp : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ x ^ a * (1 - x) ^ b ∧ x ^ a * (1 - x) ^ b ≤ 1 := by
    intro x hx
    have hy0 : 0 ≤ 1-x := by linarith [hx.2]
    have hy1 : 1-x ≤ 1 := by linarith [hx.1]
    exact ⟨mul_nonneg (pow_nonneg hx.1 _) (pow_nonneg hy0 _),
      by
        simpa using mul_le_mul (pow_le_one₀ hx.1 hx.2) (pow_le_one₀ hy0 hy1)
          (pow_nonneg hy0 _) zero_le_one⟩
  have hI : IntervalIntegrable
      (fun x : ℝ => x ^ a * (1 - x) ^ b * Real.exp (s * x)) volume 0 1 := by
    have h : Continuous (fun x : ℝ => x ^ a * (1 - x) ^ b * Real.exp (s * x)) := by fun_prop
    exact h.intervalIntegrable _ _
  have hn : 0 ≤ ∫ x in (0 : ℝ)..1, x ^ a * (1 - x) ^ b * Real.exp (s * x) := by
    apply intervalIntegral.integral_nonneg zero_le_one
    intro x hx
    exact mul_nonneg (hp x hx).1 (Real.exp_pos _).le
  have hu : (∫ x in (0 : ℝ)..1, x ^ a * (1 - x) ^ b * Real.exp (s * x)) ≤ normalizer s := by
    apply intervalIntegral.integral_mono_on zero_le_one hI (numerator_integrable s 0)
    intro x hx
    simp only [pow_zero, one_mul]
    exact mul_le_of_le_one_left (Real.exp_pos _).le (hp x hx).2
  exact ⟨div_nonneg hn (normalizer_pos s).le, (div_le_one (normalizer_pos s)).2 hu⟩

theorem clipped_interval {q center radius : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (h : |q - center| ≤ radius) : max 0 (center - radius) ≤ q ∧ q ≤ min 1 (center + radius) := by
  have ha := abs_le.mp h
  exact ⟨max_le hq0 (by linarith [ha.1]), le_min hq1 (by linarith [ha.2])⟩

end Rhone.Diffusion.WeakSelectionFinite
