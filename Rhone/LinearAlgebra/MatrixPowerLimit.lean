/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecificLimits.Basic

/-! # Powers of matrices close to the identity converge to a matrix exponential -/

@[expose] public section

open Filter Topology Asymptotics NormedSpace

section NormedAlgebra

variable {𝔸 : Type*} [NormedRing 𝔸] [NormOneClass 𝔸]

theorem Rhone.LinearAlgebra.norm_pow_sub_pow_le {A B : 𝔸} {R : ℝ} (hR : 1 ≤ R) (hA : ‖A‖ ≤ R)
    (hB : ‖B‖ ≤ R)
    (k : ℕ) : ‖A ^ k - B ^ k‖ ≤ k * R ^ k * ‖A - B‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hR0 : 0 ≤ R := zero_le_one.trans hR
    have e : A ^ (k + 1) - B ^ (k + 1) = A ^ k * (A - B) + (A ^ k - B ^ k) * B := by
      rw [pow_succ, pow_succ]
      noncomm_ring
    have hAk : ‖A ^ k‖ ≤ R ^ k :=
      (norm_pow_le A k).trans (pow_le_pow_left₀ (norm_nonneg _) hA k)
    have hx : 0 ≤ ‖A - B‖ := norm_nonneg _
    have h1 : ‖A ^ (k + 1) - B ^ (k + 1)‖ ≤ ‖A ^ k‖ * ‖A - B‖ + ‖A ^ k - B ^ k‖ * ‖B‖ := by
      rw [e]
      exact (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
    have h2 : ‖A ^ k‖ * ‖A - B‖ ≤ R ^ k * ‖A - B‖ := mul_le_mul_of_nonneg_right hAk hx
    have h3 : ‖A ^ k - B ^ k‖ * ‖B‖ ≤ (k * R ^ k * ‖A - B‖) * R :=
      mul_le_mul ih hB (norm_nonneg _) (by positivity)
    have h4 : R ^ k * ‖A - B‖ ≤ R ^ k * ‖A - B‖ * R :=
      le_mul_of_one_le_right (by positivity) hR
    have h5 : ((k + 1 : ℕ) : ℝ) * R ^ (k + 1) * ‖A - B‖ =
        k * R ^ k * ‖A - B‖ * R + R ^ k * ‖A - B‖ * R := by
      push_cast
      ring
    rw [h5]
    linarith

variable [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

theorem Rhone.LinearAlgebra.tendsto_pow_floor_exp {A : ℕ → 𝔸} {c : ℕ → ℝ} {Q : 𝔸}
    (hc : ∀ᶠ m in atTop, 0 < c m) (hc0 : Tendsto c atTop (𝓝 0))
    (hA : (fun m => A m - 1 - c m • Q) =o[atTop] c) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun m => A m ^ ⌊t / c m⌋₊) atTop (𝓝 (exp (t • Q))) := by
  let _ : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  have hB : (fun m => exp (c m • Q) - 1 - c m • Q) =o[atTop] c := by
    have hd := (hasDerivAt_exp_smul_const (𝕂 := ℝ) Q (0 : ℝ)).isLittleO.comp_tendsto hc0
    simpa [Function.comp_def] using hd
  have hAB : (fun m => A m - exp (c m • Q)) =o[atTop] c :=
    (hA.sub hB).congr_left fun m => by abel
  have hnorm : ∀ {F : ℕ → 𝔸}, (fun m => F m - 1 - c m • Q) =o[atTop] c →
      ∀ᶠ m in atTop, ‖F m‖ ≤ 1 + c m * (‖Q‖ + 1) := by
    intro F hF
    filter_upwards [hF.bound zero_lt_one, hc] with m hm hcm
    have e : F m = (F m - 1 - c m • Q) + 1 + c m • Q := by abel
    have h1 : ‖F m‖ ≤ ‖F m - 1 - c m • Q‖ + ‖(1 : 𝔸)‖ + ‖c m • Q‖ := by
      conv_lhs => rw [e]
      exact (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
    rw [norm_one, norm_smul, Real.norm_of_nonneg hcm.le] at h1
    rw [Real.norm_of_nonneg hcm.le, one_mul] at hm
    linarith
  have hdiff : Tendsto (fun m => A m ^ ⌊t / c m⌋₊ - exp (c m • Q) ^ ⌊t / c m⌋₊) atTop
      (𝓝 0) := by
    have hlim : Tendsto (fun m => t * Real.exp (t * (‖Q‖ + 1)) *
        (‖A m - exp (c m • Q)‖ / c m)) atTop (𝓝 0) := by
      have := (hAB.norm_left.tendsto_div_nhds_zero).const_mul (t * Real.exp (t * (‖Q‖ + 1)))
      simpa using this
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [hnorm hA, hnorm hB, hc] with m hAm hBm hcm
    have hk : (⌊t / c m⌋₊ : ℝ) ≤ t / c m := Nat.floor_le (div_nonneg ht hcm.le)
    have hQ : 0 ≤ ‖Q‖ + 1 := by positivity
    have hR1 : 1 ≤ 1 + c m * (‖Q‖ + 1) := le_add_of_nonneg_right (mul_nonneg hcm.le hQ)
    have hRk : (1 + c m * (‖Q‖ + 1)) ^ ⌊t / c m⌋₊ ≤ Real.exp (t * (‖Q‖ + 1)) := by
      have h1 : 1 + c m * (‖Q‖ + 1) ≤ Real.exp (c m * (‖Q‖ + 1)) := by
        linarith [Real.add_one_le_exp (c m * (‖Q‖ + 1))]
      calc (1 + c m * (‖Q‖ + 1)) ^ ⌊t / c m⌋₊
          ≤ Real.exp (c m * (‖Q‖ + 1)) ^ ⌊t / c m⌋₊ :=
            pow_le_pow_left₀ (zero_le_one.trans hR1) h1 _
        _ = Real.exp ((⌊t / c m⌋₊ : ℝ) * (c m * (‖Q‖ + 1))) := (Real.exp_nat_mul _ _).symm
        _ ≤ Real.exp (t * (‖Q‖ + 1)) := by
            refine Real.exp_le_exp.2 ?_
            have : (⌊t / c m⌋₊ : ℝ) * c m ≤ t := (le_div_iff₀ hcm).1 hk
            nlinarith
    have hx : 0 ≤ ‖A m - exp (c m • Q)‖ := norm_nonneg _
    calc ‖A m ^ ⌊t / c m⌋₊ - exp (c m • Q) ^ ⌊t / c m⌋₊‖
        ≤ ⌊t / c m⌋₊ * (1 + c m * (‖Q‖ + 1)) ^ ⌊t / c m⌋₊ * ‖A m - exp (c m • Q)‖ :=
          Rhone.LinearAlgebra.norm_pow_sub_pow_le hR1 hAm hBm _
      _ ≤ t / c m * Real.exp (t * (‖Q‖ + 1)) * ‖A m - exp (c m • Q)‖ := by
          gcongr
      _ = t * Real.exp (t * (‖Q‖ + 1)) * (‖A m - exp (c m • Q)‖ / c m) := by
          field_simp
  have hBlim : Tendsto (fun m => exp (c m • Q) ^ ⌊t / c m⌋₊) atTop (𝓝 (exp (t • Q))) := by
    have hkc : Tendsto (fun m => (⌊t / c m⌋₊ : ℝ) * c m) atTop (𝓝 t) := by
      have hlow : Tendsto (fun m => t - c m) atTop (𝓝 t) := by
        simpa using tendsto_const_nhds.sub hc0
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
      · filter_upwards [hc] with m hcm
        have h := Nat.lt_floor_add_one (t / c m)
        rw [div_lt_iff₀ hcm] at h
        linarith
      · filter_upwards [hc] with m hcm
        exact (le_div_iff₀ hcm).1 (Nat.floor_le (div_nonneg ht hcm.le))
    have hcont : Continuous fun u : ℝ => exp (u • Q) :=
      (exp_continuous (𝔸 := 𝔸)).comp (continuous_id.smul continuous_const)
    have h := (hcont.tendsto t).comp hkc
    refine h.congr fun m => ?_
    simp only [Function.comp_def]
    rw [← exp_nsmul, mul_smul, Nat.cast_smul_eq_nsmul]
  have h := hdiff.add hBlim
  simpa using h

end NormedAlgebra

theorem Matrix.tendsto_pow_floor_exp_apply {S : Type*} [Fintype S] [DecidableEq S]
    {A : ℕ → Matrix S S ℝ} {c : ℕ → ℝ} {Q : Matrix S S ℝ}
    (hc : ∀ᶠ m in atTop, 0 < c m) (hc0 : Tendsto c atTop (𝓝 0))
    (hA : ∀ x y, (fun m => A m x y - (1 : Matrix S S ℝ) x y - c m * Q x y) =o[atTop] c)
    {t : ℝ} (ht : 0 ≤ t) (x y : S) :
    Tendsto (fun m => (A m ^ ⌊t / c m⌋₊) x y) atTop (𝓝 (exp (t • Q) x y)) := by
  open scoped Matrix.Norms.Operator in
  have : Nonempty S := ⟨x⟩
  have hA' : (fun m => A m - 1 - c m • Q) =o[atTop] c := by
    have hsum : ∀ m, A m - 1 - c m • Q =
        ∑ i, ∑ j, (A m i j - (1 : Matrix S S ℝ) i j - c m * Q i j) •
          Matrix.single i j (1 : ℝ) := by
      intro m
      rw [Matrix.matrix_eq_sum_single (A m - 1 - c m • Q)]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.smul_single, smul_eq_mul, mul_one]
      simp [Matrix.sub_apply, Matrix.smul_apply]
    simp only [hsum]
    refine IsLittleO.fun_sum fun i _ => IsLittleO.fun_sum fun j _ => ?_
    refine IsLittleO.of_norm_left ?_
    simp only [norm_smul]
    exact ((hA i j).norm_left.const_mul_left ‖Matrix.single i j (1 : ℝ)‖).congr_left
      fun m => mul_comm _ _
  have h := Rhone.LinearAlgebra.tendsto_pow_floor_exp hc hc0 hA' ht
  exact ((LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℝ x y)).continuous.tendsto
    _).comp h
