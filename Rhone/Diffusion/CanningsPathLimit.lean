/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Diffusion.WrightFisherPathLimit
public import Rhone.Diffusion.CanningsGeneratorLimit

/-!
# A sequence of Cannings models converges in law to the Wright–Fisher diffusion

Source: mohle2001, Thm 3.3, p. 143; ethier_kurtz1986, ch. 4. -/

@[expose] public section

namespace Rhone.Diffusion

open MeasureTheory Filter Topology Set MarkovChain Analysis
open scoped NNReal BoundedContinuousFunction

theorem FinChain.sq_expect_le {S : Type*} [Fintype S] (C : FinChain S) (h : S → ℝ) (x : S) :
    C.expect h x ^ 2 ≤ C.expect (fun y => h y ^ 2) x := by
  rw [FinChain.expect_apply, FinChain.expect_apply]
  set m := ∑ y, C.P x y * h y
  have h0 : 0 ≤ ∑ y, C.P x y * (h y - m) ^ 2 :=
    Finset.sum_nonneg fun y _ => mul_nonneg (C.nonneg x y) (sq_nonneg _)
  have e : ∀ y, C.P x y * (h y - m) ^ 2 =
      C.P x y * h y ^ 2 - 2 * m * (C.P x y * h y) + m ^ 2 * C.P x y := fun y => by ring
  rw [Finset.sum_congr rfl fun y _ => e y, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, C.row_sum x] at h0
  have hm : ∑ y, C.P x y * h y = m := rfl
  rw [hm] at h0
  nlinarith [h0]

theorem countChain_isHarmonic_freq {N : ℕ} {Ω : Type*} [Fintype Ω] (M : CanningsModel N Ω) :
    M.countChain.IsHarmonic fun i => ((i : ℕ) : ℝ) / N := by
  rw [FinChain.isHarmonic_iff]
  intro i
  have h := M.countChain_expect_count i
  rw [FinChain.expect_apply] at h
  simp_rw [mul_div_assoc']
  rw [← Finset.sum_div, h]

theorem countChain_expect_freq_pow {N : ℕ} {Ω : Type*} [Fintype Ω] (M : CanningsModel N Ω)
    (p : ℕ) (z : Fin (N + 1)) :
    M.countChain.expect (fun w => (((w : ℕ) : ℝ) / N - ((z : ℕ) : ℝ) / N) ^ p) z =
      M.countChain.expect (fun w => (((w : ℕ) : ℝ) - (z : ℕ)) ^ p) z / (N : ℝ) ^ p := by
  rw [FinChain.expect_apply, FinChain.expect_apply, Finset.sum_div]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← sub_div, div_pow, mul_div_assoc]

theorem offspringVariance_sq_le {N : ℕ} {Ω : Type*} [Fintype Ω] (M : CanningsModel N Ω)
    (k : Fin N) (hvar : 0 < M.offspringVariance k) :
    M.offspringVariance k ^ 2 ≤ 496 * M.offspringAbsThirdMoment k := by
  have hN2 : 2 ≤ N := M.two_le_of_offspringVariance_pos k hvar
  let z : Fin (N + 1) := ⟨N / 2, by omega⟩
  have hz1 : 2 * (N / 2) ≤ N := Nat.mul_div_le N 2
  have hz2 : N ≤ 2 * (N / 2) + 1 := by omega
  have hz1' : 2 * ((z : ℕ) : ℝ) ≤ N := by exact_mod_cast hz1
  have hz2' : (N : ℝ) ≤ 2 * ((z : ℕ) : ℝ) + 1 := by exact_mod_cast hz2
  have hz0 : (0 : ℝ) ≤ ((z : ℕ) : ℝ) := Nat.cast_nonneg _
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hN1 : (0 : ℝ) < (N : ℝ) - 1 := by linarith
  have hprod : (N : ℝ) * ((N : ℝ) - 1) ≤ 4 * (((z : ℕ) : ℝ) * ((N : ℝ) - (z : ℕ))) := by
    nlinarith [mul_nonneg (sub_nonneg.2 hz1') (sub_nonneg.2 hz2')]
  have h2 := M.countChain_expect_sq_increment k z
  have h4 := M.countChain_expect_fourth_increment_le k z
  have hJ := FinChain.sq_expect_le M.countChain (fun w => (((w : ℕ) : ℝ) - (z : ℕ)) ^ 2) z
  have e4 : (fun y : Fin (N + 1) => ((((y : ℕ) : ℝ) - (z : ℕ)) ^ 2) ^ 2) =
      fun y : Fin (N + 1) => (((y : ℕ) : ℝ) - (z : ℕ)) ^ 4 := funext fun y => by ring
  rw [e4, h2] at hJ
  set σ2 := M.offspringVariance k
  have hm2 : σ2 * N / 4 ≤ σ2 / ((N : ℝ) - 1) * (((z : ℕ) : ℝ) * ((N : ℝ) - (z : ℕ))) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hN1, div_mul_eq_mul_div, div_le_iff₀ (by norm_num)]
    nlinarith
  have hm2' : (σ2 * N / 4) ^ 2 ≤ 31 * (N : ℝ) ^ 2 * M.offspringAbsThirdMoment k :=
    (pow_le_pow_left₀ (by positivity) hm2 2).trans (hJ.trans h4)
  have hNsq : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
  have h' : (N : ℝ) ^ 2 * σ2 ^ 2 ≤ (N : ℝ) ^ 2 * (496 * M.offspringAbsThirdMoment k) := by
    nlinarith
  exact le_of_mul_le_mul_left h' hNsq

theorem cannings_tendsto_scale {Ω : ℕ → Type*} [∀ n, Fintype (Ω n)] (N : ℕ → ℕ)
    (M : ∀ n, CanningsModel (N n) (Ω n)) (k : ∀ n, Fin (N n))
    (hvar : ∀ᶠ n in atTop, 0 < (M n).offspringVariance (k n))
    (h3 : Tendsto (fun n => (M n).offspringAbsThirdMoment (k n) /
      ((N n : ℝ) * (M n).offspringVariance (k n))) atTop (𝓝 0)) :
    Tendsto (fun n => ((N n : ℝ) - 1) / (M n).offspringVariance (k n)) atTop atTop := by
  have hsmall : Tendsto (fun n => (M n).offspringVariance (k n) / N n) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      ((h3.const_mul 496).trans (by rw [mul_zero])) ?_ ?_
    · filter_upwards [hvar] with n hn
      positivity
    · filter_upwards [hvar] with n hn
      have hN : (0 : ℝ) < N n := by
        have := (M n).two_le_of_offspringVariance_pos (k n) hn
        exact_mod_cast (by omega : 0 < N n)
      have hb := offspringVariance_sq_le (M n) (k n) hn
      rw [div_le_iff₀ hN, mul_div_assoc', div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      nlinarith
  have hpos : Tendsto (fun n => (M n).offspringVariance (k n) / N n) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hsmall, ?_⟩
    filter_upwards [hvar] with n hn
    have hN : (0 : ℝ) < N n := by
      have := (M n).two_le_of_offspringVariance_pos (k n) hn
      exact_mod_cast (by omega : 0 < N n)
    exact div_pos hn hN
  have hinv := (hpos.inv_tendsto_nhdsGT_zero).atTop_div_const (by norm_num : (0 : ℝ) < 2)
  refine tendsto_atTop_mono' atTop ?_ hinv
  filter_upwards [hvar] with n hn
  have hN2 : (2 : ℝ) ≤ N n := by
    exact_mod_cast (M n).two_le_of_offspringVariance_pos (k n) hn
  simp only [Pi.inv_apply, inv_div]
  rw [div_div, div_le_div_iff₀ (by positivity) hn]
  nlinarith [mul_nonneg (sub_nonneg.2 hN2) hn.le]

/-- Source: mohle2001, Thm 3.3, p. 143; ethier_kurtz1986, ch. 4. -/
theorem cannings_pathLaw_tendsto_wrightFisherDiffusion {Ω : ℕ → Type*} [∀ n, Fintype (Ω n)]
    (N : ℕ → ℕ) (M : ∀ n, CanningsModel (N n) (Ω n)) (k : ∀ n, Fin (N n))
    (hvar : ∀ᶠ n in atTop, 0 < (M n).offspringVariance (k n))
    (h3 : Tendsto (fun n => (M n).offspringAbsThirdMoment (k n) /
      ((N n : ℝ) * (M n).offspringVariance (k n))) atTop (𝓝 0))
    (i : ∀ n, Fin (N n + 1)) {x : ℝ}
    (hx : Tendsto (fun n => ((i n : ℕ) : ℝ) / N n) atTop (𝓝 x))
    {P : Measure C(ℝ≥0, ℝ)} (hP : IsWrightFisherDiffusionLaw x P) (F : C(ℝ≥0, ℝ) →ᵇ ℝ) :
    Tendsto (fun n => ∫ ω, F (rescaledPath (((N n : ℝ) - 1) / (M n).offspringVariance (k n))
        fun m => ((ω m : ℕ) : ℝ) / N n) ∂((M n).countChain.pathLaw (i n)))
      atTop (𝓝 (∫ w, F w ∂P)) := by
  have hv : ∀ᶠ n in atTop, ∀ z : Fin (N n + 1),
      (M n).countChain.expect (fun w => (((w : ℕ) : ℝ) / N n - ((z : ℕ) : ℝ) / N n) ^ 2) z ≤
        (1 / 4) / (((N n : ℝ) - 1) / (M n).offspringVariance (k n)) := by
    filter_upwards [hvar] with n hn z
    have hN2 : (2 : ℝ) ≤ N n := by
      exact_mod_cast (M n).two_le_of_offspringVariance_pos (k n) hn
    have hN1 : (0 : ℝ) < (N n : ℝ) - 1 := by linarith
    have hz0 : (0 : ℝ) ≤ ((z : ℕ) : ℝ) := Nat.cast_nonneg _
    rw [countChain_expect_freq_pow, (M n).countChain_expect_sq_increment (k n) z]
    have hq : ((z : ℕ) : ℝ) * ((N n : ℝ) - (z : ℕ)) / (N n : ℝ) ^ 2 ≤ 1 / 4 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [sq_nonneg ((N n : ℝ) - 2 * (z : ℕ))]
    have hA : 0 ≤ (M n).offspringVariance (k n) / ((N n : ℝ) - 1) := by positivity
    calc (M n).offspringVariance (k n) / ((N n : ℝ) - 1) *
          (((z : ℕ) : ℝ) * ((N n : ℝ) - (z : ℕ))) / (N n : ℝ) ^ 2
        = (M n).offspringVariance (k n) / ((N n : ℝ) - 1) *
          (((z : ℕ) : ℝ) * ((N n : ℝ) - (z : ℕ)) / (N n : ℝ) ^ 2) := mul_div_assoc _ _ _
      _ ≤ (M n).offspringVariance (k n) / ((N n : ℝ) - 1) * (1 / 4) :=
          mul_le_mul_of_nonneg_left hq hA
      _ = (1 / 4) / (((N n : ℝ) - 1) / (M n).offspringVariance (k n)) := by
          field_simp
  have hq : ∀ᶠ n in atTop, ∀ z : Fin (N n + 1),
      (M n).countChain.expect (fun w => (((w : ℕ) : ℝ) / N n - ((z : ℕ) : ℝ) / N n) ^ 4) z ≤
        (31 * ((M n).offspringAbsThirdMoment (k n) /
          ((N n : ℝ) * (M n).offspringVariance (k n)))) /
          (((N n : ℝ) - 1) / (M n).offspringVariance (k n)) := by
    filter_upwards [hvar] with n hn z
    have hN2 : (2 : ℝ) ≤ N n := by
      exact_mod_cast (M n).two_le_of_offspringVariance_pos (k n) hn
    have hN1 : (0 : ℝ) < (N n : ℝ) - 1 := by linarith
    have hN0 : (0 : ℝ) < N n := by linarith
    have h3n := (M n).offspringAbsThirdMoment_nonneg (k n)
    rw [countChain_expect_freq_pow]
    calc (M n).countChain.expect (fun w => (((w : ℕ) : ℝ) - (z : ℕ)) ^ 4) z / (N n : ℝ) ^ 4
        ≤ 31 * (N n : ℝ) ^ 2 * (M n).offspringAbsThirdMoment (k n) / (N n : ℝ) ^ 4 :=
          div_le_div_of_nonneg_right ((M n).countChain_expect_fourth_increment_le (k n) z)
            (by positivity)
      _ = 31 * (M n).offspringAbsThirdMoment (k n) / ((N n : ℝ) * N n) := by
          field_simp
      _ ≤ 31 * (M n).offspringAbsThirdMoment (k n) / ((N n : ℝ) * ((N n : ℝ) - 1)) :=
          div_le_div_of_nonneg_left (by positivity) (mul_pos hN0 hN1)
            (mul_le_mul_of_nonneg_left (by linarith) hN0.le)
      _ = (31 * ((M n).offspringAbsThirdMoment (k n) /
            ((N n : ℝ) * (M n).offspringVariance (k n)))) /
            (((N n : ℝ) - 1) / (M n).offspringVariance (k n)) := by
          field_simp
  have he : Tendsto (fun n => 31 * ((M n).offspringAbsThirdMoment (k n) /
      ((N n : ℝ) * (M n).offspringVariance (k n)))) atTop (𝓝 0) := by
    simpa using h3.const_mul 31
  exact tendsto_integral_of_chains (fun n => (M n).countChain) (fun n j => ((j : ℕ) : ℝ) / N n)
    (fun n => ((N n : ℝ) - 1) / (M n).offspringVariance (k n)) i
    (fun n => countChain_isHarmonic_freq (M n)) (fun n => freq_mem_Icc' (N n))
    (cannings_tendsto_scale N M k hvar h3) (1 / 4) _ hv hq he
    (cannings_generatorLimit N M k hvar h3) polynomialFunctions_continuous hx hP
    (fun _ hQ => IsWrightFisherDiffusionLaw.unique hQ hP) F

end Rhone.Diffusion
