/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Diffusion.GeneratorLimit
public import Rhone.MarkovChain.CoreBridge
public import Rhone.MarkovChain.WrightFisherDiploid
public import Rhone.Diffusion.Generator
public import Rhone.MarkovChain.WrightFisherGeneratorLimitMoments
public import Rhone.Analysis.WrightFisherGeneratorLimitTaylor
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Polynomial

/-!
# The neutral Wright–Fisher chain and the diffusion generator

Source: ewens2004, ch. 4; durrett2008, ch. 7; karlin_taylor1981, ch. 15; feller1951, sec. 8, eq.
(8.5)–(8.7), pp. 239–240. -/

@[expose] public section

namespace Rhone.Diffusion

open Finset Filter Topology MarkovChain

theorem wf_generator_error_le {f f' f'' : ℝ → ℝ} {L : ℝ}
    (hf : ∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt f (f' x) (Set.Icc 0 1) x)
    (hf' : ∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt f' (f'' x) (Set.Icc 0 1) x)
    (hL : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, |f'' x - f'' y| ≤ L * |x - y|)
    {N : ℕ} (hN : 1 ≤ N) (i : Fin (N + 1)) :
    |(N : ℝ) * ((wf N).expect (fun j => f ((j : ℝ) / N)) i - f ((i : ℝ) / N))
        - (i : ℝ) / N * (1 - (i : ℝ) / N) / 2 * f'' ((i : ℝ) / N)|
      ≤ 7 * L / (192 * √(N : ℝ)) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN0 : (N : ℝ) ≠ 0 := hNpos.ne'
  have hsq : 0 < √(N : ℝ) := Real.sqrt_pos.2 hNpos
  have hL0 : 0 ≤ L := by
    have h := hL 0 ⟨le_rfl, zero_le_one⟩ 1 ⟨zero_le_one, le_rfl⟩
    have h' : |(0 : ℝ) - 1| = 1 := by norm_num
    rw [h', mul_one] at h
    exact (abs_nonneg _).trans h
  have hx := freq_mem_Icc hN i
  have hP0 : ∀ j, 0 ≤ wf N i j := (wf_isStochastic N).1 i
  have hP1 : ∑ j, wf N i j = 1 := (wf_isStochastic N).2 i
  have hE1 := wf_expect_freq_sub hN i
  have hE2 := wf_expect_freq_sub_sq hN i
  have hE3 := wf_expect_abs_freq_sub_cube_le hN i
  simp only [CountKernel.expect] at hE1 hE2 hE3 ⊢
  obtain ⟨R, hRdef⟩ : ∃ R : Fin (N + 1) → ℝ, ∀ j, R j =
      f ((j : ℝ) / N) - f ((i : ℝ) / N) - f' ((i : ℝ) / N) * ((j : ℝ) / N - (i : ℝ) / N)
        - f'' ((i : ℝ) / N) / 2 * ((j : ℝ) / N - (i : ℝ) / N) ^ 2 := ⟨_, fun _ => rfl⟩
  have hR : ∀ j, |R j| ≤ L / 6 * |(j : ℝ) / N - (i : ℝ) / N| ^ 3 := by
    intro j
    rw [hRdef]
    exact Analysis.abs_taylor_two_remainder_le hf hf' hL hx (freq_mem_Icc hN j)
  have hdecomp : ∑ j, wf N i j * R j =
      ∑ j, wf N i j * f ((j : ℝ) / N) - f ((i : ℝ) / N) * ∑ j, wf N i j
        - f' ((i : ℝ) / N) * ∑ j, wf N i j * ((j : ℝ) / N - (i : ℝ) / N)
        - f'' ((i : ℝ) / N) / 2 * ∑ j, wf N i j * ((j : ℝ) / N - (i : ℝ) / N) ^ 2 := by
    rw [mul_sum, mul_sum, mul_sum, ← sum_sub_distrib, ← sum_sub_distrib, ← sum_sub_distrib]
    exact sum_congr rfl fun j _ => by rw [hRdef]; ring
  have hid : (N : ℝ) * (∑ j, wf N i j * f ((j : ℝ) / N) - f ((i : ℝ) / N))
      - (i : ℝ) / N * (1 - (i : ℝ) / N) / 2 * f'' ((i : ℝ) / N) =
      N * ∑ j, wf N i j * R j := by
    rw [hdecomp, hP1, hE1, hE2]
    field_simp
    ring
  rw [hid, abs_mul, abs_of_nonneg hNpos.le]
  have hsum : |∑ j, wf N i j * R j| ≤
      L / 6 * ∑ j, wf N i j * |(j : ℝ) / N - (i : ℝ) / N| ^ 3 := by
    calc |∑ j, wf N i j * R j| ≤ ∑ j, |wf N i j * R j| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, L / 6 * (wf N i j * |(j : ℝ) / N - (i : ℝ) / N| ^ 3) := by
          refine sum_le_sum fun j _ => ?_
          rw [abs_mul, abs_of_nonneg (hP0 j)]
          calc wf N i j * |R j| ≤ wf N i j * (L / 6 * |(j : ℝ) / N - (i : ℝ) / N| ^ 3) :=
                mul_le_mul_of_nonneg_left (hR j) (hP0 j)
            _ = L / 6 * (wf N i j * |(j : ℝ) / N - (i : ℝ) / N| ^ 3) := by ring
      _ = L / 6 * ∑ j, wf N i j * |(j : ℝ) / N - (i : ℝ) / N| ^ 3 := by rw [mul_sum]
  calc (N : ℝ) * |∑ j, wf N i j * R j|
      ≤ N * (L / 6 * (7 / (32 * (N * √(N : ℝ))))) := by
        refine mul_le_mul_of_nonneg_left (hsum.trans ?_) hNpos.le
        exact mul_le_mul_of_nonneg_left hE3 (by positivity)
    _ = 7 * L / (192 * √(N : ℝ)) := by
        field_simp
        ring

theorem wfDiploid_generator_error_le {f f' f'' : ℝ → ℝ} {L : ℝ}
    (hf : ∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt f (f' x) (Set.Icc 0 1) x)
    (hf' : ∀ x ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt f' (f'' x) (Set.Icc 0 1) x)
    (hL : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, |f'' x - f'' y| ≤ L * |x - y|)
    {N : ℕ} (hN : 1 ≤ N) (i : Fin (2 * N + 1)) :
    |((2 * N : ℕ) : ℝ) * ((wfDiploid N).expect (fun j => f ((j : ℝ) / (2 * N : ℕ))) i
          - f ((i : ℝ) / (2 * N : ℕ)))
        - (i : ℝ) / (2 * N : ℕ) * (1 - (i : ℝ) / (2 * N : ℕ)) / 2
          * f'' ((i : ℝ) / (2 * N : ℕ))|
      ≤ 7 * L / (192 * √((2 * N : ℕ) : ℝ)) :=
  wf_generator_error_le hf hf' hL (N := 2 * N) (by omega) i

theorem wfChain_generatorError_le {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f) {M : ℝ}
    (hM : ∀ x ∈ Set.Icc (0 : ℝ) 1, |deriv (deriv (deriv f)) x| ≤ M)
    {N : ℕ} (hN : 1 ≤ N) (i : Fin (N + 1)) :
    |generatorError (Sₙ := fun N => Fin (N + 1)) (fun N => wfChain N) (fun N => (N : ℝ))
        (fun N i => ((i : ℕ) : ℝ) / N) wfGenerator f N i| ≤ 7 * M / (192 * √(N : ℝ)) := by
  have e3 : ((2 : WithTop ℕ∞) + 1) = 3 := by norm_num
  have e2 : ((1 : WithTop ℕ∞) + 1) = 2 := by norm_num
  have hf3 : ContDiff ℝ (2 + 1) f := by rw [e3]; exact hf
  have h1 : ContDiff ℝ 2 (deriv f) := (contDiff_succ_iff_deriv.1 hf3).2.2
  have h1' : ContDiff ℝ (1 + 1) (deriv f) := by rw [e2]; exact h1
  have h2 : ContDiff ℝ 1 (deriv (deriv f)) := (contDiff_succ_iff_deriv.1 h1').2.2
  have d0 : ∀ x, HasDerivAt f (deriv f x) x := fun x =>
    ((hf.differentiable (by norm_num)) x).hasDerivAt
  have d1 : ∀ x, HasDerivAt (deriv f) (deriv (deriv f) x) x := fun x =>
    ((h1.differentiable (by norm_num)) x).hasDerivAt
  have d2 : ∀ x, DifferentiableAt ℝ (deriv (deriv f)) x := fun x =>
    (h2.differentiable (by norm_num)) x
  have hLip : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |deriv (deriv f) x - deriv (deriv f) y| ≤ M * |x - y| := by
    intro x hx y hy
    have := Convex.norm_image_sub_le_of_norm_deriv_le (f := deriv (deriv f)) (C := M)
      (s := Set.Icc (0 : ℝ) 1) (fun z _ => d2 z)
      (fun z hz => by rw [Real.norm_eq_abs]; exact hM z hz) (convex_Icc 0 1) hy hx
    simpa [Real.norm_eq_abs] using this
  exact wf_generator_error_le (fun x _ => (d0 x).hasDerivWithinAt)
    (fun x _ => (d1 x).hasDerivWithinAt) hLip hN i

theorem wf_generatorLimit :
    GeneratorLimit (Sₙ := fun N => Fin (N + 1)) (fun N => wfChain N) (fun N => (N : ℝ))
      (fun N i => ((i : ℕ) : ℝ) / N) wfGenerator {f | ContDiff ℝ 3 f} := by
  refine GeneratorLimit.of_bound fun f hf => ?_
  have hf' : ContDiff ℝ 3 f := hf
  have hc : Continuous (deriv (deriv (deriv f))) := by
    have e3 : ((2 : WithTop ℕ∞) + 1) = 3 := by norm_num
    have e2 : ((1 : WithTop ℕ∞) + 1) = 2 := by norm_num
    have hf3 : ContDiff ℝ (2 + 1) f := by rw [e3]; exact hf'
    have h1 : ContDiff ℝ 2 (deriv f) := (contDiff_succ_iff_deriv.1 hf3).2.2
    have h1' : ContDiff ℝ (1 + 1) (deriv f) := by rw [e2]; exact h1
    have h2 : ContDiff ℝ 1 (deriv (deriv f)) := (contDiff_succ_iff_deriv.1 h1').2.2
    exact h2.continuous_deriv le_rfl
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hc.continuousOn (s := Set.Icc (0 : ℝ) 1))
  have hsqrt : Tendsto (fun N : ℕ => √(N : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨fun N => 7 * M / (192 * √(N : ℝ)),
    tendsto_const_nhds.div_atTop (hsqrt.const_mul_atTop (by norm_num)), ?_⟩
  filter_upwards [eventually_ge_atTop 1] with N hN i
  exact wfChain_generatorError_le hf' (fun x hx => by simpa [Real.norm_eq_abs] using hM x hx)
    hN i

theorem wf_generatorLimit_polynomial :
    GeneratorLimit (Sₙ := fun N => Fin (N + 1)) (fun N => wfChain N) (fun N => (N : ℝ))
      (fun N i => ((i : ℕ) : ℝ) / N) wfGenerator polynomialFunctions := by
  refine wf_generatorLimit.mono ?_
  rintro _ ⟨p, rfl⟩
  have h := Polynomial.contDiff_aeval (𝕜 := ℝ) p 3
  simpa using h

end Rhone.Diffusion
