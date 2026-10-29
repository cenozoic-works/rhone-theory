/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Diffusion.GeneratorLimit
public import Rhone.Diffusion.Generator
public import Rhone.Analysis.WrightFisherGeneratorLimitTaylor
public import Rhone.MarkovChain.CanningsFourthMoment

/-! # Cannings models and the Wright–Fisher diffusion generator -/

@[expose] public section

namespace Rhone.Diffusion

open Polynomial Filter Topology MarkovChain Analysis

theorem exists_taylor_two_bound (p : ℝ[X]) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |p.eval y - p.eval x - (derivative p).eval x * (y - x)
        - (derivative (derivative p)).eval x / 2 * (y - x) ^ 2| ≤ K * |y - x| ^ 3 := by
  obtain ⟨q, hq⟩ : ∃ q : ℝ[X], q = derivative (derivative p) := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((derivative q).continuousOn (s := Set.Icc (0 : ℝ) 1))
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 ⟨le_rfl, zero_le_one⟩)
  have hL : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |q.eval x - q.eval y| ≤ C * |x - y| := by
    intro x hx y hy
    have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := fun t => q.eval t)
      (s := Set.Icc (0 : ℝ) 1) (C := C) (fun t _ => q.differentiableAt)
      (fun t ht => by rw [Polynomial.deriv]; exact hC t ht) (convex_Icc 0 1) hy hx
    simpa [Real.norm_eq_abs] using h
  refine ⟨C / 6, by positivity, fun x hx y hy => ?_⟩
  have h := Rhone.Analysis.abs_taylor_two_remainder_le (f := fun t => p.eval t)
    (f' := fun t => (derivative p).eval t) (f'' := fun t => q.eval t) (L := C)
    (fun t _ => (p.hasDerivAt t).hasDerivWithinAt)
    (fun t _ => by
      rw [hq]
      exact ((derivative p).hasDerivAt t).hasDerivWithinAt)
    hL hx hy
  rw [hq] at h
  exact h

theorem abs_pow_three_le (u : ℝ) {ε : ℝ} (hε : 0 < ε) :
    |u| ^ 3 ≤ (ε * u ^ 2 + u ^ 4 / ε) / 2 := by
  have h2 : u ^ 2 = |u| ^ 2 := (sq_abs u).symm
  have h4 : u ^ 4 = |u| ^ 4 := by
    calc u ^ 4 = (u ^ 2) ^ 2 := by ring
      _ = (|u| ^ 2) ^ 2 := by rw [h2]
      _ = |u| ^ 4 := by ring
  rw [h2, h4, ← sub_nonneg]
  have e : (ε * |u| ^ 2 + |u| ^ 4 / ε) / 2 - |u| ^ 3 = |u| ^ 2 * (ε - |u|) ^ 2 / (2 * ε) := by
    field_simp
    ring
  rw [e]
  positivity

theorem cannings_generatorError_le {p : ℝ[X]} {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |p.eval y - p.eval x - (derivative p).eval x * (y - x)
        - (derivative (derivative p)).eval x / 2 * (y - x) ^ 2| ≤ K * |y - x| ^ 3)
    {N : ℕ} {Ω : Type*} [Fintype Ω] (M : CanningsModel N Ω) (k : Fin N)
    (hvar : 0 < M.offspringVariance k) (i : Fin (N + 1)) :
    |((N : ℝ) - 1) / M.offspringVariance k *
        (M.countChain.expect ((fun y => p.eval y) ∘ fun j : Fin (N + 1) => ((j : ℕ) : ℝ) / N) i
          - p.eval (((i : ℕ) : ℝ) / N))
      - wfGenerator (fun y => p.eval y) (((i : ℕ) : ℝ) / N)| ≤
      16 * K * √(M.offspringAbsThirdMoment k / ((N : ℝ) * M.offspringVariance k)) := by
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast M.two_le_of_offspringVariance_pos k hvar
  have hNpos : (0 : ℝ) < N := by linarith
  have hN1 : (0 : ℝ) < (N : ℝ) - 1 := by linarith
  have hm3σ := M.offspringVariance_le_offspringAbsThirdMoment k
  have hE2' := M.countChain_expect_sq_increment k i
  have hE4' := M.countChain_expect_fourth_increment_le k i
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = M.offspringVariance k := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = M.offspringAbsThirdMoment k := ⟨_, rfl⟩
  rw [← hs] at hvar hm3σ hE2' ⊢
  rw [← hm] at hm3σ hE4' ⊢
  have hmpos : 0 < m := lt_of_lt_of_le hvar hm3σ
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = ((i : ℕ) : ℝ) / N := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : Fin (N + 1) → ℝ, y = fun j : Fin (N + 1) => ((j : ℕ) : ℝ) / N :=
    ⟨_, rfl⟩
  have hxI : x ∈ Set.Icc (0 : ℝ) 1 := by
    have hiN : ((i : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.lt_succ_iff.1 i.2
    rw [hx]
    exact ⟨div_nonneg (Nat.cast_nonneg _) hNpos.le, (div_le_one hNpos).2 hiN⟩
  have hyI : ∀ j, y j ∈ Set.Icc (0 : ℝ) 1 := by
    intro j
    have hjN : ((j : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.lt_succ_iff.1 j.2
    rw [hy]
    exact ⟨div_nonneg (Nat.cast_nonneg _) hNpos.le, (div_le_one hNpos).2 hjN⟩
  obtain ⟨P, hP⟩ : ∃ P : Fin (N + 1) → ℝ, P = M.countChain.P i := ⟨_, rfl⟩
  have hP0 : ∀ j, 0 ≤ P j := fun j => by
    rw [hP]
    exact M.countChain.nonneg i j
  have hP1 : ∑ j, P j = 1 := by
    rw [hP]
    exact M.countChain.row_sum i
  have hE1 : ∑ j, P j * (y j - x) = 0 := by
    have h := M.countChain_expect_count i
    rw [FinChain.expect_apply, ← hP] at h
    have e : ∀ j ∈ (Finset.univ : Finset (Fin (N + 1))),
        P j * (y j - x) = P j * ((j : ℕ) : ℝ) / N - x * P j := by
      intro j _
      rw [hy]
      ring
    rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.mul_sum,
      h, hP1, hx]
    ring
  have hE2 : ∑ j, P j * (y j - x) ^ 2 = s / ((N : ℝ) - 1) * (x * (1 - x)) := by
    rw [FinChain.expect_apply, ← hP] at hE2'
    have e : ∀ j ∈ (Finset.univ : Finset (Fin (N + 1))),
        P j * (y j - x) ^ 2 = P j * (((j : ℕ) : ℝ) - (i : ℕ)) ^ 2 / (N : ℝ) ^ 2 := by
      intro j _
      rw [hy, hx]
      field_simp
    rw [Finset.sum_congr rfl e, ← Finset.sum_div, hE2', hx]
    field_simp
  have hE4 : ∑ j, P j * (y j - x) ^ 4 ≤ 31 * (m / (N : ℝ) ^ 2) := by
    rw [FinChain.expect_apply, ← hP] at hE4'
    have e : ∀ j ∈ (Finset.univ : Finset (Fin (N + 1))),
        P j * (y j - x) ^ 4 = P j * (((j : ℕ) : ℝ) - (i : ℕ)) ^ 4 / (N : ℝ) ^ 4 := by
      intro j _
      rw [hy, hx]
      field_simp
    rw [Finset.sum_congr rfl e, ← Finset.sum_div]
    refine (div_le_div_of_nonneg_right hE4' (by positivity)).trans_eq ?_
    field_simp
  obtain ⟨d1, hd1⟩ : ∃ d : ℝ, d = (derivative p).eval x := ⟨_, rfl⟩
  obtain ⟨d2, hd2⟩ : ∃ d : ℝ, d = (derivative (derivative p)).eval x := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : Fin (N + 1) → ℝ, R = fun j =>
      p.eval (y j) - p.eval x - d1 * (y j - x) - d2 / 2 * (y j - x) ^ 2 := ⟨_, rfl⟩
  have hRle : ∀ j, |R j| ≤ K * |y j - x| ^ 3 := by
    intro j
    rw [hR, hd1, hd2]
    exact hK x hxI (y j) (hyI j)
  have hexp : M.countChain.expect
      ((fun y => p.eval y) ∘ fun j : Fin (N + 1) => ((j : ℕ) : ℝ) / N) i =
      ∑ j, P j * p.eval (y j) := by
    rw [hP, hy]
    rfl
  have hdecomp : ∑ j, P j * p.eval (y j) - p.eval x =
      d2 / 2 * (s / ((N : ℝ) - 1) * (x * (1 - x))) + ∑ j, P j * R j := by
    calc ∑ j, P j * p.eval (y j) - p.eval x
        = ∑ j, P j * p.eval (y j) - ∑ j, P j * p.eval x := by
          rw [← Finset.sum_mul _ _ (p.eval x), hP1, one_mul]
      _ = ∑ j, (d1 * (P j * (y j - x)) + d2 / 2 * (P j * (y j - x) ^ 2) + P j * R j) := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hR]
          ring
      _ = d1 * ∑ j, P j * (y j - x) + d2 / 2 * ∑ j, P j * (y j - x) ^ 2 + ∑ j, P j * R j := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
            ← Finset.mul_sum]
      _ = d2 / 2 * (s / ((N : ℝ) - 1) * (x * (1 - x))) + ∑ j, P j * R j := by
          rw [hE1, hE2]
          ring
  obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, τ = ((N : ℝ) - 1) / s := ⟨_, rfl⟩
  have hτpos : 0 < τ := by
    rw [hτ]
    exact div_pos hN1 hvar
  have hτc : τ * (s / ((N : ℝ) - 1)) = 1 := by
    rw [hτ]
    field_simp
  have herr : τ * (M.countChain.expect
      ((fun y => p.eval y) ∘ fun j : Fin (N + 1) => ((j : ℕ) : ℝ) / N) i - p.eval x)
      - wfGenerator (fun y => p.eval y) x = τ * ∑ j, P j * R j := by
    rw [hexp, hdecomp, wfGenerator_eval, ← hd2]
    linear_combination (d2 / 2 * (x * (1 - x))) * hτc
  rw [← hx, ← hτ, herr, abs_mul, abs_of_pos hτpos]
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = ∑ j, P j * |y j - x| ^ 3 := ⟨_, rfl⟩
  have hsumR : |∑ j, P j * R j| ≤ K * T := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [hT, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [abs_mul, abs_of_nonneg (hP0 j)]
    calc P j * |R j| ≤ P j * (K * |y j - x| ^ 3) :=
          mul_le_mul_of_nonneg_left (hRle j) (hP0 j)
      _ = K * (P j * |y j - x| ^ 3) := by ring
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = m / ((N : ℝ) * s) := ⟨_, rfl⟩
  have hδpos : 0 < δ := by
    rw [hδ]
    positivity
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = √δ := ⟨_, rfl⟩
  have hεpos : 0 < ε := by
    rw [hε]
    exact Real.sqrt_pos.2 hδpos
  have hεsq : ε * ε = δ := by
    rw [hε]
    exact Real.mul_self_sqrt hδpos.le
  have hTle : T ≤ (ε * (s / ((N : ℝ) - 1) * (x * (1 - x))) + 31 * (m / (N : ℝ) ^ 2) / ε) / 2 := by
    have hpt : ∀ j ∈ (Finset.univ : Finset (Fin (N + 1))), P j * |y j - x| ^ 3 ≤
        (ε * (P j * (y j - x) ^ 2) + P j * (y j - x) ^ 4 / ε) / 2 := by
      intro j _
      have h := mul_le_mul_of_nonneg_left (abs_pow_three_le (y j - x) hεpos) (hP0 j)
      refine h.trans_eq ?_
      ring
    rw [hT]
    refine (Finset.sum_le_sum hpt).trans ?_
    rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div, hE2]
    have h4 := div_le_div_of_nonneg_right hE4 hεpos.le
    linarith
  have hτδ : τ * (m / (N : ℝ) ^ 2) ≤ δ := by
    have e : τ * (m / (N : ℝ) ^ 2) = (((N : ℝ) - 1) / N) * δ := by
      rw [hτ, hδ]
      field_simp
    rw [e]
    have hfrac : ((N : ℝ) - 1) / N ≤ 1 := by
      rw [div_le_one hNpos]
      linarith
    exact (mul_le_mul_of_nonneg_right hfrac hδpos.le).trans_eq (one_mul δ)
  have hq0 : 0 ≤ x * (1 - x) := mul_nonneg hxI.1 (by linarith [hxI.2])
  have hq1 : x * (1 - x) ≤ 1 / 4 := by nlinarith [sq_nonneg (x - 1 / 2)]
  have hτT : τ * T ≤ 16 * ε := by
    have h1 : τ * T ≤
        τ * ((ε * (s / ((N : ℝ) - 1) * (x * (1 - x))) + 31 * (m / (N : ℝ) ^ 2) / ε) / 2) :=
      mul_le_mul_of_nonneg_left hTle hτpos.le
    have e : τ * ((ε * (s / ((N : ℝ) - 1) * (x * (1 - x))) + 31 * (m / (N : ℝ) ^ 2) / ε) / 2) =
        (ε * (x * (1 - x)) * (τ * (s / ((N : ℝ) - 1))) +
          31 * (τ * (m / (N : ℝ) ^ 2)) / ε) / 2 := by
      ring
    rw [e, hτc] at h1
    have h2 : 31 * (τ * (m / (N : ℝ) ^ 2)) / ε ≤ 31 * ε := by
      rw [div_le_iff₀ hεpos, mul_assoc 31 ε ε, hεsq]
      linarith
    have h3 : ε * (x * (1 - x)) ≤ ε * (1 / 4) := mul_le_mul_of_nonneg_left hq1 hεpos.le
    linarith
  calc τ * |∑ j, P j * R j| ≤ τ * (K * T) := mul_le_mul_of_nonneg_left hsumR hτpos.le
    _ = K * (τ * T) := by ring
    _ ≤ K * (16 * ε) := mul_le_mul_of_nonneg_left hτT hK0
    _ = 16 * K * √(m / ((N : ℝ) * s)) := by
        rw [hε, hδ]
        ring

theorem cannings_generatorLimit {Ω : ℕ → Type*} [∀ n, Fintype (Ω n)] (N : ℕ → ℕ)
    (M : ∀ n, CanningsModel (N n) (Ω n)) (k : ∀ n, Fin (N n))
    (hvar : ∀ᶠ n in atTop, 0 < (M n).offspringVariance (k n))
    (h3 : Tendsto (fun n => (M n).offspringAbsThirdMoment (k n) /
      ((N n : ℝ) * (M n).offspringVariance (k n))) atTop (𝓝 0)) :
    GeneratorLimit (Sₙ := fun n => Fin (N n + 1)) (fun n => (M n).countChain)
      (fun n => ((N n : ℝ) - 1) / (M n).offspringVariance (k n))
      (fun n i => ((i : ℕ) : ℝ) / N n) wfGenerator polynomialFunctions := by
  refine GeneratorLimit.of_bound fun f hf => ?_
  obtain ⟨p, rfl⟩ := hf
  obtain ⟨K, hK0, hK⟩ := exists_taylor_two_bound p
  refine ⟨fun n => 16 * K * √((M n).offspringAbsThirdMoment (k n) /
    ((N n : ℝ) * (M n).offspringVariance (k n))), ?_, ?_⟩
  · have h := (h3.sqrt).const_mul (16 * K)
    simpa using h
  · filter_upwards [hvar] with n hn i
    exact cannings_generatorError_le hK0 hK (M n) (k n) hn i

theorem cannings_generatorLimit_of_factorialMoment {Ω : ℕ → Type*} [∀ n, Fintype (Ω n)]
    (N : ℕ → ℕ) (M : ∀ n, CanningsModel (N n) (Ω n)) (k : ∀ n, Fin (N n))
    (hN : Tendsto (fun n => (N n : ℝ)) atTop atTop)
    (hvar : ∀ᶠ n in atTop, 0 < (M n).offspringVariance (k n))
    (h3 : Tendsto (fun n => (M n).offspringThirdFactorialMoment (k n) /
      ((N n : ℝ) * (M n).offspringVariance (k n))) atTop (𝓝 0)) :
    GeneratorLimit (Sₙ := fun n => Fin (N n + 1)) (fun n => (M n).countChain)
      (fun n => ((N n : ℝ) - 1) / (M n).offspringVariance (k n))
      (fun n i => ((i : ℕ) : ℝ) / N n) wfGenerator polynomialFunctions := by
  refine cannings_generatorLimit N M k hvar ?_
  have hup : Tendsto (fun n => 1 / (N n : ℝ) + 4 / 3 *
      ((M n).offspringThirdFactorialMoment (k n) /
        ((N n : ℝ) * (M n).offspringVariance (k n)))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => 1 / (N n : ℝ)) atTop (𝓝 0) := by
      simp only [one_div]
      exact hN.inv_tendsto_atTop
    have h := h1.add (h3.const_mul (4 / 3))
    simpa using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [hvar] with n hn
    have hNpos : (0 : ℝ) < N n := by exact_mod_cast Fin.pos (k n)
    exact div_nonneg ((M n).offspringAbsThirdMoment_nonneg (k n)) (mul_pos hNpos hn).le
  · filter_upwards [hvar] with n hn
    have hNpos : (0 : ℝ) < N n := by exact_mod_cast Fin.pos (k n)
    have hle := (M n).offspringAbsThirdMoment_le (k n)
    have hden : 0 < (N n : ℝ) * (M n).offspringVariance (k n) := mul_pos hNpos hn
    refine (div_le_div_of_nonneg_right hle hden.le).trans_eq ?_
    field_simp

theorem moranModel_offspringAbsThirdMoment (N : ℕ) (hN : 0 < N) (k : Fin N) :
    (moranModel N hN).offspringAbsThirdMoment k = (moranModel N hN).offspringVariance k := by
  refine Finset.sum_congr rfl fun pd _ => ?_
  congr 1
  change |((moranOffspring N pd k : ℕ) : ℝ) - 1| ^ 3 = (((moranOffspring N pd k : ℕ) : ℝ) - 1) ^ 2
  unfold moranOffspring
  split_ifs <;> norm_num

theorem moranModel_generatorLimit :
    GeneratorLimit (Sₙ := fun n => Fin (n + 1 + 1))
      (fun n => (moranModel (n + 1) n.succ_pos).countChain)
      (fun n => (((n + 1 : ℕ) : ℝ) - 1) / (moranModel (n + 1) n.succ_pos).offspringVariance 0)
      (fun n i => ((i : ℕ) : ℝ) / (n + 1 : ℕ)) wfGenerator polynomialFunctions := by
  have hvar : ∀ᶠ n : ℕ in atTop, 0 < (moranModel (n + 1) n.succ_pos).offspringVariance 0 := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [moranModel_offspringVariance]
    have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    push_cast
    have hnum : (0 : ℝ) < 2 * ((n : ℝ) + 1 - 1) := by linarith
    positivity
  have h3 : Tendsto (fun n : ℕ => (moranModel (n + 1) n.succ_pos).offspringAbsThirdMoment 0 /
      (((n + 1 : ℕ) : ℝ) * (moranModel (n + 1) n.succ_pos).offspringVariance 0)) atTop
      (𝓝 0) := by
    refine Tendsto.congr' ?_ tendsto_one_div_add_atTop_nhds_zero_nat
    filter_upwards [hvar] with n hn
    rw [moranModel_offspringAbsThirdMoment]
    push_cast
    field_simp
  exact cannings_generatorLimit (fun n => n + 1) (fun n => moranModel (n + 1) n.succ_pos)
    (fun _ => 0) hvar h3

end Rhone.Diffusion
