/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Diffusion.GeneratorLimit
public import Rhone.MarkovChain.CoreBridge
public import Rhone.Diffusion.Generator

/-! # The neutral Moran model and the Wright–Fisher diffusion generator -/

@[expose] public section

namespace Rhone.Diffusion

open Polynomial Filter Topology MarkovChain

theorem moran_generatorError_eq (p : ℝ[X]) {N : ℕ} (hN : 1 ≤ N) (i : Fin (N + 1)) :
    generatorError (Sₙ := fun N => Fin (N + 1)) (fun N => moranChain N 1 one_pos)
        (fun N => (N : ℝ) ^ 2 / 2) (fun N i => ((i : ℕ) : ℝ) / N) wfGenerator
        (fun y => p.eval y) N i =
      (N : ℝ) ^ 2 / 2 * (((i : ℕ) : ℝ) * ((N : ℝ) - (i : ℕ)) / (N : ℝ) ^ 2) *
        (p.eval (((i : ℕ) : ℝ) / N + 1 / (N : ℝ)) + p.eval (((i : ℕ) : ℝ) / N - 1 / (N : ℝ))
          - 2 * p.eval (((i : ℕ) : ℝ) / N)
          - (1 / (N : ℝ)) ^ 2 * (derivative (derivative p)).eval (((i : ℕ) : ℝ) / N)) := by
  have hn0 : (N : ℝ) ≠ 0 := by positivity
  obtain ⟨F, hF⟩ : ∃ F : ℕ → ℝ, F = fun j : ℕ => p.eval ((j : ℝ) / N) := ⟨_, rfl⟩
  have hexp : (moranChain N 1 one_pos).expect
      ((fun y => p.eval y) ∘ fun j : Fin (N + 1) => ((j : ℕ) : ℝ) / N) i =
      F i + moranUp N 1 i * (F (i + 1) - F i) + moranDown N 1 i * (F (i - 1) - F i) := by
    rw [hF]
    exact moran_expect (N := N) (r := 1) (fun j : ℕ => p.eval ((j : ℝ) / N)) i
  have hFi : F i = p.eval (((i : ℕ) : ℝ) / N) := by rw [hF]
  have hup : F (i + 1) = p.eval (((i : ℕ) : ℝ) / N + 1 / (N : ℝ)) := by
    rw [hF]
    change p.eval ((((i : ℕ) + 1 : ℕ) : ℝ) / N) = _
    congr 1
    push_cast
    ring
  have hdown : ((i : ℕ) : ℝ) * ((N : ℝ) - (i : ℕ)) / (N : ℝ) ^ 2 * (F (i - 1) - F i) =
      ((i : ℕ) : ℝ) * ((N : ℝ) - (i : ℕ)) / (N : ℝ) ^ 2 *
        (p.eval (((i : ℕ) : ℝ) / N - 1 / (N : ℝ)) - p.eval (((i : ℕ) : ℝ) / N)) := by
    rcases Nat.eq_zero_or_pos (i : ℕ) with h0 | hpos
    · rw [h0]
      simp
    · have h1 : F (i - 1) = p.eval (((i : ℕ) : ℝ) / N - 1 / (N : ℝ)) := by
        rw [hF]
        change p.eval ((((i : ℕ) - 1 : ℕ) : ℝ) / N) = _
        congr 1
        rw [Nat.cast_sub (show 1 ≤ (i : ℕ) from hpos)]
        push_cast
        ring
      rw [h1, hFi]
  have hq : ((i : ℕ) : ℝ) * ((N : ℝ) - (i : ℕ)) / (N : ℝ) ^ 2 =
      ((i : ℕ) : ℝ) / N * (1 - ((i : ℕ) : ℝ) / N) := by
    field_simp
  have hnh : (N : ℝ) ^ 2 * (1 / (N : ℝ)) ^ 2 = 1 := by
    field_simp
  change (N : ℝ) ^ 2 / 2 * ((moranChain N 1 one_pos).expect
      ((fun y => p.eval y) ∘ fun j : Fin (N + 1) => ((j : ℕ) : ℝ) / N) i -
        p.eval (((i : ℕ) : ℝ) / N)) - wfGenerator (fun y => p.eval y) (((i : ℕ) : ℝ) / N) = _
  rw [hexp, moranUp_one, moranDown_one, hdown, hup, hFi, wfGenerator_eval, ← hq]
  linear_combination (((i : ℕ) : ℝ) * ((N : ℝ) - (i : ℕ)) / (N : ℝ) ^ 2 *
    (derivative (derivative p)).eval (((i : ℕ) : ℝ) / N) / 2) * hnh

theorem moran_generatorLimit :
    GeneratorLimit (Sₙ := fun N => Fin (N + 1)) (fun N => moranChain N 1 one_pos)
      (fun N => (N : ℝ) ^ 2 / 2) (fun N i => ((i : ℕ) : ℝ) / N) wfGenerator
      polynomialFunctions := by
  refine GeneratorLimit.of_bound fun f hf => ?_
  obtain ⟨p, rfl⟩ := hf
  obtain ⟨K, hK0, hK⟩ := exists_second_difference_bound p
  refine ⟨fun N => K / 2 / N, tendsto_const_div_atTop_nhds_zero_nat _, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with N hN i
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hnpos : (0 : ℝ) < N := by linarith
  have hiN : ((i : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.lt_succ_iff.1 i.2
  have hi0 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
  have hxI : ((i : ℕ) : ℝ) / N ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg hi0 hnpos.le, (div_le_one hnpos).2 hiN⟩
  have hh0 : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
  have hh1 : |1 / (N : ℝ)| ≤ 1 := by
    rw [abs_of_nonneg hh0]
    exact (div_le_one hnpos).2 hn
  have hE := hK _ hxI _ hh1
  have hq : ((i : ℕ) : ℝ) * ((N : ℝ) - (i : ℕ)) / (N : ℝ) ^ 2 =
      ((i : ℕ) : ℝ) / N * (1 - ((i : ℕ) : ℝ) / N) := by
    field_simp
  have hq0 : 0 ≤ ((i : ℕ) : ℝ) * ((N : ℝ) - (i : ℕ)) / (N : ℝ) ^ 2 := by
    rw [hq]
    exact mul_nonneg hxI.1 (by linarith [hxI.2])
  have hq1 : ((i : ℕ) : ℝ) * ((N : ℝ) - (i : ℕ)) / (N : ℝ) ^ 2 ≤ 1 := by
    rw [hq]
    nlinarith [hxI.1, hxI.2]
  have hh3 : |1 / (N : ℝ)| ^ 3 = 1 / (N : ℝ) ^ 3 := by
    rw [abs_of_nonneg hh0]
    ring
  rw [hh3] at hE
  rw [moran_generatorError_eq p hN i, abs_mul, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ 2 / 2), abs_of_nonneg hq0]
  calc (N : ℝ) ^ 2 / 2 * (((i : ℕ) : ℝ) * ((N : ℝ) - (i : ℕ)) / (N : ℝ) ^ 2) * _
      ≤ (N : ℝ) ^ 2 / 2 * 1 * (K * (1 / (N : ℝ) ^ 3)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hq1 (by positivity)) hE (abs_nonneg _)
          (by positivity)
    _ = K / 2 / N := by
        field_simp

end Rhone.Diffusion
