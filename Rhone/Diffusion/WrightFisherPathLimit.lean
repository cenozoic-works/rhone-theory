/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Diffusion.ChainPathLimit
public import Rhone.Diffusion.WrightFisherUniqueness
public import Rhone.Diffusion.WrightFisherGeneratorLimit
public import Rhone.MarkovChain.FixationHarmonic

/-!
# The Wright–Fisher chain converges in law to the Wright–Fisher diffusion

Source: ethier_kurtz1986, ch. 10, sec. 1. -/

@[expose] public section

namespace Rhone.Diffusion

open MeasureTheory Filter Topology Set MarkovChain Analysis
open scoped NNReal BoundedContinuousFunction

theorem freq_mem_Icc' (N : ℕ) (i : Fin (N + 1)) : ((i : ℕ) : ℝ) / N ∈ Icc (0 : ℝ) 1 := by
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h
    simp
  · exact freq_mem_Icc h i

theorem wfChain_isHarmonic_freq (N : ℕ) :
    (wfChain N).IsHarmonic fun i => ((i : ℕ) : ℝ) / N :=
  (CountKernel.toFinChain_isHarmonic (wf N) (wf_isStochastic N) _).2
    (Rhone.MarkovChain.wf_isHarmonic_freq N)

theorem wfChain_expect_freq_sub_sq_le {N : ℕ} (hN : 1 ≤ N) (i : Fin (N + 1)) :
    (wfChain N).expect (fun j => (((j : ℕ) : ℝ) / N - ((i : ℕ) : ℝ) / N) ^ 2) i ≤
      (1 / 4) / (N : ℝ) := by
  rw [wfChain, CountKernel.toFinChain_expect, wf_expect_freq_sub_sq hN i]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hx := freq_mem_Icc hN i
  apply div_le_div_of_nonneg_right _ hNpos.le
  nlinarith [sq_nonneg (((i : ℕ) : ℝ) / N - 1 / 2)]

theorem wfChain_expect_freq_sub_pow_four_le {N : ℕ} (hN : 1 ≤ N) (i : Fin (N + 1)) :
    (wfChain N).expect (fun j => (((j : ℕ) : ℝ) / N - ((i : ℕ) : ℝ) / N) ^ 4) i ≤
      3 / (16 * (N : ℝ)) / N := by
  rw [wfChain, CountKernel.toFinChain_expect]
  refine (wf_expect_freq_sub_pow_four_le hN i).trans (le_of_eq ?_)
  rw [div_div, sq]
  ring

theorem polynomialFunctions_continuous :
    ∀ f ∈ polynomialFunctions, Continuous f ∧ Continuous (wfGenerator f) := by
  rintro _ ⟨p, rfl⟩
  refine ⟨p.continuous, ?_⟩
  have e : wfGenerator (fun y => p.eval y) =
      fun x => x * (1 - x) / 2 * (Polynomial.derivative (Polynomial.derivative p)).eval x :=
    funext fun x => wfGenerator_eval p x
  rw [e]
  fun_prop

theorem wf_tendsto_scale : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop

theorem wf_secondMoment_eventually :
    ∀ᶠ N : ℕ in atTop, ∀ z : Fin (N + 1),
      (wfChain N).expect (fun w => (((w : ℕ) : ℝ) / N - ((z : ℕ) : ℝ) / N) ^ 2) z ≤
        (1 / 4) / (N : ℝ) := by
  filter_upwards [eventually_ge_atTop 1] with N hN z
  exact wfChain_expect_freq_sub_sq_le hN z

theorem wf_fourthMoment_eventually :
    ∀ᶠ N : ℕ in atTop, ∀ z : Fin (N + 1),
      (wfChain N).expect (fun w => (((w : ℕ) : ℝ) / N - ((z : ℕ) : ℝ) / N) ^ 4) z ≤
        3 / (16 * (N : ℝ)) / N := by
  filter_upwards [eventually_ge_atTop 1] with N hN z
  exact wfChain_expect_freq_sub_pow_four_le hN z

theorem wf_fourthMoment_tendsto :
    Tendsto (fun N : ℕ => 3 / (16 * (N : ℝ))) atTop (𝓝 0) := by
  refine (tendsto_const_div_atTop_nhds_zero_nat (3 / 16 : ℝ)).congr fun N => ?_
  rw [div_div]

/-- Source: ethier_kurtz1986, ch. 10, sec. 1. -/
theorem wrightFisherDiffusionLaw_exists {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    ∃ P : Measure C(ℝ≥0, ℝ), IsWrightFisherDiffusionLaw x P := by
  have hle : ∀ N : ℕ, ⌊x * N⌋₊ < N + 1 := fun N => by
    have h1 : x * N ≤ N := by nlinarith [hx.2, (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
    exact Nat.lt_succ_of_le (Nat.floor_le_of_le h1 |>.trans (by simp))
  let i : ∀ N : ℕ, Fin (N + 1) := fun N => ⟨⌊x * N⌋₊, hle N⟩
  have hi : Tendsto (fun N : ℕ => ((i N : ℕ) : ℝ) / N) atTop (𝓝 x) := by
    have hb : Tendsto (fun N : ℕ => x - 1 / (N : ℝ)) atTop (𝓝 x) := by
      simpa using (tendsto_const_nhds (x := x)).sub tendsto_one_div_atTop_nhds_zero_nat
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hb tendsto_const_nhds ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with N hN
      have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
      have h1 : x * N - 1 < ⌊x * N⌋₊ := by
        have := Nat.lt_floor_add_one (x * N)
        linarith
      have e : x - 1 / (N : ℝ) = (x * N - 1) / N := by field_simp
      rw [e]
      exact div_le_div_of_nonneg_right h1.le hNpos.le
    · filter_upwards [eventually_ge_atTop 1] with N hN
      have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
      rw [div_le_iff₀ hNpos]
      exact Nat.floor_le (by have := hx.1; positivity)
  exact exists_isMartingaleSolution_of_chains (fun N => wfChain N)
    (fun N j => ((j : ℕ) : ℝ) / N) (fun N => (N : ℝ)) i wfChain_isHarmonic_freq freq_mem_Icc'
    wf_tendsto_scale (1 / 4) (fun N => 3 / (16 * (N : ℝ))) wf_secondMoment_eventually
    wf_fourthMoment_eventually wf_fourthMoment_tendsto wf_generatorLimit_polynomial
    polynomialFunctions_continuous hi

/-- Source: ethier_kurtz1986, ch. 10, sec. 1. -/
theorem wfChain_pathLaw_tendsto_wrightFisherDiffusion (i : ∀ N : ℕ, Fin (N + 1)) {x : ℝ}
    (hx : Tendsto (fun N : ℕ => ((i N : ℕ) : ℝ) / N) atTop (𝓝 x))
    {P : Measure C(ℝ≥0, ℝ)} (hP : IsWrightFisherDiffusionLaw x P) (F : C(ℝ≥0, ℝ) →ᵇ ℝ) :
    Tendsto (fun N : ℕ => ∫ ω, F (rescaledPath (N : ℝ) fun m => ((ω m : ℕ) : ℝ) / N)
        ∂((wfChain N).pathLaw (i N)))
      atTop (𝓝 (∫ w, F w ∂P)) :=
  tendsto_integral_of_chains (fun N => wfChain N) (fun N j => ((j : ℕ) : ℝ) / N)
    (fun N => (N : ℝ)) i wfChain_isHarmonic_freq freq_mem_Icc' wf_tendsto_scale (1 / 4)
    (fun N => 3 / (16 * (N : ℝ))) wf_secondMoment_eventually wf_fourthMoment_eventually
    wf_fourthMoment_tendsto wf_generatorLimit_polynomial polynomialFunctions_continuous hx hP
    (fun _ hQ => IsWrightFisherDiffusionLaw.unique hQ hP) F

end Rhone.Diffusion
