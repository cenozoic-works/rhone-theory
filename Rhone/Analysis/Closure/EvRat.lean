/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.Analysis.Polynomial.Basic

/-! # "Eventually rational in `ρ`": the small API behind the `1/ρ` expansion -/

@[expose] public section

namespace Rhone.Analysis.Closure

open Filter Topology

def EvRat (f : ℝ → ℝ) : Prop :=
  ∃ u d : Polynomial ℝ, d ≠ 0 ∧
    f =ᶠ[atTop] fun ρ => Polynomial.eval ρ u / Polynomial.eval ρ d

namespace EvRat

theorem congr' {f g : ℝ → ℝ} (hf : EvRat f) (h : g =ᶠ[atTop] f) : EvRat g := by
  obtain ⟨u, d, hd, hu⟩ := hf
  exact ⟨u, d, hd, h.trans hu⟩

theorem const (c : ℝ) : EvRat fun _ => c := by
  refine ⟨Polynomial.C c, 1, one_ne_zero, ?_⟩
  filter_upwards with ρ
  simp

theorem sub {f g : ℝ → ℝ} (hf : EvRat f) (hg : EvRat g) : EvRat fun ρ => f ρ - g ρ := by
  obtain ⟨u₁, d₁, hd₁, h₁⟩ := hf
  obtain ⟨u₂, d₂, hd₂, h₂⟩ := hg
  refine ⟨u₁ * d₂ - u₂ * d₁, d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
  filter_upwards [h₁, h₂, Polynomial.eventually_atTop_not_isRoot d₁ hd₁,
    Polynomial.eventually_atTop_not_isRoot d₂ hd₂] with ρ e₁ e₂ r₁ r₂
  have hn₁ : Polynomial.eval ρ d₁ ≠ 0 := fun h => r₁ h
  have hn₂ : Polynomial.eval ρ d₂ ≠ 0 := fun h => r₂ h
  rw [e₁, e₂]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul]
  field_simp

theorem mul_id {f : ℝ → ℝ} (hf : EvRat f) : EvRat fun ρ => ρ * f ρ := by
  obtain ⟨u, d, hd, hu⟩ := hf
  refine ⟨Polynomial.X * u, d, hd, ?_⟩
  filter_upwards [hu] with ρ e
  rw [e]
  simp [mul_div_assoc]

theorem exists_tendsto_mul {f : ℝ → ℝ} (hf : EvRat f) (h0 : Tendsto f atTop (𝓝 0)) :
    ∃ L : ℝ, Tendsto (fun ρ => ρ * f ρ) atTop (𝓝 L) := by
  obtain ⟨u, d, hd, hu⟩ := hf
  have hdeg : u.degree < d.degree :=
    (Polynomial.div_tendsto_atTop_zero_iff_degree_lt u d hd).mp (h0.congr' hu)
  have hdeg2 : (Polynomial.X * u).degree ≤ d.degree := by
    rcases eq_or_ne u 0 with rfl | hu0
    · simp
    · rw [Polynomial.degree_mul, Polynomial.degree_X, add_comm]
      exact Nat.WithBot.add_one_le_of_lt hdeg
  have heq2 : (fun ρ => ρ * f ρ)
      =ᶠ[atTop] fun ρ => Polynomial.eval ρ (Polynomial.X * u) / Polynomial.eval ρ d := by
    filter_upwards [hu] with ρ e
    rw [e]
    simp [mul_div_assoc]
  rcases lt_or_eq_of_le hdeg2 with h | h
  · exact ⟨0, (Polynomial.div_tendsto_atTop_zero_of_degree_lt _ d h).congr' heq2.symm⟩
  · exact ⟨(Polynomial.X * u).leadingCoeff / d.leadingCoeff,
      (Polynomial.div_tendsto_atTop_leadingCoeff_div_of_degree_eq _ d h).congr' heq2.symm⟩

end EvRat

end Rhone.Analysis.Closure
