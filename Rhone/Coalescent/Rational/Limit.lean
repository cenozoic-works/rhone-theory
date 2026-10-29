/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.Rational.Rho
public import Rhone.Probability.RecombinationExpansion.Limit
public import Rhone.Coalescent.TwoLocusGenealogy.Limit

/-! # Large-ρ limit of the sampling probability exists and equals `q_A(m^A) q_B(m^B)` -/

@[expose] public section

namespace Rhone.Coalescent.Rational

open Filter Topology Finset LinearAlgebra.Recursion LinearAlgebra.Recursion.Config

variable {KA KB : ℕ} {θA θB : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ}

noncomputable def qAt (hθA : 0 < θA) (hθB : 0 < θB) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ)
    (ρ : ℝ) : Config KA KB → ℝ :=
  if h : 0 ≤ ρ then LinearAlgebra.Recursion.q (πA := πA) (πB := πB) hθA hθB h else fun _ => 0

theorem qAt_eq_q (hθA : 0 < θA) (hθB : 0 < θB) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    qAt hθA hθB πA πB ρ = LinearAlgebra.Recursion.q (πA := πA) (πB := πB) hθA hθB hρ := by
  rw [qAt, dite_eq_left hρ]

theorem qAt_isSolution (hθA : 0 < θA) (hθB : 0 < θB) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    IsSolution θA θB ρ πA πB (qAt hθA hθB πA πB ρ) := by
  rw [qAt_eq_q hθA hθB hρ]
  exact LinearAlgebra.Recursion.q_isSolution hθA hθB hρ

theorem abs_qAt_le_one (hθA : 0 < θA) (hθB : 0 < θB) (hπA : ∀ i, 0 ≤ πA i)
    (hsA : ∑ i, πA i = 1) (hπB : ∀ j, 0 ≤ πB j) (hsB : ∑ j, πB j = 1) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (ξ : Config KA KB) : |qAt hθA hθB πA πB ρ ξ| ≤ 1 := by
  rw [qAt_eq_q hθA hθB hρ, abs_le]
  constructor
  · linarith [TwoLocusGenealogy.q_nonneg hθA hθB hρ hπA hsA hπB hsB ξ]
  · exact TwoLocusGenealogy.q_le_one hθA hθB hρ hπA hsA hπB hsB ξ

theorem exists_ratio_degree_le (hθA : 0 < θA) (hθB : 0 < θB) (hπA : ∀ i, 0 ≤ πA i)
    (hsA : ∑ i, πA i = 1) (hπB : ∀ j, 0 ≤ πB j) (hsB : ∑ j, πB j = 1) (ξ : Config KA KB) :
    ∃ p d : Polynomial ℝ, d ≠ 0 ∧ p.degree ≤ d.degree ∧
      (fun ρ => qAt hθA hθB πA πB ρ ξ)
        =ᶠ[atTop] fun ρ => Polynomial.eval ρ p / Polynomial.eval ρ d := by
  obtain ⟨p, d, hd, _, hq⟩ := Algebra.Rational.exists_ratio_config (πA := πA) (πB := πB) hθA hθB ξ
  have heq : (fun ρ => qAt hθA hθB πA πB ρ ξ)
      =ᶠ[atTop] fun ρ => Polynomial.eval ρ p / Polynomial.eval ρ d := by
    filter_upwards [eventually_ge_atTop (0 : ℝ), Polynomial.eventually_atTop_not_isRoot d hd]
      with ρ h1 h2
    rw [qAt_eq_q hθA hθB h1]
    exact hq ρ h1 h2
  refine ⟨p, d, hd, ?_, heq⟩
  by_contra hdeg
  rw [not_le] at hdeg
  have hbig := Polynomial.abs_div_tendsto_atTop_atTop_of_degree_gt p d hdeg hd
  have h2 : ∀ᶠ ρ in atTop, (2 : ℝ) ≤ |Polynomial.eval ρ p / Polynomial.eval ρ d| :=
    hbig.eventually_ge_atTop 2
  have h1 : ∀ᶠ ρ in atTop, |Polynomial.eval ρ p / Polynomial.eval ρ d| ≤ 1 := by
    filter_upwards [heq, eventually_ge_atTop (0 : ℝ)] with ρ he hρ
    rw [← he]
    exact abs_qAt_le_one hθA hθB hπA hsA hπB hsB hρ ξ
  obtain ⟨ρ, hρ2, hρ1⟩ := (h2.and h1).exists
  linarith

theorem exists_tendsto (hθA : 0 < θA) (hθB : 0 < θB) (hπA : ∀ i, 0 ≤ πA i)
    (hsA : ∑ i, πA i = 1) (hπB : ∀ j, 0 ≤ πB j) (hsB : ∑ j, πB j = 1) (ξ : Config KA KB) :
    ∃ L : ℝ, Tendsto (fun ρ => qAt hθA hθB πA πB ρ ξ) atTop (𝓝 L) := by
  obtain ⟨p, d, hd, hdeg, heq⟩ :=
    exists_ratio_degree_le hθA hθB hπA hsA hπB hsB ξ
  rcases lt_or_eq_of_le hdeg with h | h
  · exact ⟨0, (Polynomial.div_tendsto_atTop_zero_of_degree_lt p d h).congr' heq.symm⟩
  · exact ⟨p.leadingCoeff / d.leadingCoeff,
      (Polynomial.div_tendsto_atTop_leadingCoeff_div_of_degree_eq p d h).congr' heq.symm⟩

theorem tendsto_q_qHat (hθA : 0 < θA) (hθB : 0 < θB) (hπA : ∀ i, 0 ≤ πA i)
    (hsA : ∑ i, πA i = 1) (hπB : ∀ j, 0 ≤ πB j) (hsB : ∑ j, πB j = 1) (ξ : Config KA KB) :
    Tendsto (fun ρ => qAt hθA hθB πA πB ρ ξ) atTop
      (𝓝 (qOne θA πA ξ.mA * qOne θB πB ξ.mB)) :=
  Probability.RecombinationExpansion.tendsto_qHat_of_tendsto hθA hθB
    (fun _ hρ => qAt_isSolution hθA hθB (le_of_lt hρ))
    (fun η => exists_tendsto hθA hθB hπA hsA hπB hsB η) ξ

end Rhone.Coalescent.Rational
