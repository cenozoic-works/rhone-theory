/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.CanningsAncestralExpansion
public import Rhone.LinearAlgebra.MatrixPowerLimit
public import Rhone.MarkovChain.Semigroup
public import Rhone.MarkovChain.CanningsFourthMoment

/-!
# Cannings ancestral chains converge to Kingman's coalescent

Source: mohle_sagitov2001, pp. 1549–1551, eq. (5)–(9), Thm 2.1. -/

@[expose] public section

namespace Rhone.Coalescent

open Finset Filter Topology Asymptotics Rhone.LinearAlgebra MarkovChain Rhone.Combinatorics

section Moments

variable {N : ℕ} {Ω : Type*} [Fintype Ω] (M : CanningsModel N Ω)

theorem sum_w_mul_ν (k : Fin N) : ∑ ω, M.w ω * (M.ν ω k : ℝ) = 1 := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Fin.pos k).ne'
  have h := M.sum_w_mul_sum_parents (fun a => (a : ℝ)) k
  have h1 : ∑ ω, M.w ω * ∑ p, (M.ν ω p : ℝ) = N := by
    simp only [M.sum_ν_cast, ← Finset.sum_mul, M.sum_w, one_mul]
  exact mul_left_cancel₀ hN (by rw [← h, h1, mul_one])

theorem pairCoalProb_eq_offspringVariance (k : Fin N) :
    M.pairCoalProb = M.offspringVariance k / ((N : ℝ) - 1) := by
  rw [M.pairCoalProb_eq k, CanningsModel.offspringVariance]
  congr 1
  have h1 := sum_w_mul_ν M k
  have e : ∀ ω, M.w ω * ((M.ν ω k : ℝ) - 1) ^ 2 =
      M.w ω * ((M.ν ω k : ℝ) * ((M.ν ω k : ℝ) - 1)) - M.w ω * (M.ν ω k : ℝ) + M.w ω :=
    fun ω => by ring
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, h1, M.sum_w]
  ring

theorem tripleCoalProb_eq_offspringThirdFactorialMoment (k : Fin N) :
    M.tripleCoalProb =
      M.offspringThirdFactorialMoment k / (((N : ℝ) - 1) * ((N : ℝ) - 2)) :=
  M.tripleCoalProb_eq k

end Moments

theorem mul_div_add_one_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : x * (y / (x + 1)) ≤ y := by
  rw [← mul_div_assoc, div_le_iff₀ (by linarith)]
  nlinarith

theorem remainder_le_mul {A B η c d q ε δ : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hc : 0 ≤ c)
    (hε : 0 < ε) (hq : q ≤ 4 * ε * c + 2 * d / ε) (hAε : 4 * A * ε ≤ η / 2)
    (hdc : d ≤ δ * c) (hδ : (B + 2 * A / ε) * δ ≤ η / 2) : B * d + A * q ≤ η * c := by
  have hX : 0 ≤ B + 2 * A / ε := add_nonneg hB (div_nonneg (by linarith) hε.le)
  have h1 : A * q ≤ 4 * A * ε * c + 2 * A / ε * d := by
    have := mul_le_mul_of_nonneg_left hq hA
    have e : A * (4 * ε * c + 2 * d / ε) = 4 * A * ε * c + 2 * A / ε * d := by ring
    linarith
  have h2 : 4 * A * ε * c ≤ η / 2 * c := mul_le_mul_of_nonneg_right hAε hc
  have h3 : (B + 2 * A / ε) * d ≤ (B + 2 * A / ε) * (δ * c) :=
    mul_le_mul_of_nonneg_left hdc hX
  have h4 : (B + 2 * A / ε) * δ * c ≤ η / 2 * c := mul_le_mul_of_nonneg_right hδ hc
  have e3 : (B + 2 * A / ε) * (δ * c) = (B + 2 * A / ε) * δ * c := by ring
  have e4 : (B + 2 * A / ε) * d = B * d + 2 * A / ε * d := by ring
  linarith

section Sequence

variable {Ω : ℕ → Type*} [∀ m, Fintype (Ω m)] (N : ℕ → ℕ) (M : ∀ m, CanningsModel (N m) (Ω m))
variable (α : Type*) [Fintype α] [DecidableEq α]

theorem tripleCoalProb_le_mul {N : ℕ} {Ω : Type*} [Fintype Ω] (M : CanningsModel N Ω) {δ : ℝ}
    (h : M.tripleCoalProb / M.pairCoalProb < δ) : M.tripleCoalProb ≤ δ * M.pairCoalProb := by
  rcases (M.pairCoalProb_nonneg).eq_or_lt with hc | hc
  · have := M.tripleCoalProb_le_pairCoalProb
    rw [← hc] at this ⊢
    linarith
  · exact ((div_lt_iff₀ hc).1 h).le

theorem mohle_expansion (hN : Tendsto (fun m => (N m : ℝ)) atTop atTop)
    (hd : Tendsto (fun m => (M m).tripleCoalProb / (M m).pairCoalProb) atTop (𝓝 0))
    (π σ : Finpartition (univ : Finset α)) :
    (fun m => (M m).ancestralMatrix α π σ - (1 : Matrix _ _ ℝ) π σ -
      (M m).pairCoalProb * partitionQ π σ) =o[atTop] fun m => (M m).pairCoalProb := by
  rw [isLittleO_iff]
  intro η hη
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (Fintype.card (Finpartition (univ : Finset α)) : ℝ) := ⟨_, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n : ℝ, n = (Fintype.card α : ℝ) := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := hK ▸ Nat.cast_nonneg _
  have hn0 : 0 ≤ n := hn ▸ Nat.cast_nonneg _
  have hA : 0 ≤ K * n ^ 4 := by positivity
  have hB : 0 ≤ K * n ^ 3 := by positivity
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = η / 2 / (4 * (K * n ^ 4) + 1) := ⟨_, rfl⟩
  have hε : 0 < ε := hεdef ▸ by positivity
  have hAε : 4 * (K * n ^ 4) * ε ≤ η / 2 :=
    hεdef ▸ mul_div_add_one_le (by positivity) (by positivity)
  have hX : 0 ≤ K * n ^ 3 + 2 * (K * n ^ 4) / ε := by positivity
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = η / 2 / (K * n ^ 3 + 2 * (K * n ^ 4) / ε + 1) := ⟨_, rfl⟩
  have hδ : 0 < δ := hδdef ▸ by positivity
  have hXδ : (K * n ^ 3 + 2 * (K * n ^ 4) / ε) * δ ≤ η / 2 :=
    hδdef ▸ mul_div_add_one_le hX (by positivity)
  filter_upwards [hN.eventually_ge_atTop (max 6 (max n (1 / ε))),
    (tendsto_order.1 hd).2 δ hδ] with m hm hdm
  have h6 : 6 ≤ N m := by exact_mod_cast (le_max_left _ _).trans hm
  have hcard : Fintype.card α ≤ N m := by
    have : n ≤ N m := ((le_max_left _ _).trans (le_max_right _ _)).trans hm
    rw [hn] at this
    exact_mod_cast this
  have hεN : 1 ≤ ε * N m :=
    (div_le_iff₀' hε).1 (((le_max_right _ _).trans (le_max_right _ _)).trans hm)
  have hc := (M m).pairCoalProb_nonneg
  have hq := (M m).doublePairProb_le h6 hε hεN
  have hdc := tripleCoalProb_le_mul (M m) hdm
  have hmain := remainder_le_mul hA hB hc hε hq hAε hdc hXδ
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hc]
  refine ((M m).abs_ancestralMatrix_sub_le_card hcard π σ).trans (le_trans (le_of_eq ?_) hmain)
  rw [CanningsModel.expansionRemainder, ← hK, ← hn]
  ring

theorem pairCoalProb_tendsto_zero (hN : Tendsto (fun m => (N m : ℝ)) atTop atTop)
    (hd : Tendsto (fun m => (M m).tripleCoalProb / (M m).pairCoalProb) atTop (𝓝 0)) :
    Tendsto (fun m => (M m).pairCoalProb) atTop (𝓝 0) := by
  rw [tendsto_order]
  refine ⟨fun a ha => Eventually.of_forall fun m => ha.trans_le (M m).pairCoalProb_nonneg,
    fun a ha => ?_⟩
  have hε : 0 < a / 8 := by positivity
  filter_upwards [hN.eventually_ge_atTop (max 3 (1 / (a / 8))),
    (tendsto_order.1 hd).2 (a / 8 / 2) (by positivity)] with m hm hdm
  have h3 : 3 ≤ N m := by exact_mod_cast (le_max_left _ _).trans hm
  have hεN : 1 ≤ a / 8 * N m := (div_le_iff₀' hε).1 ((le_max_right _ _).trans hm)
  have h1 := (M m).pairCoalProb_le h3 hε hεN
  have hdc := tripleCoalProb_le_mul (M m) hdm
  have h2 : (M m).tripleCoalProb / (a / 8) ≤ (M m).pairCoalProb / 2 := by
    rw [div_le_iff₀ hε]
    linarith
  linarith

theorem mohle_limit (hN : Tendsto (fun m => (N m : ℝ)) atTop atTop)
    (hd : Tendsto (fun m => (M m).tripleCoalProb / (M m).pairCoalProb) atTop (𝓝 0))
    (hc : ∀ᶠ m in atTop, 0 < (M m).pairCoalProb)
    (hc0 : Tendsto (fun m => (M m).pairCoalProb) atTop (𝓝 0)) {t : ℝ} (ht : 0 ≤ t)
    (π σ : Finpartition (univ : Finset α)) :
    Tendsto (fun m => ((M m).ancestralMatrix α ^ ⌊t / (M m).pairCoalProb⌋₊) π σ) atTop
      (𝓝 ((partitionChain α).semigroup t π σ)) :=
  Matrix.tendsto_pow_floor_exp_apply (A := fun m => (M m).ancestralMatrix α)
    (c := fun m => (M m).pairCoalProb) (Q := partitionQ) hc hc0
    (fun x y => mohle_expansion N M α hN hd x y) ht π σ

theorem mohle_limit' (hN : Tendsto (fun m => (N m : ℝ)) atTop atTop)
    (hd : Tendsto (fun m => (M m).tripleCoalProb / (M m).pairCoalProb) atTop (𝓝 0))
    (hc : ∀ᶠ m in atTop, 0 < (M m).pairCoalProb) {t : ℝ} (ht : 0 ≤ t)
    (π σ : Finpartition (univ : Finset α)) :
    Tendsto (fun m => ((M m).ancestralMatrix α ^ ⌊t / (M m).pairCoalProb⌋₊) π σ) atTop
      (𝓝 ((partitionChain α).semigroup t π σ)) :=
  mohle_limit N M α hN hd hc (pairCoalProb_tendsto_zero N M hN hd) ht π σ

end Sequence

theorem moranOffspring_le_two (N : ℕ) (pd : Fin N × Fin N) (k : Fin N) :
    moranOffspring N pd k ≤ 2 := by
  unfold moranOffspring
  split_ifs <;> omega

theorem moranModel_tripleCoalProb (N : ℕ) (hN : 0 < N) : (moranModel N hN).tripleCoalProb = 0 := by
  rw [CanningsModel.tripleCoalProb_eq_sum]
  refine Finset.sum_eq_zero fun ω _ => ?_
  have h : (moranModel N hN).tripleCount ω = 0 :=
    Finset.sum_eq_zero fun p _ => Nat.descFactorial_eq_zero_iff_lt.2
      (Nat.lt_succ_of_le (moranOffspring_le_two N ω p))
  rw [h, Nat.cast_zero, zero_div, mul_zero]

theorem moranModel_pairCoalProb (N : ℕ) (hN : 2 ≤ N) :
    (moranModel N (by omega)).pairCoalProb = 2 / (N : ℝ) ^ 2 := by
  have h1 : ((N : ℝ) - 1) ≠ 0 := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  rw [pairCoalProb_eq_offspringVariance _ ⟨0, by omega⟩, moranModel_offspringVariance]
  field_simp

theorem moranModel_mohle_limit (α : Type*) [Fintype α] [DecidableEq α] {t : ℝ} (ht : 0 ≤ t)
    (π σ : Finpartition (univ : Finset α)) :
    Tendsto (fun m : ℕ => ((moranModel (m + 2) (Nat.succ_pos _)).ancestralMatrix α ^
      ⌊t / (moranModel (m + 2) (Nat.succ_pos _)).pairCoalProb⌋₊) π σ) atTop
      (𝓝 ((partitionChain α).semigroup t π σ)) := by
  have hN : Tendsto (fun m : ℕ => ((m + 2 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  have hc : ∀ m : ℕ, (moranModel (m + 2) (Nat.succ_pos _)).pairCoalProb =
      2 / ((m + 2 : ℕ) : ℝ) ^ 2 := fun m => moranModel_pairCoalProb (m + 2) (by omega)
  refine mohle_limit' (fun m => m + 2) (fun m => moranModel (m + 2) (Nat.succ_pos _)) α hN ?_
    (Eventually.of_forall fun m => ?_) ht π σ
  · simp only [moranModel_tripleCoalProb, zero_div]
    exact tendsto_const_nhds
  · rw [hc]
    positivity

end Rhone.Coalescent
