/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.RecombinationExpansion.Laurent
public import Rhone.Probability.RecombinationExpansion.Unique
public import Rhone.Coalescent.Closure.Expansion

/-! # `q = Σ_k q_k x^k` as an element of `F⟦x⟧`, for the `1/ρ` coefficients -/

@[expose] public section

namespace Rhone.Coalescent.RecombinationExpansion

open Filter Topology LinearAlgebra.Recursion LinearAlgebra.Recursion.Config
    Analysis.RecombinationExpansion Probability.RecombinationExpansion

variable {KA KB : ℕ} {θA θB : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ}
variable {hθA : 0 < θA} {hθB : 0 < θB}

theorem L1_qHat (ξ : Config KA KB) : L1 (qHat θA θB πA πB) ξ = 0 := by
  refine L1_of_sector_const ξ fun i j h => ?_
  rw [qHat, qHat, Config.mA_split ξ h, Config.mB_split ξ h]

theorem L0_qHat (hθA : 0 < θA) (hθB : 0 < θB) (ξ : Config KA KB) :
    L0 θA θB πA πB (qHat θA θB πA πB) ξ = -twoQ1 θA θB πA πB ξ := by
  rw [L0]
  exact source_identity hθA hθB ξ

noncomputable def qSeries (hθA : 0 < θA) (hθB : 0 < θB) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ)
    (ξ : Config KA KB) : PowerSeries ℝ :=
  PowerSeries.C (qHat θA θB πA πB ξ)
    + PowerSeries.X * gen (Closure.qCoeff hθA hθB πA πB) ξ

@[simp] theorem qSeries_coeff_zero (ξ : Config KA KB) :
    PowerSeries.coeff 0 (qSeries hθA hθB πA πB ξ) = qHat θA θB πA πB ξ := by
  rw [qSeries, map_add, PowerSeries.coeff_zero_C, PowerSeries.coeff_zero_X_mul, add_zero]

@[simp] theorem qSeries_coeff_eq_qCoeff (k : ℕ) (ξ : Config KA KB) :
    PowerSeries.coeff (k + 1) (qSeries hθA hθB πA πB ξ)
      = Closure.qCoeff hθA hθB πA πB (k + 1) ξ := by
  rw [qSeries, map_add, PowerSeries.coeff_succ_X_mul, coeff_gen]
  simp

theorem qSeries_coeff_zero_fun :
    (fun η : Config KA KB => PowerSeries.coeff 0 (qSeries hθA hθB πA πB η))
      = qHat θA θB πA πB :=
  funext fun η => qSeries_coeff_zero η

theorem qSeries_coeff_succ_fun (k : ℕ) :
    (fun η : Config KA KB => PowerSeries.coeff (k + 1) (qSeries hθA hθB πA πB η))
      = Closure.qCoeff hθA hθB πA πB (k + 1) :=
  funext fun η => qSeries_coeff_eq_qCoeff k η

section Transport

variable (hπA : ∀ i, 0 ≤ πA i) (hsA : ∑ i, πA i = 1) (hπB : ∀ j, 0 ≤ πB j)
  (hsB : ∑ j, πB j = 1)
include hπA hsA hπB hsB

theorem qSeries_transport (ξ : Config KA KB) (hn : 2 ≤ ξ.n) :
    LTrans θA θB πA πB (gen (Closure.qCoeff hθA hθB πA πB)) ξ
      = PowerSeries.C (twoQ1 θA θB πA πB ξ) :=
  LTrans_gen (Closure.qCoeff hθA hθB πA πB) (twoQ1 θA θB πA πB) ξ
    (Closure.L1_qCoeff_one hπA hsA hπB hsB ξ hn)
    (fun m => Closure.L1_qCoeff_succ hπA hsA hπB hsB m ξ hn)

theorem qSeries_laurent (ξ : Config KA KB) (hn : 2 ≤ ξ.n) :
    Lop (HahnSeries.C θA) (HahnSeries.C θB) (rhoL ℝ)
        (fun i => HahnSeries.C (πA i)) (fun j => HahnSeries.C (πB j))
        (fun η => xL ℝ * incl ℝ (gen (Closure.qCoeff hθA hθB πA πB) η)) ξ
      = HahnSeries.C (twoQ1 θA θB πA πB ξ) := by
  have h := (laurent_transport_iff (θA := θA) (θB := θB) (πA := πA) (πB := πB)
    (gen (Closure.qCoeff hθA hθB πA πB)) (PowerSeries.C (twoQ1 θA θB πA πB ξ)) ξ).mpr
    (qSeries_transport hπA hsA hπB hsB ξ hn)
  rwa [incl_C] at h

theorem L0_add_L1_qSeries (k : ℕ) (ξ : Config KA KB) (hn : 2 ≤ ξ.n) :
    L0 θA θB πA πB (fun η => PowerSeries.coeff k (qSeries hθA hθB πA πB η)) ξ
      + L1 (fun η => PowerSeries.coeff (k + 1) (qSeries hθA hθB πA πB η)) ξ = 0 := by
  rw [qSeries_coeff_succ_fun k]
  match k with
  | 0 =>
    rw [qSeries_coeff_zero_fun, L0_qHat hθA hθB ξ]
    simp only [zero_add]
    rw [Closure.L1_qCoeff_one hπA hsA hπB hsB ξ hn]
    ring
  | (m + 1) =>
    rw [qSeries_coeff_succ_fun m]
    have e : m + 1 + 1 = m + 2 := by omega
    rw [e, Closure.L1_qCoeff_succ hπA hsA hπB hsB m ξ hn]
    ring

theorem qSeries_transport_zero (ξ : Config KA KB) (hn : 2 ≤ ξ.n) :
    LTrans θA θB πA πB (qSeries hθA hθB πA πB) ξ = 0 := by
  refine PowerSeries.ext fun k => ?_
  rw [map_zero]
  match k with
  | 0 =>
    rw [coeff_zero_LTrans, qSeries_coeff_zero_fun]
    exact L1_qHat ξ
  | (k + 1) =>
    rw [coeff_succ_LTrans]
    exact L0_add_L1_qSeries hπA hsA hπB hsB k ξ hn

theorem qSeries_unique (Q : Config KA KB → PowerSeries ℝ)
    (h0 : ∀ ξ : Config KA KB, ξ.t = 0 → Q ξ = qSeries hθA hθB πA πB ξ)
    (hb : ∀ ξ : Config KA KB, ξ.n ≤ 1 → Q ξ = qSeries hθA hθB πA πB ξ)
    (heq : ∀ ξ : Config KA KB, 2 ≤ ξ.n → LTrans θA θB πA πB Q ξ = 0) :
    Q = qSeries hθA hθB πA πB := by
  refine eq_of_LTrans_eq (θA := θA) (θB := θB) (πA := πA) (πB := πB) Q
    (qSeries hθA hθB πA πB) h0 hb fun ξ hn => ?_
  rw [heq ξ hn, qSeries_transport_zero hπA hsA hπB hsB ξ hn]

end Transport

theorem trunc_qSeries_eval (k : ℕ) (ρ : ℝ) (ξ : Config KA KB) :
    ∑ j ∈ Finset.range (k + 1), PowerSeries.coeff j (qSeries hθA hθB πA πB ξ) / ρ ^ j
      = qHat θA θB πA πB ξ
        + ∑ j ∈ Finset.range k, Closure.qCoeff hθA hθB πA πB (j + 1) ξ / ρ ^ (j + 1) := by
  rw [Finset.sum_range_succ']
  simp only [qSeries_coeff_zero, qSeries_coeff_eq_qCoeff, pow_zero, div_one]
  ring

theorem abs_qAt_sub_trunc_le (hπA : ∀ i, 0 ≤ πA i) (hsA : ∑ i, πA i = 1)
    (hπB : ∀ j, 0 ≤ πB j) (hsB : ∑ j, πB j = 1) (k : ℕ) (ξ : Config KA KB) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ ρ : ℝ in atTop,
      |Rational.qAt hθA hθB πA πB ρ ξ
          - ∑ j ∈ Finset.range (k + 1),
              PowerSeries.coeff j (qSeries hθA hθB πA πB ξ) / ρ ^ j|
        ≤ C / ρ ^ (k + 1) := by
  obtain ⟨C, hC, hev⟩ := Closure.abs_Del_sub_sum_le hπA hsA hπB hsB k ξ
  refine ⟨C, hC, ?_⟩
  filter_upwards [hev] with ρ hρ
  rw [trunc_qSeries_eval k ρ ξ]
  have hDel : Rational.qAt hθA hθB πA πB ρ ξ
      - (qHat θA θB πA πB ξ
        + ∑ j ∈ Finset.range k, Closure.qCoeff hθA hθB πA πB (j + 1) ξ / ρ ^ (j + 1))
      = Rational.Del hθA hθB πA πB ρ ξ
        - ∑ j ∈ Finset.range k, Closure.qCoeff hθA hθB πA πB (j + 1) ξ / ρ ^ (j + 1) := by
    rw [Rational.Del]
    ring
  rw [hDel]
  exact hρ

end Rhone.Coalescent.RecombinationExpansion
