/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.SimultaneousOnsetFlow
public import Rhone.Statistics.Identifiability.SimultaneousOnsetLeading
public import Rhone.Statistics.Identifiability.SimultaneousOnsetBounds

/-! # A positive simultaneous-onset finite-flow witness -/

@[expose] public section

open Set MeasureTheory
open scoped BigOperators Topology Matrix Matrix.Norms.Operator
open Rhone.MarkovChain.Identifiability Rhone.Statistics.Identifiability
namespace Rhone.Statistics.Identifiability.SimultaneousOnset

theorem contractiveBoundOn_restrict_right {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Q : ℝ → Matrix ι ι ℝ} {s t T K : ℝ}
    (h : HasContractiveBoundOn Q s T K) (ht : t ≤ T) :
    HasContractiveBoundOn Q s t K := by
  exact ⟨fun u hu => h.1 u ⟨hu.1, hu.2.trans ht⟩,
    fun a b hsa hab hbt => h.2 a b hsa hab (hbt.trans ht)⟩

theorem witness_remainder_le (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r)
    {t K : ℝ} (ht : 0 ≤ t) (hK : 0 ≤ K)
    (hqn : ∀ u ∈ Icc 0 t, 0 ≤ q u) (hrn : ∀ u ∈ Icc 0 t, 0 ≤ r u)
    (h₀ : HasContractiveBoundOn (fun u => productGenerator k (c u) 0 0) 0 t K)
    (hM : HasContractiveBoundOn (fun u => productGenerator k (c u) (q u) 0) 0 t K)
    (hR : HasContractiveBoundOn (fun u => productGenerator k (c u) 0 (r u)) 0 t K)
    (hD : HasContractiveBoundOn (fun u => productGenerator k (c u) (q u) (r u)) 0 t K) :
    |witness k c q r t - leadingWitness k q r t| ≤
      (2 * K * ‖migrationMark k‖ * ‖recombinationMark k‖ * ‖witnessVec‖) * t *
        (∫ u in (0 : ℝ)..t, q u) * (∫ u in (0 : ℝ)..t, r u) := by
  let C : ℝ → Matrix ProductState ProductState ℝ := fun u => c u • coalescenceMark k
  let M : ℝ → Matrix ProductState ProductState ℝ := fun u => q u • migrationMark k
  let R : ℝ → Matrix ProductState ProductState ℝ := fun u => r u • recombinationMark k
  have hC : ∀ i j, Continuous (fun u => C u i j) := fun i j => hc.mul continuous_const
  have e₀ : C = fun u => productGenerator k (c u) 0 0 := by
    funext u; simp [C, productGenerator_affine]
  have eM : C + M = fun u => productGenerator k (c u) (q u) 0 := by
    funext u; simp [C, M, productGenerator_affine]
  have eR : C + R = fun u => productGenerator k (c u) 0 (r u) := by
    funext u; simp [C, R, productGenerator_affine]
  have eD : C + M + R = fun u => productGenerator k (c u) (q u) (r u) := by
    funext u; exact (productGenerator_affine k (c u) (q u) (r u)).symm
  have hb₀ : HasContractiveBoundOn C 0 t K := e₀ ▸ h₀
  have hbM : HasContractiveBoundOn (C + M) 0 t K := eM ▸ hM
  have hbR : HasContractiveBoundOn (C + R) 0 t K := eR ▸ hR
  have hbD : HasContractiveBoundOn (C + M + R) 0 t K := eD ▸ hD
  have h := inhomogeneousTransition_scalar_mixed_remainder_le C q r
    (migrationMark k) (recombinationMark k) hC hq hr (a := 1) (b := 1)
    (by norm_num) (by norm_num) ht hK hqn hrn
    hb₀ (by simpa [M] using hbM) (by simpa [R] using hbR) (by simpa [M, R] using hbD)
  simp only [one_mul, mul_one, one_smul, sub_zero] at h
  change ‖inhomogeneousTransition (C + M + R) 0 t -
    inhomogeneousTransition (C + M) 0 t - inhomogeneousTransition (C + R) 0 t +
    inhomogeneousTransition C 0 t - orderedTwoMarkIntegral M R 0 t‖ ≤ _ at h
  let E : Matrix ProductState ProductState ℝ :=
    inhomogeneousTransition (C + M + R) 0 t - inhomogeneousTransition (C + M) 0 t -
      inhomogeneousTransition (C + R) 0 t + inhomogeneousTransition C 0 t -
        orderedTwoMarkIntegral M R 0 t
  have he : (E *ᵥ witnessVec) (0, 0) = witness k c q r t - leadingWitness k q r t := by
    dsimp only [E]
    rw [eD, eM, eR, e₀]
    simp only [Matrix.sub_mulVec, Matrix.add_mulVec, Pi.sub_apply, Pi.add_apply]
    rw [← witness_eq_product_output k c q r hc hq hr,
      product_output_zero_recombination k c q hc hq,
      product_output_zero_migration k c r hc hr,
      product_output_zero_migration k c (fun _ => 0) hc continuous_const]
    simp only [M, R, orderedTwoMarkIntegral_witness, sub_zero, add_zero]
  calc
    _ = ‖(E *ᵥ witnessVec) (0, 0)‖ := by rw [he, Real.norm_eq_abs]
    _ ≤ ‖E *ᵥ witnessVec‖ := norm_le_pi_norm _ _
    _ ≤ ‖E‖ * ‖witnessVec‖ := Matrix.linfty_opNorm_mulVec E witnessVec
    _ ≤ ((2 * K * ‖migrationMark k‖ * ‖recombinationMark k‖) * t *
        (∫ u in (0 : ℝ)..t, q u) * (∫ u in (0 : ℝ)..t, r u)) * ‖witnessVec‖ :=
      mul_le_mul_of_nonneg_right h (norm_nonneg _)
    _ = _ := by ring

theorem exists_positive_witness_horizon (k : ℕ) (c q r : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hr : Continuous r)
    (hcn : ∀ u, 0 ≤ u → 0 ≤ c u) (hqn : ∀ u, 0 ≤ u → 0 ≤ q u)
    (hrn : ∀ u, 0 ≤ u → 0 ≤ r u) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < δ →
      0 < (∫ u in (0 : ℝ)..t, q u) → 0 < (∫ u in (0 : ℝ)..t, r u) →
      0 < witness k c q r t := by
  obtain ⟨K, hK, h₀, hM, hR, hD⟩ := exists_common_contractiveBound k c q r hc hq hr hcn hqn hrn
  let D : ℝ := 2 * K * ‖migrationMark k‖ * ‖recombinationMark k‖ * ‖witnessVec‖
  have hDn : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨min 1 (1 / (D + 1)), lt_min (by norm_num) (one_div_pos.mpr (by positivity)), ?_⟩
  intro t ht hδ hQ hE
  have ht1 : t ≤ 1 := (hδ.trans_le (min_le_left _ _)).le
  have htD : t < 1 / (D + 1) := hδ.trans_le (min_le_right _ _)
  have hDt : D * t < 1 := by
    have hh := (lt_div_iff₀ (show 0 < D + 1 by positivity)).mp htD
    nlinarith
  have hrem := witness_remainder_le k c q r hc hq hr ht.le hK
    (fun u hu => hqn u hu.1) (fun u hu => hrn u hu.1)
    (contractiveBoundOn_restrict_right h₀ ht1) (contractiveBoundOn_restrict_right hM ht1)
    (contractiveBoundOn_restrict_right hR ht1) (contractiveBoundOn_restrict_right hD ht1)
  have hlead := leadingWitness_lower_bound k q r hq hr ht.le
    (fun u hu => hqn u hu.1) (fun u hu => hrn u hu.1)
  have hprod : 0 < (∫ u in (0 : ℝ)..t, q u) * (∫ u in (0 : ℝ)..t, r u) := mul_pos hQ hE
  have hscaled := mul_lt_mul_of_pos_right hDt hprod
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hkp := mul_nonneg hk hprod.le
  have habs := (abs_le.mp hrem).1
  change -(D * t * (∫ u in (0 : ℝ)..t, q u) * (∫ u in (0 : ℝ)..t, r u)) ≤
    witness k c q r t - leadingWitness k q r t at habs
  nlinarith

end Rhone.Statistics.Identifiability.SimultaneousOnset
