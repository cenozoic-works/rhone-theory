/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.SimultaneousOnsetCertificates
public import Rhone.Statistics.Identifiability.TimeOrderedMixedRemainder

/-! # Exact noncommutative leading term and its exposure-product lower bound -/

@[expose] public section

open Set MeasureTheory
open scoped BigOperators Topology Matrix Matrix.Norms.Operator
open Rhone.MarkovChain.Identifiability Rhone.Statistics.Identifiability
namespace Rhone.Statistics.Identifiability.SimultaneousOnset

noncomputable def upperExposure (q r : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..t, q u * (∫ v in u..t, r v)
noncomputable def lowerExposure (q r : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..t, q u * (∫ v in (0 : ℝ)..u, r v)

noncomputable def leadingWitness (k : ℕ) (q r : ℝ → ℝ) (t : ℝ) : ℝ :=
  4 * (k + 1 : ℝ) * upperExposure q r t + 2 * (k + 1 : ℝ) * lowerExposure q r t

theorem orderedTwoMarkIntegral_scalar (q r : ℝ → ℝ)
    (M R : Matrix ProductState ProductState ℝ) (t : ℝ) :
    orderedTwoMarkIntegral (fun u => q u • M) (fun u => r u • R) 0 t =
      upperExposure q r t • (M * R) + lowerExposure q r t • (R * M) := by
  simp only [orderedTwoMarkIntegral, smul_mul_assoc, mul_smul_comm, smul_smul,
    intervalIntegral.integral_smul_const]
  congr 1
  · congr 1
    simp only [mul_comm, intervalIntegral.integral_const_mul, upperExposure]
  · congr 1
    simp only [intervalIntegral.integral_const_mul, lowerExposure]

theorem orderedTwoMarkIntegral_witness (k : ℕ) (q r : ℝ → ℝ) (t : ℝ) :
    (orderedTwoMarkIntegral (fun u => q u • migrationMark k)
      (fun u => r u • recombinationMark k) 0 t *ᵥ witnessVec) (0, 0) =
      leadingWitness k q r t := by
  rw [orderedTwoMarkIntegral_scalar, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.smul_mulVec]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    migration_recombination_witness, recombination_migration_witness, leadingWitness]
  ring

theorem upperExposure_add_lowerExposure (q r : ℝ → ℝ)
    (hq : Continuous q) (hr : Continuous r) (t : ℝ) :
    upperExposure q r t + lowerExposure q r t =
      (∫ u in (0 : ℝ)..t, q u) * (∫ u in (0 : ℝ)..t, r u) := by
  have hu : Continuous (fun u => q u * (∫ v in u..t, r v)) :=
    hq.mul (continuous_integral_upper (fun _ v => r v) (hr.comp continuous_snd) t)
  have hl : Continuous (fun u => q u * (∫ v in (0 : ℝ)..u, r v)) :=
    hq.mul (intervalIntegral.continuous_primitive hr.intervalIntegrable 0)
  unfold upperExposure lowerExposure
  rw [← intervalIntegral.integral_add (hu.intervalIntegrable 0 t) (hl.intervalIntegrable 0 t)]
  calc
    _ = ∫ u in (0 : ℝ)..t, q u * (∫ v in (0 : ℝ)..t, r v) := by
      apply intervalIntegral.integral_congr
      intro u _
      dsimp only
      rw [← mul_add, add_comm (∫ v in u..t, r v),
        intervalIntegral.integral_add_adjacent_intervals
          (hr.intervalIntegrable 0 u) (hr.intervalIntegrable u t)]
    _ = _ := intervalIntegral.integral_mul_const _ _

theorem upperExposure_nonneg (q r : ℝ → ℝ) {t : ℝ} (ht : 0 ≤ t)
    (hq : ∀ u ∈ Icc 0 t, 0 ≤ q u) (hr : ∀ u ∈ Icc 0 t, 0 ≤ r u) :
    0 ≤ upperExposure q r t := by
  apply intervalIntegral.integral_nonneg ht
  intro u hu
  apply mul_nonneg (hq u hu)
  apply intervalIntegral.integral_nonneg hu.2
  intro v hv
  exact hr v ⟨hu.1.trans hv.1, hv.2⟩

theorem leadingWitness_lower_bound (k : ℕ) (q r : ℝ → ℝ)
    (hq : Continuous q) (hr : Continuous r) {t : ℝ} (ht : 0 ≤ t)
    (hqn : ∀ u ∈ Icc 0 t, 0 ≤ q u) (hrn : ∀ u ∈ Icc 0 t, 0 ≤ r u) :
    2 * (k + 1 : ℝ) * (∫ u in (0 : ℝ)..t, q u) * (∫ u in (0 : ℝ)..t, r u) ≤
      leadingWitness k q r t := by
  have he := upperExposure_add_lowerExposure q r hq hr t
  have hn := upperExposure_nonneg q r ht hqn hrn
  have hk : 0 ≤ (k + 1 : ℝ) := by positivity
  unfold leadingWitness
  nlinarith [mul_nonneg hk hn]

end Rhone.Statistics.Identifiability.SimultaneousOnset
