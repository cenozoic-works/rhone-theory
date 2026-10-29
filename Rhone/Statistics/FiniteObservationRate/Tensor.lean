/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.FiniteObservationRate.Hellinger

/-! # Iid tensorization of finite Hellinger distance -/

@[expose] public section

open scoped BigOperators
namespace Rhone.Statistics.FiniteObservationRate
open DependenceBudget DependentPairedTest
variable {X : Type*} [Fintype X]

theorem affinity_iid (P Q : Law X) (N : ℕ) : affinity (iid P N) (iid Q N) = affinity P Q ^ N := by
  have hp (x : Fin N → X) : Real.sqrt ((iid P N).mass x) =
      ∏ i, Real.sqrt (P.mass (x i)) := by
    simpa only [iid] using Real.sqrt_prod Finset.univ (fun i _ => P.nonneg (x i))
  have hq (x : Fin N → X) : Real.sqrt ((iid Q N).mass x) =
      ∏ i, Real.sqrt (Q.mass (x i)) := by
    simpa only [iid] using Real.sqrt_prod Finset.univ (fun i _ => Q.nonneg (x i))
  simp only [affinity, hp, hq, ← Finset.prod_mul_distrib]
  have h := (Fintype.prod_sum (fun (_ : Fin N) x =>
    Real.sqrt (P.mass x) * Real.sqrt (Q.mass x))).symm
  simpa using h

theorem one_sub_pow_le {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) (N : ℕ) :
    1 - a ^ N ≤ (N : ℝ) * (1 - a) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [pow_succ, Nat.cast_add, Nat.cast_one]
    have hp := pow_nonneg ha N
    have hp1 := pow_le_one₀ ha ha1 (n := N)
    nlinarith

theorem iid_hellinger_le (P Q : Law X) (N : ℕ) :
    hellingerSq (iid P N) (iid Q N) ≤ (N : ℝ) * hellingerSq P Q := by
  rw [hellinger_affinity, affinity_iid, hellinger_affinity]
  have h := one_sub_pow_le (affinity_nonneg P Q) (affinity_le_one P Q) N
  linarith

theorem iid_tv_sq_le (P Q : Law X) (N : ℕ) :
    totalVariation (iid P N) (iid Q N) ^ 2 ≤ (N : ℝ) * hellingerSq P Q :=
  (totalVariation_sq_le_hellinger (iid P N) (iid Q N)).trans (iid_hellinger_le P Q N)

end Rhone.Statistics.FiniteObservationRate
