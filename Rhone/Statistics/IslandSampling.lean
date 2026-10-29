/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.EffectiveSampling
public import Rhone.Dynamics.IslandIdentity
public import Rhone.Statistics.FStatistics

/-! # Concrete island sampling and identity-reference differentiation -/

@[expose] public section

namespace Rhone.Statistics.IslandIdentity

open Finset MarkovChain.EffectiveSize Filter Topology

noncomputable def coinMass (p : ℝ) (b : Bool) : ℝ := if b then p else 1 - p

noncomputable def islandSampleMass (N : ℕ) (m F : ℝ)
    (z : (Bool × Bool) × ((Fin (2 * N) × Fin (2 * N)) × Bool)) : ℝ :=
  coinMass (1 - m) z.1.1 * coinMass (1 - m) z.1.2 *
    uniformCopyPairMass (2 * N) z.2.1 * coinMass F z.2.2

noncomputable def islandIdentityMass (N : ℕ) (m F : ℝ) : ℝ :=
  ∑ z : (Bool × Bool) × ((Fin (2 * N) × Fin (2 * N)) × Bool),
    if z.1.1 = true ∧ z.1.2 = true ∧ (z.2.1.1 = z.2.1.2 ∨ z.2.2 = true)
    then islandSampleMass N m F z else 0

theorem island_sample_mass_nonneg (N : ℕ) {m F : ℝ}
    (hm0 : 0 ≤ m) (hm1 : m ≤ 1) (hF0 : 0 ≤ F) (hF1 : F ≤ 1)
    (z : (Bool × Bool) × ((Fin (2 * N) × Fin (2 * N)) × Bool)) :
    0 ≤ islandSampleMass N m F z := by
  have hc : ∀ b, 0 ≤ coinMass (1 - m) b := by
    intro b
    cases b <;> simp only [coinMass, Bool.false_eq_true, ite_false, ite_true] <;> linarith
  have hF : ∀ b, 0 ≤ coinMass F b := by
    intro b
    cases b <;> simp only [coinMass, Bool.false_eq_true, ite_false, ite_true] <;> linarith
  unfold islandSampleMass uniformCopyPairMass
  exact mul_nonneg (mul_nonneg (mul_nonneg (hc _) (hc _)) (by positivity)) (hF _)

theorem island_sample_mass_sum {N : ℕ} (hN : 0 < N) (m F : ℝ) :
    ∑ z, islandSampleMass N m F z = 1 := by
  have hcoin : ∀ p : ℝ, ∑ b : Bool, coinMass p b = 1 := by
    intro p
    simp [coinMass]
  simp only [islandSampleMass, Fintype.sum_prod_type, ← mul_sum, hcoin, mul_one]
  have hcopy : ∑ x, ∑ y, uniformCopyPairMass (2 * N) (x, y) = 1 := by
    simpa only [Fintype.sum_prod_type] using
      uniform_copy_pair_mass_sum (by omega : 0 < 2 * N)
  simp only [hcopy, mul_one, ← mul_sum, hcoin]

/-- Source: wright1951, p. 331. -/
theorem island_identity_mass_eq {N : ℕ} (hN : 0 < N) (m F : ℝ) :
    islandIdentityMass N m F = Dynamics.ibdStep (2 * N) m F := by
  have hshape : islandIdentityMass N m F =
      (1 - m) ^ 2 * ∑ ab : Fin (2 * N) × Fin (2 * N),
        uniformCopyPairMass (2 * N) ab * (if ab.1 = ab.2 then 1 else F) := by
    simp only [islandIdentityMass, islandSampleMass, Fintype.sum_prod_type]
    simp only [coinMass, Fintype.univ_bool, mem_singleton, Bool.true_eq_false,
      not_false_eq_true, sum_insert, or_true, and_true, sum_singleton,
      Bool.false_eq_true, or_false, true_and, and_false, ↓reduceIte, false_and,
      add_zero, sum_const_zero, mul_ite, mul_one]
    rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    rw [mul_sum]
    apply sum_congr rfl
    intro j hj
    by_cases h : i = j <;> simp [h] <;> ring
  rw [hshape]
  have hterm : ∀ ab : Fin (2 * N) × Fin (2 * N),
      uniformCopyPairMass (2 * N) ab * (if ab.1 = ab.2 then 1 else F) =
        F * uniformCopyPairMass (2 * N) ab +
        (1 - F) * (if ab.1 = ab.2 then uniformCopyPairMass (2 * N) ab else 0) := by
    intro ab
    split_ifs <;> ring
  simp only [hterm, sum_add_distrib, ← mul_sum]
  rw [uniform_copy_pair_mass_sum (by omega : 0 < 2 * N)]
  change (1 - m) ^ 2 * (F * 1 + (1 - F) * uniformCopyCoincidence (2 * N)) = _
  rw [diploid_uniform_coincidence hN]
  unfold Dynamics.ibdStep
  push_cast
  ring

/-- Source: wright1951, p. 328. -/
noncomputable def ibdFst (Fwithin Fbetween : ℝ) : ℝ :=
  (Fwithin - Fbetween) / (1 - Fbetween)

theorem ibd_fst_infinite_pool (Fwithin : ℝ) : ibdFst Fwithin 0 = Fwithin := by
  simp [ibdFst]

/-- Source: wright1951, p. 328. -/
theorem ibd_fst_diversity_bridge (Fwithin Fbetween c : ℝ)
    (hbetween : Fbetween ≠ 1) (hc : c ≠ 0) :
    ibdFst Fwithin Fbetween =
      Rhone.Statistics.FStatistics.fRatio (c * (1 - Fwithin)) (c * (1 - Fbetween)) := by
  have hb : 1 - Fbetween ≠ 0 := sub_ne_zero.mpr (Ne.symm hbetween)
  unfold ibdFst Rhone.Statistics.FStatistics.fRatio
  field_simp
  ring

/-- Source: wright1951, p. 331. -/
theorem tendsto_island_ibd_fst {M : ℝ} (hM : 0 ≤ M) :
    Tendsto (fun N : ℕ => ibdFst (Dynamics.ibdFixed (2 * N) (M / (N : ℝ))) 0)
      atTop (nhds (1 / (1 + 4 * M))) := by
  simpa only [ibd_fst_infinite_pool] using Dynamics.IslandIdentity.tendsto_island_equilibrium hM

end Rhone.Statistics.IslandIdentity
