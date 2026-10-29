/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Dynamics.DriftMutation

/-! # Island identity as an exact recurrence specialization -/

@[expose] public section

namespace Rhone.Dynamics.IslandIdentity

open Filter Topology

/-- Source: wright1951, p. 331. -/
theorem island_fixed (N : ℕ) (hN : 0 < N) (m : ℝ)
    (hm0 : 0 ≤ m) (hm1 : m ≤ 1) :
    ibdStep (2 * N) m (ibdFixed (2 * N) m) = ibdFixed (2 * N) m :=
  ibdStep_fixed (by omega) hm0 hm1

/-- Source: wright1951, p. 331. -/
theorem island_fixed_unique (N : ℕ) (hN : 0 < N) (m : ℝ)
    (hm0 : 0 ≤ m) (hm1 : m ≤ 1) (F : ℝ)
    (hF : ibdStep (2 * N) m F = F) : F = ibdFixed (2 * N) m :=
  eq_ibdFixed_of_ibdStep_eq (by omega) hm0 hm1 hF

/-- Source: wright1951, p. 331. -/
theorem island_equilibrium_formula (N : ℕ) (m : ℝ) :
    ibdFixed (2 * N) m = (1 - m) ^ 2 /
      (2 * (N : ℝ) - (2 * (N : ℝ) - 1) * (1 - m) ^ 2) := by
  unfold ibdFixed
  push_cast
  congr 1
  ring

/-- Source: wright1951, p. 331. -/
theorem island_iterate (N : ℕ) (hN : 0 < N) (m : ℝ)
    (hm0 : 0 ≤ m) (hm1 : m ≤ 1) (t : ℕ) (F0 : ℝ) :
    ibdIter (2 * N) m t F0 - ibdFixed (2 * N) m =
      ((1 - m) ^ 2 * (1 - 1 / (2 * (N : ℝ)))) ^ t * (F0 - ibdFixed (2 * N) m) := by
  simpa only [Nat.cast_mul, Nat.cast_ofNat]
    using ibdIter_sub_fixed (by omega : 1 ≤ 2 * N) hm0 hm1 t F0

/-- Source: wright1951, p. 331. -/
theorem tendsto_island_iterate (N : ℕ) (hN : 0 < N) (m : ℝ)
    (hm0 : 0 ≤ m) (hm1 : m ≤ 1) (F0 : ℝ) :
    Tendsto (fun t : ℕ => ibdIter (2 * N) m t F0)
      atTop (nhds (ibdFixed (2 * N) m)) := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hr0 : 0 ≤ (1 - m) ^ 2 * (1 - 1 / (2 * (N : ℝ))) := by
    apply mul_nonneg (sq_nonneg _)
    have : 1 / (2 * (N : ℝ)) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
    linarith
  have hr1 : (1 - m) ^ 2 * (1 - 1 / (2 * (N : ℝ))) < 1 := by
    have hcoef : (1 - m) ^ 2 ≤ 1 := by nlinarith
    have hdiv : 0 < 1 / (2 * (N : ℝ)) := by positivity
    have hdiv1 : 1 / (2 * (N : ℝ)) ≤ 1 := (div_le_one (by linarith)).mpr (by linarith)
    have hprod : 0 ≤ (1 - (1 - m) ^ 2) * (1 - 1 / (2 * (N : ℝ))) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith [hprod]
  have hpow := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).mul_const
    (F0 - ibdFixed (2 * N) m)
  have hlim := hpow.add_const (ibdFixed (2 * N) m)
  simp only [zero_mul, zero_add] at hlim
  apply hlim.congr
  intro t
  have h := island_iterate N hN m hm0 hm1 t F0
  linarith

/-- Source: wright1951, p. 331. -/
theorem tendsto_island_equilibrium {M : ℝ} (hM : 0 ≤ M) :
    Tendsto (fun N : ℕ => ibdFixed (2 * N) (M / (N : ℝ)))
      atTop (nhds (1 / (1 + 4 * M))) := by
  have hbase := tendsto_ibdFixed_scaling (by positivity : 0 ≤ 4 * M)
  have hdouble : Tendsto (fun N : ℕ => 2 * N) atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    filter_upwards [eventually_ge_atTop b] with N hN
    omega
  have hlim := hbase.comp hdouble
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  simp only [Function.comp]
  congr 1
  push_cast
  have hN' : (N : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  field_simp
  ring

end Rhone.Dynamics.IslandIdentity
