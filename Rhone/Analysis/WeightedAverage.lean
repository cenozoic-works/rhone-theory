/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
public import Mathlib.Topology.Order.MonotoneConvergence

/-! # Vanishing raw averages from bounded nonnegative harmonic weighted sums -/

@[expose] public section

namespace Rhone.Analysis
open Filter

theorem average_zero_of_bounded_weighted_sums (e : ℕ → ℝ) (he : ∀ k, 0 ≤ e k)
    (hb : BddAbove (Set.range (fun n => ∑ k ∈ Finset.range n, e k / (k + 1)))) :
    Tendsto (fun n : ℕ => (∑ k ∈ Finset.range n, e k) / n) atTop (nhds 0) := by
  let A : ℕ → ℝ := fun n => ∑ k ∈ Finset.range n, e k / (k + 1)
  have hm : Monotone A := monotone_nat_of_le_succ (fun n => by
    simp only [A, Finset.sum_range_succ]
    exact le_add_of_nonneg_right (div_nonneg (he n) (by positivity)))
  have ht := tendsto_atTop_ciSup hm hb
  have hc := ht.cesaro
  have hidentity (n : ℕ) :
      (n : ℝ) * A n = (∑ k ∈ Finset.range n, e k) + ∑ k ∈ Finset.range n, A k := by
    induction n with
    | zero => simp [A]
    | succ n ih =>
      have hne : (n : ℝ) + 1 ≠ 0 := by positivity
      simp only [A, Finset.sum_range_succ, Nat.cast_add, Nat.cast_one] at ih ⊢
      field_simp
      nlinarith [ih]
  have hraw : (fun n : ℕ => (∑ k ∈ Finset.range n, e k) / n) =ᶠ[atTop]
      (fun n => A n - (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, A k) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hne : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hn)
    apply (div_eq_iff hne).mpr
    have hi := hidentity n
    field_simp
    linarith
  have hlim := ht.sub hc
  simpa only [sub_self] using hlim.congr' hraw.symm

end Rhone.Analysis
