/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanRootSampling
public import Mathlib.Analysis.SpecificLimits.Basic
/-!
# The finite sample-root probability tends to the fixed-sample Kingman ratio

Source: kingman1982, sec. 1, eq. (1.1)–(1.4), (1.7). -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
theorem card_initial_sample (N n : ℕ) (hnN : n ≤ N) :
    (Finset.univ.filter (fun x : Fin N => x.val < n)).card = n := by
  suffices he : (univ : Finset (Fin n)).card =
      (univ.filter (fun x : Fin N => x.val < n)).card by simpa using he.symm
  apply card_bij (fun x _ => (⟨x.val, lt_of_lt_of_le x.isLt hnN⟩ : Fin N))
  · intro x hx
    exact mem_filter.mpr ⟨mem_univ _, x.isLt⟩
  · intro x hx y hy he
    exact Fin.ext (congrArg (fun z : Fin N => z.val) he)
  · intro x hx
    obtain ⟨_, hxn⟩ := mem_filter.mp hx
    refine ⟨⟨x.val, hxn⟩, mem_univ _, ?_⟩
    exact Fin.ext rfl
theorem tendsto_sample_population_root_probability (n : ℕ) (hn : 1 ≤ n) :
    Filter.Tendsto
      (fun N => samplePopulationRootMass N
        (Finset.univ.filter (fun x : Fin N => x.val < n)))
      Filter.atTop (nhds (((n - 1 : ℕ) : ℝ) / (n + 1 : ℕ))) := by
  have hratio : Filter.Tendsto (fun N : ℕ => (1 + (N : ℝ)) / (-1 + (N : ℝ)))
      Filter.atTop (nhds (1 : ℝ)) := by
    simpa only [one_mul, div_one] using
      (tendsto_add_mul_div_add_mul_atTop_nhds (1 : ℝ) (-1) 1 (d := 1) one_ne_zero)
  have hlim := hratio.const_mul (((n - 1 : ℕ) : ℝ) / (n + 1 : ℕ))
  rw [mul_one] at hlim
  apply hlim.congr'
  filter_upwards [Filter.eventually_ge_atTop (max n 2)] with N hN
  have hnN : n ≤ N := le_trans (le_max_left _ _) hN
  have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hN
  rw [sample_population_root_probability N hN2 _
    (by rw [card_initial_sample N n hnN]; exact hn), card_initial_sample N n hnN]
  rw [Nat.cast_sub (by omega : 1 ≤ N)]
  simp only [Nat.cast_add, Nat.cast_one]
  rw [div_mul_div_comm]
  congr 1 <;> ring
end Rhone.Coalescent
