/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Tactic.Linarith

/-! # Scalar comparison for exponentially decaying nonnegative observables -/

@[expose] public section

open Set Filter
open scoped Topology
namespace Rhone.Statistics.Identifiability

set_option backward.isDefEq.respectTransparency false

theorem exponential_decay_bound (f f' : ℝ → ℝ) (e : ℝ)
    (hf : ∀ t, HasDerivAt f (f' t) t)
    (hd : ∀ t, 0 ≤ t → f' t ≤ -e * f t) {t : ℝ} (ht : 0 ≤ t) :
    f t ≤ f 0 * Real.exp (-e*t) := by
  let g : ℝ → ℝ := fun x => Real.exp (e*x) * f x
  have hg : ∀ x, HasDerivAt g
      (Real.exp (e*x) * (e * f x + f' x)) x := by
    intro x
    convert! ((((hasDerivAt_id x).const_mul e).exp).mul (hf x)) using 1
    dsimp [g]
    ring
  have ha : AntitoneOn g (Ici 0) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
      (fun x _ => (hg x).continuousAt.continuousWithinAt)
      (fun x _ => (hg x).hasDerivWithinAt) (by
        intro x hx
        have hx0 : 0 ≤ x := (interior_subset hx)
        exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (by linarith [hd x hx0]))
  have hb := ha self_mem_Ici ht ht
  have hb' : f t * Real.exp (e*t) ≤ f 0 := by simpa [g, mul_comm] using hb
  have hc := (le_div_iff₀ (Real.exp_pos (e*t))).2 hb'
  simpa [div_eq_mul_inv, ← Real.exp_neg, neg_mul] using hc

theorem tendsto_zero_of_exponential_decay (f f' : ℝ → ℝ) {e : ℝ} (he : 0 < e)
    (hf : ∀ t, HasDerivAt f (f' t) t)
    (hn : ∀ t, 0 ≤ t → 0 ≤ f t)
    (hd : ∀ t, 0 ≤ t → f' t ≤ -e * f t) : Tendsto f atTop (𝓝 0) := by
  have hb : Tendsto (fun t : ℝ => f 0 * Real.exp (-e*t)) atTop (𝓝 0) := by
    convert (Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (neg_lt_zero.mpr he))).const_mul (f 0) using 1 <;> simp
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hb
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact hn t ht
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact exponential_decay_bound f f' e hf hd ht

end Rhone.Statistics.Identifiability
