/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ConditionalClockLaw
public import Rhone.Statistics.Identifiability.PanPostPair

/-! # Survival comparison for a variable deterministic coalescence clock -/

@[expose] public section

open Set Filter
open scoped Topology
namespace Rhone.Statistics.Identifiability

set_option backward.isDefEq.respectTransparency false

theorem clock_decay_bound (G Gdot H rate : ℝ → ℝ)
    (hg : ∀ t, 0 ≤ t → HasDerivAt G (Gdot t) t)
    (hh : ∀ t, 0 ≤ t → HasDerivAt H (rate t) t)
    (hb : ∀ t, 0 ≤ t → Gdot t ≤ -rate t * G t) {t : ℝ} (ht : 0 ≤ t) :
    G t ≤ G 0*Real.exp (H 0-H t) := by
  let f : ℝ → ℝ := fun x => Real.exp (H x)*G x
  have hf : ∀ x, 0 ≤ x → HasDerivAt f
      (Real.exp (H x)*(rate x*G x+Gdot x)) x := by
    intro x hx
    convert! (hh x hx).exp.mul (hg x hx) using 1
    ring
  have ha : AntitoneOn f (Ici 0) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
      (fun x hx => (hf x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hf x (interior_subset hx)).hasDerivWithinAt) (by
        intro x hx
        exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
          (by linarith [hb x (interior_subset hx)]))
  have he : G t*Real.exp (H t) ≤ G 0*Real.exp (H 0) := by
    simpa only [f,mul_comm] using ha self_mem_Ici ht ht
  calc
    G t ≤ (G 0*Real.exp (H 0))/Real.exp (H t) := (le_div_iff₀ (Real.exp_pos _)).mpr he
    _ = G 0*Real.exp (H 0-H t) := by
      rw [div_eq_mul_inv,← Real.exp_neg,mul_assoc,← Real.exp_add,sub_eq_add_neg]

theorem clock_decay_tendsto_zero (G Gdot H rate : ℝ → ℝ)
    (hg : ∀ t, 0 ≤ t → HasDerivAt G (Gdot t) t)
    (hh : ∀ t, 0 ≤ t → HasDerivAt H (rate t) t)
    (hb : ∀ t, 0 ≤ t → Gdot t ≤ -rate t * G t)
    (hn : ∀ t, 0 ≤ t → 0 ≤ G t) (htail : Tendsto H atTop atTop) :
    Tendsto G atTop (𝓝 0) := by
  have hu : Tendsto (fun t => G 0*Real.exp (H 0-H t)) atTop (𝓝 0) := by
    simpa using (conditionalPair_survival_tendsto_zero H 0 htail).const_mul (G 0)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact hn t ht
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact clock_decay_bound G Gdot H rate hg hh hb ht

end Rhone.Statistics.Identifiability
