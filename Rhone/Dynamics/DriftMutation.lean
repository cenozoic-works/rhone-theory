/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Topology.Algebra.Order.Field

/-!
# Identity by descent under mutation and drift

Source: malecot1969, secs. 3.1.1, 3.1.3, pp. 37, 40–41; felsenstein_teg2019, sec. VII.1, eq.
(VII-2)–(VII-6), p. 285; kimura_crow1964, p. 726, eq. (2)–(3); ewens2004, sec. 3.6. -/

@[expose] public section

namespace Rhone.Dynamics

open Filter Topology

noncomputable def ibdStep (N : ℕ) (u F : ℝ) : ℝ :=
  (1 - u) ^ 2 * (1 / (N : ℝ) + (1 - 1 / (N : ℝ)) * F)

noncomputable def ibdIter (N : ℕ) (u : ℝ) : ℕ → ℝ → ℝ
  | 0, F => F
  | t + 1, F => ibdStep N u (ibdIter N u t F)

noncomputable def ibdFixed (N : ℕ) (u : ℝ) : ℝ :=
  (1 - u) ^ 2 / ((N : ℝ) - (1 - u) ^ 2 * ((N : ℝ) - 1))

section Fixed

variable {N : ℕ} {u : ℝ}

private theorem coef_bounds (hu0 : 0 ≤ u) (hu1 : u ≤ 1) : 0 ≤ (1 - u) ^ 2 ∧ (1 - u) ^ 2 ≤ 1 := by
  refine ⟨sq_nonneg _, ?_⟩
  nlinarith

private theorem denom_pos (hN : 1 ≤ N) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    0 < (N : ℝ) - (1 - u) ^ 2 * ((N : ℝ) - 1) := by
  have h := coef_bounds hu0 hu1
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  nlinarith

theorem ibdStep_fixed (hN : 1 ≤ N) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ibdStep N u (ibdFixed N u) = ibdFixed N u := by
  have hD := (denom_pos hN hu0 hu1).ne'
  have hN' : (N : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  unfold ibdStep ibdFixed
  field_simp
  ring

theorem eq_ibdFixed_of_ibdStep_eq (hN : 1 ≤ N) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) {F : ℝ}
    (hF : ibdStep N u F = F) : F = ibdFixed N u := by
  have hD := denom_pos hN hu0 hu1
  have hN' : (N : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  unfold ibdStep at hF
  unfold ibdFixed
  rw [eq_div_iff hD.ne']
  field_simp at hF
  nlinarith [hF]

theorem ibdFixed_eq (N : ℕ) (u : ℝ) :
    ibdFixed N u = (1 - u) ^ 2 / (1 + ((N : ℝ) - 1) * (u * (2 - u))) := by
  unfold ibdFixed
  congr 1
  ring

theorem ibdIter_sub_fixed (hN : 1 ≤ N) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (t : ℕ) (F₀ : ℝ) :
    ibdIter N u t F₀ - ibdFixed N u =
      ((1 - u) ^ 2 * (1 - 1 / (N : ℝ))) ^ t * (F₀ - ibdFixed N u) := by
  induction t with
  | zero => simp [ibdIter]
  | succ t ih =>
    have hfix := ibdStep_fixed hN hu0 hu1
    have : ibdIter N u (t + 1) F₀ - ibdFixed N u =
        ibdStep N u (ibdIter N u t F₀) - ibdStep N u (ibdFixed N u) := by
      rw [hfix]; rfl
    rw [this]
    have h2 : ibdStep N u (ibdIter N u t F₀) - ibdStep N u (ibdFixed N u) =
        ((1 - u) ^ 2 * (1 - 1 / (N : ℝ))) * (ibdIter N u t F₀ - ibdFixed N u) := by
      unfold ibdStep; ring
    rw [h2, ih]; ring

theorem tendsto_ibdIter (hN : 1 ≤ N) (hu0 : 0 < u) (hu1 : u ≤ 1) (F₀ : ℝ) :
    Tendsto (fun t => ibdIter N u t F₀) atTop (𝓝 (ibdFixed N u)) := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hc := coef_bounds hu0.le hu1
  have hq0 : 0 ≤ 1 - 1 / (N : ℝ) := by
    have : 1 / (N : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hN'
    linarith
  have hq1 : 1 - 1 / (N : ℝ) ≤ 1 := by
    have : 0 ≤ 1 / (N : ℝ) := by positivity
    linarith
  have hlt : (1 - u) ^ 2 < 1 := by nlinarith
  have hr1 : (1 - u) ^ 2 * (1 - 1 / (N : ℝ)) < 1 := by nlinarith
  have hr0 : 0 ≤ (1 - u) ^ 2 * (1 - 1 / (N : ℝ)) := mul_nonneg hc.1 hq0
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).mul_const (F₀ - ibdFixed N u)
  rw [zero_mul] at h
  have h' := h.add_const (ibdFixed N u)
  rw [zero_add] at h'
  refine h'.congr fun t => ?_
  have := ibdIter_sub_fixed hN hu0.le hu1 t F₀
  linarith

end Fixed

theorem tendsto_ibdFixed_scaling {θ : ℝ} (hθ : 0 ≤ θ) :
    Tendsto (fun N : ℕ => ibdFixed N (θ / (2 * N))) atTop (𝓝 (1 / (1 + θ))) := by
  set G : ℝ → ℝ := fun x => (1 - θ * x / 2) ^ 2 / (1 + (1 - x) * (θ / 2) * (2 - θ * x / 2))
    with hG
  have hGlim : Tendsto G (𝓝 0) (𝓝 (1 / (1 + θ))) := by
    have hn : Tendsto (fun x : ℝ => (1 - θ * x / 2) ^ 2) (𝓝 0) (𝓝 1) := by
      have : Continuous fun x : ℝ => (1 - θ * x / 2) ^ 2 := by fun_prop
      simpa using this.tendsto 0
    have hd : Tendsto (fun x : ℝ => 1 + (1 - x) * (θ / 2) * (2 - θ * x / 2)) (𝓝 0) (𝓝 (1 + θ)) := by
      have : Continuous fun x : ℝ => 1 + (1 - x) * (θ / 2) * (2 - θ * x / 2) := by fun_prop
      have h0 := this.tendsto 0
      have e : (1 : ℝ) + (1 - 0) * (θ / 2) * (2 - θ * 0 / 2) = 1 + θ := by ring
      simpa [e] using h0
    exact hn.div hd (by linarith)
  have hx : Tendsto (fun N : ℕ => (1 : ℝ) / N) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
  refine (hGlim.comp hx).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN' : (N : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  simp only [Function.comp, hG]
  rw [ibdFixed_eq]
  have : 1 + ((N : ℝ) - 1) * (θ / (2 * N) * (2 - θ / (2 * N))) =
      1 + (1 - 1 / (N : ℝ)) * (θ / 2) * (2 - θ * (1 / (N : ℝ)) / 2) := by
    field_simp
  rw [this]
  congr 2
  field_simp

end Rhone.Dynamics
