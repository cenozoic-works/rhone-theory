/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ObservableProbe

/-! # Exact pure-recombination and pure-coalescence phases, and their observable fluxes -/

@[expose] public section

open Set MeasureTheory
namespace Rhone.Statistics.Identifiability

set_option backward.isDefEq.respectTransparency false

theorem clockJointLaw_congr_fluxes (rate H D₁ D₂ N₁ N₂ : ℝ → ℝ)
    (hd : EqOn (fun t => rate t * D₁ t) (fun t => rate t * D₂ t) (Ioi 0))
    (hn : EqOn (fun t => rate t * N₁ t) (fun t => rate t * N₂ t) (Ioi 0)) :
    clockJointLaw rate H D₁ N₁ = clockJointLaw rate H D₂ N₂ := by
  apply regularJointLaw_congr_on_support hd
  intro p hp
  change rate p.1 * N₁ p.1 * rate p.2 * Real.exp (H p.1 - H p.2) = _
  have hn' : rate p.1 * N₁ p.1 = rate p.1 * N₂ p.1 := hn hp.1
  exact congrArg (fun v => v * rate p.2 * Real.exp (H p.1 - H p.2)) hn'

theorem clockJointLaw_congr_after_zero_interval (rate H D₁ D₂ N₁ N₂ : ℝ → ℝ) (b : ℝ)
    (hz : ∀ t, 0 < t → t ≤ b → rate t = 0)
    (hd : EqOn D₁ D₂ (Ioi b)) (hn : EqOn N₁ N₂ (Ioi b)) :
    clockJointLaw rate H D₁ N₁ = clockJointLaw rate H D₂ N₂ := by
  apply clockJointLaw_congr_fluxes
  · intro t ht
    change rate t * D₁ t = rate t * D₂ t
    by_cases hb : t ≤ b
    · simp [hz t ht hb]
    · rw [hd (lt_of_not_ge hb)]
  · intro t ht
    change rate t * N₁ t = rate t * N₂ t
    by_cases hb : t ≤ b
    · simp [hz t ht hb]
    · rw [hn (lt_of_not_ge hb)]

theorem pureRecombination_derivatives (x : ℝ → ℝ) (d r u ρ t : ℝ)
    (hx : HasDerivAt x (-ρ * x t) t) :
    HasDerivAt (fun s => d * (x s)^2) (-2*ρ*(d*(x t)^2)) t ∧
    HasDerivAt (fun s => r*x s+2*d*x s*(1-x s))
      (2*ρ*(d*(x t)^2)-ρ*(r*x t+2*d*x t*(1-x t))) t ∧
    HasDerivAt (fun s => u+r*(1-x s)+d*(1-x s)^2)
      (ρ*(r*x t+2*d*x t*(1-x t))) t := by
  refine ⟨?_,?_,?_⟩
  · convert! (hx.pow 2).const_mul d using 1; ring
  · convert! (hx.const_mul r).add (((hx.const_mul (2*d)).mul (hx.const_sub 1))) using 1; ring
  · convert! (((hx.const_sub 1).const_mul r).const_add u).add
      (((hx.const_sub 1).pow 2).const_mul d) using 1; ring

theorem exponential_clock_derivative (A : ℝ → ℝ) (ρ t : ℝ)
    (hA : HasDerivAt A ρ t) :
    HasDerivAt (fun s => Real.exp (-A s)) (-ρ * Real.exp (-A t)) t := by
  simpa only [Pi.neg_apply, mul_comm] using hA.neg.exp

noncomputable def coalescenceTailD (d r u y : ℝ) : ℝ :=
  d*y+(r/2)*(y-y^3)+u*((2/5)*y-(2/3)*y^3+(4/15)*y^6)

noncomputable def coalescenceTailR (r u y : ℝ) : ℝ :=
  r*y^3+(4/3)*u*(y^3-y^6)

noncomputable def coalescenceTailU (u y : ℝ) : ℝ := u*y^6

theorem coalescenceTailD_factored (d r u y : ℝ) :
    coalescenceTailD d r u y =
      d*y+(r/2)*y*(1-y)*(1+y)+(2/15)*u*y*(1-y)^2*(2*y^3+4*y^2+6*y+3) := by
  unfold coalescenceTailD
  ring

theorem coalescenceTailR_factored (r u y : ℝ) :
    coalescenceTailR r u y = r*y^3+(4/3)*u*y^3*(1-y^3) := by
  unfold coalescenceTailR
  ring

theorem coalescenceTail_initial (d r u : ℝ) :
    coalescenceTailD d r u 1 = d ∧
      coalescenceTailR r u 1 = r ∧ coalescenceTailU u 1 = u := by
  norm_num [coalescenceTailD,coalescenceTailR,coalescenceTailU]

theorem coalescenceTail_derivatives (y : ℝ → ℝ) (d r u rate t : ℝ)
    (hy : HasDerivAt y (-rate * y t) t) :
    HasDerivAt (fun s => coalescenceTailD d r u (y s))
      (rate*(-coalescenceTailD d r u (y t)+coalescenceTailR r u (y t))) t ∧
    HasDerivAt (fun s => coalescenceTailR r u (y s))
      (rate*(-3*coalescenceTailR r u (y t)+4*coalescenceTailU u (y t))) t ∧
    HasDerivAt (fun s => coalescenceTailU u (y s))
      (-6*rate*coalescenceTailU u (y t)) t := by
  have hd := ((hy.const_mul d).add ((hy.sub (hy.pow 3)).const_mul (r/2))).add
    ((((hy.const_mul (2/5)).sub ((hy.pow 3).const_mul (2/3))).add
      ((hy.pow 6).const_mul (4/15))).const_mul u)
  have hr := ((hy.pow 3).const_mul r).add
    (((hy.pow 3).sub (hy.pow 6)).const_mul ((4/3)*u))
  have hu := (hy.pow 6).const_mul u
  refine ⟨?_,?_,?_⟩
  · convert! hd using 1
    unfold coalescenceTailD coalescenceTailR
    ring
  · convert! hr using 1
    unfold coalescenceTailR coalescenceTailU
    ring
  · convert! hu using 1
    unfold coalescenceTailU
    ring

theorem coalescenceTail_positive (d r u y : ℝ)
    (hd : 0 < d) (hr : 0 ≤ r) (hu : 0 ≤ u) (hy : 0 < y) (hy1 : y ≤ 1) :
    0 < coalescenceTailD d r u y ∧
      0 ≤ coalescenceTailR r u y ∧ 0 ≤ coalescenceTailU u y := by
  have h1 : 0 ≤ 1-y := sub_nonneg.mpr hy1
  have h3 : y^3 ≤ 1 := pow_le_one₀ hy.le hy1
  have h31 : 0 ≤ 1-y^3 := sub_nonneg.mpr h3
  rw [coalescenceTailD_factored,coalescenceTailR_factored]
  unfold coalescenceTailU
  exact ⟨by positivity,by positivity,by positivity⟩

end Rhone.Statistics.Identifiability
