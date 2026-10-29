/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.FullPanLaw
public import Rhone.Statistics.Identifiability.IntegralRank

/-! # The marginal clock recovered from first-merger and pending-pair masses -/

@[expose] public section

open Set MeasureTheory
namespace Rhone.Statistics.Identifiability

set_option backward.isDefEq.respectTransparency false

noncomputable def pendingPairMass (rate H N : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (-H t) * primitiveFrom (fun s => rate s*N s*Real.exp (H s)) 0 t

theorem pendingPairMass_continuous (rate H N : ℝ → ℝ)
    (hr : Continuous rate) (hH : Continuous H) (hN : Continuous N) :
    Continuous (pendingPairMass rate H N) := by
  have hg : Continuous (fun s => rate s*N s*Real.exp (H s)) :=
    (hr.mul hN).mul (Real.continuous_exp.comp hH)
  have hi : Continuous (primitiveFrom (fun s => rate s*N s*Real.exp (H s)) 0) :=
    continuous_iff_continuousAt.mpr fun t => (primitiveFrom_hasDerivAt _ hg 0 t).continuousAt
  exact (Real.continuous_exp.comp hH.neg).mul hi

theorem pendingPairMass_nonneg (rate H N : ℝ → ℝ)
    (hr : ∀ t, 0 ≤ t → 0 ≤ rate t) (hN : ∀ t, 0 ≤ t → 0 ≤ N t)
    {t : ℝ} (ht : 0 ≤ t) : 0 ≤ pendingPairMass rate H N t := by
  unfold pendingPairMass primitiveFrom
  apply mul_nonneg (Real.exp_pos _).le
  apply intervalIntegral.integral_nonneg ht
  intro s hs
  exact mul_nonneg (mul_nonneg (hr s hs.1) (hN s hs.1)) (Real.exp_pos _).le

theorem pendingPairMass_derivative (rate H N : ℝ → ℝ)
    (hr : Continuous rate) (hH : Continuous H) (hN : Continuous N) (t : ℝ)
    (hclock : HasDerivAt H (rate t) t) :
    HasDerivAt (pendingPairMass rate H N)
      (rate t*N t-rate t*pendingPairMass rate H N t) t := by
  have hi := primitiveFrom_hasDerivAt (fun s => rate s*N s*Real.exp (H s))
    ((hr.mul hN).mul (Real.continuous_exp.comp hH)) 0 t
  have he : Real.exp (-H t)*Real.exp (H t) = 1 := by
    rw [← Real.exp_add,neg_add_cancel,Real.exp_zero]
  convert! hclock.neg.exp.mul hi using 1
  unfold pendingPairMass
  first | linear_combination (rate t*N t)*he | linear_combination -(rate t*N t)*he

theorem pendingPairMass_zero (rate H N : ℝ → ℝ) : pendingPairMass rate H N 0 = 0 := by
  simp [pendingPairMass,primitiveFrom]

theorem marginal_mass_clock_identity (rate H D N : ℝ → ℝ)
    (hr : Continuous rate) (hH : Continuous H) (hN : Continuous N)
    (hzero : D 0 + N 0 = 1)
    (hclock : ∀ t, 0 ≤ t → HasDerivAt H (rate t) t)
    (hbalance : ∀ t, 0 ≤ t →
      HasDerivAt (fun x => D x + N x) (-rate t * (D t + 2 * N t)) t)
    {t : ℝ} (ht : 0 ≤ t) :
    D t+N t+pendingPairMass rate H N t = Real.exp (H 0-H t) := by
  have hm : ∀ x, 0 ≤ x → HasDerivAt
      (fun y => D y+N y+pendingPairMass rate H N y)
      (-rate x*(D x + N x+pendingPairMass rate H N x)) x := by
    intro x hx
    convert! (hbalance x hx).add
      (pendingPairMass_derivative rate H N hr hH hN x (hclock x hx)) using 1
    ring
  have he := survival_clock_of_forward_equation
    (fun x => D x + N x+pendingPairMass rate H N x) rate H 0 hm hclock ht
  simpa only [pendingPairMass_zero,add_zero,hzero,one_mul] using he

end Rhone.Statistics.Identifiability
