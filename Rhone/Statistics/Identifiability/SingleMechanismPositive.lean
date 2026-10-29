/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.SingleMechanismPayoff

/-! # Strict positivity at exposure onset, without a nonzero instantaneous rate -/

@[expose] public section

open Set MeasureTheory
open scoped BigOperators Topology Matrix Matrix.Norms.Operator
namespace Rhone.Statistics.Identifiability
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem rowPayoff_positive_near_single_onset
    (C : ℝ → Matrix ι ι ℝ) (r : ℝ → ℝ) (R : Matrix ι ι ℝ) (ρ v : ι → ℝ)
    (hC : ∀ i j, Continuous (fun t => C t i j)) (hr : Continuous r)
    (hrn : ∀ u, 0 ≤ u → 0 ≤ r u) {K : ℝ} (hK : 0 ≤ K)
    (hbC : HasContractiveBoundOn C 0 1 K)
    (hbD : HasContractiveBoundOn (C + fun u => r u • R) 0 1 K)
    (hzero : ∀ t, rowPayoff ρ (inhomogeneousTransition C 0 t) v = 0)
    (hlead : 0 < rowPayoff ρ R v) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t, 0 < t → t < δ → (0 < ∫ u in (0 : ℝ)..t, r u) →
      0 < rowPayoff ρ (inhomogeneousTransition (C + fun u => r u • R) 0 t) v := by
  let D : ℝ := (∑ i, |ρ i|) * K * ‖R‖ * ‖v‖
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨min 1 (rowPayoff ρ R v / (D + 1)),
    lt_min (by norm_num) (div_pos hlead (by positivity)), ?_⟩
  intro t ht htδ hexp
  have ht1 : t ≤ 1 := (htδ.trans_le (min_le_left _ _)).le
  have hsmall : D * t < rowPayoff ρ R v := by
    have h := (lt_div_iff₀ (show 0 < D + 1 by positivity)).mp
      (htδ.trans_le (min_le_right _ _))
    nlinarith
  have hbC' : HasContractiveBoundOn C 0 t K :=
    ⟨fun u hu => hbC.1 u ⟨hu.1, hu.2.trans ht1⟩,
      fun a b ha hab hb => hbC.2 a b ha hab (hb.trans ht1)⟩
  have hbD' : HasContractiveBoundOn (C + fun u => r u • R) 0 t K :=
    ⟨fun u hu => hbD.1 u ⟨hu.1, hu.2.trans ht1⟩,
      fun a b ha hab hb => hbD.2 a b ha hab (hb.trans ht1)⟩
  have hrem := rowPayoff_single_remainder_le C r R ρ v hC hr ht.le
    (fun u hu => hrn u hu.1) hbC' hbD' (hzero t)
  simp only [sub_zero] at hrem
  have hscale := mul_lt_mul_of_pos_right hsmall hexp
  have hlow := (abs_le.mp hrem).1
  change -(D * t * (∫ u in (0 : ℝ)..t, r u)) ≤ _ at hlow
  nlinarith

end Rhone.Statistics.Identifiability
