/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.CollapsedGenealogy.Object
public import Rhone.Statistics.ThreeSiteSeparator.ScoreSymmetry

/-! # Measurable decoder of the three pairwise conditional means -/

@[expose] public section

noncomputable section
namespace Rhone.Statistics.CollapsedGenealogy
open ThreeSiteSeparator

def largest (x : Fin 3 → ℝ) : ℝ := max (x 0) (max (x 1) (x 2))
def smallest (x : Fin 3 → ℝ) : ℝ := min (x 0) (min (x 1) (x 2))
def cherry (x : Fin 3 → ℝ) : Fin 3 :=
  if x 0 = x 1 ∧ x 1 = x 2 then 0 else if x 1 < x 0 then 0 else if x 1 < x 2 then 1 else 2

def decode (x : Fin 3 → ℝ) : Joint :=
  ((-Real.log (largest x), Real.log (largest x) - Real.log (smallest x)), cherry x)

theorem decode_measurable : Measurable decode := by
  have hc : Measurable cherry := by
    unfold cherry
    apply Measurable.ite
    · exact (measurableSet_eq_fun (measurable_pi_apply 0) (measurable_pi_apply 1)).inter
        (measurableSet_eq_fun (measurable_pi_apply 1) (measurable_pi_apply 2))
    · exact measurable_const
    · apply Measurable.ite
      · exact measurableSet_lt (measurable_pi_apply 1) (measurable_pi_apply 0)
      · exact measurable_const
      · exact Measurable.ite
          (measurableSet_lt (measurable_pi_apply 1) (measurable_pi_apply 2))
          measurable_const measurable_const
  unfold decode largest smallest
  apply Measurable.prodMk
  · apply Measurable.prodMk <;> fun_prop
  · exact hc

theorem means_extrema {a b : ℝ} (hab : b ≤ a) (q : Fin 3) :
    largest (pairMeans a b q) = a ∧ smallest (pairMeans a b q) = b := by
  fin_cases q <;> simp [largest, smallest, pairMeans, max_eq_left hab, max_eq_right hab,
    min_eq_left hab, min_eq_right hab]

theorem means_cherry_equal (a : ℝ) (q : Fin 3) : cherry (pairMeans a a q) = 0 := by
  simp [cherry, pairMeans]

theorem means_cherry_strict {a b : ℝ} (hab : b < a) (q : Fin 3) :
    cherry (pairMeans a b q) = q := by
  fin_cases q <;> simp [cherry, pairMeans, hab, ne_of_gt hab, ne_of_lt hab, not_lt_of_ge hab.le]

theorem decode_means (g : Joint) (hv : 0 ≤ g.1.2) :
    decode (pairMeans (Real.exp (-g.1.1)) (Real.exp (-(g.1.1 + g.1.2))) g.2) = collapse g := by
  have hab : Real.exp (-(g.1.1 + g.1.2)) ≤ Real.exp (-g.1.1) :=
    Real.exp_le_exp.mpr (by linarith)
  obtain ⟨hmax, hmin⟩ := means_extrema hab g.2
  unfold decode collapse
  rw [hmax, hmin, Real.log_exp, Real.log_exp]
  apply Prod.ext
  · apply Prod.ext <;> dsimp <;> ring
  · dsimp
    by_cases hz : g.1.2 = 0
    · rw [hz, add_zero, means_cherry_equal, ite_eq_left rfl]
    · rw [ite_eq_right hz]
      apply means_cherry_strict
      apply Real.exp_lt_exp.mpr
      have hp := lt_of_le_of_ne hv (Ne.symm hz)
      linarith

end Rhone.Statistics.CollapsedGenealogy
