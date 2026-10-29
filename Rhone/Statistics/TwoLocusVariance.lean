/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Dynamics.LDDecay
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Two-locus score variance under random union of gametes

Source: bulmer1971, eq. (4), (9), pp. 202–203; bulmer1974, p. 282, eq. (2), (4). -/

@[expose] public section
namespace Rhone.Statistics

/-- Source: bulmer1971, eq. (4), (9), pp. 202–203; bulmer1974, p. 282, eq. (2), (4). -/
noncomputable def gameteProbability (g : Rhone.Dynamics.Gametes ℝ) : Fin 4 → ℝ :=
  ![g.x11, g.x12, g.x21, g.x22]

/-- Source: bulmer1971, eq. (3), p. 201; bulmer1974, p. 282, eq. (2), (4). -/
noncomputable def gameteScore (a b : ℝ) : Fin 4 → ℝ := ![a+b,a,b,0]

/-- Source: bulmer1974, p. 282, eq. (2), (4). -/
noncomputable def twoLocusScoreMean (g : Rhone.Dynamics.Gametes ℝ) (a b : ℝ) : ℝ :=
  ∑ i, ∑ j, gameteProbability g i * gameteProbability g j *
    (gameteScore a b i + gameteScore a b j)

/-- Source: bulmer1971, eq. (4), (9), pp. 202–203; bulmer1974, p. 282, eq. (2), (4). -/
noncomputable def twoLocusScoreVariance (g : Rhone.Dynamics.Gametes ℝ) (a b : ℝ) : ℝ :=
  ∑ i, ∑ j, gameteProbability g i * gameteProbability g j *
    (gameteScore a b i + gameteScore a b j - twoLocusScoreMean g a b)^2

/-- Source: bulmer1974, p. 282, eq. (2), (4). -/
private theorem score_mean (g : Rhone.Dynamics.Gametes ℝ) (a b : ℝ) (ht : g.total = 1) :
    twoLocusScoreMean g a b = 2*(a*g.pA+b*g.pB) := by
  have hx : g.x22 = 1-g.x11-g.x12-g.x21 := by
    unfold Rhone.Dynamics.Gametes.total at ht
    linarith
  simp [twoLocusScoreMean, gameteProbability, gameteScore, Fin.sum_univ_succ,
    Rhone.Dynamics.Gametes.pA, Rhone.Dynamics.Gametes.pB, hx]
  ring

/-- Source: bulmer1971, eq. (4), (9), pp. 202–203; bulmer1974, p. 282, eq. (2), (4). -/
theorem two_locus_score_variance
    (g : Rhone.Dynamics.Gametes ℝ) (a b : ℝ) (ht : g.total = 1)
    (h11 : 0 ≤ g.x11) (h12 : 0 ≤ g.x12) (h21 : 0 ≤ g.x21) (h22 : 0 ≤ g.x22) :
    twoLocusScoreVariance g a b =
      2*a^2*g.pA*(1-g.pA) + 2*b^2*g.pB*(1-g.pB) + 4*a*b*g.D := by
  have _hprob : 0 ≤ g.x11 ∧ 0 ≤ g.x12 ∧ 0 ≤ g.x21 ∧ 0 ≤ g.x22 :=
    ⟨h11, h12, h21, h22⟩
  have hx : g.x22 = 1-g.x11-g.x12-g.x21 := by
    unfold Rhone.Dynamics.Gametes.total at ht
    linarith
  unfold twoLocusScoreVariance
  rw [score_mean g a b ht]
  simp [gameteProbability, gameteScore, Fin.sum_univ_succ,
    Rhone.Dynamics.Gametes.pA, Rhone.Dynamics.Gametes.pB, Rhone.Dynamics.Gametes.D, hx]
  ring

/-- Source: bulmer1971, p. 204; bulmer1974, p. 282, eq. (2), (4). -/
theorem recombination_score_variance_change
    (g : Rhone.Dynamics.Gametes ℝ) (a b r : ℝ) (ht : g.total = 1)
    (h11 : 0 ≤ g.x11) (h12 : 0 ≤ g.x12) (h21 : 0 ≤ g.x21) (h22 : 0 ≤ g.x22)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    twoLocusScoreVariance (g.recombine r) a b - twoLocusScoreVariance g a b =
      -4*r*a*b*g.D := by
  obtain ⟨h11', h12', h21', h22'⟩ :=
    Rhone.Dynamics.Gametes.recombine_nonneg hr0 hr1 h11 h12 h21 h22
  rw [two_locus_score_variance (g.recombine r) a b
    (Rhone.Dynamics.Gametes.total_recombine r ht) h11' h12' h21' h22',
    two_locus_score_variance g a b ht h11 h12 h21 h22,
    Rhone.Dynamics.Gametes.recombine_pA r ht, Rhone.Dynamics.Gametes.recombine_pB r ht,
    Rhone.Dynamics.Gametes.D_recombine r ht]
  ring

end Rhone.Statistics
