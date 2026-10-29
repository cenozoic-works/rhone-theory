/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.IslandThreeJointTimes
public import Rhone.Statistics.Identifiability.CommonClockIslandPairMarginal
public import Rhone.Statistics.Identifiability.IntegrableDiagonalLowerBound
public import Rhone.Statistics.Identifiability.ExponentialTwoEventLaw
public import Rhone.Statistics.Identifiability.PanThreeSampleLaw

/-! # Density bounds for the three-sample joint law without migration -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory Matrix
open scoped BigOperators Topology Matrix Matrix.Norms.Operator
namespace Rhone.Statistics.Identifiability.ThreeNoMigration

lemma exponential_diagonal_lower_bound {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : IsMetzler Q) {t : ℝ} (ht : 0 ≤ t) (i : Fin d) :
    Real.exp (t * Q i i) ≤ NormedSpace.exp (t • Q) i i := by
  have h := integrableTransition_diagonal_lower_bound (fun _ => Q)
    (fun i j => locallyIntegrable_const (Q i j)) (ae_of_all _ fun _ _ => hQ)
    le_rfl ht i
  simpa [inhomogeneousTransition_const_eq_exp, intervalIntegral.integral_const,
    smul_eq_mul] using h

def density (k : ℕ) (c q : ℝ) (p : ℝ × ℝ) : ℝ :=
  (3 * c * Real.exp (-(3 * (c + MarkovChain.Identifiability.totalMigration k q)) * p.1)) *
    (c * Real.exp (-(c + 2 * MarkovChain.Identifiability.totalMigration k q) * (p.2 - p.1)))

lemma density_continuous (k : ℕ) (c q : ℝ) : Continuous (density k c q) := by
  unfold density
  fun_prop

lemma entry_lower (k : ℕ) {c q s : ℝ} (hc : 0 ≤ c) (hq : 0 ≤ q) (hs : 0 ≤ s) :
    3 * c * Real.exp (-(3 * (c + MarkovChain.Identifiability.totalMigration k q)) * s) ≤
      IslandThreeTimes.entryFlux k c q 0 s := by
  have he : IslandThreeTimes.entryFlux k c q 0 s =
      3 * c * NormedSpace.exp (s • threeGenerator k c q) 0 0 := by
    simp [IslandThreeTimes.entryFlux, flowOutput, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, IslandThreeTimes.firstRate]
    ring
  rw [he]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) hc)
  have h := exponential_diagonal_lower_bound (threeGenerator k c q)
    (threeGenerator_metzler k c hq) hs 0
  convert! h using 1
  congr 1
  simp [threeGenerator]
  ring

lemma post_lower (k : ℕ) {c q u : ℝ} (hc : 0 ≤ c) (hq : 0 ≤ q) (hu : 0 ≤ u) :
    c * Real.exp (-(c + 2 * MarkovChain.Identifiability.totalMigration k q) * u) ≤
      IslandThreeTimes.postDensity k c q 0 u := by
  have he : IslandThreeTimes.postDensity k c q 0 u =
      c * NormedSpace.exp (u • MarkovChain.Identifiability.pairGenerator k c q) 0 0 := by
    simp only [IslandThreeTimes.postDensity, flowOutput, pow_zero, Matrix.one_mul]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, exitRate,
        MarkovChain.Identifiability.pairGenerator]
    ring
  rw [he]
  apply mul_le_mul_of_nonneg_left _ hc
  have h := exponential_diagonal_lower_bound (MarkovChain.Identifiability.pairGenerator k c q)
    (pairGenerator_metzler k hq) hu 0
  convert! h using 1
  congr 1
  simp [MarkovChain.Identifiability.pairGenerator]
  ring

lemma density_le_island (k : ℕ) {c q : ℝ} (hc : 0 ≤ c) (hq : 0 ≤ q)
    {p : ℝ × ℝ} (hp : p ∈ upperWedge) :
    density k c q p ≤ IslandThreeTimes.density k c q p := by
  have hu : 0 ≤ p.2 - p.1 := sub_nonneg.mpr hp.2.le
  have h := mul_le_mul (entry_lower k hc hq hp.1.le) (post_lower k hc hq hu)
    (mul_nonneg hc (Real.exp_pos _).le) (IslandThreeTimes.entryFlux_nonneg k hc hq hp.1.le 0)
  change density k c q p ≤
    ∑ j : Fin 2, IslandThreeTimes.entryFlux k c q j p.1 *
      IslandThreeTimes.postDensity k c q j (p.2 - p.1)
  rw [Fin.sum_univ_two]
  exact h.trans (le_add_of_nonneg_right (mul_nonneg
    (IslandThreeTimes.entryFlux_nonneg k hc hq hp.1.le 1)
    (IslandThreeTimes.postDensity_nonneg k hc hq hu 1)))

lemma pan_const_density (c : ℝ) (p : ℝ × ℝ) :
    PanThreeSample.jointDensity (fun _ => c) p = ExponentialTwoEvent.density (3 * c) c p := by
  simp only [PanThreeSample.jointDensity, PanThreeSample.firstDensity, conditionalPairDensity,
    integratedClock, intervalIntegral.integral_const, sub_zero, smul_eq_mul,
    ExponentialTwoEvent.density, ExponentialTwoEvent.shiftedDensity]
  congr 2 <;> congr 1 <;> ring

lemma density_le_pan (k : ℕ) {c q : ℝ} (hc : 0 ≤ c) (hq : 0 ≤ q)
    {p : ℝ × ℝ} (hp : p ∈ upperWedge) :
    density k c q p ≤ PanThreeSample.jointDensity (fun _ => c) p := by
  have hm : 0 ≤ MarkovChain.Identifiability.totalMigration k q :=
      by unfold MarkovChain.Identifiability.totalMigration; positivity
  have hms := mul_nonneg hm hp.1.le
  have hmu := mul_nonneg hm (sub_nonneg.mpr hp.2.le)
  have hfirst : Real.exp (-(3 * (c + MarkovChain.Identifiability.totalMigration k q)) * p.1) ≤
      Real.exp (-(3 * c) * p.1) := Real.exp_le_exp.mpr (by nlinarith only [hms])
  have hpost : Real.exp (-(c + 2 * MarkovChain.Identifiability.totalMigration k q) * (p.2 - p.1)) ≤
      Real.exp (-c * (p.2 - p.1)) := Real.exp_le_exp.mpr (by nlinarith only [hmu])
  rw [pan_const_density]
  simp only [density, ExponentialTwoEvent.density, ExponentialTwoEvent.shiftedDensity, sub_zero]
  exact mul_le_mul (mul_le_mul_of_nonneg_left hfirst (mul_nonneg (by norm_num) hc))
    (mul_le_mul_of_nonneg_left hpost hc) (mul_nonneg hc (Real.exp_pos _).le)
    (mul_nonneg (mul_nonneg (by norm_num) hc) (Real.exp_pos _).le)

end Rhone.Statistics.Identifiability.ThreeNoMigration
