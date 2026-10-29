/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.PeanoBaker
public import Rhone.Statistics.Identifiability.PanODEPositivity
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-! # Global finite-dimensional row evolution for continuous time-dependent generators -/

@[expose] public section

open Set Filter
open scoped BigOperators Topology
namespace Rhone.Statistics.Identifiability

variable {ι : Type*} [Fintype ι]

noncomputable def inhomogeneousRowOperator (Q : ι → ι → ℝ) : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  LinearMap.toContinuousLinearMap
  { toFun := fun x j => ∑ i, x i * Q i j
    map_add' := by intro x y; ext j; simp [add_mul, Finset.sum_add_distrib]
    map_smul' := by intro a x; ext j; simp [Finset.mul_sum, mul_assoc] }

@[simp] theorem inhomogeneousRowOperator_apply (Q : ι → ι → ℝ) (x : ι → ℝ) (j : ι) :
    inhomogeneousRowOperator Q x j = ∑ i, x i * Q i j := rfl

theorem inhomogeneousRowOperator_continuous (Q : ℝ → ι → ι → ℝ)
    (hQ : ∀ i j, Continuous (fun t => Q t i j)) :
    Continuous (fun t => inhomogeneousRowOperator (Q t)) := by
  apply continuous_clm_apply.mpr
  intro x
  apply continuous_pi
  intro j
  simp only [inhomogeneousRowOperator_apply]
  exact continuous_finsetSum _ (fun i _ => continuous_const.mul (hQ i j))

theorem exists_inhomogeneous_row_solution (Q : ℝ → ι → ι → ℝ)
    (hQ : ∀ i j, Continuous (fun t => Q t i j)) (x : ι → ℝ) :
    ∃ v : ℝ → ι → ℝ, v 0 = x ∧ Continuous v ∧
      ∀ t j, HasDerivAt (fun s => v s j) (∑ i, v t i * Q t i j) t := by
  obtain ⟨v, hv₀, hvc, hv⟩ := PeanoBaker.exists_global_solution
    (fun t => inhomogeneousRowOperator (Q t))
    (inhomogeneousRowOperator_continuous Q hQ) x
  exact ⟨v, hv₀, hvc, fun t j => (hasDerivAt_pi.mp (hv t)) j⟩

theorem metzler_negative_cross_bound (x y q : ℝ) (hq : x = y ∨ 0 ≤ q) :
    2 * min y 0 * (x * q) ≤ |q| * ((min x 0)^2 + (min y 0)^2) := by
  rcases hq with rfl | hq
  · have hm := pan_min_zero_mul_self x
    have h := mul_le_mul_of_nonneg_left (le_abs_self q) (sq_nonneg (min x 0))
    have hmq := congrArg (fun z => z * q) hm
    nlinarith only [h, hmq]
  · have hc := mul_le_mul_of_nonpos_left (min_le_left x 0) (min_le_right y 0)
    have hmul := mul_le_mul_of_nonneg_left hc hq
    have hs := mul_nonneg hq (sq_nonneg (min x 0 - min y 0))
    rw [abs_of_nonneg hq]
    nlinarith only [hmul, hs]

theorem metzler_negative_energy_bound (Q : ι → ι → ℝ) (x : ι → ℝ)
    (hQ : ∀ i j, i ≠ j → 0 ≤ Q i j) :
    (∑ j, 2 * min (x j) 0 * (∑ i, x i * Q i j)) ≤
      (2 * ∑ j, ∑ i, |Q i j|) * (∑ i, (min (x i) 0)^2) := by
  classical
  let E : ℝ := ∑ i, (min (x i) 0)^2
  have hE : ∀ i, (min (x i) 0)^2 ≤ E := fun i =>
    Finset.single_le_sum (fun k _ => sq_nonneg (min (x k) 0)) (Finset.mem_univ i)
  calc
    _ = ∑ j, ∑ i, 2 * min (x j) 0 * (x i * Q i j) := by
      simp only [Finset.mul_sum]
    _ ≤ ∑ j, ∑ i, |Q i j| * ((min (x i) 0)^2 + (min (x j) 0)^2) := by
      apply Finset.sum_le_sum; intro j _
      apply Finset.sum_le_sum; intro i _
      apply metzler_negative_cross_bound
      by_cases hij : i = j
      · exact Or.inl (congrArg x hij)
      · exact Or.inr (hQ i j hij)
    _ ≤ ∑ j, ∑ i, |Q i j| * (2 * E) := by
      apply Finset.sum_le_sum; intro j _
      apply Finset.sum_le_sum; intro i _
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      linarith [hE i, hE j]
    _ = _ := by simp only [← Finset.sum_mul]; ring

theorem inhomogeneous_row_solution_nonneg (Q : ℝ → ι → ι → ℝ) (v : ℝ → ι → ℝ)
    (hQc : ∀ i j, Continuous (fun t => Q t i j))
    (hQ : ∀ t, 0 ≤ t → ∀ i j, i ≠ j → 0 ≤ Q t i j)
    (he : ∀ t, 0 ≤ t → ∀ j,
      HasDerivAt (fun s => v s j) (∑ i, v t i * Q t i j) t)
    (hzero : ∀ i, 0 ≤ v 0 i) :
    ∀ t, 0 ≤ t → ∀ i, 0 ≤ v t i := by
  classical
  let E : ℝ → ℝ := fun t => ∑ i, (min (v t i) 0)^2
  let Edot : ℝ → ℝ := fun t => ∑ j, 2 * min (v t j) 0 * (∑ i, v t i * Q t i j)
  let C : ℝ → ℝ := fun t => 2 * ∑ j, ∑ i, |Q t i j|
  let H : ℝ → ℝ := fun t => -(∫ s in (0 : ℝ)..t, C s)
  have hCc : Continuous C := by
    apply continuous_const.mul
    apply continuous_finsetSum; intro j _
    apply continuous_finsetSum; intro i _
    exact (hQc i j).abs
  have hE : ∀ t, 0 ≤ t → HasDerivAt E (Edot t) t := by
    intro t ht
    apply HasDerivAt.fun_sum
    intro j _
    simpa only [Function.comp_def] using
      (hasDerivAt_sq_min_zero (v t j)).comp t (he t ht j)
  have hH : ∀ t, 0 ≤ t → HasDerivAt H (-C t) t := by
    intro t _
    exact (intervalIntegral.integral_hasDerivAt_right (hCc.intervalIntegrable 0 t)
      hCc.aestronglyMeasurable.stronglyMeasurableAtFilter hCc.continuousAt).neg
  have hbound : ∀ t, 0 ≤ t → Edot t ≤ -(-C t) * E t := by
    intro t ht
    simpa only [C, E, Edot, neg_neg] using
      metzler_negative_energy_bound (Q t) (v t) (hQ t ht)
  have hEzero : E 0 = 0 := by simp [E, hzero]
  intro t ht i
  have hle := clock_decay_bound E Edot H (fun t => -C t) hE hH hbound ht
  rw [hEzero, zero_mul] at hle
  have hi : (min (v t i) 0)^2 ≤ E t :=
    Finset.single_le_sum (fun j _ => sq_nonneg (min (v t j) 0)) (Finset.mem_univ i)
  have hz : min (v t i) 0 = 0 := by nlinarith [hi.trans hle]
  simpa only [hz] using min_le_left (v t i) 0

theorem finiteRowODE_mass_hasDerivAt (Q : ℝ → ι → ι → ℝ) (v : ℝ → ι → ℝ)
    (he : ∀ t, 0 ≤ t → ∀ j,
      HasDerivAt (fun s => v s j) (∑ i, v t i * Q t i j) t)
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun s => ∑ i, v s i) (∑ i, v t i * ∑ j, Q t i j) t := by
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => he t ht j)
  rw [Finset.sum_comm] at hsum
  simpa only [Finset.mul_sum] using hsum

theorem finiteRowODE_mass_antitoneOn (Q : ℝ → ι → ι → ℝ) (v : ℝ → ι → ℝ)
    (he : ∀ t, 0 ≤ t → ∀ j,
      HasDerivAt (fun s => v s j) (∑ i, v t i * Q t i j) t)
    (hnonneg : ∀ t, 0 ≤ t → ∀ i, 0 ≤ v t i)
    (hrows : ∀ t, 0 ≤ t → ∀ i, ∑ j, Q t i j ≤ 0) :
    AntitoneOn (fun t => ∑ i, v t i) (Ici 0) := by
  have hd : ∀ t, 0 ≤ t →
      HasDerivAt (fun s => ∑ i, v s i) (∑ i, v t i * ∑ j, Q t i j) t :=
    fun _ ht => finiteRowODE_mass_hasDerivAt Q v he ht
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici (0 : ℝ))
  · exact fun t ht => (hd t ht).continuousAt.continuousWithinAt
  · exact fun t ht => (hd t (interior_subset ht)).hasDerivWithinAt
  · intro t ht
    exact Finset.sum_nonpos fun i _ =>
      mul_nonpos_of_nonneg_of_nonpos (hnonneg t (interior_subset ht) i)
        (hrows t (interior_subset ht) i)

theorem finiteRowODE_mass_le_initial (Q : ℝ → ι → ι → ℝ) (v : ℝ → ι → ℝ)
    (he : ∀ t, 0 ≤ t → ∀ j,
      HasDerivAt (fun s => v s j) (∑ i, v t i * Q t i j) t)
    (hnonneg : ∀ t, 0 ≤ t → ∀ i, 0 ≤ v t i)
    (hrows : ∀ t, 0 ≤ t → ∀ i, ∑ j, Q t i j ≤ 0)
    {t : ℝ} (ht : 0 ≤ t) :
    (∑ i, v t i) ≤ ∑ i, v 0 i :=
  finiteRowODE_mass_antitoneOn Q v he hnonneg hrows (by simp) ht ht

theorem finiteRowODE_mass_eq_initial (Q : ℝ → ι → ι → ℝ) (v : ℝ → ι → ℝ)
    (he : ∀ t, 0 ≤ t → ∀ j,
      HasDerivAt (fun s => v s j) (∑ i, v t i * Q t i j) t)
    (hrows : ∀ t, 0 ≤ t → ∀ i, ∑ j, Q t i j = 0)
    {t : ℝ} (ht : 0 ≤ t) :
    (∑ i, v t i) = ∑ i, v 0 i := by
  have hd : ∀ s, 0 ≤ s → HasDerivAt (fun u => ∑ i, v u i) 0 s := by
    intro s hs
    simpa only [hrows s hs, mul_zero, Finset.sum_const_zero] using
      finiteRowODE_mass_hasDerivAt Q v he hs
  have hanti : AntitoneOn (fun s => ∑ i, v s i) (Ici 0) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici (0 : ℝ))
    · exact fun s hs => (hd s hs).continuousAt.continuousWithinAt
    · exact fun s hs => (hd s (interior_subset hs)).hasDerivWithinAt
    · exact fun _ _ => le_rfl
  have hmono : MonotoneOn (fun s => ∑ i, v s i) (Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici (0 : ℝ))
    · exact fun s hs => (hd s hs).continuousAt.continuousWithinAt
    · exact fun s hs => (hd s (interior_subset hs)).hasDerivWithinAt
    · exact fun _ _ => le_rfl
  exact le_antisymm (hanti (by simp) ht ht) (hmono (by simp) ht ht)

theorem inhomogeneous_row_solution_comparison (Q : ℝ → ι → ι → ℝ)
    (v w : ℝ → ι → ℝ)
    (hQc : ∀ i j, Continuous (fun t => Q t i j))
    (hQ : ∀ t, 0 ≤ t → ∀ i j, i ≠ j → 0 ≤ Q t i j)
    (hv : ∀ t, 0 ≤ t → ∀ j,
      HasDerivAt (fun s => v s j) (∑ i, v t i * Q t i j) t)
    (hw : ∀ t, 0 ≤ t → ∀ j,
      HasDerivAt (fun s => w s j) (∑ i, w t i * Q t i j) t)
    (hzero : ∀ i, v 0 i ≤ w 0 i) :
    ∀ t, 0 ≤ t → ∀ i, v t i ≤ w t i := by
  have hd : ∀ t, 0 ≤ t → ∀ j,
      HasDerivAt (fun s => w s j - v s j) (∑ i, (w t i - v t i) * Q t i j) t := by
    intro t ht j
    convert! (hw t ht j).sub (hv t ht j) using 1
    simp only [sub_mul, Finset.sum_sub_distrib]
  have hn := inhomogeneous_row_solution_nonneg Q (fun t i => w t i - v t i)
    hQc hQ hd (fun i => sub_nonneg.mpr (hzero i))
  exact fun t ht i => sub_nonneg.mp (hn t ht i)

theorem inhomogeneous_row_solution_unique (Q : ℝ → ι → ι → ℝ)
    (v w : ℝ → ι → ℝ)
    (hQc : ∀ i j, Continuous (fun t => Q t i j))
    (hQ : ∀ t, 0 ≤ t → ∀ i j, i ≠ j → 0 ≤ Q t i j)
    (hv : ∀ t, 0 ≤ t → ∀ j,
      HasDerivAt (fun s => v s j) (∑ i, v t i * Q t i j) t)
    (hw : ∀ t, 0 ≤ t → ∀ j,
      HasDerivAt (fun s => w s j) (∑ i, w t i * Q t i j) t)
    (hzero : v 0 = w 0) :
    ∀ t, 0 ≤ t → v t = w t := by
  have hvw := inhomogeneous_row_solution_comparison Q v w hQc hQ hv hw
    (fun i => le_of_eq (congrFun hzero i))
  have hwv := inhomogeneous_row_solution_comparison Q w v hQc hQ hw hv
    (fun i => le_of_eq (congrFun hzero.symm i))
  exact fun t ht => funext (fun i => le_antisymm (hvw t ht i) (hwv t ht i))

theorem exists_inhomogeneous_subgenerator_solution (Q : ℝ → ι → ι → ℝ)
    (hQc : ∀ i j, Continuous (fun t => Q t i j))
    (hQ : ∀ t, 0 ≤ t → ∀ i j, i ≠ j → 0 ≤ Q t i j)
    (hrows : ∀ t, 0 ≤ t → ∀ i, ∑ j, Q t i j ≤ 0)
    (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) :
    ∃ v : ℝ → ι → ℝ, v 0 = x ∧ Continuous v ∧
      (∀ t j, HasDerivAt (fun s => v s j) (∑ i, v t i * Q t i j) t) ∧
      (∀ t, 0 ≤ t → ∀ i, 0 ≤ v t i) ∧
      AntitoneOn (fun t => ∑ i, v t i) (Ici 0) ∧
      (∀ t, 0 ≤ t → (∑ i, v t i) ≤ ∑ i, x i) := by
  obtain ⟨v, hvzero, hvc, hv⟩ := exists_inhomogeneous_row_solution Q hQc x
  have he := fun t (_ : 0 ≤ t) j => hv t j
  have hn := inhomogeneous_row_solution_nonneg Q v hQc hQ he
    (fun i => by simpa only [hvzero] using hx i)
  refine ⟨v, hvzero, hvc, hv, hn, finiteRowODE_mass_antitoneOn Q v he hn hrows, ?_⟩
  intro t ht
  simpa only [hvzero] using finiteRowODE_mass_le_initial Q v he hn hrows ht

theorem exists_inhomogeneous_generator_solution (Q : ℝ → ι → ι → ℝ)
    (hQc : ∀ i j, Continuous (fun t => Q t i j))
    (hQ : ∀ t, 0 ≤ t → ∀ i j, i ≠ j → 0 ≤ Q t i j)
    (hrows : ∀ t, 0 ≤ t → ∀ i, ∑ j, Q t i j = 0)
    (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) :
    ∃ v : ℝ → ι → ℝ, v 0 = x ∧ Continuous v ∧
      (∀ t j, HasDerivAt (fun s => v s j) (∑ i, v t i * Q t i j) t) ∧
      (∀ t, 0 ≤ t → ∀ i, 0 ≤ v t i) ∧
      (∀ t, 0 ≤ t → (∑ i, v t i) = ∑ i, x i) := by
  obtain ⟨v, hvzero, hvc, hv⟩ := exists_inhomogeneous_row_solution Q hQc x
  have he := fun t (_ : 0 ≤ t) j => hv t j
  have hn := inhomogeneous_row_solution_nonneg Q v hQc hQ he
    (fun i => by simpa only [hvzero] using hx i)
  refine ⟨v, hvzero, hvc, hv, hn, ?_⟩
  intro t ht
  simpa only [hvzero] using finiteRowODE_mass_eq_initial Q v he hrows ht

theorem finiteRowODE_mass_lower_clock (Q : ℝ → ι → ι → ℝ) (v : ℝ → ι → ℝ)
    (c H : ℝ → ℝ)
    (he : ∀ t, 0 ≤ t → ∀ j,
      HasDerivAt (fun s => v s j) (∑ i, v t i * Q t i j) t)
    (hnonneg : ∀ t, 0 ≤ t → ∀ i, 0 ≤ v t i)
    (hrows : ∀ t, 0 ≤ t → ∀ i, -c t ≤ ∑ j, Q t i j)
    (hH : ∀ t, 0 ≤ t → HasDerivAt H (c t) t)
    {t : ℝ} (ht : 0 ≤ t) :
    (∑ i, v 0 i) * Real.exp (H 0 - H t) ≤ ∑ i, v t i := by
  have hb : ∀ s, 0 ≤ s →
      -(∑ i, v s i * ∑ j, Q s i j) ≤ -c s * (-(∑ i, v s i)) := by
    intro s hs
    have hsum : (∑ i, v s i) * (-c s) ≤ ∑ i, v s i * ∑ j, Q s i j := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (hrows s hs i) (hnonneg s hs i)
    nlinarith only [hsum]
  have h := clock_decay_bound (fun s => -(∑ i, v s i))
    (fun s => -(∑ i, v s i * ∑ j, Q s i j)) H c
    (fun _ hs => (finiteRowODE_mass_hasDerivAt Q v he hs).neg) hH hb ht
  linarith

theorem finiteRowODE_mass_lower_integral (Q : ℝ → ι → ι → ℝ) (v : ℝ → ι → ℝ)
    (c : ℝ → ℝ) (hc : Continuous c)
    (he : ∀ t, 0 ≤ t → ∀ j,
      HasDerivAt (fun s => v s j) (∑ i, v t i * Q t i j) t)
    (hnonneg : ∀ t, 0 ≤ t → ∀ i, 0 ≤ v t i)
    (hrows : ∀ t, 0 ≤ t → ∀ i, -c t ≤ ∑ j, Q t i j)
    {t : ℝ} (ht : 0 ≤ t) :
    (∑ i, v 0 i) * Real.exp (-(∫ s in (0 : ℝ)..t, c s)) ≤ ∑ i, v t i := by
  have hH : ∀ t, 0 ≤ t → HasDerivAt (fun u => ∫ s in (0 : ℝ)..u, c s) (c t) t := by
    intro t _
    exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
      hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  simpa only [intervalIntegral.integral_same, zero_sub] using
    finiteRowODE_mass_lower_clock Q v c (fun t => ∫ s in (0 : ℝ)..t, c s)
      he hnonneg hrows hH ht

theorem tendsto_atTop_of_survival_lower_bound (S H : ℝ → ℝ) {a : ℝ}
    (ha : 0 < a) (hS : Tendsto S atTop (𝓝 0))
    (hlower : ∀ t, 0 ≤ t → a * Real.exp (-H t) ≤ S t) :
    Tendsto H atTop atTop := by
  have hexp : Tendsto (fun t => Real.exp (-H t)) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (show Tendsto (fun t => S t / a) atTop (𝓝 0) by simpa using hS.div_const a)
    · exact Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      exact (le_div_iff₀ ha).mpr (by simpa only [mul_comm] using hlower t ht)
  exact tendsto_neg_atBot_iff.mp (Real.tendsto_exp_comp_nhds_zero.mp hexp)

theorem finiteRowODE_integrated_rate_tendsto_atTop
    (Q : ℝ → ι → ι → ℝ) (v : ℝ → ι → ℝ) (c : ℝ → ℝ) (hc : Continuous c)
    (he : ∀ t, 0 ≤ t → ∀ j,
      HasDerivAt (fun s => v s j) (∑ i, v t i * Q t i j) t)
    (hnonneg : ∀ t, 0 ≤ t → ∀ i, 0 ≤ v t i)
    (hrows : ∀ t, 0 ≤ t → ∀ i, -c t ≤ ∑ j, Q t i j)
    (hinit : 0 < ∑ i, v 0 i)
    (hproper : Tendsto (fun t => ∑ i, v t i) atTop (𝓝 0)) :
    Tendsto (fun t => ∫ s in (0 : ℝ)..t, c s) atTop atTop := by
  exact tendsto_atTop_of_survival_lower_bound (fun t => ∑ i, v t i)
    (fun t => ∫ s in (0 : ℝ)..t, c s) hinit hproper
    (fun _ ht => finiteRowODE_mass_lower_integral Q v c hc he hnonneg hrows ht)

theorem inhomogeneous_row_coordinate_lower_bound (Q : ℝ → ι → ι → ℝ)
    (v : ℝ → ι → ℝ) (j : ι)
    (hQc : Continuous (fun t => Q t j j))
    (hQ : ∀ t, 0 ≤ t → ∀ i, i ≠ j → 0 ≤ Q t i j)
    (he : ∀ t, 0 ≤ t → HasDerivAt (fun s => v s j) (∑ i, v t i * Q t i j) t)
    (hn : ∀ t, 0 ≤ t → ∀ i, 0 ≤ v t i)
    {t : ℝ} (ht : 0 ≤ t) :
    v 0 j * Real.exp (∫ s in (0 : ℝ)..t, Q s j j) ≤ v t j := by
  classical
  let H : ℝ → ℝ := fun u => -(∫ s in (0 : ℝ)..u, Q s j j)
  have hH : ∀ s, 0 ≤ s → HasDerivAt H (-Q s j j) s := by
    intro s _
    exact (intervalIntegral.integral_hasDerivAt_right (hQc.intervalIntegrable 0 s)
      hQc.aestronglyMeasurable.stronglyMeasurableAtFilter hQc.continuousAt).neg
  have hbound : ∀ s, 0 ≤ s →
      -(∑ i, v s i * Q s i j) ≤ -(-Q s j j) * (-v s j) := by
    intro s hs
    have hsum : v s j * Q s j j ≤ ∑ i, v s i * Q s i j := by
      rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ j)]
      exact le_add_of_nonneg_left (Finset.sum_nonneg fun i hi =>
        mul_nonneg (hn s hs i) (hQ s hs i (Finset.mem_erase.mp hi).1))
    nlinarith only [hsum]
  have h := clock_decay_bound (fun s => -v s j)
    (fun s => -(∑ i, v s i * Q s i j)) H (fun s => -Q s j j)
    (fun s hs => (he s hs).neg) hH hbound ht
  simp only [H, intervalIntegral.integral_same, neg_zero, zero_sub, neg_neg] at h
  linarith

theorem inhomogeneous_row_coordinate_positive (Q : ℝ → ι → ι → ℝ)
    (v : ℝ → ι → ℝ) (j : ι)
    (hQc : Continuous (fun t => Q t j j))
    (hQ : ∀ t, 0 ≤ t → ∀ i, i ≠ j → 0 ≤ Q t i j)
    (he : ∀ t, 0 ≤ t → HasDerivAt (fun s => v s j) (∑ i, v t i * Q t i j) t)
    (hn : ∀ t, 0 ≤ t → ∀ i, 0 ≤ v t i)
    (hzero : 0 < v 0 j) {t : ℝ} (ht : 0 ≤ t) : 0 < v t j :=
  (mul_pos hzero (Real.exp_pos _)).trans_le
    (inhomogeneous_row_coordinate_lower_bound Q v j hQc hQ he hn ht)

end Rhone.Statistics.Identifiability
