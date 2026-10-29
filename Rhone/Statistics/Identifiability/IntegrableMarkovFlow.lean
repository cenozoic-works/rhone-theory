/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.IntegrableMarkovBasic
public import Rhone.Statistics.Identifiability.ACComparisonBounds

/-! # Integrable Markov row flows: nonnegativity, comparison, uniqueness, existence -/

@[expose] public section

open Set Filter MeasureTheory
open scoped BigOperators Topology
namespace Rhone.Statistics.Identifiability
variable {ι : Type*} [Fintype ι]

theorem integrable_row_solution_nonneg (Q : ℝ → ι → ι → ℝ) (v : ℝ → ι → ℝ)
    (hQi : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume)
    (hQ : ∀ᵐ t, 0 ≤ t → ∀ i j, i ≠ j → 0 ≤ Q t i j)
    (hv : ∀ t, 0 ≤ t → ∀ i, AbsolutelyContinuousOnInterval (fun s => v s i) 0 t)
    (he : ∀ᵐ t, 0 ≤ t → ∀ j,
      HasDerivAt (fun s => v s j) (∑ i, v t i * Q t i j) t)
    (hzero : ∀ i, 0 ≤ v 0 i) :
    ∀ t, 0 ≤ t → ∀ i, 0 ≤ v t i := by
  classical
  let E : ℝ → ℝ := fun t => ∑ i, (min (v t i) 0)^2
  let Edot : ℝ → ℝ := fun t => ∑ j, 2 * min (v t j) 0 * (∑ i, v t i * Q t i j)
  let C : ℝ → ℝ := fun t => 2 * ∑ j, ∑ i, |Q t i j|
  let H : ℝ → ℝ := fun t => -(∫ s in (0 : ℝ)..t, C s)
  have hCi : LocallyIntegrable C volume := metzler_energy_coefficient_locallyIntegrable hQi
  have hEzero : E 0 = 0 := by simp [E, hzero]
  intro t ht i
  have hEac : AbsolutelyContinuousOnInterval E 0 t :=
    ac_finset_sum Finset.univ (fun j _ => ac_sq_min_zero (hv t ht j))
  have hHac : AbsolutelyContinuousOnInterval H 0 t := by
    exact ((LocallyIntegrablePeanoBaker.intervalIntegrable_of_locallyIntegrable hCi 0
      t).absolutelyContinuousOnInterval_intervalIntegral (by simp)).neg
  have hEd : ∀ᵐ s, s ∈ uIcc 0 t → HasDerivAt E (Edot s) s := by
    filter_upwards [he] with s hs hmem
    have hs0 : 0 ≤ s := (by simpa only [uIcc_of_le ht, mem_Icc] using hmem : 0 ≤ s ∧ s ≤ t).1
    apply HasDerivAt.fun_sum
    intro j _
    simpa only [Function.comp_def] using
      (hasDerivAt_sq_min_zero (v s j)).comp s (hs hs0 j)
  have hHd : ∀ᵐ s, s ∈ uIcc 0 t → HasDerivAt H (-C s) s := by
    filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hCi] with s hs _
    exact (hs 0).neg
  have hb : ∀ᵐ s, s ∈ uIcc 0 t → Edot s ≤ -(-C s) * E s := by
    filter_upwards [hQ] with s hs hmem
    have hs0 : 0 ≤ s := (by simpa only [uIcc_of_le ht, mem_Icc] using hmem : 0 ≤ s ∧ s ≤ t).1
    simpa only [Edot, C, E, neg_neg] using metzler_negative_energy_bound (Q s) (v s) (hs hs0)
  have hle := ac_comparison_upper E Edot H (fun s => -C s) 0 t ht hEac hHac hEd hHd hb
  rw [hEzero, zero_mul] at hle
  have hi : (min (v t i) 0)^2 ≤ E t :=
    Finset.single_le_sum (fun j _ => sq_nonneg (min (v t j) 0)) (Finset.mem_univ i)
  have hz : min (v t i) 0 = 0 := by nlinarith [hi.trans hle]
  simpa only [hz] using min_le_left (v t i) 0

theorem integrable_row_solution_comparison (Q : ℝ → ι → ι → ℝ) (v w : ℝ → ι → ℝ)
    (hQi : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume)
    (hQ : ∀ᵐ t, 0 ≤ t → ∀ i j, i ≠ j → 0 ≤ Q t i j)
    (hv : ∀ t, 0 ≤ t → ∀ i, AbsolutelyContinuousOnInterval (fun s => v s i) 0 t)
    (hw : ∀ t, 0 ≤ t → ∀ i, AbsolutelyContinuousOnInterval (fun s => w s i) 0 t)
    (hve : ∀ᵐ t, 0 ≤ t → ∀ j,
      HasDerivAt (fun s => v s j) (∑ i, v t i * Q t i j) t)
    (hwe : ∀ᵐ t, 0 ≤ t → ∀ j,
      HasDerivAt (fun s => w s j) (∑ i, w t i * Q t i j) t)
    (hzero : ∀ i, v 0 i ≤ w 0 i) :
    ∀ t, 0 ≤ t → ∀ i, v t i ≤ w t i := by
  have hd : ∀ᵐ t, 0 ≤ t → ∀ j,
      HasDerivAt (fun s => w s j - v s j) (∑ i, (w t i - v t i) * Q t i j) t := by
    filter_upwards [hve, hwe] with t hvt hwt ht j
    convert! (hwt ht j).sub (hvt ht j) using 1
    simp only [sub_mul, Finset.sum_sub_distrib]
  have hn := integrable_row_solution_nonneg Q (fun t i => w t i - v t i) hQi hQ
    (fun t ht i => (hw t ht i).fun_sub (hv t ht i)) hd
    (fun i => sub_nonneg.mpr (hzero i))
  exact fun t ht i => sub_nonneg.mp (hn t ht i)

theorem integrable_row_solution_unique (Q : ℝ → ι → ι → ℝ) (v w : ℝ → ι → ℝ)
    (hQi : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume)
    (hQ : ∀ᵐ t, 0 ≤ t → ∀ i j, i ≠ j → 0 ≤ Q t i j)
    (hv : ∀ t, 0 ≤ t → ∀ i, AbsolutelyContinuousOnInterval (fun s => v s i) 0 t)
    (hw : ∀ t, 0 ≤ t → ∀ i, AbsolutelyContinuousOnInterval (fun s => w s i) 0 t)
    (hve : ∀ᵐ t, 0 ≤ t → ∀ j,
      HasDerivAt (fun s => v s j) (∑ i, v t i * Q t i j) t)
    (hwe : ∀ᵐ t, 0 ≤ t → ∀ j,
      HasDerivAt (fun s => w s j) (∑ i, w t i * Q t i j) t)
    (hzero : v 0 = w 0) :
    ∀ t, 0 ≤ t → v t = w t := by
  have hvw := integrable_row_solution_comparison Q v w hQi hQ hv hw hve hwe
    (fun i => le_of_eq (congrFun hzero i))
  have hwv := integrable_row_solution_comparison Q w v hQi hQ hw hv hwe hve
    (fun i => le_of_eq (congrFun hzero.symm i))
  exact fun t ht => funext (fun i => le_antisymm (hvw t ht i) (hwv t ht i))

theorem exists_integrable_row_solution (Q : ℝ → ι → ι → ℝ)
    (hQi : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume) (x : ι → ℝ) :
    ∃ v : ℝ → ι → ℝ, v 0 = x ∧ Continuous v ∧
      (∀ a b, AbsolutelyContinuousOnInterval v a b) ∧
      (∀ a b i, AbsolutelyContinuousOnInterval (fun t => v t i) a b) ∧
      (∀ t, v t = x + ∫ s in (0 : ℝ)..t, inhomogeneousRowOperator (Q s) (v s)) ∧
      (∀ᵐ t, ∀ j, HasDerivAt (fun s => v s j) (∑ i, v t i * Q t i j) t) := by
  obtain ⟨v, hv0, hvc, hvac, hvi, hve⟩ := LocallyIntegrableLinearODE.exists_global_solution
    (fun t => inhomogeneousRowOperator (Q t)) (inhomogeneousRowOperator_locallyIntegrable Q hQi) x
  refine ⟨v, hv0, hvc, hvac, fun a b i => ac_coordinate (hvac a b) i, hvi, ?_⟩
  filter_upwards [hve] with t ht j
  exact (hasDerivAt_pi.mp ht) j

end Rhone.Statistics.Identifiability
