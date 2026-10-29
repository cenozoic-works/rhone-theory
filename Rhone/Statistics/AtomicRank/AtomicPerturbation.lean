/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.AtomicRank.CubicWeights

/-! # Normalized finite-atomic perturbations and their cubic-law Jacobian -/

@[expose] public section

noncomputable section
open scoped BigOperators
namespace Rhone.Statistics.AtomicRank

variable {N d : ℕ}

def mixtureWeight (u : Fin d → ℝ) : Fin N ⊕ Fin d → ℝ :=
  Sum.elim (fun _ => (1 - ∑ j, u j) / (N : ℝ)) u

def mixtureLocation (h : ℝ) (z : Fin d → ℝ) : Fin N ⊕ Fin d → ℝ :=
  Sum.elim (fun i => atom h i.val) z

def mixtureKernel (f : Coefficients) (h : ℝ) (z : Fin d → ℝ)
    (p : (Fin N ⊕ Fin d) × (Fin N ⊕ Fin d) × (Fin N ⊕ Fin d)) : ℝ :=
  sortedKernel f (mixtureLocation h z p.1) (mixtureLocation h z p.2.1)
    (mixtureLocation h z p.2.2)

def atomicMoment (f : Coefficients) (h : ℝ) (z u : Fin d → ℝ) : ℝ :=
  weightedTriple (mixtureKernel (N := N) f h z) (mixtureWeight u)

def baselineMean (N : ℕ) (h : ℝ) (f : Coefficients) : ℝ :=
  (∑ i ∈ Finset.range N, uniformKernel N h f (atom h i)) / (N : ℝ)

def weightDirection (j : Fin d) : Fin N ⊕ Fin d → ℝ :=
  Sum.elim (fun _ => -(1 / (N : ℝ))) (Pi.single j 1)

lemma mixtureKernel_swap12 (f : Coefficients) (h : ℝ) (z : Fin d → ℝ)
    (p : (Fin N ⊕ Fin d) × (Fin N ⊕ Fin d) × (Fin N ⊕ Fin d)) :
    mixtureKernel f h z (swapFirstTwo p) = mixtureKernel f h z p := by
  exact sortedKernel_swap_first f _ _ _

lemma mixtureKernel_swap13 (f : Coefficients) (h : ℝ) (z : Fin d → ℝ)
    (p : (Fin N ⊕ Fin d) × (Fin N ⊕ Fin d) × (Fin N ⊕ Fin d)) :
    mixtureKernel f h z (swapOuter p) = mixtureKernel f h z p := by
  change sortedKernel f (mixtureLocation h z p.2.2) (mixtureLocation h z p.2.1)
    (mixtureLocation h z p.1) = sortedKernel f (mixtureLocation h z p.1)
      (mixtureLocation h z p.2.1) (mixtureLocation h z p.2.2)
  rw [sortedKernel_swap_first f (mixtureLocation h z p.2.2),
    sortedKernel_swap_last f (mixtureLocation h z p.2.1),
    sortedKernel_swap_first f (mixtureLocation h z p.2.1)]

lemma weightedConditional_baseline (f : Coefficients) (h : ℝ) (z : Fin d → ℝ)
    (a : Fin N ⊕ Fin d) :
    weightedConditional (mixtureKernel f h z) (mixtureWeight (0 : Fin d → ℝ)) a =
      uniformKernel N h f (mixtureLocation h z a) := by
  simp only [weightedConditional, Fintype.sum_sum_type, mixtureWeight, Sum.elim_inl,
    Sum.elim_inr, Pi.zero_apply, Finset.sum_const_zero, sub_zero, zero_mul, mul_zero,
    Finset.sum_const_zero, add_zero]
  rw [uniformKernel, ← Fin.sum_univ_eq_sum_range]
  simp_rw [← Fin.sum_univ_eq_sum_range, Finset.sum_div, pairKernel_eq_sorted]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  simp only [mixtureKernel, mixtureLocation, Sum.elim_inl]
  simp [div_eq_mul_inv]
  ring

lemma atomicMoment_zero (f : Coefficients) (h : ℝ) (z : Fin d → ℝ) :
    atomicMoment (N := N) f h z 0 = baselineMean N h f := by
  rw [atomicMoment, weightedTriple_eq_conditional]
  simp_rw [weightedConditional_baseline]
  simp only [Fintype.sum_sum_type, mixtureWeight, mixtureLocation, Sum.elim_inl,
    Sum.elim_inr, Pi.zero_apply, Finset.sum_const_zero, sub_zero, zero_mul,
    Finset.sum_const_zero, add_zero]
  rw [baselineMean, ← Fin.sum_univ_eq_sum_range, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma mixtureWeight_path_hasDerivAt (j : Fin d) (a : Fin N ⊕ Fin d) :
    HasDerivAt (fun t => mixtureWeight (Pi.single j t) a) (weightDirection j a) 0 := by
  cases a with
  | inl i =>
      simp only [mixtureWeight, weightDirection, Sum.elim_inl]
      convert! ((hasDerivAt_id (0 : ℝ)).const_sub 1).div_const (N : ℝ) using 1
      all_goals norm_num [div_eq_mul_inv]
  | inr i =>
      by_cases hi : i = j
      · subst i
        simp only [mixtureWeight, weightDirection, Sum.elim_inr, Pi.single_eq_same]
        convert! hasDerivAt_id (0 : ℝ)
      · simp only [mixtureWeight, weightDirection, Sum.elim_inr, Pi.single_eq_of_ne hi]
        exact hasDerivAt_const (0 : ℝ) 0

lemma direction_conditional (f : Coefficients) (h : ℝ) (z : Fin d → ℝ) (j : Fin d) :
    (∑ a : Fin N ⊕ Fin d, weightDirection j a *
      weightedConditional (mixtureKernel f h z) (mixtureWeight (0 : Fin d → ℝ)) a) =
        uniformKernel N h f (z j) - baselineMean N h f := by
  simp_rw [weightedConditional_baseline]
  simp only [Fintype.sum_sum_type, weightDirection, mixtureLocation, Sum.elim_inl, Sum.elim_inr]
  rw [← Finset.mul_sum]
  simp [Pi.single_apply, ite_mul, Finset.sum_ite_eq', baselineMean,
    ← Fin.sum_univ_eq_sum_range]
  ring

theorem atomicMoment_path_hasDerivAt (f : Coefficients) (h : ℝ) (z : Fin d → ℝ) (j : Fin d) :
    HasDerivAt (fun t => atomicMoment (N := N) f h z (Pi.single j t))
      (3 * (uniformKernel N h f (z j) - baselineMean N h f)) 0 := by
  have he := weightedTriple_symmetric_hasDerivAt (mixtureKernel (N := N) f h z)
    (mixtureWeight_path_hasDerivAt j) (mixtureKernel_swap12 f h z) (mixtureKernel_swap13 f h z)
  simp only [Pi.single_zero] at he
  rw [direction_conditional] at he
  exact he

end Rhone.Statistics.AtomicRank
