/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.AtomicRank.AtomicPerturbation
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Topology.Instances.Matrix

/-! # The cubic moment-map Jacobian and its continuity -/

@[expose] public section

noncomputable section
open scoped Topology BigOperators
namespace Rhone.Statistics.AtomicRank

variable {N d : ℕ}

def atomicMomentMap (f : Fin d → Coefficients) (h : ℝ) (z : Fin d → ℝ)
    (u : Fin d → ℝ) : Fin d → ℝ := fun i => atomicMoment (N := N) (f i) h z u

def atomicJacobian (f : Fin d → Coefficients) (h : ℝ) (z u : Fin d → ℝ) :
    Matrix (Fin d) (Fin d) ℝ :=
  fun i j => fderiv ℝ (atomicMomentMap (N := N) f h z) u (Pi.single j 1) i

lemma mixtureWeight_contDiff (a : Fin N ⊕ Fin d) :
    ContDiff ℝ 1 (fun u : Fin d → ℝ => mixtureWeight u a) := by
  cases a <;> simp only [mixtureWeight, Sum.elim_inl, Sum.elim_inr] <;> fun_prop

lemma atomicMomentMap_contDiff (f : Fin d → Coefficients) (h : ℝ) (z : Fin d → ℝ) :
    ContDiff ℝ 1 (atomicMomentMap (N := N) f h z) := by
  apply contDiff_pi.mpr
  intro i
  have hw (a : Fin N ⊕ Fin d) := mixtureWeight_contDiff a
  unfold atomicMomentMap atomicMoment weightedTriple
  fun_prop

lemma single_path_hasDerivAt (j : Fin d) :
    HasDerivAt (fun t : ℝ => (Pi.single j t : Fin d → ℝ)) (Pi.single j 1) 0 := by
  apply hasDerivAt_pi.mpr
  intro i
  by_cases hi : i = j
  · subst i
    simp only [Pi.single_eq_same]
    convert! hasDerivAt_id (0 : ℝ)
  · simp only [Pi.single_eq_of_ne hi]
    exact hasDerivAt_const (0 : ℝ) 0

lemma atomicJacobian_zero (f : Fin d → Coefficients) (h : ℝ) (z : Fin d → ℝ)
    (i j : Fin d) :
    atomicJacobian (N := N) f h z 0 i j =
      3 * (uniformKernel N h (f i) (z j) - baselineMean N h (f i)) := by
  have hd := (atomicMomentMap_contDiff (N := N) f h z).differentiable (by norm_num)
  have hfd : HasFDerivAt (atomicMomentMap (N := N) f h z)
      (fderiv ℝ (atomicMomentMap (N := N) f h z) 0) (Pi.single j 0) := by
    rw [Pi.single_zero]
    exact (hd (0 : Fin d → ℝ)).hasFDerivAt
  have hpath := hfd.comp_hasDerivAt
    (f := fun t : ℝ => (Pi.single j t : Fin d → ℝ)) 0 (single_path_hasDerivAt j)
  have ht : HasDerivAt (fun t : ℝ => atomicMomentMap (N := N) f h z (Pi.single j t))
      (fun i => 3 * (uniformKernel N h (f i) (z j) - baselineMean N h (f i))) 0 := by
    apply hasDerivAt_pi.mpr
    intro k
    exact atomicMoment_path_hasDerivAt (f k) h z j
  exact congrFun (hpath.unique ht) i

lemma atomicJacobian_continuous (f : Fin d → Coefficients) (h : ℝ) (z : Fin d → ℝ) :
    Continuous (atomicJacobian (N := N) f h z) := by
  have hc := (atomicMomentMap_contDiff (N := N) f h z).continuous_fderiv (by norm_num)
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (continuous_apply i).comp (hc.clm_apply continuous_const)

lemma atomicJacobian_det_continuous (f : Fin d → Coefficients) (h : ℝ) (z : Fin d → ℝ) :
    Continuous (fun u => Matrix.det (atomicJacobian (N := N) f h z u)) :=
  (atomicJacobian_continuous f h z).matrix_det

theorem exists_nonsingular_atomic_baseline {n d : ℕ} (f : Fin d → Coefficients)
    (hf : ∀ i, DegreeBound (f i) n) (hi : IndependentModuloConstants f) :
    ∃ z : Fin d → OpenUnitInterval,
      Matrix.det (atomicJacobian (N := n + 1) f (1 / ((n : ℝ) + 2))
        (fun j => (z j).val) 0) ≠ 0 := by
  obtain ⟨z, hz⟩ := exists_full_rank_locations f hf hi
    (fun i => baselineMean (n + 1) (1 / ((n : ℝ) + 2)) (f i))
  refine ⟨z, ?_⟩
  let A : Matrix (Fin d) (Fin d) ℝ := fun i j => centeredKernel n (f i)
    (baselineMean (n + 1) (1 / ((n : ℝ) + 2)) (f i)) (z j)
  have hA : A.det ≠ 0 := hz
  have he : atomicJacobian (N := n + 1) f (1 / ((n : ℝ) + 2)) (fun j => (z j).val) 0 =
      (3 : ℝ) • A := by
    ext i j
    rw [atomicJacobian_zero]
    rfl
  rw [he, Matrix.det_smul]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hA

end Rhone.Statistics.AtomicRank
