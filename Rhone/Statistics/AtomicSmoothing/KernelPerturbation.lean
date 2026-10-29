/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.AtomicRank.PositiveAtomicRank

/-! # Continuity of the true iid weight Jacobian under finite kernel perturbations -/

@[expose] public section

noncomputable section
open Filter
open scoped Topology BigOperators
namespace Rhone.Statistics.AtomicSmoothing
open AtomicRank

variable {N d : ℕ}

abbrev AtomIndex (N d : ℕ) := Fin N ⊕ Fin d
abbrev KernelArray (N d : ℕ) := Fin d → (AtomIndex N d × AtomIndex N d × AtomIndex N d) → ℝ

def momentMap (K : KernelArray N d) (u : Fin d → ℝ) : Fin d → ℝ :=
  fun i => weightedTriple (K i) (mixtureWeight u)

def jacobian (K : KernelArray N d) (u : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => rawWeightDerivative (K i) (mixtureWeight u) (weightDirection j)

lemma mixtureWeight_affine_path (u : Fin d → ℝ) (j : Fin d) (t : ℝ) (a : AtomIndex N d) :
    mixtureWeight (u + Pi.single j t) a = mixtureWeight u a + t * weightDirection j a := by
  have hs : (∑ i : Fin d, (Pi.single j t : Fin d → ℝ) i) = t := by
    simp [Pi.single_apply]
  cases a with
  | inl i =>
      simp only [mixtureWeight, weightDirection, Sum.elim_inl, Pi.add_apply,
        Finset.sum_add_distrib, hs]
      ring
  | inr i =>
      by_cases hi : i = j <;> simp [mixtureWeight, weightDirection, Pi.single_apply, hi]

lemma mixtureWeight_affine_hasDerivAt (u : Fin d → ℝ) (j : Fin d) (a : AtomIndex N d) :
    HasDerivAt (fun t : ℝ => mixtureWeight (u + Pi.single j t) a) (weightDirection j a) 0 := by
  have he : (fun t : ℝ => mixtureWeight (u + Pi.single j t) a) =
      fun t => mixtureWeight u a + t * weightDirection j a :=
    funext fun t => mixtureWeight_affine_path u j t a
  rw [he]
  convert! ((hasDerivAt_id (0 : ℝ)).mul_const (weightDirection j a)).const_add
    (mixtureWeight u a) using 1
  simp only [one_mul]

lemma momentMap_contDiff (K : KernelArray N d) : ContDiff ℝ 1 (momentMap K) := by
  apply contDiff_pi.mpr
  intro i
  have hw (a : AtomIndex N d) := mixtureWeight_contDiff a
  unfold momentMap weightedTriple
  fun_prop

lemma momentMap_path_hasDerivAt (K : KernelArray N d) (u : Fin d → ℝ) (j : Fin d) :
    HasDerivAt (fun t : ℝ => momentMap K (u + Pi.single j t)) (fun i => jacobian K u i j) 0 := by
  apply hasDerivAt_pi.mpr
  intro i
  have he := weightedTriple_hasDerivAt (K i) (mixtureWeight_affine_hasDerivAt u j)
  simp only [Pi.single_zero, add_zero] at he
  convert! he using 1

lemma jacobian_eq_fderiv (K : KernelArray N d) (u : Fin d → ℝ) (i j : Fin d) :
    jacobian K u i j = fderiv ℝ (momentMap K) u (Pi.single j 1) i := by
  have hd := (momentMap_contDiff K).differentiable (by norm_num)
  have hfd : HasFDerivAt (momentMap K) (fderiv ℝ (momentMap K) u) (u + Pi.single j 0) := by
    simpa only [Pi.single_zero, add_zero] using (hd u).hasFDerivAt
  have hp := hfd.comp_hasDerivAt (f := fun t : ℝ => u + Pi.single j t) 0
    ((single_path_hasDerivAt j).const_add u)
  exact (congrFun (hp.unique (momentMap_path_hasDerivAt K u j)) i).symm

lemma atomicJacobian_eq (f : Fin d → Coefficients) (h : ℝ) (z u : Fin d → ℝ) :
    atomicJacobian (N := N) f h z u = jacobian (N := N) (fun i => mixtureKernel (f i) h z) u := by
  ext i j
  rw [jacobian_eq_fderiv]
  rfl

lemma jacobian_kernel_continuous (u : Fin d → ℝ) :
    Continuous (fun K : KernelArray N d => jacobian K u) := by
  unfold jacobian rawWeightDerivative
  fun_prop

lemma jacobian_det_kernel_continuous (u : Fin d → ℝ) :
    Continuous (fun K : KernelArray N d => Matrix.det (jacobian K u)) :=
  (jacobian_kernel_continuous u).matrix_det

theorem nonsingular_kernel_neighborhood (K : KernelArray N d) (u : Fin d → ℝ)
    (hn : Matrix.det (jacobian K u) ≠ 0) :
    ∀ᶠ K' in 𝓝 K, Matrix.det (jacobian K' u) ≠ 0 :=
  (jacobian_det_kernel_continuous u).continuousAt.tendsto.eventually_ne hn

theorem eventually_nonsingular_kernel {ι : Type*} {l : Filter ι}
    {K : ι → KernelArray N d} {K0 : KernelArray N d} (hK : Tendsto K l (𝓝 K0))
    (u : Fin d → ℝ) (hn : Matrix.det (jacobian K0 u) ≠ 0) :
    ∀ᶠ t in l, Matrix.det (jacobian (K t) u) ≠ 0 :=
  hK.eventually (nonsingular_kernel_neighborhood K0 u hn)

end Rhone.Statistics.AtomicSmoothing
