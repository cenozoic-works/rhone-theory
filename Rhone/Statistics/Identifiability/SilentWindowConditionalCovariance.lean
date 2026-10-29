/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.SilentWindowCovarianceLower

/-! # Conditional independent daughter positions produce a PSD covariance excess -/

@[expose] public section

noncomputable section
open Matrix
open scoped BigOperators Matrix
namespace Rhone.Statistics.Identifiability.SilentWindow
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def mixtureMean (μ : ι → ℝ) (P : ι → κ → ℝ) (j : κ) : ℝ := ∑ i, μ i * P i j

def mixtureSecond (μ : ι → ℝ) (P : ι → κ → ℝ) : Matrix κ κ ℝ :=
  ∑ i, μ i • vecMulVec (P i) (P i)

omit [Fintype κ] in
lemma mixture_covariance_identity (μ : ι → ℝ) (P : ι → κ → ℝ) (hμ : ∑ i, μ i = 1) :
    mixtureSecond μ P - vecMulVec (mixtureMean μ P) (mixtureMean μ P) =
      ∑ i, μ i • vecMulVec (P i - mixtureMean μ P) (P i - mixtureMean μ P) := by
  ext j k
  simp only [mixtureSecond, Matrix.sub_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, vecMulVec_apply, Pi.sub_apply]
  have he (i : ι) : μ i * ((P i j - mixtureMean μ P j) * (P i k - mixtureMean μ P k)) =
      μ i * (P i j * P i k) - mixtureMean μ P k * (μ i * P i j) -
        mixtureMean μ P j * (μ i * P i k) + μ i * (mixtureMean μ P j * mixtureMean μ P k) := by
    ring
  simp_rw [he]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_mul, hμ]
  change _ = (∑ i, μ i * (P i j * P i k)) - mixtureMean μ P k * mixtureMean μ P j -
    mixtureMean μ P j * mixtureMean μ P k + 1 * (mixtureMean μ P j * mixtureMean μ P k)
  ring

omit [Fintype ι] [Fintype κ] in
lemma psd_finset_sum (s : Finset ι) (A : ι → Matrix κ κ ℝ)
    (hA : ∀ i ∈ s, (A i).PosSemidef) : (∑ i ∈ s, A i).PosSemidef :=
  Matrix.posSemidef_sum s hA

omit [Fintype κ] in
theorem mixture_covariance_psd [Finite κ] (μ : ι → ℝ) (P : ι → κ → ℝ)
    (hμn : ∀ i, 0 ≤ μ i) (hμ : ∑ i, μ i = 1) :
    (mixtureSecond μ P - vecMulVec (mixtureMean μ P) (mixtureMean μ P)).PosSemidef := by
  rw [mixture_covariance_identity μ P hμ]
  apply psd_finset_sum
  intro i _
  have ho : (vecMulVec (P i - mixtureMean μ P) (P i - mixtureMean μ P)).PosSemidef := by
    simpa only [star_trivial] using posSemidef_vecMulVec_self_star (P i - mixtureMean μ P)
  exact ho.smul (hμn i)

end Rhone.Statistics.Identifiability.SilentWindow
