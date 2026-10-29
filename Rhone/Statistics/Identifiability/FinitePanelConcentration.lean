/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.RectangleFrequencyBound
public import Mathlib.Probability.Independence.Basic

/-! # Finite-product sampling and range-two Hoeffding bounds for observable scores -/

@[expose] public section

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace Rhone.Statistics.Identifiability
namespace FinitePanelSampling

variable {Ω : Type*} [MeasurableSpace Ω]

def iidLaw (ν : Measure Ω) (S : ℕ) : Measure (Fin S → Ω) :=
  Measure.pi (fun _ => ν)

instance iidLaw_probability (ν : Measure Ω) [IsProbabilityMeasure ν] (S : ℕ) :
    IsProbabilityMeasure (iidLaw ν S) := by unfold iidLaw; infer_instance

def sampleMean {S : ℕ} (f : Ω → ℝ) (x : Fin S → Ω) : ℝ :=
  (∑ s : Fin S, f (x s)) / S

theorem sampleMean_measurable {S : ℕ} {f : Ω → ℝ} (hf : Measurable f) :
    Measurable (sampleMean (S := S) f) := by
  unfold sampleMean
  exact (Finset.measurable_sum _ fun s _ => hf.comp (measurable_pi_apply s)).div_const _

theorem iid_sampleMean_abs_ge (ν : Measure Ω) [IsProbabilityMeasure ν]
    (f : Ω → ℝ) (hf : Measurable f) (hb : ∀ x, |f x| ≤ 1)
    {S : ℕ} (hS : 0 < S) {ε : ℝ} (hε : 0 ≤ ε) :
    (iidLaw ν S).real {x | ε ≤ |sampleMean f x - ∫ y, f y ∂ν|} ≤
      2 * Real.exp (-(S : ℝ) * ε ^ 2 / 2) := by
  let Q := iidLaw ν S
  have hmean (s : Fin S) : (∫ x, f (x s) ∂Q) = ∫ y, f y ∂ν := by
    change (∫ x, f (x s) ∂Measure.pi (fun _ : Fin S => ν)) = _
    rw [← integral_map (measurable_pi_apply s).aemeasurable hf.aestronglyMeasurable,
      (measurePreserving_eval (fun _ : Fin S => ν) s).map_eq]
  have hi : iIndepFun (fun s : Fin S => fun x : Fin S → Ω =>
      f (x s) - ∫ y, f y ∂ν) Q := by
    exact iIndepFun_pi (fun _ => (hf.sub_const _).aemeasurable)
  have hsg (s : Fin S) : HasSubgaussianMGF
      (fun x : Fin S → Ω => f (x s) - ∫ y, f y ∂ν) 1 Q := by
    have h := hasSubgaussianMGF_of_mem_Icc
      ((hf.comp (measurable_pi_apply s)).aemeasurable (μ := Q))
      (ae_of_all Q (fun x => (abs_le.mp (hb (x s)))))
    simp only [Function.comp_def] at h
    rw [hmean s] at h
    convert h using 1
    norm_num
  have hsum : HasSubgaussianMGF
      (fun x : Fin S → Ω => ∑ s : Fin S, (f (x s) - ∫ y, f y ∂ν)) (S : ℝ≥0) Q := by
    simpa using HasSubgaussianMGF.sum_of_iIndepFun (s := Finset.univ) hi (fun s _ => hsg s)
  have h := measure_abs_ge_of_subGaussian hsum (mul_nonneg (Nat.cast_nonneg S) hε)
  have hSr : (0 : ℝ) < S := by exact_mod_cast hS
  have hset : {x : Fin S → Ω | ε ≤ |sampleMean f x - ∫ y, f y ∂ν|} =
      {x | (S : ℝ)*ε ≤ |∑ s : Fin S, (f (x s) - ∫ y, f y ∂ν)|} := by
    ext x
    simp only [Set.mem_ofPred_eq, sampleMean, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have heq : (∑ s : Fin S, f (x s)) / (S : ℝ) - ∫ y, f y ∂ν =
        ((∑ s : Fin S, f (x s)) - (S : ℝ) * ∫ y, f y ∂ν) / (S : ℝ) := by
      field_simp
    rw [heq, abs_div, abs_of_pos hSr, le_div_iff₀ hSr, mul_comm ε]
  rw [hset]
  convert h using 1
  congr 2
  push_cast
  field_simp [hSr.ne']

theorem iid_finite_scores_abs_ge {ι : Type*} [Fintype ι]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (f : ι → Ω → ℝ) (hf : ∀ i, Measurable (f i)) (hb : ∀ i x, |f i x| ≤ 1)
    {S : ℕ} (hS : 0 < S) {ε : ℝ} (hε : 0 ≤ ε) :
    (iidLaw ν S).real {x | ∃ i, ε ≤ |sampleMean (f i) x - ∫ y, f i y ∂ν|} ≤
      2 * Fintype.card ι * Real.exp (-(S : ℝ) * ε ^ 2 / 2) := by
  have heq : {x : Fin S → Ω | ∃ i, ε ≤ |sampleMean (f i) x - ∫ y, f i y ∂ν|} =
      ⋃ i, {x | ε ≤ |sampleMean (f i) x - ∫ y, f i y ∂ν|} := by ext x; simp
  rw [heq]
  calc
    _ ≤ ∑ i : ι, (iidLaw ν S).real
        {x | ε ≤ |sampleMean (f i) x - ∫ y, f i y ∂ν|} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _i : ι, 2 * Real.exp (-(S : ℝ) * ε ^ 2 / 2) := by
      exact Finset.sum_le_sum fun i _ => iid_sampleMean_abs_ge ν (f i) (hf i) (hb i) hS hε
    _ = _ := by simp; ring

def hoeffdingSampleBudget (M : ℕ) (ε γ : ℝ) : ℝ :=
  2 * Real.log (2 * M / γ) / ε ^ 2

def hoeffdingSampleSize (M : ℕ) (ε γ : ℝ) : ℕ :=
  1 + ⌈hoeffdingSampleBudget M ε γ⌉₊

theorem hoeffdingSampleSize_pos (M : ℕ) (ε γ : ℝ) :
    0 < hoeffdingSampleSize M ε γ := by unfold hoeffdingSampleSize; omega

theorem hoeffdingSampleBudget_le_size (M : ℕ) (ε γ : ℝ) :
    hoeffdingSampleBudget M ε γ ≤ (hoeffdingSampleSize M ε γ : ℝ) := by
  have h := Nat.le_ceil (hoeffdingSampleBudget M ε γ)
  unfold hoeffdingSampleSize
  push_cast
  linarith

theorem hoeffding_failure_le {M S : ℕ} (hM : 0 < M) {ε γ : ℝ}
    (hε : 0 < ε) (hγ : 0 < γ)
    (hS : hoeffdingSampleBudget M ε γ ≤ (S : ℝ)) :
    2 * M * Real.exp (-(S : ℝ) * ε ^ 2 / 2) ≤ γ := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hx : 0 < 2 * (M : ℝ) / γ := div_pos (by positivity) hγ
  have hε2 : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hs : 2 * Real.log (2 * M / γ) ≤ (S : ℝ) * ε ^ 2 :=
    (div_le_iff₀ hε2).mp hS
  have hexp : Real.exp (-(S : ℝ) * ε ^ 2 / 2) ≤
      Real.exp (-Real.log (2 * M / γ)) := by
    apply Real.exp_le_exp.mpr
    linarith
  calc
    _ ≤ 2 * M * Real.exp (-Real.log (2 * M / γ)) :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = γ := by
      rw [Real.exp_neg, Real.exp_log hx]
      field_simp

theorem hoeffding_failure_at_size_le {M : ℕ} (hM : 0 < M) {ε γ : ℝ}
    (hε : 0 < ε) (hγ : 0 < γ) :
    2 * M * Real.exp (-(hoeffdingSampleSize M ε γ : ℝ) * ε ^ 2 / 2) ≤ γ :=
  hoeffding_failure_le hM hε hγ (hoeffdingSampleBudget_le_size M ε γ)

end FinitePanelSampling
end Rhone.Statistics.Identifiability
