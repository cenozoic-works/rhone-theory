/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.FinitePhaseRootMarginal
public import Rhone.Statistics.Identifiability.FiniteExitMassBound

/-! # Proper observed mass recovers the first marginal without conditional properness -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory Matrix
open scoped Topology Matrix Matrix.Norms.Operator ENNReal
namespace Rhone.Statistics.Identifiability.FinitePhase
open FiniteExponentialJets
variable {n m : ℕ}

def entryFlux (A : Matrix (Fin n) (Fin n) ℝ) (F : Matrix (Fin n) (Fin m) ℝ)
    (α : Fin n → ℝ) (s : ℝ) : Fin m → ℝ := α ᵥ* NormedSpace.exp (s • A) ᵥ* F

lemma entryFlux_nonnegative (A : Matrix (Fin n) (Fin n) ℝ)
    (F : Matrix (Fin n) (Fin m) ℝ) (α : Fin n → ℝ)
    (hA : IsMetzler A) (hF : ∀ i j, 0 ≤ F i j) (hα : ∀ i, 0 ≤ α i)
    {s : ℝ} (hs : 0 ≤ s) (j : Fin m) : 0 ≤ entryFlux A F α s j := by
  unfold entryFlux Matrix.vecMul dotProduct
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg _ (hF i j)
  exact Finset.sum_nonneg fun l _ => mul_nonneg (hα l) (exp_generator_nonneg A hA hs l i)

lemma density_entryFlux (A : Matrix (Fin n) (Fin n) ℝ)
    (F : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin m) ℝ)
    (α : Fin n → ℝ) (s t : ℝ) :
    density A F B α (s,t) = ∑ j, entryFlux A F α s j *
      flowOutput B j (exitRate B) 0 (t - s) := by
  simp only [density, orderedKernelDensity, kernelValue,
    entryFlux, flowOutput, pow_zero, Matrix.one_mul]
  rw [dotProduct_mulVec, dotProduct_mulVec]
  rfl

lemma entryFlux_sum (A : Matrix (Fin n) (Fin n) ℝ)
    (F : Matrix (Fin n) (Fin m) ℝ) (α : Fin n → ℝ)
    (hF : F *ᵥ (fun _ => 1) = exitRate A) (s : ℝ) :
    (∑ j, entryFlux A F α s j) = WeightedExit.density A α s := by
  have he : dotProduct (entryFlux A F α s) (fun _ => 1) =
      dotProduct α (NormedSpace.exp (s • A) *ᵥ exitRate A) := by
    unfold entryFlux
    rw [← dotProduct_mulVec, ← dotProduct_mulVec, hF]
  simpa only [dotProduct, mul_one, WeightedExit.density, flowOutput, pow_zero,
    Matrix.one_mul] using he

lemma density_row_lintegral_le (A : Matrix (Fin n) (Fin n) ℝ)
    (F : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin m) ℝ) (α : Fin n → ℝ)
    (hA : IsMetzler A) (hB : IsMetzler B) (hBr : ∀ i, (∑ j, B i j) ≤ 0)
    (hF : ∀ i j, 0 ≤ F i j) (hα : ∀ i, 0 ≤ α i)
    (hflux : F *ᵥ (fun _ => 1) = exitRate A) {s : ℝ} (hs : 0 < s) :
    (∫⁻ t in Ioi s, ENNReal.ofReal (density A F B α (s,t))) ≤
      ENNReal.ofReal (WeightedExit.density A α s) := by
  have hn := entryFlux_nonnegative A F α hA hF hα hs.le
  have he : (∫⁻ t in Ioi s, ENNReal.ofReal (density A F B α (s,t))) =
      ∫⁻ t in Ioi s, ∑ j, ENNReal.ofReal (entryFlux A F α s j) *
        ENNReal.ofReal (flowOutput B j (exitRate B) 0 (t - s)) := by
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [density_entryFlux, ENNReal.ofReal_sum_of_nonneg]
    · apply Finset.sum_congr rfl
      intro j _
      exact ENNReal.ofReal_mul (hn j)
    · intro j _
      exact mul_nonneg (hn j) (firstExit_density_nonneg B hB hBr j (sub_nonneg.mpr ht.le))
  have hm (j : Fin m) : Measurable (fun t : ℝ =>
      ENNReal.ofReal (entryFlux A F α s j) *
        ENNReal.ofReal (flowOutput B j (exitRate B) 0 (t - s))) :=
    measurable_const.mul (((flowOutput_continuous B j (exitRate B) 0).comp
      (continuous_id.sub continuous_const)).measurable.ennreal_ofReal)
  rw [he, lintegral_finsetSum _ (fun j _ => hm j)]
  simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc
    _ ≤ ∑ j, ENNReal.ofReal (entryFlux A F α s j) * 1 :=
      Finset.sum_le_sum fun j _ =>
        mul_le_mul_right (finite_exit_shifted_mass_bound B hB hBr j s) _
    _ = _ := by
      simp only [mul_one]
      rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hn j), entryFlux_sum A F α hflux]

lemma law_map_first_le (A : Matrix (Fin n) (Fin n) ℝ)
    (F : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin m) ℝ) (α : Fin n → ℝ)
    (hA : IsMetzler A) (hB : IsMetzler B) (hBr : ∀ i, (∑ j, B i j) ≤ 0)
    (hF : ∀ i j, 0 ≤ F i j) (hα : ∀ i, 0 ≤ α i)
    (hflux : F *ᵥ (fun _ => 1) = exitRate A) :
    (law A F B α).map Prod.fst ≤ WeightedExit.law A α := by
  have hc : Continuous (density A F B α) := orderedKernelDensity_continuous A B α F (exitRate B)
  rw [law, triangular_map_fst_ae _ hc.measurable.aemeasurable]
  apply withDensity_mono
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  exact density_row_lintegral_le A F B α hA hB hBr hF hα hflux hs

lemma law_map_first_of_probability (A : Matrix (Fin n) (Fin n) ℝ)
    (F : Matrix (Fin n) (Fin m) ℝ) (B : Matrix (Fin m) (Fin m) ℝ) (α : Fin n → ℝ)
    [IsProbabilityMeasure (law A F B α)]
    (hA : IsMetzler A) (hAr : ∀ i, (∑ j, A i j) ≤ 0)
    (hB : IsMetzler B) (hBr : ∀ i, (∑ j, B i j) ≤ 0)
    (hF : ∀ i j, 0 ≤ F i j) (hα : ∀ i, 0 ≤ α i) (hαsum : ∑ i, α i = 1)
    (hflux : F *ᵥ (fun _ => 1) = exitRate A) :
    (law A F B α).map Prod.fst = WeightedExit.law A α := by
  let : IsProbabilityMeasure ((law A F B α).map Prod.fst) :=
    inferInstance
  have hle := law_map_first_le A F B α hA hB hBr hF hα hflux
  apply Measure.eq_of_le_of_measure_univ_eq hle
  apply le_antisymm (hle univ)
  simpa only [measure_univ] using WeightedExit.law_mass_le_one A α hA hAr hα hαsum

end Rhone.Statistics.Identifiability.FinitePhase
