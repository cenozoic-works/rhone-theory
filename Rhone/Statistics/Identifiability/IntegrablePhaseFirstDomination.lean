/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.IntegrablePhaseRootMarginal

/-! # First-event marginal recovery without proper conditional pair tails for L1 histories -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory Matrix
open scoped Topology Matrix ENNReal
namespace Rhone.Statistics.Identifiability.IntegrablePhase.History
variable {n m : ℕ}

def entryFlux (M : History n m) (s : ℝ) : Fin m → ℝ :=
  M.α ᵥ* inhomogeneousTransition M.A 0 s ᵥ* M.F s

def postDensity (M : History n m) (s : ℝ) (j : Fin m) (t : ℝ) : ℝ :=
  IntegrableWeightedExit.density M.B (Pi.single j 1) s t

lemma postDensity_eq (M : History n m) (s t : ℝ) (j : Fin m) :
    M.postDensity s j t = (inhomogeneousTransition M.B s t *ᵥ exitRate (M.B t)) j := by
  simp only [postDensity, IntegrableWeightedExit.density, IntegrableWeightedExit.row,
    Matrix.single_one_vecMul]
  rfl

lemma entryFlux_nonnegative_at (M : History n m) {s : ℝ} (hs : 0 ≤ s)
    (hF : ∀ i j, 0 ≤ M.F s i j) (j : Fin m) : 0 ≤ M.entryFlux s j := by
  unfold entryFlux Matrix.vecMul dotProduct
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg _ (hF i j)
  exact Finset.sum_nonneg fun l _ => mul_nonneg (M.α_nonnegative l)
    (integrableTransition_nonneg M.A M.A_integrable M.A_metzler le_rfl hs l i)

lemma postDensity_nonnegative_at (M : History n m) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (hB : ∀ i, (∑ j, M.B t i j) ≤ 0) (j : Fin m) : 0 ≤ M.postDensity s j t := by
  rw [M.postDensity_eq]
  exact matrix_mulVec_nonneg _ _
    (integrableTransition_nonneg M.B M.B_integrable M.B_metzler hs hst)
    (exitRate_nonneg (M.B t) hB) j

lemma density_entryFlux (M : History n m) (s t : ℝ) :
    M.density (s,t) = ∑ j, M.entryFlux s j * M.postDensity s j t := by
  simp only [density, FiniteExponentialJets.kernelValue, entryFlux, M.postDensity_eq]
  rw [dotProduct_mulVec, dotProduct_mulVec]
  rfl

lemma entryFlux_sum (M : History n m) {s : ℝ}
    (hF : M.F s *ᵥ (fun _ => 1) = exitRate (M.A s)) :
    (∑ j, M.entryFlux s j) = IntegrableWeightedExit.density M.A M.α 0 s := by
  have he : dotProduct (M.entryFlux s) (fun _ => 1) =
      dotProduct (IntegrableWeightedExit.row M.A M.α 0 s) (exitRate (M.A s)) := by
    unfold entryFlux IntegrableWeightedExit.row
    rw [← dotProduct_mulVec, hF]
  simpa only [dotProduct, mul_one, IntegrableWeightedExit.density] using he

lemma postDensity_mass_le_one (M : History n m) {s : ℝ} (hs : 0 ≤ s) (j : Fin m) :
    (∫⁻ t in Ioi s, ENNReal.ofReal (M.postDensity s j t)) ≤ 1 := by
  have hα : ∀ i : Fin m, 0 ≤ (Pi.single j 1 : Fin m → ℝ) i := by
    intro i
    by_cases hi : i = j <;> simp [hi]
  have he := IntegrableWeightedExit.law_mass_le_initial M.B (Pi.single j 1)
    M.B_integrable M.B_metzler M.B_rows hα hs
  simpa [IntegrableWeightedExit.law, postDensity,
    withDensity_apply _ MeasurableSet.univ] using he

lemma density_row_lintegral_le (M : History n m) {s : ℝ} (hs : 0 < s)
    (hF : ∀ i j, 0 ≤ M.F s i j) (hflux : M.F s *ᵥ (fun _ => 1) = exitRate (M.A s)) :
    (∫⁻ t in Ioi s, ENNReal.ofReal (M.density (s,t))) ≤
      ENNReal.ofReal (IntegrableWeightedExit.density M.A M.α 0 s) := by
  have hn := M.entryFlux_nonnegative_at hs.le hF
  have he : (∫⁻ t in Ioi s, ENNReal.ofReal (M.density (s,t))) =
      ∫⁻ t in Ioi s, ∑ j, ENNReal.ofReal (M.entryFlux s j) *
        ENNReal.ofReal (M.postDensity s j t) := by
    apply lintegral_congr_ae
    filter_upwards [M.B_rows.filter_mono (ae_mono Measure.restrict_le_self),
      ae_restrict_mem measurableSet_Ioi] with t ht hst
    have hp := M.postDensity_nonnegative_at hs.le hst.le (ht (hs.le.trans hst.le))
    rw [M.density_entryFlux, ENNReal.ofReal_sum_of_nonneg]
    · apply Finset.sum_congr rfl
      intro j _
      exact ENNReal.ofReal_mul (hn j)
    · intro j _
      exact mul_nonneg (hn j) (hp j)
  have hm (j : Fin m) : AEMeasurable (fun t => ENNReal.ofReal (M.entryFlux s j) *
      ENNReal.ofReal (M.postDensity s j t)) (volume.restrict (Ioi s)) :=
    aemeasurable_const.mul ((IntegrableWeightedExit.density_locallyIntegrable
      M.B (Pi.single j 1) M.B_integrable s).aestronglyMeasurable.aemeasurable
        |>.ennreal_ofReal.restrict)
  rw [he, lintegral_finsetSum' _ (fun j _ => hm j)]
  simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  calc
    _ ≤ ∑ j, ENNReal.ofReal (M.entryFlux s j) * 1 :=
      Finset.sum_le_sum fun j _ => mul_le_mul_right (M.postDensity_mass_le_one hs.le j) _
    _ = _ := by
      simp only [mul_one]
      rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hn j), M.entryFlux_sum hflux]

lemma first_marginal_le (M : History n m) :
    M.law.map Prod.fst ≤ IntegrableWeightedExit.law M.A M.α 0 := by
  rw [law, triangular_map_fst_ae _ M.density_aemeasurable.restrict]
  apply withDensity_mono
  filter_upwards [M.F_nonnegative.filter_mono (ae_mono Measure.restrict_le_self),
    M.flux.filter_mono (ae_mono Measure.restrict_le_self),
    ae_restrict_mem measurableSet_Ioi] with s hF hf hs
  exact M.density_row_lintegral_le hs (hF hs.le) (hf hs.le)

lemma first_marginal (M : History n m) [IsProbabilityMeasure M.law] :
    M.law.map Prod.fst = IntegrableWeightedExit.law M.A M.α 0 := by
  let : IsProbabilityMeasure (M.law.map Prod.fst) :=
    inferInstance
  have hle := M.first_marginal_le
  apply Measure.eq_of_le_of_measure_univ_eq hle
  apply le_antisymm (hle univ)
  have h := IntegrableWeightedExit.law_mass_le_initial M.A M.α M.A_integrable
    M.A_metzler M.A_rows M.α_nonnegative (le_refl (0 : ℝ))
  simpa only [measure_univ, M.α_sum, ENNReal.ofReal_one] using h

end Rhone.Statistics.Identifiability.IntegrablePhase.History
