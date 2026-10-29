/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeSampleMarginalBridge
public import Rhone.Statistics.Identifiability.CommonClockIslandPhaseIntegral
public import Rhone.Statistics.Identifiability.TwoEventFluxLaw

/-! # Ordered merger-time law of the constant island three-sample model -/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Matrix Matrix.Norms.Operator Topology ENNReal
open MeasureTheory Set Filter
namespace Rhone.Statistics.Identifiability
namespace IslandThreeTimes

def firstRate (c : ℝ) : Matrix (Fin 3) (Fin 2) ℝ := !![3*c, 0; 0, c; 0, 0]

def entryFlux (k : ℕ) (c q : ℝ) (j : Fin 2) (s : ℝ) : ℝ :=
  flowOutput (threeGenerator k c q) 0 (fun i => firstRate c i j) 0 s

def postDensity (k : ℕ) (c q : ℝ) (j : Fin 2) (u : ℝ) : ℝ :=
  flowOutput (MarkovChain.Identifiability.pairGenerator k c q) j
      (exitRate (MarkovChain.Identifiability.pairGenerator k c q)) 0 u

def density (k : ℕ) (c q : ℝ) (p : ℝ × ℝ) : ℝ :=
  ∑ j : Fin 2, entryFlux k c q j p.1 * postDensity k c q j (p.2-p.1)

lemma entryFlux_continuous (k : ℕ) (c q : ℝ) (j : Fin 2) :
    Continuous (entryFlux k c q j) := flowOutput_continuous _ _ _ _
lemma postDensity_continuous (k : ℕ) (c q : ℝ) (j : Fin 2) :
    Continuous (postDensity k c q j) := flowOutput_continuous _ _ _ _
lemma density_continuous (k : ℕ) (c q : ℝ) : Continuous (density k c q) := by
  apply continuous_finsetSum
  intro j _
  exact ((entryFlux_continuous k c q j).comp continuous_fst).mul
    ((postDensity_continuous k c q j).comp (continuous_snd.sub continuous_fst))

lemma firstRate_nonneg {c : ℝ} (hc : 0 ≤ c) (i : Fin 3) (j : Fin 2) :
    0 ≤ firstRate c i j := by
  fin_cases i <;> fin_cases j <;> simp [firstRate, hc]

lemma entryFlux_nonneg (k : ℕ) {c q s : ℝ}
    (hc : 0 ≤ c) (hq : 0 ≤ q) (hs : 0 ≤ s) (j : Fin 2) :
    0 ≤ entryFlux k c q j s := by
  simp only [entryFlux, flowOutput, pow_zero, Matrix.one_mul]
  exact matrix_mulVec_nonneg _ _
    (exp_generator_nonneg _ (threeGenerator_metzler k c hq) hs)
    (fun i => firstRate_nonneg hc i j) 0

lemma postDensity_nonneg (k : ℕ) {c q u : ℝ}
    (hc : 0 ≤ c) (hq : 0 ≤ q) (hu : 0 ≤ u) (j : Fin 2) :
    0 ≤ postDensity k c q j u :=
  firstExit_density_nonneg _ (pairGenerator_metzler k hq)
    (pairGenerator_rows_nonpos k hc) j hu

lemma density_nonneg (k : ℕ) {c q : ℝ} (hc : 0 ≤ c) (hq : 0 ≤ q)
    {p : ℝ × ℝ} (hp : p ∈ upperWedge) : 0 ≤ density k c q p := by
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (entryFlux_nonneg k hc hq hp.1.le j)
    (postDensity_nonneg k hc hq (sub_nonneg.mpr hp.2.le) j)

lemma entryFlux_sum (k : ℕ) (c q s : ℝ) :
    (∑ j : Fin 2, entryFlux k c q j s) =
      flowOutput (threeGenerator k c q) 0 (exitRate (threeGenerator k c q)) 0 s := by
  have hexit : exitRate (threeGenerator k c q) = ![3*c,c,0] := by
    simp only [exitRate, threeGenerator_row_sum]
    ext i
    fin_cases i <;> simp
  rw [hexit]
  simp only [entryFlux, flowOutput, pow_zero, Matrix.one_mul, Matrix.mulVec,
    dotProduct, Fin.sum_univ_succ, firstRate]
  simp

lemma density_matrix (k : ℕ) (c q s t : ℝ) :
    density k c q (s,t) =
      ((NormedSpace.exp (s • threeGenerator k c q) * firstRate c *
        NormedSpace.exp ((t-s) • MarkovChain.Identifiability.pairGenerator k c q)) *ᵥ
          exitRate (MarkovChain.Identifiability.pairGenerator k c q)) 0 := by
  rw [← Matrix.mulVec_mulVec]
  simp only [density, entryFlux, postDensity, flowOutput, pow_zero,
    Matrix.mul_apply, Matrix.mulVec, dotProduct]
  simp [Matrix.one_apply]

lemma pre_pre (k : ℕ) (c q : ℝ) (i j : Fin 3) :
    islandThreeTreeGenerator k c q (Fin.castAdd 2 i) (Fin.castAdd 2 j) =
      threeGenerator k c q i j := islandThreeTree_first_block k c q i j
lemma post_pre (k : ℕ) (c q : ℝ) (i : Fin 2) (j : Fin 3) :
    islandThreeTreeGenerator k c q (Fin.natAdd 3 i) (Fin.castAdd 2 j) = 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [islandThreeTreeGenerator, Fin.castAdd, Fin.natAdd, Fin.castLE]
lemma pre_post (k : ℕ) (c q : ℝ) (i : Fin 3) (j : Fin 2) :
    islandThreeTreeGenerator k c q (Fin.castAdd 2 i) (Fin.natAdd 3 j) = firstRate c i j := by
  fin_cases i <;> fin_cases j <;>
    norm_num [islandThreeTreeGenerator, firstRate, Fin.castAdd, Fin.natAdd, Fin.castLE]
lemma post_post (k : ℕ) (c q : ℝ) (i j : Fin 2) :
    islandThreeTreeGenerator k c q (Fin.natAdd 3 i) (Fin.natAdd 3 j) =
      MarkovChain.Identifiability.pairGenerator k c q i j := islandThreeTree_pair_block k c q i j

lemma full_exitRate (k : ℕ) (c q : ℝ) :
    exitRate (islandThreeTreeGenerator k c q) = ![0,0,0,c,0] := by
  ext i
  fin_cases i <;>
    simp [exitRate, islandThreeTreeGenerator, dotProduct, Fin.sum_univ_succ]
  ring

theorem density_columnIntegral (k : ℕ) (c q t : ℝ) :
    (∫ s in (0 : ℝ)..t, density k c q (s,t)) =
      flowOutput (islandThreeTreeGenerator k c q) 0
        (exitRate (islandThreeTreeGenerator k c q)) 0 t := by
  have h := phase_block_post_integral (islandThreeTreeGenerator k c q)
    (threeGenerator k c q) (firstRate c) (MarkovChain.Identifiability.pairGenerator k c q)
    (pre_pre k c q) (post_pre k c q) (pre_post k c q) (post_post k c q)
    (0 : Fin 3) (exitRate (MarkovChain.Identifiability.pairGenerator k c q)) t
  simp_rw [← density_matrix] at h
  rw [← h, full_exitRate, pair_exitRate]
  simp [flowOutput, MarkovChain.Identifiability.pairDensity, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ,
    Fin.castAdd, Fin.natAdd, Fin.castLE]

def law (k : ℕ) (c q : ℝ) : Measure (ℝ × ℝ) := triangularDensityLaw (density k c q)

theorem law_map_root (k : ℕ) {c q : ℝ} (hc : 0 ≤ c) (hq : 0 ≤ q) :
    (law k c q).map Prod.snd = firstExitLaw (islandThreeTreeGenerator k c q) 0 := by
  rw [law, triangular_map_snd_positive_ae _
    (density_continuous k c q).measurable.aemeasurable]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [← density_columnIntegral]
  exact (TwoEventFluxLaw.ofReal_columnIntegral (density k c q) ht.le
    (((density_continuous k c q).comp
      (continuous_id.prodMk continuous_const)).intervalIntegrable 0 t)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      exact density_nonneg k hc hq ⟨hs.1,hs.2⟩)).symm

theorem law_probability (k : ℕ) {c q : ℝ} (hc : 0 < c) (hq : 0 < q) :
    IsProbabilityMeasure (law k c q) := by
  have hroot := firstExitLaw_probability (islandThreeTreeGenerator k c q)
    (islandThreeTree_metzler k hc.le hq.le) (islandThreeTree_rows_nonpos k hc.le) 0
    (islandThree_survival_tendsto_zero k hc hq 0)
  apply (Measure.isProbabilityMeasure_map_iff measurable_snd.aemeasurable).mp
  rw [law_map_root k hc.le hq.le]
  exact hroot

end IslandThreeTimes
end Rhone.Statistics.Identifiability
