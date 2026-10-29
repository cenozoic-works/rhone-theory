/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.IntegrablePhasePayoff
public import Rhone.Statistics.Identifiability.IntegrableWeightedExitBounds
public import Rhone.Statistics.Identifiability.MatrixKernelJetCertificate
public import Rhone.Statistics.Identifiability.AEDensityMarginals

/-! # Literal finite two-stage histories with arbitrary locally-integrable coefficients -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory Matrix
open scoped Topology Matrix
namespace Rhone.Statistics.Identifiability.IntegrablePhase
open FiniteExponentialJets

structure History (n m : ℕ) where
  A : ℝ → Matrix (Fin n) (Fin n) ℝ
  B : ℝ → Matrix (Fin m) (Fin m) ℝ
  F : ℝ → Matrix (Fin n) (Fin m) ℝ
  N : ℝ → Matrix (Fin (n + m)) (Fin (n + m)) ℝ
  α : Fin n → ℝ
  A_integrable : ∀ i j, LocallyIntegrable (fun t => A t i j) volume
  B_integrable : ∀ i j, LocallyIntegrable (fun t => B t i j) volume
  F_integrable : ∀ i j, LocallyIntegrable (fun t => F t i j) volume
  N_integrable : ∀ i j, LocallyIntegrable (fun t => N t i j) volume
  A_metzler : ∀ᵐ t, 0 ≤ t → IsMetzler (A t)
  B_metzler : ∀ᵐ t, 0 ≤ t → IsMetzler (B t)
  N_metzler : ∀ᵐ t, 0 ≤ t → IsMetzler (N t)
  A_rows : ∀ᵐ t, 0 ≤ t → ∀ i, (∑ j, A t i j) ≤ 0
  B_rows : ∀ᵐ t, 0 ≤ t → ∀ i, (∑ j, B t i j) ≤ 0
  N_rows : ∀ᵐ t, 0 ≤ t → ∀ i, (∑ j, N t i j) ≤ 0
  F_nonnegative : ∀ᵐ t, 0 ≤ t → ∀ i j, 0 ≤ F t i j
  α_nonnegative : ∀ i, 0 ≤ α i
  α_sum : ∑ i, α i = 1
  flux : ∀ᵐ t, 0 ≤ t → F t *ᵥ (fun _ => 1) = exitRate (A t)
  pre_pre : ∀ᵐ t, ∀ i j, N t (Fin.castAdd m i) (Fin.castAdd m j) = A t i j
  post_pre : ∀ᵐ t, ∀ i j, N t (Fin.natAdd n i) (Fin.castAdd m j) = 0
  pre_post : ∀ᵐ t, ∀ i j, N t (Fin.castAdd m i) (Fin.natAdd n j) = F t i j
  post_post : ∀ᵐ t, ∀ i j, N t (Fin.natAdd n i) (Fin.natAdd n j) = B t i j
  exit_pre : ∀ᵐ t, 0 ≤ t → ∀ i, exitRate (N t) (Fin.castAdd m i) = 0
  exit_post : ∀ᵐ t, 0 ≤ t → ∀ j, exitRate (N t) (Fin.natAdd n j) = exitRate (B t) j

namespace History
variable {n m : ℕ}

def γ (M : History n m) : Fin (n + m) → ℝ := Fin.addCases M.α (fun _ => 0)

def density (M : History n m) (p : ℝ × ℝ) : ℝ :=
  kernelValue M.α (M.F p.1) (exitRate (M.B p.2))
    (inhomogeneousTransition M.A 0 p.1) (inhomogeneousTransition M.B p.1 p.2)

def law (M : History n m) : Measure (ℝ × ℝ) := triangularDensityLaw M.density

lemma γ_nonnegative (M : History n m) (i : Fin (n + m)) : 0 ≤ M.γ i := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa [γ] using M.α_nonnegative j
  · simp [γ]

lemma γ_sum (M : History n m) : ∑ i, M.γ i = 1 := by simp [γ, Fin.sum_univ_add, M.α_sum]

lemma density_matrix (M : History n m) (s t : ℝ) :
    M.density (s,t) = ∑ i, M.α i *
      (((inhomogeneousTransition M.A 0 s * M.F s * inhomogeneousTransition M.B s t) *ᵥ
        exitRate (M.B t)) i) := by
  simp only [density, kernelValue, ← Matrix.mulVec_mulVec, dotProduct]

lemma density_aemeasurable (M : History n m) : AEMeasurable M.density planeVolume := by
  have hU (i j : Fin n) :
      Continuous (fun p : ℝ × ℝ => inhomogeneousTransition M.A 0 p.1 i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp
      ((integrableTransition_continuous M.A M.A_integrable).comp
        (continuous_const.prodMk continuous_fst)))
  have hV (i j : Fin m) :
      Continuous (fun p : ℝ × ℝ => inhomogeneousTransition M.B p.1 p.2 i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp
      (integrableTransition_continuous M.B M.B_integrable))
  have hF (i : Fin n) (j : Fin m) : AEMeasurable (fun p : ℝ × ℝ => M.F p.1 i j) planeVolume :=
    (M.F_integrable i j).aestronglyMeasurable.aemeasurable.comp_fst
  have hv (j : Fin m) : AEMeasurable (fun p : ℝ × ℝ => exitRate (M.B p.2) j) planeVolume :=
    (IntegrableWeightedExit.exitRate_locallyIntegrable M.B M.B_integrable j)
      |>.aestronglyMeasurable.aemeasurable.comp_snd
  unfold density kernelValue Matrix.mulVec dotProduct
  apply Finset.aemeasurable_fun_sum
  intro i _
  apply aemeasurable_const.mul
  apply Finset.aemeasurable_fun_sum
  intro j _
  apply (hU i j).measurable.aemeasurable.mul
  apply Finset.aemeasurable_fun_sum
  intro k _
  apply (hF j k).mul
  apply Finset.aemeasurable_fun_sum
  intro l _
  exact (hV k l).measurable.aemeasurable.mul (hv l)

lemma density_nonnegative_at (M : History n m) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (hF : ∀ i j, 0 ≤ M.F s i j) (hB : ∀ i, (∑ j, M.B t i j) ≤ 0) :
    0 ≤ M.density (s,t) := by
  unfold density kernelValue dotProduct
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg (M.α_nonnegative i)
  apply matrix_mulVec_nonneg _ _
    (integrableTransition_nonneg M.A M.A_integrable M.A_metzler le_rfl hs)
  intro a
  apply matrix_mulVec_nonneg _ _ hF
  exact matrix_mulVec_nonneg _ _
    (integrableTransition_nonneg M.B M.B_integrable M.B_metzler hs hst)
    (exitRate_nonneg (M.B t) hB)

lemma density_nonnegative_ae (M : History n m) :
    ∀ᵐ p ∂planeVolume.restrict upperWedge, 0 ≤ M.density p := by
  have hf : ∀ᵐ p ∂planeVolume, 0 ≤ p.1 → ∀ i j, 0 ≤ M.F p.1 i j :=
    Measure.quasiMeasurePreserving_fst.ae M.F_nonnegative
  have hb : ∀ᵐ p ∂planeVolume, 0 ≤ p.2 → ∀ i, (∑ j, M.B p.2 i j) ≤ 0 :=
    Measure.quasiMeasurePreserving_snd.ae M.B_rows
  filter_upwards [hf.filter_mono (ae_mono Measure.restrict_le_self),
    hb.filter_mono (ae_mono Measure.restrict_le_self),
    ae_restrict_mem upperWedge_open.measurableSet] with p hp1 hp2 hp
  exact M.density_nonnegative_at hp.1.le hp.2.le (hp1 hp.1.le) (hp2 (hp.1.trans hp.2).le)

end History
end Rhone.Statistics.Identifiability.IntegrablePhase
