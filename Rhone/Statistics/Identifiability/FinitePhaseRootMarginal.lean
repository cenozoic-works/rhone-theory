/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.GeneralPhaseBlockIntegral
public import Rhone.Statistics.Identifiability.FiniteKernelDensity
public import Rhone.Statistics.Identifiability.WeightedFirstExit
public import Rhone.Statistics.Identifiability.TwoEventFluxLaw

/-! # Root-time marginal of an arbitrary finite two-stage flux construction -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory Matrix
open scoped Topology Matrix Matrix.Norms.Operator ENNReal
namespace Rhone.Statistics.Identifiability.FinitePhase
open FiniteExponentialJets
variable {n m : ℕ}

def initial (α : Fin n → ℝ) : Fin (n + m) → ℝ := Fin.addCases α (fun _ => 0)

def density (A : Matrix (Fin n) (Fin n) ℝ) (F : Matrix (Fin n) (Fin m) ℝ)
    (B : Matrix (Fin m) (Fin m) ℝ) (α : Fin n → ℝ) : ℝ × ℝ → ℝ :=
  orderedKernelDensity A B α F (exitRate B)

def law (A : Matrix (Fin n) (Fin n) ℝ) (F : Matrix (Fin n) (Fin m) ℝ)
    (B : Matrix (Fin m) (Fin m) ℝ) (α : Fin n → ℝ) : Measure (ℝ × ℝ) :=
  triangularDensityLaw (density A F B α)

lemma density_matrix (A : Matrix (Fin n) (Fin n) ℝ) (F : Matrix (Fin n) (Fin m) ℝ)
    (B : Matrix (Fin m) (Fin m) ℝ) (α : Fin n → ℝ) (s t : ℝ) :
    density A F B α (s,t) = ∑ i, α i *
      (((NormedSpace.exp (s • A) * F * NormedSpace.exp ((t - s) • B)) *ᵥ exitRate B) i) := by
  simp only [density, orderedKernelDensity, kernelValue, ← Matrix.mulVec_mulVec, dotProduct]

lemma columnIntegral (N : Matrix (Fin (n + m)) (Fin (n + m)) ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (F : Matrix (Fin n) (Fin m) ℝ)
    (B : Matrix (Fin m) (Fin m) ℝ) (α : Fin n → ℝ)
    (hpp : ∀ i j, N (Fin.castAdd m i) (Fin.castAdd m j) = A i j)
    (hlp : ∀ i j, N (Fin.natAdd n i) (Fin.castAdd m j) = 0)
    (hpl : ∀ i j, N (Fin.castAdd m i) (Fin.natAdd n j) = F i j)
    (hll : ∀ i j, N (Fin.natAdd n i) (Fin.natAdd n j) = B i j)
    (hep : ∀ i, exitRate N (Fin.castAdd m i) = 0)
    (hel : ∀ j, exitRate N (Fin.natAdd n j) = exitRate B j) (t : ℝ) :
    (∫ s in 0..t, density A F B α (s,t)) = WeightedExit.density N (initial α) t := by
  have hi (i : Fin n) : IntervalIntegrable
      (fun s => ((NormedSpace.exp (s • A) * F * NormedSpace.exp ((t - s) • B)) *ᵥ
        exitRate B) i) volume 0 t := by
    have h : Continuous (fun s : ℝ =>
        orderedKernelDensity A B (Pi.single i 1) F (exitRate B) (s,t)) :=
      (orderedKernelDensity_continuous A B (Pi.single i 1) F (exitRate B)).comp
      (continuous_id.prodMk continuous_const)
    convert! h.intervalIntegrable (μ := volume) 0 t using 1
    funext s
    simp [orderedKernelDensity, kernelValue, dotProduct, Pi.single_apply, ← Matrix.mulVec_mulVec]
  simp_rw [density_matrix]
  rw [intervalIntegral.integral_finsetSum (fun i _ => (hi i).const_mul (α i))]
  simp_rw [intervalIntegral.integral_const_mul]
  unfold WeightedExit.density initial
  rw [Fin.sum_univ_add]
  simp only [Fin.addCases_left, Fin.addCases_right, zero_mul, Finset.sum_const_zero, add_zero]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [← phase_block_post_integral_general N A F B hpp hlp hpl hll i (exitRate B) t]
  simp [flowOutput, Matrix.mulVec, dotProduct, Fin.sum_univ_add, hep, hel]

lemma law_map_root (N : Matrix (Fin (n + m)) (Fin (n + m)) ℝ)
    (A : Matrix (Fin n) (Fin n) ℝ) (F : Matrix (Fin n) (Fin m) ℝ)
    (B : Matrix (Fin m) (Fin m) ℝ) (α : Fin n → ℝ)
    (hpp : ∀ i j, N (Fin.castAdd m i) (Fin.castAdd m j) = A i j)
    (hlp : ∀ i j, N (Fin.natAdd n i) (Fin.castAdd m j) = 0)
    (hpl : ∀ i j, N (Fin.castAdd m i) (Fin.natAdd n j) = F i j)
    (hll : ∀ i j, N (Fin.natAdd n i) (Fin.natAdd n j) = B i j)
    (hep : ∀ i, exitRate N (Fin.castAdd m i) = 0)
    (hel : ∀ j, exitRate N (Fin.natAdd n j) = exitRate B j)
    (hn : ∀ p ∈ upperWedge, 0 ≤ density A F B α p) :
    (law A F B α).map Prod.snd = WeightedExit.law N (initial α) := by
  have hc : Continuous (density A F B α) :=
    orderedKernelDensity_continuous A B α F (exitRate B)
  rw [law, triangular_map_snd_positive_ae _ hc.measurable.aemeasurable]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [← columnIntegral N A F B α hpp hlp hpl hll hep hel]
  exact (TwoEventFluxLaw.ofReal_columnIntegral (density A F B α) ht.le
    ((hc.comp (continuous_id.prodMk continuous_const)).intervalIntegrable 0 t)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      exact hn (s,t) ⟨hs.1, hs.2⟩)).symm

end Rhone.Statistics.Identifiability.FinitePhase
