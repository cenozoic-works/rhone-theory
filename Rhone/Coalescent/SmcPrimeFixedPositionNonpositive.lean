/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeTVBound
public import Rhone.Coalescent.SmcPrimeKingmanZeroRecombination

/-!
# Fixed-position marginals for a nonpositive recombination parameter

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/

@[expose] public section

namespace Rhone.Coalescent.SmcPrime
open MeasureTheory IntervalProcess MarkovChain Probability

theorem eq_of_eventTV_eq_zero {α : Type*} [MeasurableSpace α] (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h : eventTV μ ν = 0) : μ = ν := by
  ext s hs
  have hle := (eventTV_le_iff μ ν 0).mp h.le s hs
  have habs : |μ.real s - ν.real s| ≤ 0 := ENNReal.ofReal_eq_zero.mp (le_antisymm hle zero_le)
  have heq : μ.real s = ν.real s := sub_eq_zero.mp (abs_nonpos_iff.mp habs)
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ s) (measure_ne_top ν s)).mp heq

theorem spatialStep_of_nonpos (N : ℕ) {R : ℝ} (hR : R ≤ 0) :
    spatialStep N R = spatialStep N 0 := by
  funext z u
  simp [spatialStep, hR]

theorem smcPrimeGenealogyLaw_of_nonpos (N : ℕ) {R : ℝ} (hR : R ≤ 0) :
    smcPrimeGenealogyLaw N R = smcPrimeGenealogyLaw N 0 := by
  have hk : spatialKernel N R = spatialKernel N 0 := by
    unfold spatialKernel
    rw [spatialStep_of_nonpos N hR]
  have hp : spatialProcess N R = spatialProcess N 0 := by
    simp [spatialProcess, hk]
  unfold smcPrimeGenealogyLaw
  rw [hp]

theorem sampleStep_of_nonpos (mode : Mode) {R : ℝ} (hR : R ≤ 0) :
    sampleStep mode R = sampleStep mode 0 := by
  classical
  have hc : ∀ s : State, candidateRate mode R s = candidateRate mode 0 s := by
    intro s
    funext a
    cases a <;> simp [candidateRate, Real.toNNReal_of_nonpos hR]
  have ht : ∀ s : State, totalRate mode R s = totalRate mode 0 s := by
    intro s
    simp [totalRate, hc]
  have hs : ∀ (s : State) (u : Noise), selectedAction mode R s u = selectedAction mode 0 s u := by
    intro s u
    simp [selectedAction, hc, ht]
  funext s u
  simp [sampleStep, ht, hs]

theorem fullARGGenealogyLaw_of_nonpos (N : ℕ) {R : ℝ} (hR : R ≤ 0) :
    fullARGGenealogyLaw N R = fullARGGenealogyLaw N 0 := by
  have hk : eventKernel false R = eventKernel false 0 := by
    unfold eventKernel augmentedStep
    rw [sampleStep_of_nonpos false hR]
  have hp : eventProcess false R = eventProcess false 0 := by
    simp [eventProcess, hk]
  unfold fullARGGenealogyLaw
  rw [hp]

theorem smcPrimeGenealogyLaw_zero_eq_kingmanTree (N : ℕ) :
    smcPrimeGenealogyLaw N 0 =
      (kingmanTreeLaw N).map (fun T => fun _ i j => treePairMRCA T i j) := by
  rw [← fullARGGenealogyLaw_zero_eq_kingmanTree]
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have hsub : Subsingleton (Genealogy 0) :=
      ⟨fun G G' => by funext q i; exact i.elim0⟩
    ext s hs
    rcases Set.eq_empty_or_nonempty s with rfl | ⟨x, hx⟩
    · simp
    · have hu : s = Set.univ := Set.eq_univ_of_forall fun y => by
        rw [Subsingleton.elim y x]
        exact hx
      rw [hu, measure_univ, measure_univ]
  · exact (eq_of_eventTV_eq_zero _ _
      (fullARG_smcPrime_tv_zero_recombination N hN)).symm

theorem smcPrimeGenealogyLaw_at_probe_eq_kingman_of_nonpos (N : ℕ) {R : ℝ}
    (hR : R ≤ 0) (q : GenomicProbe) :
    (smcPrimeGenealogyLaw N R).map (fun G => G q) =
      (kingmanTreeLaw N).map (fun T i j => treePairMRCA T i j) := by
  rw [smcPrimeGenealogyLaw_of_nonpos N hR,
    smcPrimeGenealogyLaw_zero_eq_kingmanTree,
    Measure.map_map (measurable_pi_apply q) (treeConstantGenealogy_measurable N)]
  rfl

theorem fullARGGenealogyLaw_at_probe_eq_kingman_of_nonpos (N : ℕ) {R : ℝ}
    (hR : R ≤ 0) (q : GenomicProbe) :
    (fullARGGenealogyLaw N R).map (fun G => G q) =
      (kingmanTreeLaw N).map (fun T i j => treePairMRCA T i j) := by
  rw [fullARGGenealogyLaw_of_nonpos N hR, fullARGGenealogyLaw_zero_eq_kingmanTree,
    Measure.map_map (measurable_pi_apply q) (treeConstantGenealogy_measurable N)]
  rfl

end Rhone.Coalescent.SmcPrime
