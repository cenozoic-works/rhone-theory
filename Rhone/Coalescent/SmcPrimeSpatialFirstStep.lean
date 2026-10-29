/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeSpatialSourceLaw
public import Rhone.Coalescent.SmcPrimeSpatialLengthMean
public import Rhone.MarkovChain.Shift

/-!
# First step and shift of the SMC′ chain

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”. -/

@[expose] public section

namespace Rhone.Coalescent.SmcPrime
open MeasureTheory ProbabilityTheory IntervalProcess
open scoped ENNReal

def streamCons {α : Type*} (p : α × (ℕ → α)) : ℕ → α
  | 0 => p.1
  | k + 1 => p.2 k

theorem measurable_streamCons {α : Type*} [MeasurableSpace α] :
    Measurable (streamCons (α := α)) :=
  measurable_pi_iff.mpr fun k => by
    cases k with
    | zero => exact measurable_fst
    | succ k => exact (measurable_pi_apply k).comp measurable_snd

theorem streamCons_shift {α : Type*} (a : α) (v : ℕ → α) :
    (fun k => streamCons (a, v) (1 + k)) = v := by
  funext k
  rw [Nat.add_comm]
  rfl

theorem infinitePi_map_streamCons {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] :
    (μ.prod (Measure.infinitePi fun _ : ℕ => μ)).map streamCons =
      Measure.infinitePi fun _ : ℕ => μ := by
  classical
  refine Measure.eq_infinitePi _ fun s t ht => ?_
  obtain ⟨n, hn⟩ : ∃ n, s ⊆ Finset.range (n + 1) :=
    ⟨s.sup id, fun i hi => Finset.mem_range.mpr
      (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi))⟩
  let t' : ℕ → Set α := fun i => if i ∈ s then t i else Set.univ
  have ht' : ∀ i, MeasurableSet (t' i) := by
    intro i
    by_cases his : i ∈ s
    · simp only [t', his, ↓reduceIte]
      exact ht i
    · simp only [t', his, ↓reduceIte]
      exact MeasurableSet.univ
  have hpi : Set.pi (s : Set ℕ) t = Set.pi (Finset.range (n + 1) : Set ℕ) t' := by
    ext x
    simp only [Set.mem_pi, Finset.mem_coe, t']
    constructor
    · intro h i _
      by_cases his : i ∈ s
      · simp only [his, ↓reduceIte]
        exact h i his
      · simp only [his, ↓reduceIte]
        exact Set.mem_univ _
    · intro h i his
      have hi := h i (hn his)
      simpa only [his, ↓reduceIte] using hi
  have hprod : ∏ i ∈ s, μ (t i) = ∏ i ∈ Finset.range (n + 1), μ (t' i) := by
    rw [← Finset.prod_subset hn (f := fun i => μ (t' i))]
    · exact Finset.prod_congr rfl fun i hi => by simp only [t', hi, ↓reduceIte]
    · intro i _ his
      simp only [t', his, ↓reduceIte, measure_univ]
  have hpre : streamCons ⁻¹' (Set.pi (Finset.range (n + 1) : Set ℕ) t') =
      t' 0 ×ˢ Set.pi (Finset.range n : Set ℕ) (fun j => t' (j + 1)) := by
    ext p
    simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Finset.mem_range, Set.mem_prod]
    constructor
    · intro h
      exact ⟨h 0 (Nat.succ_pos n), fun j hj => h (j + 1) (Nat.succ_lt_succ hj)⟩
    · rintro ⟨h0, h1⟩ i hi
      cases i with
      | zero => exact h0
      | succ j => exact h1 j (Nat.lt_of_succ_lt_succ hi)
  rw [hpi, hprod, Measure.map_apply measurable_streamCons
    (MeasurableSet.pi (Finset.countable_toSet _) fun i _ => ht' i), hpre, Measure.prod_prod,
    Measure.infinitePi_pi _ (fun j _ => ht' (j + 1)), Finset.prod_range_succ', mul_comm]

theorem sourceSpatialRun_streamCons (N : ℕ) (R : ℝ) (z : SpatialState N) (a : ProposalNoise)
    (v : ℕ → ProposalNoise) :
    sourceSpatialRun N R z (streamCons (a, v)) =
      streamCons (z, sourceSpatialRun N R (spatialStep N R z a) v) := by
  funext k
  cases k with
  | zero => rfl
  | succ j =>
    change sourceSpatialRun N R z (streamCons (a, v)) (j + 1) =
      sourceSpatialRun N R (spatialStep N R z a) v j
    induction j with
    | zero => rfl
    | succ j ih =>
      change spatialStep N R (sourceSpatialRun N R z (streamCons (a, v)) (j + 1)) (v j) =
        spatialStep N R (sourceSpatialRun N R (spatialStep N R z a) v j) (v j)
      rw [ih]

theorem spatialProcess_pathLaw_lintegral_first_step (N : ℕ) (R : ℝ) (z : SpatialState N)
    (F : (ℕ → SpatialState N) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ ω, F ω ∂(spatialProcess N R).pathLaw z =
      ∫⁻ a, ∫⁻ ω', F (streamCons (z, ω'))
        ∂(spatialProcess N R).pathLaw (spatialStep N R z a) ∂proposalNoiseLaw := by
  have hrun := sourceSpatialRun_measurable N R z
  have hcons : Measurable (fun ω' : ℕ → SpatialState N => streamCons (z, ω')) :=
    measurable_streamCons.comp (measurable_const.prodMk measurable_id)
  have hstream : sourceProposalStreamLaw =
      (proposalNoiseLaw.prod sourceProposalStreamLaw).map streamCons :=
    (infinitePi_map_streamCons proposalNoiseLaw).symm
  have hinner : ∀ a : ProposalNoise,
      ∫⁻ ω', F (streamCons (z, ω')) ∂(spatialProcess N R).pathLaw (spatialStep N R z a) =
        ∫⁻ v, F (sourceSpatialRun N R z (streamCons (a, v))) ∂sourceProposalStreamLaw := by
    intro a
    rw [← sourceSpatialRun_law, lintegral_map
      (show Measurable (fun ω' : ℕ → SpatialState N => F (streamCons (z, ω'))) from
        hF.comp hcons) (sourceSpatialRun_measurable N R _)]
    simp only [sourceSpatialRun_streamCons]
  simp only [hinner]
  rw [← sourceSpatialRun_law, lintegral_map hF hrun]
  conv_lhs => rw [hstream]
  rw [lintegral_map (show Measurable (fun u => F (sourceSpatialRun N R z u)) from
      hF.comp hrun) measurable_streamCons,
    lintegral_prod _ (show Measurable (fun p : ProposalNoise × (ℕ → ProposalNoise) =>
      F (sourceSpatialRun N R z (streamCons p))) from
        (hF.comp hrun).comp measurable_streamCons).aemeasurable]

theorem spatialProcess_map_shift_one (N : ℕ) (R : ℝ) (y : SpatialState N) :
    ((spatialProcess N R).pathLaw y).map (fun ω k => ω (1 + k)) =
      ((spatialProcess N R).step y).bind (spatialProcess N R).traj := by
  ext B hB
  have hsh := Rhone.MarkovChain.DiscreteProcess.measurable_shift (S := SpatialState N) 1
  have hind : ∀ ω' : ℕ → SpatialState N,
      ((fun (ω : ℕ → SpatialState N) (k : ℕ) => ω (1 + k)) ⁻¹' B).indicator
        (1 : (ℕ → SpatialState N) → ℝ≥0∞) (streamCons (y, ω')) =
        B.indicator (1 : (ℕ → SpatialState N) → ℝ≥0∞) ω' := by
    intro ω'
    have hmem : streamCons (y, ω') ∈ (fun (ω : ℕ → SpatialState N) (k : ℕ) => ω (1 + k)) ⁻¹' B
        ↔ ω' ∈ B := by
      rw [Set.mem_preimage, streamCons_shift]
    by_cases h : ω' ∈ B
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hmem.mpr h)]
      simp only [Pi.one_apply]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun hc => h (hmem.mp hc))]
  rw [Measure.map_apply hsh hB, ← lintegral_indicator_one (hsh hB),
    spatialProcess_pathLaw_lintegral_first_step N R y _ (measurable_one.indicator (hsh hB)),
    Measure.bind_apply hB (Kernel.measurable _).aemeasurable]
  change _ = ∫⁻ z', (spatialProcess N R).traj z' B ∂spatialKernel N R y
  rw [spatialKernel_apply, lintegral_map (Kernel.measurable_coe _ hB)
    (show Measurable (fun u => spatialStep N R y u) from
      (spatialStep_measurable N R).comp measurable_prodMk_left)]
  refine lintegral_congr fun a => ?_
  simp only [hind]
  rw [lintegral_indicator_one hB]
  rfl

theorem spatialProcess_map_shift (N : ℕ) (R : ℝ) (x : SpatialState N) (n : ℕ) :
    ((spatialProcess N R).pathLaw x).map (fun ω k => ω (n + k)) =
      (((spatialProcess N R).pathLaw x).map (fun ω => ω n)).bind (spatialProcess N R).traj :=
  (spatialProcess N R).map_shift_of_one (spatialProcess_map_shift_one N R) x n

end Rhone.Coalescent.SmcPrime
