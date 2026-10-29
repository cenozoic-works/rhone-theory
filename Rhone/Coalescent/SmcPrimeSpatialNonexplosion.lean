/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.SmcPrimeSpatialNonexplosionSource
public import Rhone.Coalescent.SmcPrimeSpatialSourceLaw
public import Rhone.Coalescent.SmcPrimeKingmanChronology
public import Rhone.Coalescent.SmcPrimeGenealogyLaw

/-!
# The full SMC′ spatial path covers the chromosome almost surely

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 1–7. -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem spatial_path_reaches_end_measurable (N : ℕ) :
    MeasurableSet {ω : ℕ → SpatialState N | ∃ k, (ω k).1 = 1} := by
  have he : {ω : ℕ → SpatialState N | ∃ k, (ω k).1 = 1} =
      ⋃ k : ℕ, {ω | (ω k).1 = 1} := by ext ω; simp
  rw [he]
  exact MeasurableSet.iUnion fun k =>
    measurableSet_eq_fun (measurable_pi_apply k).fst measurable_const

theorem spatialProcess_nonexplosive_of_stopped (N : ℕ) (R : ℝ) (z : SpatialState N)
    (hstop : 1 ≤ z.1 ∨ R ≤ 0 ∨ treeLength z.2 ≤ 0) :
    ∀ᵐ ω ∂(spatialProcess N R).pathLaw z, ∃ k, (ω k).1 = 1 := by
  rw [← sourceSpatialRun_law]
  apply (ae_map_iff (sourceSpatialRun_measurable N R z).aemeasurable
    (spatial_path_reaches_end_measurable N)).mpr
  exact Filter.Eventually.of_forall fun u => ⟨1, by simp [sourceSpatialRun, spatialStep, hstop]⟩

theorem treeLength_sample_le_one {N : ℕ} (hN : N ≤ 1) (T : Tree N) : treeLength T = 0 := by
  have hs : Subsingleton (Fin N) := ⟨fun i j => by
    apply Fin.ext
    have hi := i.isLt
    have hj := j.isLt
    omega⟩
  let := hs
  unfold treeLength
  apply Finset.sum_eq_zero
  intro i _
  have hc : (T.2 i).1 = ∅ ∨ (T.2 i).1 = Finset.univ := by
    rcases (T.2 i).1.eq_empty_or_nonempty with he | ⟨j, hj⟩
    · exact Or.inl he
    · right
      apply Finset.eq_univ_of_forall
      intro a
      simpa only [Subsingleton.elim a j] using hj
  simp only [branchLength, hc, ↓reduceIte]

theorem spatialProcess_nonexplosive_from_tree {N : ℕ} (R : ℝ) (z : SpatialState N)
    (hN : 0 < N) (hnorm : TreeNormalized z.2) (hnonneg : TreeNonnegative z.2)
    (hchron : TreeChronology z.2) :
    ∀ᵐ ω ∂(spatialProcess N R).pathLaw z, ∃ k, (ω k).1 = 1 := by
  rw [← sourceSpatialRun_law]
  exact (ae_map_iff (sourceSpatialRun_measurable N R z).aemeasurable
    (spatial_path_reaches_end_measurable N)).mpr
    (sourceSpatialRun_nonexplosive R z hN hnorm hnonneg hchron)

theorem spatialProcess_nonexplosive (N : ℕ) (R : ℝ) :
    ∀ᵐ ω ∂(spatialProcess N R).law (spatialInitialLaw N), ∃ k, (ω k).1 = 1 := by
  have hi : ∀ᵐ z ∂spatialInitialLaw N,
      ∀ᵐ ω ∂(spatialProcess N R).pathLaw z, ∃ k, (ω k).1 = 1 := by
    by_cases hsmall : N ≤ 1
    · exact Filter.Eventually.of_forall fun z =>
        spatialProcess_nonexplosive_of_stopped N R z
          (Or.inr (Or.inr (by rw [treeLength_sample_le_one hsmall])))
    · have hN : 0 < N := by omega
      have hg : ∀ᵐ T ∂kingmanTreeLaw N,
          TreeNormalized T ∧ TreeNonnegative T ∧ TreeChronology T := by
        filter_upwards [kingmanTreeLaw_normalized N, kingmanTreeLaw_nonnegative N,
          kingmanTreeLaw_chronology N hN] with T hn hp hc
        exact ⟨hn, hp, hc⟩
      unfold spatialInitialLaw
      have hgeom : MeasurableSet {z : SpatialState N |
          TreeNormalized z.2 ∧ TreeNonnegative z.2 ∧ TreeChronology z.2} :=
        ((TreeNormalized_measurable N).preimage measurable_snd).inter
          (((TreeNonnegative_measurable N).preimage measurable_snd).inter
            ((TreeChronology_measurable N).preimage measurable_snd))
      have hz : ∀ᵐ z ∂(kingmanTreeLaw N).map (fun T => ((0 : ℝ), T)),
          TreeNormalized z.2 ∧ TreeNonnegative z.2 ∧ TreeChronology z.2 :=
        (ae_map_iff (measurable_const.prodMk measurable_id).aemeasurable hgeom).mpr hg
      filter_upwards [hz] with z hz
      exact spatialProcess_nonexplosive_from_tree R z hN hz.1 hz.2.1 hz.2.2
  rw [Rhone.MarkovChain.DiscreteProcess.law, ae_iff]
  have hc : MeasurableSet {ω : ℕ → SpatialState N | ¬ ∃ k, (ω k).1 = 1} :=
    (spatial_path_reaches_end_measurable N).compl
  rw [Measure.bind_apply hc (Kernel.measurable _).aemeasurable]
  calc
    _ = ∫⁻ _z, (0 : ℝ≥0∞) ∂spatialInitialLaw N := by
      apply lintegral_congr_ae
      filter_upwards [hi] with z hz
      exact (ae_iff).mp hz
    _ = 0 := by simp
end Rhone.Coalescent.SmcPrime
