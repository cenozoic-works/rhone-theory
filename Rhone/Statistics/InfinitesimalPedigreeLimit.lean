/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Statistics.InfinitesimalPedigreeProjectedCLT
public import Mathlib.Probability.CramerWold
public import Mathlib.Analysis.InnerProductSpace.PiL2
/-!
# The joint unconditional infinitesimal limit on an arbitrary finite pedigree

Source: barton_etheridge_veber2017, sec. 3.1. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Rhone.Statistics Rhone.Combinatorics Filter Topology
open scoped ENNReal InnerProductSpace
namespace Rhone.Statistics

private theorem weighted_normalized_sum {n : Nat} (M : Nat) (a : Real) (t : Fin n → Real)
    (R : Nat → Fin n → Real) :
    (∑ i, t i * (a * ∑ k ∈ Finset.range M, R k i)) =
      a * ∑ k ∈ Finset.range M, ∑ i, t i * R k i := by
  have hi : (∑ i, t i * (a * ∑ k ∈ Finset.range M, R k i)) =
      ∑ i, a * ∑ k ∈ Finset.range M, t i * R k i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [← mul_assoc, mul_comm (t i) a, mul_assoc, Finset.mul_sum]
  rw [hi, ← Finset.mul_sum, Finset.sum_comm]

theorem pedigree_joint_iid_limit {n : Nat} (P : Pedigree n) (ν : Measure Real)
    [IsProbabilityMeasure ν] (hν : MemLp id 2 ν) :
    TendstoInDistribution
      (fun (M : Nat) (ω : Nat → (Fin n → Real) × (Fin n → Bool)) =>
        fun i : Fin n => (Real.sqrt (M : Real))⁻¹ * ∑ k ∈ Finset.range M,
          locusSegregationResidual P (∫ x, x ∂ν) (ω k).1 (ω k).2 i)
      atTop (id : (Fin n → Real) → (Fin n → Real))
      (fun _ => Measure.infinitePi fun _ : Nat => locusLaw n ν)
      (Measure.pi fun i : Fin n => gaussianReal 0
        (segregationVariance P (Var[id; ν]) i).toNNReal) := by
  let Q := Measure.infinitePi (fun _ : Nat => locusLaw n ν)
  let U := fun (M : Nat) (ω : Nat → (Fin n → Real) × (Fin n → Bool)) =>
    WithLp.toLp 2 (fun i : Fin n => (Real.sqrt (M : Real))⁻¹ * ∑ k ∈ Finset.range M,
      locusSegregationResidual P (∫ x, x ∂ν) (ω k).1 (ω k).2 i)
  let V := fun z : Fin n → Real => WithLp.toLp 2 z
  have hu (M : Nat) : Measurable (U M) := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin n => Real)).measurable.comp
    apply Measurable.of_eval
    intro i
    exact (Finset.measurable_sum _ (fun k _ =>
      (locus_residual_measurable P (∫ x, x ∂ν) i).comp
        (measurable_pi_apply k))).const_mul _
  have hv : Measurable V := (PiLp.continuous_toLp 2 (fun _ : Fin n => Real)).measurable
  have hvec : TendstoInDistribution U atTop V (fun _ => Q)
      (Measure.pi fun i : Fin n => gaussianReal 0
        (segregationVariance P (Var[id; ν]) i).toNNReal) := by
    apply TendstoInDistribution.of_inner hv.aemeasurable (fun M => (hu M).aemeasurable)
    intro t
    have h := pedigree_projection_iid_limit P ν hν (fun i => t i)
    convert h using 1
    · funext M ω
      simp only [U, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
      exact weighted_normalized_sum M _ (fun i => t i)
        (fun k i => locusSegregationResidual P (∫ x, x ∂ν) (ω k).1 (ω k).2 i)
  have h := hvec.continuous_comp (g := WithLp.ofLp) (PiLp.continuous_ofLp 2 (fun _ : Fin n => Real))
  exact h
end Rhone.Statistics

namespace Rhone.Statistics
theorem infinitesimal_pedigree_tendsto_gaussian {n : Nat} (P : Pedigree n) (ν : Measure Real)
    [IsProbabilityMeasure ν] (hν : MemLp id 2 ν)
    (g : BoundedContinuousFunction (Fin n → Real) Real) :
    Tendsto (fun M : Nat => ∫ ω, g (segregationResidual P (traitDeviation P (∫ y, y ∂ν) M ω))
        ∂(genomeLaw n ν M))
      atTop (𝓝 (∫ z, g z ∂(Measure.pi fun i =>
        gaussianReal 0 (segregationVariance P (variance id ν) i).toNNReal))) := by
  let Q := Measure.infinitePi (fun _ : Nat => locusLaw n ν)
  let F := fun (M : Nat) (ω : Fin M → (Fin n → Real) × (Fin n → Bool)) =>
    segregationResidual P (traitDeviation P (∫ y, y ∂ν) M ω)
  let U := fun (M : Nat) (ω : Nat → (Fin n → Real) × (Fin n → Bool)) =>
    fun i : Fin n => (Real.sqrt (M : Real))⁻¹ * ∑ k ∈ Finset.range M,
      locusSegregationResidual P (∫ y, y ∂ν) (ω k).1 (ω k).2 i
  have hm (M : Nat) : Measurable (F M) := by
    have heq : F M = (fun ω => fun i : Fin n => (Real.sqrt (M : Real))⁻¹ *
        ∑ l : Fin M, locusSegregationResidual P (∫ y, y ∂ν) (ω l).1 (ω l).2 i) := by
      funext ω
      exact segregationResidual_traitDeviation_sum P _ M ω
    rw [heq]
    apply Measurable.of_eval
    intro i
    exact (Finset.measurable_sum _ (fun l _ =>
      (locus_residual_measurable P (∫ y, y ∂ν) i).comp
        (measurable_pi_apply l))).const_mul _
  have hr (M : Nat) : HasLaw
      (fun ω : Nat → (Fin n → Real) × (Fin n → Bool) => fun l : Fin M => ω l.val)
      (genomeLaw n ν M) Q := by
    refine ⟨(Measurable.of_eval (fun l : Fin M => measurable_pi_apply l.val)).aemeasurable, ?_⟩
    change (Measure.infinitePi (fun _ : Nat => locusLaw n ν)).map
      (fun ω => fun l : Fin M => ω l.val) = _
    rw [Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective, Measure.infinitePi_eq_pi]
    rfl
  have hFU (M : Nat) (ω : Nat → (Fin n → Real) × (Fin n → Bool)) :
      F M (fun l : Fin M => ω l.val) = U M ω := by
    change segregationResidual P (traitDeviation P _ M _) = _
    rw [segregationResidual_traitDeviation_sum]
    funext i
    simp only [U]
    rw [Fin.sum_univ_eq_sum_range (fun k : Nat =>
      locusSegregationResidual P (∫ y, y ∂ν) (ω k).1 (ω k).2 i)]
  have hj := pedigree_joint_iid_limit P ν hν
  have hlim := (tendstoInDistribution_iff_forall_integral_rclike_tendsto Real
    hj.forall_aemeasurable hj.aemeasurable_limit).mp hj g
  have heq (M : Nat) : (∫ ω, g (U M ω) ∂Q) = ∫ ω, g (F M ω) ∂(genomeLaw n ν M) := by
    calc
      _ = ∫ ω, g (F M (fun l : Fin M => ω l.val)) ∂Q := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun ω => by
          change g (U M ω) = g (F M (fun l : Fin M => ω l.val))
          rw [hFU])
      _ = _ := (hr M).integral_comp (g.continuous.measurable.comp (hm M)).aestronglyMeasurable
  change Tendsto (fun M : Nat => ∫ ω, g (U M ω) ∂Q) atTop
    (𝓝 (∫ z, g z ∂(Measure.pi fun i =>
      gaussianReal 0 (segregationVariance P (variance id ν) i).toNNReal))) at hlim
  simpa only [heq] using hlim
end Rhone.Statistics
