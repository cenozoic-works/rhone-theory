/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Statistics.InfinitesimalPedigreeMeasurable
public import Rhone.Statistics.InfinitesimalPedigreeGaussianProjection
public import Mathlib.Probability.CentralLimitTheorem
public import Mathlib.Probability.Independence.InfinitePi
/-!
# Scalar iid CLT bridge for the pedigree residuals

Source: barton_etheridge_veber2017, sec. 3.1, Thm A.2. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Rhone.Statistics Rhone.Combinatorics Filter Topology
open scoped ENNReal
namespace Rhone.Statistics
theorem pedigree_projection_iid_limit {n : Nat} (P : Pedigree n) (ν : Measure Real)
    [IsProbabilityMeasure ν] (hν : MemLp id 2 ν) (t : Fin n → Real) :
    TendstoInDistribution
      (fun (M : Nat) (ω : Nat → (Fin n → Real) × (Fin n → Bool)) =>
        (Real.sqrt (M : Real))⁻¹ * ∑ k ∈ Finset.range M,
          locusResidualProjection P (∫ x, x ∂ν) t (ω k))
      atTop (fun z : Fin n → Real => ∑ i, t i * z i)
      (fun _ => Measure.infinitePi fun _ : Nat => locusLaw n ν)
      (Measure.pi fun i : Fin n => gaussianReal 0
        (segregationVariance P (Var[id; ν]) i).toNNReal) := by
  let L := locusLaw n ν
  let Q := Measure.infinitePi (fun _ : Nat => L)
  let f := locusResidualProjection P (∫ x, x ∂ν) t
  let X := fun k : Nat => fun ω : Nat → (Fin n → Real) × (Fin n → Bool) => f (ω k)
  have hm : Measurable f := locus_projection_measurable P _ t
  have heval (k : Nat) :
      HasLaw (fun ω : Nat → (Fin n → Real) × (Fin n → Bool) => ω k) L Q :=
    ⟨(measurable_pi_apply k).aemeasurable, Measure.infinitePi_map_eval _ k⟩
  have hflaw := hasLaw_map (P := L) hm.aemeasurable
  have hXlaw (k : Nat) : HasLaw (X k) (L.map f) Q := hflaw.fun_comp (heval k)
  have hbase : IdentDistrib (X 0) f Q L := (hXlaw 0).identDistrib hflaw
  have hi : iIndepFun X Q := iIndepFun_infinitePi (X := fun _ : Nat => f) (fun _ => hm)
  have hid (k : Nat) : IdentDistrib (X k) (X 0) Q Q := (hXlaw k).identDistrib (hXlaw 0)
  have hx : MemLp (X 0) 2 Q := (heval 0).memLp_fun_comp (locus_projection_memLp P ν hν _ t)
  have hmean : (∫ ω, X 0 ω ∂Q) = 0 := by
    rw [hbase.integral_eq]
    exact locus_projection_mean_zero P ν hν t
  have hv : Var[X 0; Q] = ∑ i, (t i)^2 * segregationVariance P (Var[id; ν]) i := by
    rw [hbase.variance_eq]
    exact locus_projection_variance P ν hν t
  have hg : HasLaw (fun z : Fin n → Real => ∑ i, t i * z i)
      (gaussianReal 0 Var[X 0; Q].toNNReal)
      (Measure.pi fun i : Fin n => gaussianReal 0
        (segregationVariance P (Var[id; ν]) i).toNNReal) := by
    rw [hv]
    convert gaussian_product_projection_law
      (fun i => (segregationVariance P (Var[id; ν]) i).toNNReal) t using 1
    congr 2
    apply Finset.sum_congr rfl
    intro i _
    rw [Real.coe_toNNReal _ (segregationVariance_nonneg P (variance_nonneg id ν) i)]
  have h := tendstoInDistribution_inv_sqrt_mul_sum_sub hg hx hi hid
  simpa only [hmean, mul_zero, sub_zero] using h
end Rhone.Statistics
