/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.AtomicSmoothing.KernelPerturbation
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Concrete uniform-noise kernel coefficients and a uniform-baseline mixture -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators
namespace Rhone.Statistics.AtomicSmoothing
open AtomicRank

def noiseMeasure : Measure ℝ :=
  ENNReal.ofReal (1 / 2 : ℝ) • volume.restrict (Icc (-1 : ℝ) 1)

lemma half_mass : ENNReal.ofReal (1 / 2 : ℝ) * 2 = 1 := by
  calc
    _ = ENNReal.ofReal (1 / 2 : ℝ) * ENNReal.ofReal (2 : ℝ) := by norm_num
    _ = ENNReal.ofReal ((1 / 2 : ℝ) * 2) :=
      (ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)).symm
    _ = 1 := by norm_num

instance noiseMeasure_probability : IsProbabilityMeasure noiseMeasure := by
  constructor
  norm_num [noiseMeasure, Measure.smul_apply, Measure.restrict_apply_univ, Real.volume_Icc]
  exact half_mass

lemma noiseMeasure_interval : noiseMeasure (Icc (-1 : ℝ) 1) = 1 := by
  norm_num [noiseMeasure, Measure.smul_apply,
    Measure.restrict_apply measurableSet_Icc, Real.volume_Icc]
  exact half_mass

def noiseTriple : Measure (ℝ × ℝ × ℝ) := noiseMeasure.prod (noiseMeasure.prod noiseMeasure)

instance noiseTriple_probability : IsProbabilityMeasure noiseTriple := by
  unfold noiseTriple
  infer_instance

def noiseCube : Set (ℝ × ℝ × ℝ) := Icc (-1 : ℝ) 1 ×ˢ (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)

lemma noiseCube_compact : IsCompact noiseCube :=
  isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)

lemma noiseCube_mass : noiseTriple noiseCube = 1 := by
  rw [noiseTriple, noiseCube, Measure.prod_prod, Measure.prod_prod, noiseMeasure_interval]
  norm_num

def mixedCoordinate (a ε : ℝ) (b : Bool) (v : ℝ) : ℝ :=
  if b then (v + 1) / 2 else a + ε * v

def flagWeight (ε : ℝ) (b : Bool × Bool × Bool) : ℝ :=
  (if b.1 then ε else 1-ε) * (if b.2.1 then ε else 1-ε) * (if b.2.2 then ε else 1-ε)

def kernelTerm (f : Coefficients) (a b c : ℝ) (flags : Bool × Bool × Bool) (ε : ℝ) : ℝ :=
  ∫ p in noiseCube, sortedKernel f
    (mixedCoordinate a ε flags.1 p.1) (mixedCoordinate b ε flags.2.1 p.2.1)
    (mixedCoordinate c ε flags.2.2 p.2.2) ∂noiseTriple

def smoothedKernel (f : Coefficients) (a b c ε : ℝ) : ℝ :=
  ∑ flags : Bool × Bool × Bool, flagWeight ε flags * kernelTerm f a b c flags ε

lemma kernelTerm_continuous (f : Coefficients) (a b c : ℝ) (flags : Bool × Bool × Bool) :
    Continuous (kernelTerm f a b c flags) := by
  apply continuous_parametric_integral_of_continuous _ noiseCube_compact
  have hc : Continuous (fun p : ℝ × (ℝ × ℝ × ℝ) =>
      (mixedCoordinate a p.1 flags.1 p.2.1,
        mixedCoordinate b p.1 flags.2.1 p.2.2.1,
        mixedCoordinate c p.1 flags.2.2 p.2.2.2)) := by
    rcases flags with ⟨b1, b2, b3⟩
    cases b1 <;> cases b2 <;> cases b3 <;> unfold mixedCoordinate <;> simp only
      [Bool.false_eq_true, ↓reduceIte] <;> fun_prop
  exact (sortedKernel_continuous f).comp hc

lemma flagWeight_continuous (flags : Bool × Bool × Bool) :
    Continuous (fun ε => flagWeight ε flags) := by
  rcases flags with ⟨b1, b2, b3⟩
  cases b1 <;> cases b2 <;> cases b3 <;> unfold flagWeight <;> simp only
    [Bool.false_eq_true, ↓reduceIte] <;> fun_prop

lemma smoothedKernel_continuous (f : Coefficients) (a b c : ℝ) :
    Continuous (smoothedKernel f a b c) := by
  apply continuous_finsetSum
  intro flags _
  exact (flagWeight_continuous flags).mul (kernelTerm_continuous f a b c flags)

lemma kernelTerm_false_zero (f : Coefficients) (a b c : ℝ) :
    kernelTerm f a b c (false, false, false) 0 = sortedKernel f a b c := by
  simp only [kernelTerm, mixedCoordinate, Bool.false_eq_true, ↓reduceIte, zero_mul, add_zero]
  simp [integral_const, measureReal_def, noiseCube_mass]

theorem smoothedKernel_zero (f : Coefficients) (a b c : ℝ) :
    smoothedKernel f a b c 0 = sortedKernel f a b c := by
  rw [smoothedKernel, Finset.sum_eq_single (false, false, false)]
  · simp [flagWeight, kernelTerm_false_zero]
  · intro flags _ hn
    rcases flags with ⟨b1, b2, b3⟩
    cases b1 <;> cases b2 <;> cases b3 <;> simp_all [flagWeight]
  · intro hn
    exact (hn (Finset.mem_univ _)).elim

theorem smoothedKernel_tendsto (f : Coefficients) (a b c : ℝ) :
    Tendsto (smoothedKernel f a b c) (𝓝 (0 : ℝ)) (𝓝 (sortedKernel f a b c)) := by
  have ht : Tendsto (smoothedKernel f a b c) (𝓝 (0 : ℝ)) (𝓝 (smoothedKernel f a b c 0)) :=
    (smoothedKernel_continuous f a b c).continuousAt.tendsto
  rw [smoothedKernel_zero] at ht
  exact ht

end Rhone.Statistics.AtomicSmoothing
