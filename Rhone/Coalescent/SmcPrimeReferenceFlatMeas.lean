/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeAttachmentFlatLaw
public import Rhone.Coalescent.SmcPrimeIndexedCutFlat
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Joint measurability of the indexed cut and attachment densities

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 1–6. -/

@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess SmcSupport MeasureTheory Set

theorem attachmentRate_joint_measurable (N : ℕ) :
    Measurable (fun p : Tree N × ℝ => attachmentRate p.1 p.2) := by
  apply measurable_prod_sigma_of_fibers
  intro m
  exact attachmentRateFiber_measurable N m

theorem attachmentHazard_joint_measurable (N : ℕ) :
    Measurable (fun p : Tree N × ℝ × ℝ => attachmentHazard p.1 p.2.1 p.2.2) := by
  let f (p : (Tree N × ℝ × ℝ) × ℝ) : ℝ :=
    if p.1.2.1 < p.2 ∧ p.2 ≤ p.1.2.2 then attachmentRate p.1.1 p.2 else 0
  let g (p : (Tree N × ℝ × ℝ) × ℝ) : ℝ :=
    if p.1.2.2 < p.2 ∧ p.2 ≤ p.1.2.1 then attachmentRate p.1.1 p.2 else 0
  have hr : Measurable (fun p : (Tree N × ℝ × ℝ) × ℝ => attachmentRate p.1.1 p.2) :=
    (attachmentRate_joint_measurable N).comp (measurable_fst.fst.prodMk measurable_snd)
  have hf : Measurable f := hr.ite
    ((measurableSet_lt measurable_fst.snd.fst measurable_snd).inter
      (measurableSet_le measurable_snd measurable_fst.snd.snd)) measurable_const
  have hg : Measurable g := hr.ite
    ((measurableSet_lt measurable_fst.snd.snd measurable_snd).inter
      (measurableSet_le measurable_snd measurable_fst.snd.fst)) measurable_const
  have hm := (hf.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable.sub
    (hg.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable
  convert hm using 1
  funext p
  unfold attachmentHazard intervalIntegral
  rw [← integral_indicator measurableSet_Ioc, ← integral_indicator measurableSet_Ioc]
  simp only [f, g, Set.indicator_apply, Set.mem_Ioc, Pi.sub_apply]

theorem indexedCutDensity_joint_measurable (N : ℕ) :
    Measurable (fun p : Tree N × (ℕ × ℝ) => indexedCutDensity p.1 p.2) := by
  apply measurable_prod_sigma_of_fibers
  intro m
  let P := (Fin m → Branch N) × (ℕ × ℝ)
  let d (b : ℕ) (p : P) := indexedCutDensity (⟨m, p.1⟩ : Tree N) (b, p.2.2)
  apply measurable_countable_choice (fun p : P => p.2.1) measurable_snd.fst d
  intro b
  by_cases hb : b < m
  · simp only [d, indexedCutDensity, dite_eq_left hb]
    have hi : Measurable (fun p : P => p.1 ⟨b, hb⟩) :=
      (measurable_pi_apply (⟨b, hb⟩ : Fin m)).comp measurable_fst
    apply Measurable.ite _ measurable_const measurable_const
    exact (measurableSet_eq_fun hi.fst measurable_const).compl.inter
      ((measurableSet_eq_fun hi.fst measurable_const).compl.inter
        ((measurableSet_lt hi.snd.fst measurable_snd.snd).inter
          (measurableSet_lt measurable_snd.snd hi.snd.snd)))
  · simp only [d, indexedCutDensity, dite_eq_right hb]
    exact measurable_const

theorem attachmentTargetRate_joint_measurable (N : ℕ) (c : Finset (Fin N)) :
    Measurable (fun p : Tree N × ℝ => attachmentTargetRate p.1 p.2 c) := by
  classical
  apply measurable_prod_sigma_of_fibers
  intro m
  let P := (Fin m → Branch N) × ℝ
  have hA := activeBranchesFiber_measurable N m
  have hsum : Measurable (fun p : P => ∑ i : Fin m,
      if i ∈ activeBranches ⟨m, p.1⟩ p.2 ∧ (p.1 i).1 = c then (1 : ℝ) else 0) := by
    apply Finset.measurable_sum
    intro i _
    apply Measurable.ite _ measurable_const measurable_const
    have hmem : MeasurableSet {p : P | i ∈ activeBranches ⟨m, p.1⟩ p.2} :=
      (show MeasurableSet {a : Finset (Fin m) | i ∈ a} from .of_discrete).preimage hA
    exact hmem.inter (measurableSet_eq_fun
      ((measurable_pi_apply i).comp measurable_fst).fst measurable_const)
  have hcard : Measurable (fun p : P =>
      (((activeBranches ⟨m, p.1⟩ p.2).filter (fun i => (p.1 i).1 = c)).card : ℝ)) := by
    convert hsum using 1
    funext p
    rw [Finset.card_eq_sum_ones, Nat.cast_sum]
    simp only [Nat.cast_one]
    symm
    rw [← Finset.sum_filter]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact measurable_const.piecewise
    (measurableSet_le ((rootHeightFiber_measurable N m).comp measurable_fst) measurable_snd)
    hcard

end Rhone.Coalescent.SmcPrime
