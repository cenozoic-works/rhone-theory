/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.Inbreeding
public import Rhone.Dynamics.Inbreeding
public import Rhone.MarkovChain.EffectiveSize
public import Mathlib.Algebra.Order.Field.Rat

/-!
# Scalar inbreeding evaluators equal the existing specification

Source: wright1931, pp. 108–110; felsenstein1971, pp. 584–585. -/
@[expose] public section
namespace Rhone.Computation.Inbreeding
lemma partialStep_cast (s F : Rat) :
    (partialStep s F : Real) = Rhone.Dynamics.Inbreeding.partialSelfingStep s F := by
  simp [partialStep, Rhone.Dynamics.Inbreeding.partialSelfingStep]
lemma partialFixed_cast (s : Rat) :
    (partialFixed s : Real) = Rhone.Dynamics.Inbreeding.partialSelfingFixed s := by
  simp [partialFixed, Rhone.Dynamics.Inbreeding.partialSelfingFixed]
lemma fullSibStep_cast (z : Rat × Rat) :
    (((fullSibStep z).1 : Real), ((fullSibStep z).2 : Real)) =
      Rhone.Dynamics.Inbreeding.fullSibStep ((z.1 : Real), (z.2 : Real)) := by
  simp [fullSibStep, Rhone.Dynamics.Inbreeding.fullSibStep]
lemma consecutiveEffective_eq (F0 F1 : Rat) (h : 0 ≤ F0 ∧ F0 < F1 ∧ F1 ≤ 1) :
    ∃ v : Rat, consecutiveEffective F0 F1 = some v ∧
      (v : Real) = Rhone.MarkovChain.EffectiveSize.inbreedingEffective F0 F1 := by
  refine ⟨1 / (2 * ((F1 - F0) / (1 - F0))),
    by simp [consecutiveEffective, h], ?_⟩
  simp [Rhone.MarkovChain.EffectiveSize.inbreedingEffective,
    Rhone.MarkovChain.EffectiveSize.coalescenceEffective]

lemma partialOrbit_cast (s F0 : Rat) (n : Nat) :
    (partialOrbit s F0 n : Real) =
      ((Rhone.Dynamics.Inbreeding.partialSelfingStep (s : Real))^[n]) F0 := by
  induction n with
  | zero => simp [partialOrbit]
  | succ n ih => simp [partialOrbit, partialStep_cast, ih, Function.iterate_succ_apply']
lemma fullSibOrbit_cast (z : Rat × Rat) (n : Nat) :
    (((fullSibOrbit z n).1 : Real), ((fullSibOrbit z n).2 : Real)) =
      (Rhone.Dynamics.Inbreeding.fullSibStep^[n]) ((z.1 : Real), (z.2 : Real)) := by
  induction n with
  | zero => simp [fullSibOrbit]
  | succ n ih => simp [fullSibOrbit, fullSibStep_cast, ih, Function.iterate_succ_apply']
lemma partialFixed_fixed (s : Rat) (h : 2 - s ≠ 0) :
    partialStep s (partialFixed s) = partialFixed s := by
  unfold partialStep partialFixed
  field_simp
  ring
lemma fullSib_fixed : fullSibStep (1, 1) = (1, 1) := by
  norm_num [fullSibStep]
lemma consecutiveEffective_none (F0 F1 : Rat) :
    consecutiveEffective F0 F1 = none ↔ ¬ (0 ≤ F0 ∧ F0 < F1 ∧ F1 ≤ 1) := by
  unfold consecutiveEffective
  split_ifs <;> simp_all

lemma consecutiveEffective_recursion (F0 c : Rat) (hF0 : 0 ≤ F0) (hF1 : F0 < 1)
    (hc : 0 < c) (hc1 : c ≤ 1) :
    ∃ v : Rat, consecutiveEffective F0 (c + (1 - c) * F0) = some v ∧
      (v : Real) = Rhone.MarkovChain.EffectiveSize.coalescenceEffective c := by
  have hvalid : 0 ≤ F0 ∧ F0 < c + (1 - c) * F0 ∧ c + (1 - c) * F0 ≤ 1 := by
    constructor
    · exact hF0
    constructor <;> nlinarith
  obtain ⟨v, hv, he⟩ := consecutiveEffective_eq F0 (c + (1 - c) * F0) hvalid
  refine ⟨v, hv, he.trans ?_⟩
  apply Rhone.MarkovChain.EffectiveSize.inbreeding_effective_recursion
  · exact ne_of_lt (show (F0 : Real) < 1 by exact_mod_cast hF1)
  · exact ne_of_gt (show (0 : Real) < c by exact_mod_cast hc)
  · push_cast
    rfl

lemma partialOrbit_tendsto (s F0 : Rat) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    Filter.Tendsto (fun n => (partialOrbit s F0 n : Real)) Filter.atTop
      (nhds (partialFixed s : Real)) := by
  simpa only [partialOrbit_cast, partialFixed_cast] using
    Rhone.Dynamics.Inbreeding.tendsto_partial_selfing
      (show (0 : Real) ≤ s by exact_mod_cast hs0)
      (show (s : Real) ≤ 1 by exact_mod_cast hs1) (F0 : Real)

lemma fullSibOrbit_tendsto (z : Rat × Rat) :
    Filter.Tendsto (fun n => (((fullSibOrbit z n).1 : Real), ((fullSibOrbit z n).2 : Real)))
      Filter.atTop (nhds (1, 1)) := by
  simpa only [fullSibOrbit_cast] using
    Rhone.Dynamics.Inbreeding.tendsto_full_sib ((z.1 : Real), (z.2 : Real))

end Rhone.Computation.Inbreeding
