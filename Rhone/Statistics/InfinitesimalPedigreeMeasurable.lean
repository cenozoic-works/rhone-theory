/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Statistics.InfinitesimalPedigreeProjectedMoments
/-!
# Measurability of pedigree residuals

Source: barton_etheridge_veber2017, sec. 3.1. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Rhone.Statistics Rhone.Combinatorics
namespace Rhone.Statistics
theorem inherited_effect_measurable {n : Nat} (m : Real) (k : (Fin n → Bool) → Fin n) :
    Measurable (fun ω : (Fin n → Real) × (Fin n → Bool) => ω.1 (k ω.2) - m) := by
  classical
  have hs (a : Fin n) : MeasurableSet {ω : (Fin n → Real) × (Fin n → Bool) | k ω.2 = a} := by
    exact (MeasurableSet.singleton a).preimage ((measurable_of_countable k).comp measurable_snd)
  have hi (a : Fin n) : Measurable (fun ω : (Fin n → Real) × (Fin n → Bool) => ω.1 a - m) :=
    ((measurable_pi_apply a).comp measurable_fst).sub measurable_const
  have hm : Measurable (fun ω : (Fin n → Real) × (Fin n → Bool) =>
      ∑ a : Fin n, Set.indicator {ω : (Fin n → Real) × (Fin n → Bool) | k ω.2 = a}
        (fun ω => ω.1 a - m) ω) :=
    Finset.measurable_sum Finset.univ (fun a _ => (hi a).indicator (hs a))
  convert hm using 1
  funext ω
  simp [Set.indicator]

theorem locus_residual_measurable {n : Nat} (P : Pedigree n) (m : Real) (i : Fin n) :
    Measurable (fun ω : (Fin n → Real) × (Fin n → Bool) =>
      locusSegregationResidual P m ω.1 ω.2 i) := by
  have hy (j : Fin n) := inherited_effect_measurable m (fun c => geneFounder P c j)
  cases hp : P.parents i with
  | none =>
    simpa only [locusSegregationResidual, segregationResidual, hp, locusTraitDeviation] using hy i
  | some parents =>
    have h := (hy i).sub (((hy parents.1).add (hy parents.2)).div_const 2)
    convert h using 1
    funext ω
    simp only [locusSegregationResidual, segregationResidual, hp, locusTraitDeviation,
      Pi.sub_apply, Pi.add_apply]

theorem locus_projection_measurable {n : Nat} (P : Pedigree n) (m : Real) (t : Fin n → Real) :
    Measurable (locusResidualProjection P m t) := by
  exact Finset.measurable_sum Finset.univ (fun i _ =>
    (locus_residual_measurable P m i).const_mul (t i))
end Rhone.Statistics
