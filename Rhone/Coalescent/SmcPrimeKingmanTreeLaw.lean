/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeKingmanHistoryMeas
public import Rhone.Coalescent.SmcPrimeKingmanGeometry

/-! # Tree-valued initialization law of the SMC′ sampler -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open MeasureTheory

noncomputable def kingmanTreeLaw (N : ℕ) : Measure (Tree N) :=
  (kingmanHistoryLaw N).map (metricTreeFromHistory N)

instance kingmanTreeLaw_probability (N : ℕ) :
    IsProbabilityMeasure (kingmanTreeLaw N) := by
  unfold kingmanTreeLaw
  infer_instance

theorem TreeNormalized_measurable (N : ℕ) :
    MeasurableSet {T : Tree N | TreeNormalized T} := by
  classical
  apply Rhone.Coalescent.SmcSupport.measurableSet_sigma_of_fibers
  intro m
  change MeasurableSet {f : Fin m → Branch N | ∀ i,
    (f i).2.1 ≤ (f i).2.2 ∧
      ((f i).1 = ∅ ∨ (f i).1 = Finset.univ → (f i).2.2 = (f i).2.1)}
  apply Rhone.Coalescent.SmcSupport.measurableSet_forall
  intro i
  have hi : Measurable (fun f : Fin m → Branch N => f i) := measurable_pi_apply i
  have hc : MeasurableSet {f : Fin m → Branch N |
      (f i).1 = ∅ ∨ (f i).1 = Finset.univ} :=
    (measurableSet_eq_fun hi.fst measurable_const).union
      (measurableSet_eq_fun hi.fst measurable_const)
  convert (measurableSet_le hi.snd.fst hi.snd.snd).inter
    (hc.compl.union (measurableSet_eq_fun hi.snd.snd hi.snd.fst)) using 1
  ext f
  simp only [Set.mem_inter_iff, Set.mem_union, Set.mem_compl_iff,
    Set.mem_ofPred_eq, imp_iff_not_or]

theorem kingmanTreeLaw_normalized (N : ℕ) :
    ∀ᵐ T ∂kingmanTreeLaw N, TreeNormalized T := by
  unfold kingmanTreeLaw
  apply (ae_map_iff (metricTreeFromHistory_measurable N).aemeasurable _).mpr
  · exact Filter.Eventually.of_forall (metric_tree_from_history_normalized N)
  · exact (show MeasurableSet {T : Tree N | TreeNormalized T} from
      TreeNormalized_measurable N)

end Rhone.Coalescent.SmcPrime
