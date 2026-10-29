/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.AsymmetricPairDesign.Laplace
public import Rhone.Statistics.PairObservationChannel.Observation
public import Rhone.Statistics.PairObservationChannel.Law

/-! # Finite observation of the asymmetric source through a channel -/

@[expose] public section

open MeasureTheory Set
namespace Rhone.Statistics.AsymmetricPairDesign
open MarkovChain.Identifiability Identifiability PairObservationChannel DependenceBudget

theorem pair_law_positive_support (a b c d : ℝ) (i : Fin 3) :
    ∀ᵐ t ∂pairLaw a b c d i, 0 < t := by
  apply (withDensity_absolutelyContinuous _ _).ae_le
  exact ae_restrict_mem measurableSet_Ioi

theorem laplace_bounds {a b c d k : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) (hk : 0 ≤ k) (i : Fin 3) :
    0 ≤ laplace a b c d k i ∧ laplace a b c d k i ≤ 1 := by
  let : IsProbabilityMeasure (pairLaw a b c d i) := pair_law_probability ha hb hc hd i
  exact pair_laplace_bounds (pairLaw a b c d i) hk
    ((pair_law_positive_support a b c d i).mono (fun _ h => h.le))

noncomputable def reportedPairLaw {K : ℕ} {H : Type*} [Fintype H] (E : Channel K H)
    {a b c d k : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hk : 0 ≤ k) (i : Fin 3) : Law (H × H) :=
  reportedLaw E (laplace a b c d k i) (laplace_bounds ha hb hc hd hk i)

theorem reportedPairLaw_mass {K : ℕ} {H : Type*} [Fintype H] (E : Channel K H)
    {a b c d k : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hk : 0 ≤ k) (i : Fin 3) (x y : H) :
    (reportedPairLaw E ha hb hc hd hk i).mass (x, y) =
      observedMass E (pairLaw a b c d i) k x y := by
  let : IsProbabilityMeasure (pairLaw a b c d i) := pair_law_probability ha hb hc hd i
  exact (observed_mass_formula E (pairLaw a b c d i) hk
    ((pair_law_positive_support a b c d i).mono (fun _ h => h.le)) x y).symm

end Rhone.Statistics.AsymmetricPairDesign
