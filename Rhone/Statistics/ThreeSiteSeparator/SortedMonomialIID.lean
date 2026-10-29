/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ThreeSiteSeparator.SortedPairSupport
public import Rhone.Statistics.PanIIDRepresentation.PolynomialLaw

/-! # Identification of the sorted law's monomials with the iid polynomial kernel -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory
namespace Rhone.Statistics.ThreeSiteSeparator
open AtomicRank PanIIDRepresentation

lemma sortedPair_monomial_iid (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : ∀ᵐ z ∂μ, z ∈ Icc (0 : ℝ) 1) (p q : ℕ) :
    (∫ z, z.1^p*z.2^q ∂sortedPairLaw μ) =
      ∫ z : RightCube, sortedKernel (Finsupp.single (p,q) 1) z.1 z.2.1 z.2.2
        ∂μ.prod (μ.prod μ) := by
  have hA := unitSquare_power_integrable _ (sortedLowerPair_unit_support μ hμ) p q
  have hB := unitSquare_power_integrable _ (sortedMiddlePair_unit_support μ hμ) p q
  have hiA : Integrable (fun z => (sortedLowerPair z).1^p*(sortedLowerPair z).2^q)
      (μ.prod (μ.prod μ)) := by
    exact (integrable_map_measure (by fun_prop) sortedLowerPair_measurable.aemeasurable).mp hA
  have hiB : Integrable (fun z => (sortedMiddlePair z).1^p*(sortedMiddlePair z).2^q)
      (μ.prod (μ.prod μ)) := by
    exact (integrable_map_measure (by fun_prop) sortedMiddlePair_measurable.aemeasurable).mp hB
  rw [sortedPairLaw_monomial_integral μ hμ]
  have he : (fun z : RightCube => sortedKernel (Finsupp.single (p,q) 1) z.1 z.2.1 z.2.2) =
      fun z => ((sortedLowerPair z).1^p*(sortedLowerPair z).2^q +
        (sortedMiddlePair z).1^p*(sortedMiddlePair z).2^q)/2 := by
    funext z
    simp only [sortedKernel, value_single, one_mul, sortedLowerPair, sortedMiddlePair]
  rw [he, integral_div, integral_add hiA hiB]
  ring

lemma mapped_iid_polynomial (μ : Measure ℝ) [SFinite μ]
    (g : ℝ → ℝ) (hg : Measurable g) (f : Coefficients) :
    (∫ z : RightCube, sortedKernel f z.1 z.2.1 z.2.2 ∂(μ.map g).prod ((μ.map g).prod (μ.map g))) =
      ∫ z : LeftCube, sortedKernel f (g z.1.1) (g z.1.2) (g z.2) ∂(μ.prod μ).prod μ := by
  rw [Measure.map_prod_map μ μ hg hg,
    Measure.map_prod_map μ (μ.prod μ) hg (hg.prodMap hg),
    integral_map (hg.prodMap (hg.prodMap hg)).aemeasurable
      (sortedKernel_continuous f).aestronglyMeasurable]
  exact ((measurePreserving_prodAssoc μ μ μ).integral_comp'
    (fun z : RightCube => sortedKernel f (g z.1) (g z.2.1) (g z.2.2))).symm

end Rhone.Statistics.ThreeSiteSeparator
