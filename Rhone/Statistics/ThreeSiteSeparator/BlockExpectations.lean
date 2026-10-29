/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ThreeSiteSeparator.ScoreSymmetry

/-! # Finite-block expectation algebra with one topology shared by all sites -/

@[expose] public section

noncomputable section
open scoped BigOperators
namespace Rhone.Statistics.ThreeSiteSeparator
open ThreeTipSites SingleSiteChannel

def uniformBlockRoots (K L : ℕ) (hK : 0 < K) : Roots K L where
  weight := fun _ _ => 1/(K : ℝ)
  nonneg := fun _ _ => by positivity
  normalized := fun _ => Identifiability.EqualRatesMutation.uniform_weights_sum hK

def fixedMean {K : ℕ} (π : Roots K 3) (k : ℝ) (t : ℝ × ℝ)
    (q : Fin 3) (f : Panel K 3 → ℝ) : ℝ :=
  ∑ x, f x*fixedTopology π k t q x

def threeProduct {K : ℕ} (f g h : Triple K → ℝ) (x : Panel K 3) : ℝ :=
  f (x 0)*g (x 1)*h (x 2)

lemma fixedMean_add {K : ℕ} (π : Roots K 3) (k : ℝ) (t : ℝ × ℝ)
    (q : Fin 3) (f g : Panel K 3 → ℝ) :
    fixedMean π k t q (fun x => f x + g x) = fixedMean π k t q f + fixedMean π k t q g := by
  simp only [fixedMean, add_mul, Finset.sum_add_distrib]

lemma fixedMean_div {K : ℕ} (π : Roots K 3) (k : ℝ) (t : ℝ × ℝ)
    (q : Fin 3) (f : Panel K 3 → ℝ) (c : ℝ) :
    fixedMean π k t q (fun x => f x/c) = fixedMean π k t q f/c := by
  simp only [fixedMean, div_mul_eq_mul_div, ← Finset.sum_div]

lemma fixedMean_sum {K : ℕ} {ι : Type*} [Fintype ι] (π : Roots K 3)
    (k : ℝ) (t : ℝ × ℝ) (q : Fin 3) (f : ι → Panel K 3 → ℝ) :
    fixedMean π k t q (fun x => ∑ i, f i x) = ∑ i, fixedMean π k t q (f i) := by
  simp only [fixedMean, Finset.sum_mul]
  rw [Finset.sum_comm]

lemma threeProduct_mean {K : ℕ} (hK : 0 < K) (k : ℝ) (t : ℝ × ℝ)
    (q : Fin 3) (f g h : Triple K → ℝ) :
    fixedMean (uniformBlockRoots K 3 hK) k t q (threeProduct f g h) =
      (∑ x, f x*site K (fun _ => 1/(K : ℝ)) k t (orientation K q x))*
      (∑ x, g x*site K (fun _ => 1/(K : ℝ)) k t (orientation K q x))*
      (∑ x, h x*site K (fun _ => 1/(K : ℝ)) k t (orientation K q x)) := by
  have he := fixedTopology_product_scores (uniformBlockRoots K 3 hK) k t q
    (![f,g,h] : Fin 3 → Triple K → ℝ)
  simpa [fixedMean, threeProduct, uniformBlockRoots, Fin.prod_univ_three] using he

lemma oriented_one_mean {K : ℕ} (hK : 0 < K) (k : ℝ) (t : ℝ × ℝ) (q : Fin 3) :
    (∑ x : Triple K, (1 : ℝ)*site K (fun _ => 1/(K : ℝ)) k t (orientation K q x)) = 1 := by
  simp only [one_mul]
  rw [Equiv.sum_comp (orientation K q)]
  exact site_sum hK _ (Identifiability.EqualRatesMutation.uniform_weights_sum hK) k t

end Rhone.Statistics.ThreeSiteSeparator
