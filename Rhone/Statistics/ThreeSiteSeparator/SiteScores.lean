/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ThreeSiteSeparator.TripleScoreMean
public import Rhone.Statistics.ThreeSiteSeparator.ObservableBounds
public import Rhone.Statistics.SingleSiteChannel.Formula

/-! # Identification of the explicit score means with the mutation channel -/

@[expose] public section

noncomputable section
open scoped BigOperators
namespace Rhone.Statistics.ThreeSiteSeparator
open ThreeTipSites SingleSiteChannel

lemma site_patternMass {K : ℕ} (hK : 0 < K) (k : ℝ) (t : ℝ × ℝ)
    (a b c : Fin K) :
    site K (fun _ => 1/(K : ℝ)) k t (a,b,c) =
      patternMass K (Real.exp (-k*t.1)) (Real.exp (-k*(t.1+t.2)))
        (secondMomentKernel k t) a b c := by
  rw [site_expansion hK]
  rfl

lemma pair_score_means {K : ℕ} (hK : 2 ≤ K) (k : ℝ) (t : ℝ × ℝ) :
    (∑ x : Triple K, pairScore K x.1 x.2.1*site K (fun _ => 1/(K : ℝ)) k t x) =
      Real.exp (-k*t.1) ∧
    (∑ x : Triple K, pairScore K x.1 x.2.2*site K (fun _ => 1/(K : ℝ)) k t x) =
      Real.exp (-k*(t.1+t.2)) ∧
    (∑ x : Triple K, pairScore K x.2.1 x.2.2*site K (fun _ => 1/(K : ℝ)) k t x) =
      Real.exp (-k*(t.1+t.2)) := by
  have hp : 0 < K := lt_of_lt_of_le (by decide : 0 < 2) hK
  simp only [Fintype.sum_prod_type]
  simp_rw [site_patternMass hp]
  exact ⟨pairScore_mean hK _ _ _, pairScore_noncherry_mean hK _ _ _, pairScore_other_mean hK _ _ _⟩

lemma triple_score_mean {K : ℕ} (hK : 3 ≤ K) (k : ℝ) (t : ℝ × ℝ) :
    (∑ x : Triple K, tripleScore K x.1 x.2.1 x.2.2*
      site K (fun _ => 1/(K : ℝ)) k t x) = secondMomentKernel k t := by
  have hp : 0 < K := lt_of_lt_of_le (by decide : 0 < 3) hK
  simp only [Fintype.sum_prod_type]
  simp_rw [site_patternMass hp]
  exact tripleScore_mean hK _ _ _

lemma fixedTopology_product_scores {K L : ℕ} (π : Roots K L) (k : ℝ) (t : ℝ × ℝ)
    (q : Fin 3) (f : Fin L → Triple K → ℝ) :
    (∑ x : Panel K L, (∏ s, f s (x s))*fixedTopology π k t q x) =
      ∏ s, ∑ y : Triple K, f s y*site K (π.weight s) k t (orientation K q y) := by
  simp only [fixedTopology, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun (s : Fin L) (y : Triple K) =>
    f s y*site K (π.weight s) k t (orientation K q y))).symm

lemma conditional_product_scores {K L : ℕ} (π : Roots K L) (k : ℝ) (t : ℝ × ℝ)
    (f : Fin L → Triple K → ℝ) :
    (∑ x : Panel K L, (∏ s, f s (x s))*conditional π k t x) =
      (1/3 : ℝ)*∑ q : Fin 3,
        ∏ s, ∑ y : Triple K, f s y*site K (π.weight s) k t (orientation K q y) := by
  have he (x : Panel K L) :
      (∏ s, f s (x s))*conditional π k t x =
        (1/3 : ℝ)*∑ q : Fin 3, (∏ s, f s (x s))*fixedTopology π k t q x := by
    unfold conditional
    rw [← Finset.mul_sum]
    ring
  simp_rw [he]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp_rw [fixedTopology_product_scores]

end Rhone.Statistics.ThreeSiteSeparator
