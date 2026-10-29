/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeTimeVaryingWitness
public import Rhone.Statistics.Identifiability.DelayedOnsetPrefixes

/-! # One-mark exposure positivity for the three-sample first/root witness -/

@[expose] public section

noncomputable section
open Set Matrix MeasureTheory
open scoped BigOperators Topology Matrix Matrix.Norms.Operator
namespace Rhone.Statistics.Identifiability.ThreeTimeVarying

lemma productGenerator_metzler (k : ℕ) (c : ℝ) {q : ℝ} (hq : 0 ≤ q)
    (i j : ProductState) (hij : i ≠ j) : 0 ≤ productGenerator k c q i j := by
  by_cases hp : i.1 = j.1
  · have ha : i.2 ≠ j.2 := fun h => hij (Prod.ext hp h)
    simpa [productGenerator, productRowGenerator, hp, ha] using
      threeGenerator_metzler k c hq i.2 j.2 ha
  · by_cases ha : i.2 = j.2
    · simpa [productGenerator, productRowGenerator, hp, ha] using
        threeGenerator_metzler k c hq i.1 j.1 hp
    · simp [productGenerator, productRowGenerator, hp, ha]

lemma productGenerator_rows_nonpos (k : ℕ) {c q : ℝ} (hc : 0 ≤ c) (i : ProductState) :
    (∑ j, productGenerator k c q i j) ≤ 0 := by
  have he : (∑ j, productGenerator k c q i j) =
      (∑ j, threeGenerator k c q i.1 j) + (∑ j, threeGenerator k c q i.2 j) := by
    simp [productGenerator, productRowGenerator, Fintype.sum_prod_type,
      Finset.sum_add_distrib, mul_ite, ite_mul]
  rw [he]
  exact add_nonpos (threeGenerator_rows_nonpos k hc i.1) (threeGenerator_rows_nonpos k hc i.2)

lemma exists_contractiveBound (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t) :
    ∃ K : ℝ, 0 ≤ K ∧ HasContractiveBoundOn (fun t => productGenerator k (c t) (q t)) 0 1 K := by
  have hcont := productGenerator_continuous k c q hc hq
  have hmatrix : Continuous (fun t => productGenerator k (c t) (q t)) :=
    continuous_pi fun i => continuous_pi (hcont i)
  obtain ⟨L, hL⟩ := isCompact_Icc.exists_bound_of_continuousOn hmatrix.continuousOn
    (s := Icc (0 : ℝ) 1)
  refine ⟨max L 0, le_max_right _ _, ?_⟩
  apply hasContractiveBoundOn_of_subgenerator _ hcont
    (fun t ht => productGenerator_metzler k (c t) (hqn t ht))
    (fun t ht i => productGenerator_rows_nonpos k (hcn t ht) i) (by norm_num)
  intro t ht
  exact (hL t ht).trans (le_max_left _ _)

lemma zero_migration_output (k : ℕ) (c : ℝ → ℝ) (hc : Continuous c) (t : ℝ) :
    (inhomogeneousTransition (fun u => productGenerator k (c u) 0) 0 t *ᵥ
      witnessVec) (0, 0) = 0 := by
  apply inhomogeneousTransition_mulVec_zero_of_closed _
    (productGenerator_continuous k c (fun _ => 0) hc continuous_const)
    (fun i : ProductState => i = (0, 0)) _ witnessVec _ 0 t (0, 0) rfl
  · intro u i j hi hj
    subst i
    rcases j with ⟨j,b⟩
    fin_cases j <;> fin_cases b <;>
      simp_all [productGenerator, productRowGenerator, threeGenerator,
          MarkovChain.Identifiability.totalMigration]
  · intro i hi
    subst i
    exact witnessVec_initial

theorem witness_positive_near_migration_onset (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t, 0 < t → t < δ → (0 < ∫ u in (0 : ℝ)..t, q u) →
      0 < witness k c q t := by
  obtain ⟨K0, hK0, hb0⟩ := exists_contractiveBound k c (fun _ => 0) hc continuous_const hcn
    (fun _ _ => le_rfl)
  obtain ⟨K1, _, hb1⟩ := exists_contractiveBound k c q hc hq hcn hqn
  let K := max K0 K1
  have hK : 0 ≤ K := hK0.trans (le_max_left _ _)
  let C := fun u => productGenerator k (c u) 0
  have he : C + (fun u => q u • migrationMark k) = fun u => productGenerator k (c u) (q u) := by
    funext u
    simp only [C, Pi.add_apply, productGenerator_affine, zero_smul, add_zero]
  have hCb : HasContractiveBoundOn C 0 1 K :=
    ⟨fun u hu => (hb0.1 u hu).trans (le_max_left _ _), hb0.2⟩
  have hDb : HasContractiveBoundOn (C + fun u => q u • migrationMark k) 0 1 K := by
    rw [he]
    exact ⟨fun u hu => (hb1.1 u hu).trans (le_max_right _ _), hb1.2⟩
  obtain ⟨δ, hδ, hpos⟩ := rowPayoff_positive_near_single_onset C q (migrationMark k)
    (Pi.single (0, 0) 1) witnessVec
    (productGenerator_continuous k c (fun _ => 0) hc continuous_const) hq hqn hK hCb hDb
    (fun t => by simpa only [rowPayoff_single, one_mul] using zero_migration_output k c hc t)
    (by rw [rowPayoff_single, one_mul, migrationMark_witness_initial]; positivity)
  refine ⟨δ, hδ, fun t ht htδ hQ => ?_⟩
  have h := hpos t ht htδ hQ
  rw [rowPayoff_single, one_mul, he, ← witness_eq_product_output k c q hc hq t] at h
  exact h

end Rhone.Statistics.Identifiability.ThreeTimeVarying
