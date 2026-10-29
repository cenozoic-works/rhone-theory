/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.WrightFisherAllocation
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv

/-! # Independent draws into finitely many cells have multinomial counts -/

@[expose] public section

namespace Rhone.MarkovChain

open Finset MvPolynomial MeasureTheory
open scoped ENNReal

theorem sum_single_eq_allocationCounts (N K : ℕ) (ω : Fin N → Fin K) :
    (∑ t : Fin N, Finsupp.single (ω t) 1) =
      Finsupp.equivFunOnFinite.symm (wfAlleleAllocationCounts N K ω).val := by
  ext l
  simp only [Finsupp.finsetSum_apply, Finsupp.single_apply, Finsupp.coe_equivFunOnFinite_symm]
  rw [wfAlleleAllocationCounts_apply, Finset.card_eq_sum_ones, Finset.sum_filter]

theorem sum_allocation_prod_eq_multinomial {R : Type*} [CommSemiring R] (N K : ℕ)
    (p : Fin K → R) (b : AlleleCounts N K) :
    (∑ ω : Fin N → Fin K,
      if wfAlleleAllocationCounts N K ω = b then ∏ t, p (ω t) else 0) =
      (Nat.multinomial (Finset.univ : Finset (Fin K)) b.val : R) * ∏ l, p l ^ b.val l := by
  classical
  let d : Fin K →₀ ℕ := Finsupp.equivFunOnFinite.symm b.val
  have hd : d.sum (fun _ m => m) = N := by
    rw [d.sum_fintype (fun _ m => m) (by simp)]
    exact b.sum
  have heq (ω : Fin N → Fin K) :
      (∑ t : Fin N, Finsupp.single (ω t) 1) = d ↔ wfAlleleAllocationCounts N K ω = b := by
    rw [sum_single_eq_allocationCounts]
    constructor
    · intro h
      apply Subtype.ext
      exact congrArg (fun x : Fin K →₀ ℕ => (x : Fin K → ℕ)) h
    · intro h
      rw [h]
  have hterm (ω : Fin N → Fin K) :
      (∏ t : Fin N, p (ω t) • (X (ω t) : MvPolynomial (Fin K) R)).coeff d =
        if wfAlleleAllocationCounts N K ω = b then ∏ t, p (ω t) else 0 := by
    have hm := monomial_sum_prod (R := R) Finset.univ
      (fun t : Fin N => Finsupp.single (ω t) 1) (fun t => p (ω t))
    have hp : (∏ t : Fin N, p (ω t) • (X (ω t) : MvPolynomial (Fin K) R)) =
        monomial (∑ t : Fin N, Finsupp.single (ω t) 1) (∏ t, p (ω t)) := by
      simpa [X, smul_monomial, smul_eq_mul] using hm.symm
    simp only [hp, MvPolynomial.coeff_monomial, heq]
  have hc : ((∑ l : Fin K, p l • (X l : MvPolynomial (Fin K) R)) ^ N).coeff d =
      (Nat.multinomial (Finset.univ : Finset (Fin K)) b.val : R) * ∏ l, p l ^ b.val l := by
    rw [coeff_linearCombination_X_pow_of_fintype, ite_eq_left hd,
      Finsupp.multinomial_eq_of_support_subset (Finset.subset_univ d.support),
      d.prod_fintype (fun l m => p l ^ m) (by simp)]
    rfl
  have hexp := Fintype.sum_pow (fun l : Fin K => p l • (X l : MvPolynomial (Fin K) R)) N
  have he := congrArg (fun q : MvPolynomial (Fin K) R => q.coeff d) hexp
  rw [MvPolynomial.coeff_sum] at he
  calc
    _ = ∑ ω : Fin N → Fin K,
        (∏ t : Fin N, p (ω t) • (X (ω t) : MvPolynomial (Fin K) R)).coeff d :=
      Finset.sum_congr rfl fun ω _ => (hterm ω).symm
    _ = _ := he.symm.trans hc

theorem pi_allocationCounts {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]
    (N K : ℕ) {g : Ω → Fin K} (hg : Measurable g) (b : AlleleCounts N K) :
    Measure.pi (fun _ : Fin N => μ)
        {y | wfAlleleAllocationCounts N K (fun t => g (y t)) = b} =
      (Nat.multinomial (Finset.univ : Finset (Fin K)) b.val : ℝ≥0∞) *
        ∏ l, μ (g ⁻¹' {l}) ^ b.val l := by
  classical
  have hset : {y : Fin N → Ω | wfAlleleAllocationCounts N K (fun t => g (y t)) = b} =
      ⋃ ω ∈ (Finset.univ.filter fun ω : Fin N → Fin K => wfAlleleAllocationCounts N K ω = b),
        Set.pi Set.univ fun t => g ⁻¹' {ω t} := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and,
      Set.mem_pi, Set.mem_univ, Set.mem_preimage, Set.mem_singleton_iff, forall_const,
      exists_prop]
    constructor
    · intro h
      exact ⟨fun t => g (y t), h, fun t => rfl⟩
    · rintro ⟨ω, hω, hy⟩
      have hfun : (fun t => g (y t)) = ω := funext hy
      rw [hfun]
      exact hω
  rw [hset, measure_biUnion_finset]
  · simp only [Measure.pi_pi]
    rw [Finset.sum_filter]
    exact sum_allocation_prod_eq_multinomial N K (fun l => μ (g ⁻¹' {l})) b
  · intro ω _ ω' _ hne
    obtain ⟨t, ht⟩ := Function.ne_iff.1 hne
    refine Set.disjoint_left.2 fun y hy hy' => ht ?_
    have h1 := hy t (Set.mem_univ t)
    have h2 := hy' t (Set.mem_univ t)
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at h1 h2
    exact h1.symm.trans h2
  · intro ω _
    exact MeasurableSet.univ_pi fun t => hg (measurableSet_singleton _)

theorem pi_card_mem {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ] (N : ℕ)
    {A : Set Ω} [DecidablePred (· ∈ A)] (hA : MeasurableSet A) (j : ℕ) :
    Measure.pi (fun _ : Fin N => μ) {y | (Finset.univ.filter fun t => y t ∈ A).card = j} =
      (N.choose j : ℝ≥0∞) * μ A ^ j * μ Aᶜ ^ (N - j) := by
  by_cases hj : j ≤ N
  · let g : Ω → Fin 2 := fun ω => if ω ∈ A then 0 else 1
    have hg : Measurable g := Measurable.ite hA measurable_const measurable_const
    have hmem : (![j, N - j] : Fin 2 → ℕ) ∈ Finset.piAntidiag (Finset.univ : Finset (Fin 2)) N :=
      Finset.mem_piAntidiag.2 ⟨by simp [Fin.sum_univ_two]; omega, by simp⟩
    let b : AlleleCounts N 2 := ⟨![j, N - j], hmem⟩
    have hzero : ∀ y : Fin N → Ω,
        (wfAlleleAllocationCounts N 2 (fun t => g (y t))).val 0 =
          (Finset.univ.filter fun t => y t ∈ A).card := by
      intro y
      rw [wfAlleleAllocationCounts_apply]
      congr 1
      ext t
      by_cases h : y t ∈ A <;> simp [g, h]
    have hset : {y : Fin N → Ω | (Finset.univ.filter fun t => y t ∈ A).card = j} =
        {y | wfAlleleAllocationCounts N 2 (fun t => g (y t)) = b} := by
      ext y
      simp only [Set.mem_ofPred_eq]
      constructor
      · intro h
        have h0 : (wfAlleleAllocationCounts N 2 (fun t => g (y t))).val 0 = j :=
          (hzero y).trans h
        have hsum := (wfAlleleAllocationCounts N 2 (fun t => g (y t))).sum
        rw [Fin.sum_univ_two] at hsum
        apply Subtype.ext
        funext l
        fin_cases l
        · exact h0
        · change (wfAlleleAllocationCounts N 2 (fun t => g (y t))).val 1 = N - j
          omega
      · intro h
        rw [← hzero y, h]
        rfl
    have hpre0 : g ⁻¹' {0} = A := by
      ext ω
      by_cases h : ω ∈ A <;> simp [g, h]
    have hpre1 : g ⁻¹' {1} = Aᶜ := by
      ext ω
      by_cases h : ω ∈ A <;> simp [g, h]
    have hmult : Nat.multinomial (Finset.univ : Finset (Fin 2)) b.val = N.choose j := by
      change Nat.multinomial (Finset.univ : Finset (Fin 2)) ![j, N - j] = N.choose j
      rw [Nat.multinomial_univ_two, Nat.add_sub_cancel' hj,
        Nat.choose_eq_factorial_div_factorial hj]
    rw [hset, pi_allocationCounts μ N 2 hg b, hmult, Fin.prod_univ_two, hpre0, hpre1, mul_assoc]
    rfl
  · have hempty : {y : Fin N → Ω | (Finset.univ.filter fun t => y t ∈ A).card = j} = ∅ := by
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      have hle := Finset.card_filter_le (Finset.univ : Finset (Fin N)) fun t => y t ∈ A
      rw [Finset.card_univ, Fintype.card_fin] at hle
      omega
    rw [hempty, measure_empty, Nat.choose_eq_zero_of_lt (not_le.1 hj)]
    simp

theorem sum_multinomial_of_apply_eq_zero {R : Type*} [CommSemiring R] (N K : ℕ) (p : Fin K → R)
    (l₀ : Fin K) :
    (∑ b : AlleleCounts N K,
      if b.val l₀ = 0 then
        (Nat.multinomial (Finset.univ : Finset (Fin K)) b.val : R) * ∏ l, p l ^ b.val l
      else 0) = (∑ l ∈ Finset.univ.erase l₀, p l) ^ N := by
  have h := Finset.sum_pow_eq_sum_piAntidiag (Finset.univ : Finset (Fin K))
    (Function.update p l₀ 0) N
  rw [← Finset.sum_coe_sort (Finset.piAntidiag (Finset.univ : Finset (Fin K)) N)] at h
  have hsum : ∑ l, Function.update p l₀ 0 l = ∑ l ∈ Finset.univ.erase l₀, p l := by
    rw [Finset.sum_update_of_mem (Finset.mem_univ l₀), zero_add, Finset.sdiff_singleton_eq_erase]
  rw [← hsum, h]
  refine Finset.sum_congr rfl fun b _ => ?_
  split_ifs with hb
  · congr 1
    refine Finset.prod_congr rfl fun l _ => ?_
    by_cases hl : l = l₀
    · rw [hl, hb, pow_zero, pow_zero]
    · rw [Function.update_of_ne hl]
  · rw [Finset.prod_eq_zero (Finset.mem_univ l₀), mul_zero]
    rw [Function.update_self, zero_pow hb]

theorem cond_pi {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (N : ℕ)
    {A : Set Ω} (hA : MeasurableSet A) (h0 : μ A ≠ 0) :
    ProbabilityTheory.cond (Measure.pi fun _ : Fin N => μ) (Set.pi Set.univ fun _ => A) =
      Measure.pi fun _ : Fin N => ProbabilityTheory.cond μ A := by
  have := ProbabilityTheory.cond_isProbabilityMeasure h0
  symm
  refine Measure.pi_eq fun s _ => ?_
  rw [ProbabilityTheory.cond_apply (MeasurableSet.univ_pi fun _ => hA), ← Set.pi_inter_distrib,
    Measure.pi_pi, Measure.pi_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ENNReal.inv_pow]
  simp only [ProbabilityTheory.cond_apply hA]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem card_alleleCounts (N K : ℕ) : Fintype.card (AlleleCounts N K) = (K + N - 1).choose N := by
  have h := Finset.card_finsuppAntidiag_nat_eq_choose (s := (Finset.univ : Finset (Fin K))) N
  rw [Finset.card_univ, Fintype.card_fin] at h
  rw [Fintype.card_coe, ← h]
  refine Finset.card_bij' (fun f _ => Finsupp.equivFunOnFinite.symm f) (fun g _ => ⇑g)
    ?_ ?_ ?_ ?_
  · intro f hf
    simpa [Finset.mem_piAntidiag] using hf
  · intro g hg
    simpa [Finset.mem_piAntidiag] using hg
  · intro f _
    rfl
  · intro g _
    ext l
    rfl

end Rhone.MarkovChain
