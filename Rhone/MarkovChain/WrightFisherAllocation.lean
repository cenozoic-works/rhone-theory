/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.WrightFisherMultiallele
public import Mathlib.Algebra.MvPolynomial.Coeff

/-!
# Independent offspring allocations give the multinomial law

Source: ewens2004, sec. 3.5; cannings1974, sec. 3.1, pp. 268–269. -/

@[expose] public section
namespace Rhone.MarkovChain

open Finset MvPolynomial

/-- Source: cannings1974, sec. 3.1. -/
private theorem allocation_finsupp (N K : ℕ) (ω : Fin N → Fin K) :
    (∑ t : Fin N, Finsupp.single (ω t) 1) =
      Finsupp.equivFunOnFinite.symm (wfAlleleAllocationCounts N K ω).val := by
  ext l
  simp only [Finsupp.finsetSum_apply, Finsupp.single_apply,
    Finsupp.coe_equivFunOnFinite_symm]
  rw [wfAlleleAllocationCounts_apply, Finset.card_eq_sum_ones, Finset.sum_filter]

/-- Source: ewens2004, sec. 3.5; cannings1974, sec. 3.1, pp. 268–269. -/
theorem wfMultiallele_allocation_law (N K : ℕ) (a b : AlleleCounts N K) :
    (∑ ω : Fin N → Fin K,
      if wfAlleleAllocationCounts N K ω = b
      then wfMultialleleAllocationWeight N K a ω else 0) =
      wfMultiallele N K a b := by
  classical
  let d : Fin K →₀ ℕ := Finsupp.equivFunOnFinite.symm b.val
  have hd : d.sum (fun _ m => m) = N := by
    rw [d.sum_fintype (fun _ m => m) (by simp)]
    exact b.sum
  have heq (ω : Fin N → Fin K) :
      (∑ t : Fin N, Finsupp.single (ω t) 1) = d ↔
        wfAlleleAllocationCounts N K ω = b := by
    rw [allocation_finsupp]
    constructor
    · intro h
      apply Subtype.ext
      exact congrArg (fun x : Fin K →₀ ℕ => (x : Fin K → ℕ)) h
    · intro h
      rw [h]
  have hterm (ω : Fin N → Fin K) :
      (∏ t : Fin N, ((a.val (ω t) : ℝ) / N) •
        (X (ω t) : MvPolynomial (Fin K) ℝ)).coeff d =
        if wfAlleleAllocationCounts N K ω = b
        then wfMultialleleAllocationWeight N K a ω else 0 := by
    have hm := monomial_sum_prod (R := ℝ) Finset.univ
      (fun t : Fin N => Finsupp.single (ω t) 1)
      (fun t => (a.val (ω t) : ℝ) / N)
    have hp : (∏ t : Fin N, ((a.val (ω t) : ℝ) / N) • X (ω t)) =
        monomial (∑ t : Fin N, Finsupp.single (ω t) 1)
          (wfMultialleleAllocationWeight N K a ω) := by
      simpa [X, smul_monomial, smul_eq_mul, wfMultialleleAllocationWeight] using hm.symm
    simp only [hp, MvPolynomial.coeff_monomial, heq]
  have hc : ((∑ l : Fin K, ((a.val l : ℝ) / N) •
        (X l : MvPolynomial (Fin K) ℝ)) ^ N).coeff d =
      wfMultiallele N K a b := by
    rw [coeff_linearCombination_X_pow_of_fintype, ite_eq_left hd]
    rw [Finsupp.multinomial_eq_of_support_subset (Finset.subset_univ d.support)]
    rw [d.prod_fintype (fun l m => ((a.val l : ℝ) / N) ^ m) (by simp)]
    rfl
  have hexp := Fintype.sum_pow
    (fun l : Fin K => ((a.val l : ℝ) / N) • (X l : MvPolynomial (Fin K) ℝ)) N
  have he := congrArg (fun p : MvPolynomial (Fin K) ℝ => p.coeff d) hexp
  rw [MvPolynomial.coeff_sum] at he
  calc
    _ = ∑ ω : Fin N → Fin K,
        (∏ t : Fin N, ((a.val (ω t) : ℝ) / N) •
          (X (ω t) : MvPolynomial (Fin K) ℝ)).coeff d := by
      apply Finset.sum_congr rfl
      intro ω _
      exact (hterm ω).symm
    _ = _ := he.symm.trans hc

namespace WrightFisherAllocationSupport

/-- Source: ewens2004, sec. 3.5. -/
theorem expect (N K : ℕ) (a : AlleleCounts N K)
    (f : AlleleCounts N K → ℝ) :
    (∑ b, wfMultiallele N K a b * f b) =
      ∑ ω : Fin N → Fin K,
        wfMultialleleAllocationWeight N K a ω * f (wfAlleleAllocationCounts N K ω) := by
  classical
  simp_rw [← wfMultiallele_allocation_law, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  simp [ite_mul]

end WrightFisherAllocationSupport

end Rhone.MarkovChain
