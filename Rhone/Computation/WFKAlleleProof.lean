/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.WFKAllele
public import Rhone.MarkovChain.WrightFisherMultiallele
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Rat.Cast.Lemmas

/-!
# Executable K-allele Wright-Fisher probability equals the specification

Source: cannings1974, sec. 3.1, pp. 268–269; ewens2004, sec. 3.5. -/

@[expose] public section
namespace Rhone.Computation.WFKAllele
open Finset

theorem fact_eq (n : Nat) : fact n = n.factorial := by
  induction n with
  | zero => rfl
  | succ n ih => rw [fact, ih, Nat.factorial_succ]

theorem sumNat_eq (f : Nat → Nat) (n : Nat) : sumNat f n = ∑ i ∈ range n, f i := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumNat, ih, Finset.sum_range_succ]

theorem prodNat_eq (f : Nat → Nat) (n : Nat) : prodNat f n = ∏ i ∈ range n, f i := by
  induction n with
  | zero => rfl
  | succ n ih => rw [prodNat, ih, Finset.prod_range_succ]

theorem cast_prodRat (f : Nat → Rat) (n : Nat) :
    ((prodRat f n : Rat) : ℝ) = ∏ i ∈ range n, ((f i : Rat) : ℝ) := by
  induction n with
  | zero => simp [prodRat]
  | succ n ih => rw [prodRat, Rat.cast_mul, ih, Finset.prod_range_succ]

def extend {N K : Nat} (a : Rhone.MarkovChain.AlleleCounts N K) : Nat → Nat :=
  fun i => if h : i < K then a.val ⟨i, h⟩ else 0

theorem multinomial_eq {N K : Nat} (b : Rhone.MarkovChain.AlleleCounts N K) :
    multinomial K (extend b) = Nat.multinomial (Finset.univ : Finset (Fin K)) b.val := by
  unfold multinomial Nat.multinomial
  rw [fact_eq, sumNat_eq, prodNat_eq]
  congr 1
  · congr 1
    rw [← Fin.sum_univ_eq_sum_range (fun i => extend b i)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [extend, i.2]
  · simp only [fact_eq]
    rw [← Fin.prod_univ_eq_prod_range (fun i => (extend b i).factorial)]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [extend, i.2]

theorem wfMultiallele_eq {N K : Nat} (a b : Rhone.MarkovChain.AlleleCounts N K) :
    ((wfMultiallele N K (extend a) (extend b) : Rat) : ℝ) = Rhone.MarkovChain.wfMultiallele N K a
        b := by
  unfold wfMultiallele Rhone.MarkovChain.wfMultiallele
  rw [Rat.cast_mul, cast_prodRat, multinomial_eq, ← Fin.prod_univ_eq_prod_range]
  · push_cast
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [extend, i.2]

end Rhone.Computation.WFKAllele
