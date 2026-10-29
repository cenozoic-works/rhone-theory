/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Tactic.LinearCombination
public import Rhone.Combinatorics.Combinatorics

/-!
# The cycle index of the symmetric group, as a polynomial identity

Source: flajolet_sedgewick2009, p. 85, eq. (89). -/

@[expose] public section

namespace Rhone.Combinatorics

open Finset Polynomial

variable {F : Type*} [Field F]

def partWeight (F : Type*) [Field F] (s : Multiset ℕ) : F :=
  ((s.prod : F) * ∏ j ∈ s.toFinset, ((s.count j).factorial : F))⁻¹

noncomputable def cycleIndex (F : Type*) [Field F] (n : ℕ) : F[X] :=
  ∑ p : Nat.Partition n, C (partWeight F p.parts) * X ^ p.parts.card

theorem prod_factorial_count_eq {s : Multiset ℕ} {T : Finset ℕ} (hT : s.toFinset ⊆ T) :
    ∏ j ∈ s.toFinset, ((s.count j).factorial : F) = ∏ j ∈ T, ((s.count j).factorial : F) := by
  refine Finset.prod_subset hT fun j _ hj => ?_
  have : s.count j = 0 := Multiset.count_eq_zero.2 (by simpa using hj)
  simp [this]

theorem partWeight_erase [CharZero F] {s : Multiset ℕ} (hs : ∀ x ∈ s, 0 < x) {j : ℕ}
    (hj : j ∈ s) : partWeight F (s.erase j) = j * (s.count j) * partWeight F s := by
  classical
  have hc : 0 < s.count j := Multiset.count_pos.2 hj
  have hprod : (s.prod : F) = j * ((s.erase j).prod : F) := by
    rw [← Multiset.prod_erase hj]; push_cast; rfl
  have hsub : (s.erase j).toFinset ⊆ s.toFinset := fun x hx => by
    simp only [Multiset.mem_toFinset] at hx ⊢
    exact Multiset.mem_of_mem_erase hx
  have hjT : j ∈ s.toFinset := Multiset.mem_toFinset.2 hj
  have hfact : ∏ k ∈ s.toFinset, ((s.count k).factorial : F) =
      (s.count j : F) * ∏ k ∈ (s.erase j).toFinset, (((s.erase j).count k).factorial : F) := by
    rw [prod_factorial_count_eq (s := s.erase j) hsub,
      ← Finset.mul_prod_erase _ _ hjT, ← Finset.mul_prod_erase _ (fun k =>
        (((s.erase j).count k).factorial : F)) hjT]
    have hcongr : ∏ k ∈ s.toFinset.erase j, ((s.count k).factorial : F) =
        ∏ k ∈ s.toFinset.erase j, (((s.erase j).count k).factorial : F) :=
      Finset.prod_congr rfl fun k hk => by
        rw [Multiset.count_erase_of_ne (Finset.ne_of_mem_erase hk)]
    rw [hcongr, Multiset.count_erase_self, ← mul_assoc]
    congr 1
    rw [← Nat.cast_mul]
    exact_mod_cast (Nat.mul_factorial_pred hc.ne').symm
  have hne1 : ((s.erase j).prod : F) ≠ 0 := by
    refine Nat.cast_ne_zero.2 (Multiset.prod_ne_zero fun h0 => ?_)
    exact (hs 0 (Multiset.mem_of_mem_erase h0)).ne rfl
  have hne2 : ∏ k ∈ (s.erase j).toFinset, (((s.erase j).count k).factorial : F) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have hj0 : (j : F) ≠ 0 := Nat.cast_ne_zero.2 (hs j hj).ne'
  have hc0 : (s.count j : F) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  unfold partWeight
  rw [hprod, hfact]
  field_simp

def erasePart {n : ℕ} (p : Nat.Partition n) (j : ℕ) (hj : j ∈ p.parts) :
    Nat.Partition (n - j) where
  parts := p.parts.erase j
  parts_pos := fun h => p.parts_pos (Multiset.mem_of_mem_erase h)
  parts_sum := by
    have h1 := Multiset.sum_erase hj
    have h2 := p.parts_sum
    omega

def consPart {n j : ℕ} (q : Nat.Partition (n - j)) (hj : 0 < j) (hjn : j ≤ n) :
    Nat.Partition n where
  parts := j ::ₘ q.parts
  parts_pos := fun {i} h => by
    rcases Multiset.mem_cons.1 h with rfl | h
    · exact hj
    · exact q.parts_pos h
  parts_sum := by
    have := q.parts_sum
    simp only [Multiset.sum_cons, this]
    omega

theorem sum_partition_erase {M : Type*} [AddCommMonoid M] (n : ℕ) (g : ℕ → Multiset ℕ → M) :
    ∑ p : Nat.Partition n, ∑ j ∈ p.parts.toFinset, g j (p.parts.erase j) =
      ∑ j ∈ Icc 1 n, ∑ q : Nat.Partition (n - j), g j q.parts := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij' (fun a ha => ⟨a.2, erasePart a.1 a.2 (by
      simpa using (Finset.mem_sigma.1 ha).2)⟩)
    (fun b hb => ⟨consPart b.2 (mem_Icc.1 (Finset.mem_sigma.1 hb).1).1
      (mem_Icc.1 (Finset.mem_sigma.1 hb).1).2, b.1⟩) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    have h := (Finset.mem_sigma.1 ha).2
    simp only [Multiset.mem_toFinset] at h
    simp only [Finset.mem_sigma, mem_Icc, Finset.mem_univ, and_true]
    exact ⟨Nat.Partition.parts_pos _ h, Nat.Partition.le_of_mem_parts h⟩
  · intro b hb
    simp only [Finset.mem_sigma, Finset.mem_univ, true_and, Multiset.mem_toFinset, consPart,
      Multiset.mem_cons_self]
  · intro a ha
    have h := (Finset.mem_sigma.1 ha).2
    simp only [Multiset.mem_toFinset] at h
    refine Sigma.ext (Nat.Partition.ext ?_) (heq_of_eq rfl)
    exact Multiset.cons_erase h
  · intro b hb
    refine Sigma.ext rfl (heq_of_eq (Nat.Partition.ext ?_))
    exact Multiset.erase_cons_head _ _
  · intro a ha
    rfl

theorem term_erase [CharZero F] {n : ℕ} (p : Nat.Partition n) {j : ℕ} (hj : j ∈ p.parts) :
    (((p.parts.count j • j : ℕ)) : F[X]) * (C (partWeight F p.parts) * X ^ p.parts.card) =
      X * (C (partWeight F (p.parts.erase j)) * X ^ (p.parts.erase j).card) := by
  rw [partWeight_erase (fun x hx => p.parts_pos hx) hj, Multiset.card_erase_of_mem hj]
  have hc : 0 < p.parts.card := Multiset.card_pos_iff_exists_mem.2 ⟨j, hj⟩
  obtain ⟨c, hc'⟩ : ∃ c, p.parts.card = c + 1 := ⟨p.parts.card - 1, by omega⟩
  rw [hc', Nat.pred_succ]
  simp only [smul_eq_mul, Nat.cast_mul, map_mul, map_natCast, pow_succ]
  ring

theorem cycleIndex_recursion [CharZero F] (n : ℕ) :
    (n : F[X]) * cycleIndex F n = X * ∑ j ∈ Icc 1 n, cycleIndex F (n - j) := by
  unfold cycleIndex
  have h1 : ∀ p : Nat.Partition n, (n : F[X]) * (C (partWeight F p.parts) * X ^ p.parts.card) =
      ∑ j ∈ p.parts.toFinset, X * (C (partWeight F (p.parts.erase j)) *
        X ^ (p.parts.erase j).card) := by
    intro p
    have hn : (n : F[X]) = ∑ j ∈ p.parts.toFinset, (((p.parts.count j • j : ℕ)) : F[X]) := by
      rw [← Nat.cast_sum, ← Finset.sum_multiset_count, p.parts_sum]
    rw [hn, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j hj => term_erase p (Multiset.mem_toFinset.1 hj)
  rw [Finset.mul_sum, Finset.sum_congr rfl fun p _ => h1 p,
    sum_partition_erase n (fun j s => X * (C (partWeight F s) * X ^ s.card)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]

theorem cycleIndex_zero : cycleIndex F 0 = 1 := by
  unfold cycleIndex
  rw [Fintype.sum_unique]
  simp [partWeight]

theorem ascPochhammer_recursion [CharZero F] (n : ℕ) :
    (n : F[X]) * (C ((n.factorial : F)⁻¹) * ascPochhammer F n) =
      X * ∑ m ∈ range n, C ((m.factorial : F)⁻¹) * ascPochhammer F m := by
  induction n with
  | zero => simp
  | succ n ih =>
    have key : ((n + 1 : ℕ) : F[X]) * C (((n + 1).factorial : F)⁻¹) = C ((n.factorial : F)⁻¹) := by
      rw [← map_natCast (C : F →+* F[X]), ← map_mul, Nat.factorial_succ]
      congr 1
      have h1 : ((n + 1 : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.2 (Nat.succ_ne_zero n)
      have h2 : (n.factorial : F) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
      push_cast
      field_simp
    rw [Finset.sum_range_succ, ← mul_assoc, key, ascPochhammer_succ_right]
    linear_combination ih

theorem cycleIndex_eq [CharZero F] (n : ℕ) :
    cycleIndex F n = C ((n.factorial : F)⁻¹) * ascPochhammer F n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [cycleIndex_zero]
    · have h1 : ∑ j ∈ Icc 1 n, cycleIndex F (n - j) =
          ∑ m ∈ range n, C ((m.factorial : F)⁻¹) * ascPochhammer F m := by
        refine Finset.sum_nbij' (fun j => n - j) (fun m => n - m) ?_ ?_ ?_ ?_ ?_
        · intro j hj; simp only [mem_Icc] at hj; simp only [mem_range]; omega
        · intro m hm; simp only [mem_range] at hm; simp only [mem_Icc]; omega
        · intro j hj; simp only [mem_Icc] at hj; omega
        · intro m hm; simp only [mem_range] at hm; omega
        · intro j hj
          simp only [mem_Icc] at hj
          exact ih (n - j) (by omega)
      have h2 := cycleIndex_recursion (F := F) n
      rw [h1, ← ascPochhammer_recursion] at h2
      have hn0 : (n : F[X]) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
      exact mul_left_cancel₀ hn0 h2

theorem factorial_mul_cycleIndex [CharZero F] (n : ℕ) :
    C (n.factorial : F) * cycleIndex F n = ascPochhammer F n := by
  rw [cycleIndex_eq, ← mul_assoc, ← map_mul, mul_inv_cancel₀
    (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)), map_one, one_mul]

theorem factorial_mul_sum_partWeight_card [CharZero F] (n k : ℕ) :
    (n.factorial : F) *
      ∑ p ∈ (Finset.univ : Finset (Nat.Partition n)).filter (fun p => p.parts.card = k),
        partWeight F p.parts = (Nat.stirlingFirst n k : F) := by
  have h := congrArg (fun q => q.coeff k) (factorial_mul_cycleIndex (F := F) n)
  simp only [coeff_C_mul] at h
  rw [ascPochhammer_eq_sum_stirlingFirst, finsetSum_coeff] at h
  simp only [coeff_C_mul_X_pow] at h
  rw [cycleIndex, finsetSum_coeff] at h
  simp only [coeff_C_mul_X_pow] at h
  rw [Finset.sum_ite_eq] at h
  simp only [eq_comm (a := k), ← Finset.sum_filter] at h
  rw [h]
  split_ifs with hk
  · rfl
  · have : n < k := by simpa [Nat.lt_succ_iff] using hk
    simp [Nat.stirlingFirst_eq_zero_of_lt this]

end Rhone.Combinatorics
