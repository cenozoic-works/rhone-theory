/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Probability.EwensInsertion

/-!
# Uniform deletion from allelic partitions

Source: berestycki2009, sec. 2.3.2. -/

@[expose] public section
namespace Rhone.Probability
open Finset Polynomial Rhone.Combinatorics

theorem sum_deletionWeight {n : ℕ} (p : Nat.Partition (n + 1)) :
    ∑ q : Nat.Partition n, deletionWeight p q = 1 := by
  classical
  unfold deletionWeight
  rw [Finset.sum_comm]
  have hinner : ∀ j ∈ p.parts.toFinset,
      (∑ q : Nat.Partition n,
        if deleteGeneParts p.parts j = q.parts
        then (j : ℚ) * p.parts.count j / (n + 1) else 0) =
      (j : ℚ) * p.parts.count j / (n + 1) := by
    intro j hj
    let d := deleteGene p j (Multiset.mem_toFinset.1 hj)
    have hcond : ∀ q : Nat.Partition n,
        deleteGeneParts p.parts j = q.parts ↔ q = d := by
      intro q
      constructor
      · intro h
        exact Nat.Partition.ext h.symm
      · intro h
        exact congrArg Nat.Partition.parts h.symm
    simp_rw [hcond]
    simp
  rw [Finset.sum_congr rfl hinner, ← Finset.sum_div]
  have hsum : ∑ j ∈ p.parts.toFinset, (j : ℚ) * p.parts.count j = n + 1 := by
    have hnat := Finset.sum_multiset_count p.parts
    simp only [smul_eq_mul, p.parts_sum] at hnat
    have hnat' : ∑ j ∈ p.parts.toFinset, j * p.parts.count j = n + 1 := by
      simpa only [Nat.mul_comm] using hnat.symm
    exact_mod_cast hnat'
  rw [hsum]
  exact div_self (by positivity)

/-- Source: berestycki2009, sec. 2.3.2. -/
theorem esf_deletion_consistent {n : ℕ} {θ : ℚ} (hθ : 0 < θ)
    (q : Nat.Partition n) :
    ∑ p : Nat.Partition (n + 1), esf θ p * deletionWeight p q = esf θ q := by
  classical
  let mass (s : Multiset ℕ) : ℚ :=
    ((n + 1).factorial : ℚ) * θ ^ s.card * partWeight ℚ s /
      (ascPochhammer ℚ (n + 1)).eval θ
  let g (s : Multiset ℕ) (j : ℕ) : ℚ :=
    mass s * (if deleteGeneParts s j = q.parts
      then (j : ℚ) * s.count j / (n + 1) else 0)
  have hθn : θ + n ≠ 0 := by positivity
  have hlocal (r : Nat.Partition n) (j : ℕ) (hj : j = 0 ∨ j ∈ r.parts) :
      g (partitionInsert r j hj).parts (j + 1) =
        if r.parts = q.parts
        then esf θ r * (if j = 0 then θ else (j : ℚ) * r.parts.count j) / (θ + n)
        else 0 := by
    have hd : deleteGeneParts (partitionInsert r j hj).parts (j + 1) = r.parts :=
      congrArg Nat.Partition.parts (partitionDelete_insert r j hj)
    dsimp [g]
    rw [hd]
    by_cases h : r.parts = q.parts
    · simp only [ite_eq_left h]
      change esf θ (partitionInsert r j hj) *
        (((j + 1 : ℕ) : ℚ) * (partitionInsert r j hj).parts.count (j + 1) / (n + 1)) = _
      simpa only [mul_div_assoc, mul_assoc] using esf_partitionInsert_balance hθ r j hj
    · simp [h]
  have hnew (r : Nat.Partition n) :
      g (1 ::ₘ r.parts) 1 =
        if r.parts = q.parts then esf θ r * θ / (θ + n) else 0 := by
    simpa only [partitionInsert, ite_true, zero_add] using hlocal r 0 (Or.inl rfl)
  have hgrow (r : Nat.Partition n) (j : ℕ) (hj : j ∈ r.parts) :
      g ((j + 1) ::ₘ r.parts.erase j) (j + 1) =
        if r.parts = q.parts then esf θ r * (j : ℚ) * r.parts.count j / (θ + n) else 0 := by
    have hne := (r.parts_pos hj).ne'
    simpa only [partitionInsert, hne, ite_false, mul_assoc] using hlocal r j (Or.inr hj)
  have heach (r : Nat.Partition n) :
      g (1 ::ₘ r.parts) 1 +
        ∑ j ∈ r.parts.toFinset, g ((j + 1) ::ₘ r.parts.erase j) (j + 1) =
      if r.parts = q.parts then esf θ r else 0 := by
    rw [hnew]
    rw [Finset.sum_congr rfl (fun j hj => hgrow r j (Multiset.mem_toFinset.1 hj))]
    by_cases h : r.parts = q.parts
    · simp only [ite_eq_left h]
      have hsum : ∑ j ∈ r.parts.toFinset, (j : ℚ) * r.parts.count j = n := by
        have hnat := Finset.sum_multiset_count r.parts
        simp only [smul_eq_mul, r.parts_sum] at hnat
        have hnat' : ∑ j ∈ r.parts.toFinset, j * r.parts.count j = n := by
          simpa only [Nat.mul_comm] using hnat.symm
        exact_mod_cast hnat'
      have hfactor : ∀ j : ℕ,
          esf θ r * (j : ℚ) * r.parts.count j / (θ + n) =
            (esf θ r / (θ + n)) * ((j : ℚ) * r.parts.count j) := by
        intro j
        ring
      rw [Finset.sum_congr rfl (fun j _ => hfactor j), ← Finset.mul_sum, hsum]
      field_simp
    · simp [h]
  unfold deletionWeight
  simp_rw [Finset.mul_sum]
  change (∑ p : Nat.Partition (n + 1), ∑ j ∈ p.parts.toFinset, g p.parts j) = _
  rw [sum_partition_individual_delete n g, Finset.sum_congr rfl (fun r _ => heach r)]
  have hcond : ∀ r : Nat.Partition n, r.parts = q.parts ↔ r = q := by
    intro r
    exact ⟨Nat.Partition.ext, fun h => congrArg Nat.Partition.parts h⟩
  simp_rw [hcond]
  simp

end Rhone.Probability
