/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Probability.EwensConsistency
public import Rhone.Statistics.EwensSufficiency
public import Mathlib.Basic.Real.Basic

/-!
# Real mutation parameters for Ewens insertion and sufficient allele counts

Source: ewens1972, eq. (18), (29)–(30), pp. 94, 100–102; durrett2008, Thm 1.13, eq. (1.14). -/

@[expose] public section
namespace Rhone.Statistics
open Finset Polynomial Rhone.Combinatorics Probability

/-- Source: ewens1972, eq. (18), eq. (A1)–(A3), pp. 94, 107; durrett2008, sec. 1.3.1, Thm 1.11. -/
theorem esf_partitionInsert_balance_real {n : ℕ} {θ : ℝ} (hθ : 0 < θ)
    (q : Nat.Partition n) (j : ℕ) (hj : j = 0 ∨ j ∈ q.parts) :
    esf θ (partitionInsert q j hj) * (j + 1 : ℕ) *
        (partitionInsert q j hj).parts.count (j + 1) / (n + 1) =
      esf θ q * (if j = 0 then θ else (j : ℝ) * q.parts.count j) / (θ + n) := by
  let p := partitionInsert q j hj
  have hP : (ascPochhammer ℝ n).eval θ ≠ 0 := (ascPochhammer_pos n θ hθ).ne'
  have hθn : θ + n ≠ 0 := by positivity
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have hbase : esf θ p * (j + 1 : ℕ) * p.parts.count (j + 1) / (n + 1) =
      (n.factorial : ℝ) * θ ^ p.parts.card *
        (((j + 1 : ℕ) : ℝ) * p.parts.count (j + 1) * partWeight ℝ p.parts) /
          ((ascPochhammer ℝ n).eval θ * (θ + n)) := by
    unfold esf
    rw [Nat.factorial_succ, ascPochhammer_succ_eval]
    push_cast
    field_simp
  rw [hbase]
  have hpw := partWeight_erase (F := ℝ) (fun _ hx => p.parts_pos hx) (partitionInsert_mem q j hj)
  by_cases h : j = 0
  · subst j
    have hparts : p.parts = 1 ::ₘ q.parts := rfl
    have herase : p.parts.erase 1 = q.parts := by rw [hparts, Multiset.erase_cons_head]
    rw [herase] at hpw
    have hcard : p.parts.card = q.parts.card + 1 := by simp [hparts]
    rw [hcard, ← hpw]
    simp only [ite_true, pow_succ]
    unfold esf
    simp only [div_eq_mul_inv, mul_inv]
    ring
  · have hmem : j ∈ q.parts := hj.resolve_left h
    have hparts : p.parts = (j + 1) ::ₘ q.parts.erase j := by
      simp [p, partitionInsert, h]
    have hq := partWeight_erase (F := ℝ) (fun _ hx => q.parts_pos hx) hmem
    have herase : p.parts.erase (j + 1) = q.parts.erase j := by
      rw [hparts, Multiset.erase_cons_head]
    rw [herase] at hpw
    have hcard : p.parts.card = q.parts.card := by
      rw [hparts, Multiset.card_cons, Multiset.card_erase_of_mem hmem, Nat.pred_eq_sub_one]
      have hc : 0 < q.parts.card := Multiset.card_pos_iff_exists_mem.2 ⟨j, hmem⟩
      omega
    rw [hcard, ← hpw, hq]
    simp only [h, ite_false]
    unfold esf
    simp only [div_eq_mul_inv, mul_inv]
    ring

/-- Source: ewens1972, eq. (29)–(30), pp. 100–102; durrett2008, Thm 1.13, eq. (1.14). -/
theorem esf_conditional_card_real {n : ℕ} {θ : ℝ} (hθ : 0 < θ)
    (p : Nat.Partition n) :
    esf θ p /
        (∑ q ∈ (Finset.univ : Finset (Nat.Partition n)).filter
          (fun q => q.parts.card = p.parts.card), esf θ q) =
      (n.factorial : ℝ) * partWeight ℝ p.parts /
        (Nat.stirlingFirst n p.parts.card : ℝ) := by
  rw [sum_esf_card]
  have hP : (ascPochhammer ℝ n).eval θ ≠ 0 := (ascPochhammer_pos n θ hθ).ne'
  have hpow : θ ^ p.parts.card ≠ 0 := pow_ne_zero _ hθ.ne'
  unfold esf
  by_cases hs : (Nat.stirlingFirst n p.parts.card : ℝ) = 0
  · simp [hs]
  · field_simp

/-- Source: berestycki2009, sec. 2.3.2. -/
theorem esf_deletion_consistent_real {n : ℕ} {θ : ℝ} (hθ : 0 < θ)
    (q : Nat.Partition n) :
    ∑ p : Nat.Partition (n + 1), esf θ p * (deletionWeight p q : ℝ) = esf θ q := by
  classical
  unfold deletionWeight
  push_cast
  simp only [apply_ite (fun x : ℚ => (x : ℝ))]
  push_cast
  let mass (s : Multiset ℕ) : ℝ :=
    ((n + 1).factorial : ℝ) * θ ^ s.card * partWeight ℝ s /
      (ascPochhammer ℝ (n + 1)).eval θ
  let g (s : Multiset ℕ) (j : ℕ) : ℝ :=
    mass s * (if deleteGeneParts s j = q.parts
      then (j : ℝ) * s.count j / (n + 1) else 0)
  have hθn : θ + n ≠ 0 := by positivity
  have hlocal (r : Nat.Partition n) (j : ℕ) (hj : j = 0 ∨ j ∈ r.parts) :
      g (partitionInsert r j hj).parts (j + 1) =
        if r.parts = q.parts
        then esf θ r * (if j = 0 then θ else (j : ℝ) * r.parts.count j) / (θ + n)
        else 0 := by
    have hd : deleteGeneParts (partitionInsert r j hj).parts (j + 1) = r.parts :=
      congrArg Nat.Partition.parts (partitionDelete_insert r j hj)
    dsimp [g]
    rw [hd]
    by_cases h : r.parts = q.parts
    · simp only [ite_eq_left h]
      change esf θ (partitionInsert r j hj) *
        (((j + 1 : ℕ) : ℝ) * (partitionInsert r j hj).parts.count (j + 1) / (n + 1)) = _
      simpa only [mul_div_assoc, mul_assoc] using esf_partitionInsert_balance_real hθ r j hj
    · simp [h]
  have hnew (r : Nat.Partition n) :
      g (1 ::ₘ r.parts) 1 =
        if r.parts = q.parts then esf θ r * θ / (θ + n) else 0 := by
    simpa only [partitionInsert, ite_true, zero_add] using hlocal r 0 (Or.inl rfl)
  have hgrow (r : Nat.Partition n) (j : ℕ) (hj : j ∈ r.parts) :
      g ((j + 1) ::ₘ r.parts.erase j) (j + 1) =
        if r.parts = q.parts then esf θ r * (j : ℝ) * r.parts.count j / (θ + n) else 0 := by
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
      have hsum : ∑ j ∈ r.parts.toFinset, (j : ℝ) * r.parts.count j = n := by
        have hnat := Finset.sum_multiset_count r.parts
        simp only [smul_eq_mul, r.parts_sum] at hnat
        have hnat' : ∑ j ∈ r.parts.toFinset, j * r.parts.count j = n := by
          simpa only [Nat.mul_comm] using hnat.symm
        exact_mod_cast hnat'
      have hfactor : ∀ j : ℕ,
          esf θ r * (j : ℝ) * r.parts.count j / (θ + n) =
            (esf θ r / (θ + n)) * ((j : ℝ) * r.parts.count j) := by
        intro j
        ring
      rw [Finset.sum_congr rfl (fun j _ => hfactor j), ← Finset.mul_sum, hsum]
      field_simp
    · simp [h]
  simp_rw [Finset.mul_sum]
  change (∑ p : Nat.Partition (n + 1), ∑ j ∈ p.parts.toFinset, g p.parts j) = _
  rw [sum_partition_individual_delete n g, Finset.sum_congr rfl (fun r _ => heach r)]
  have hcond : ∀ r : Nat.Partition n, r.parts = q.parts ↔ r = q := by
    intro r
    exact ⟨Nat.Partition.ext, fun h => congrArg Nat.Partition.parts h⟩
  simp_rw [hcond]
  simp

end Rhone.Statistics
