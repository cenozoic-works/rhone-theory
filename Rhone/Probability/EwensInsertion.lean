/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Probability.Ewens
public import Rhone.Combinatorics.PartitionInsertion

/-!
# Insertion and deletion of allele classes

Source: ewens1972, eq. (18), eq. (A1)–(A3), pp. 94, 107; durrett2008, sec. 1.3.1, Thm 1.11. -/

@[expose] public section
namespace Rhone.Probability
open Finset Polynomial Rhone.Combinatorics

def deleteGeneParts (s : Multiset ℕ) (j : ℕ) : Multiset ℕ :=
  partitionDeleteParts s j

def deleteGene {n : ℕ} (p : Nat.Partition (n + 1)) (j : ℕ)
    (hj : j ∈ p.parts) : Nat.Partition n := partitionDelete p j hj

noncomputable def deletionWeight {n : ℕ}
    (p : Nat.Partition (n + 1)) (q : Nat.Partition n) : ℚ :=
  ∑ j ∈ p.parts.toFinset,
    if deleteGeneParts p.parts j = q.parts
    then (j : ℚ) * p.parts.count j / (n + 1) else 0

/-- Source: ewens1972, eq. (18), eq. (A1)–(A3), pp. 94, 107; durrett2008, sec. 1.3.1, Thm 1.11. -/
theorem esf_partitionInsert_balance {n : ℕ} {θ : ℚ} (hθ : 0 < θ)
    (q : Nat.Partition n) (j : ℕ) (hj : j = 0 ∨ j ∈ q.parts) :
    esf θ (partitionInsert q j hj) * (j + 1 : ℕ) *
        (partitionInsert q j hj).parts.count (j + 1) / (n + 1) =
      esf θ q * (if j = 0 then θ else (j : ℚ) * q.parts.count j) / (θ + n) := by
  let p := partitionInsert q j hj
  have hP : (ascPochhammer ℚ n).eval θ ≠ 0 := (ascPochhammer_pos n θ hθ).ne'
  have hθn : θ + n ≠ 0 := by positivity
  have hn : (n : ℚ) + 1 ≠ 0 := by positivity
  have hbase : esf θ p * (j + 1 : ℕ) * p.parts.count (j + 1) / (n + 1) =
      (n.factorial : ℚ) * θ ^ p.parts.card *
        (((j + 1 : ℕ) : ℚ) * p.parts.count (j + 1) * partWeight ℚ p.parts) /
          ((ascPochhammer ℚ n).eval θ * (θ + n)) := by
    unfold esf
    rw [Nat.factorial_succ, ascPochhammer_succ_eval]
    push_cast
    field_simp
  rw [hbase]
  have hpw := partWeight_erase (F := ℚ) (fun _ hx => p.parts_pos hx) (partitionInsert_mem q j hj)
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
    have hq := partWeight_erase (F := ℚ) (fun _ hx => q.parts_pos hx) hmem
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

end Rhone.Probability
