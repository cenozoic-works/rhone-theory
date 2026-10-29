module

public import Mathlib

set_option maxSynthPendingDepth 3

@[expose] public section

elab "clear_aux_proof_cache" : command =>
  Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

elab "set_main_module " m:ident : command =>
  Lean.modifyEnv fun env => env.setMainModule m.getId

set_main_module Rhone.Combinatorics.PartitionInsertion

namespace Rhone.Combinatorics
open Finset

def partitionDeleteParts (s : Multiset ℕ) (j : ℕ) : Multiset ℕ :=
  if j = 1 then s.erase j else (j - 1) ::ₘ s.erase j

def partitionDelete {n : ℕ} (p : Nat.Partition (n + 1)) (j : ℕ)
    (hj : j ∈ p.parts) : Nat.Partition n where
  parts := partitionDeleteParts p.parts j
  parts_pos := by
    intro i hi
    unfold partitionDeleteParts at hi
    split_ifs at hi with h
    · exact p.parts_pos (Multiset.mem_of_mem_erase hi)
    · rcases Multiset.mem_cons.1 hi with rfl | hi
      · have := p.parts_pos hj
        omega
      · exact p.parts_pos (Multiset.mem_of_mem_erase hi)
  parts_sum := by
    have hsum := Multiset.sum_erase hj
    have hp := p.parts_sum
    unfold partitionDeleteParts
    split_ifs with h
    · omega
    · simp only [Multiset.sum_cons]
      have := p.parts_pos hj
      omega

def partitionInsert {n : ℕ} (q : Nat.Partition n) (j : ℕ)
    (hj : j = 0 ∨ j ∈ q.parts) : Nat.Partition (n + 1) where
  parts := if j = 0 then 1 ::ₘ q.parts else (j + 1) ::ₘ q.parts.erase j
  parts_pos := by
    intro i hi
    split_ifs at hi with h
    · rcases Multiset.mem_cons.1 hi with rfl | hi
      · omega
      · exact q.parts_pos hi
    · rcases Multiset.mem_cons.1 hi with rfl | hi
      · omega
      · exact q.parts_pos (Multiset.mem_of_mem_erase hi)
  parts_sum := by
    split_ifs with h
    · simp [q.parts_sum, Nat.add_comm]
    · have hmem : j ∈ q.parts := hj.resolve_left h
      have he := Multiset.sum_erase hmem
      simp only [Multiset.sum_cons]
      have hq := q.parts_sum
      omega

end Rhone.Combinatorics

set_main_module Palomar.EwensUrn.Challenge

clear_aux_proof_cache

namespace Rhone.Combinatorics

open Finset Polynomial

variable {F : Type*} [Field F]

def partWeight (F : Type*) [Field F] (s : Multiset ℕ) : F :=
  ((s.prod : F) * ∏ j ∈ s.toFinset, ((s.count j).factorial : F))⁻¹

end Rhone.Combinatorics

clear_aux_proof_cache

namespace Rhone.Probability

open Finset Polynomial Rhone.Combinatorics

variable {F : Type*} [Field F]

noncomputable def esf (θ : F) {n : ℕ} (p : Nat.Partition n) : F :=
  (n.factorial : F) * θ ^ p.parts.card * partWeight F p.parts / (ascPochhammer F n).eval θ

end Rhone.Probability

clear_aux_proof_cache

namespace Rhone.Probability
open Finset Polynomial Rhone.Combinatorics

def deleteGeneParts (s : Multiset ℕ) (j : ℕ) : Multiset ℕ :=
  partitionDeleteParts s j

noncomputable def deletionWeight {n : ℕ}
    (p : Nat.Partition (n + 1)) (q : Nat.Partition n) : ℚ :=
  ∑ j ∈ p.parts.toFinset,
    if deleteGeneParts p.parts j = q.parts
    then (j : ℚ) * p.parts.count j / (n + 1) else 0

end Rhone.Probability

clear_aux_proof_cache

namespace Rhone.Statistics
open Finset Polynomial Rhone.Combinatorics Probability

noncomputable def ewensUrnStep {n : ℕ} (θ : ℝ)
    (q : Nat.Partition n) (p : Nat.Partition (n + 1)) : ℝ :=
  (if p.parts = 1 ::ₘ q.parts then θ / (θ + n) else 0) +
    ∑ j ∈ q.parts.toFinset,
      if p.parts = (j + 1) ::ₘ q.parts.erase j
      then (j : ℝ) * q.parts.count j / (θ + n) else 0

theorem ewensUrnStep_nonneg {n : ℕ} {θ : ℝ} (hθ : 0 < θ)
    (q : Nat.Partition n) (p : Nat.Partition (n + 1)) :
    0 ≤ ewensUrnStep θ q p := by
  unfold ewensUrnStep
  apply add_nonneg
  · split_ifs <;> positivity
  · apply Finset.sum_nonneg
    intro j _
    split_ifs <;> positivity

theorem sum_ewensUrnStep {n : ℕ} {θ : ℝ} (hθ : 0 < θ)
    (q : Nat.Partition n) :
    ∑ p : Nat.Partition (n + 1), ewensUrnStep θ q p = 1 := by
  classical
  have hnew : (∑ p : Nat.Partition (n + 1),
      if p.parts = 1 ::ₘ q.parts then θ / (θ + n) else 0) = θ / (θ + n) := by
    have he (p : Nat.Partition (n + 1)) :
        p.parts = 1 ::ₘ q.parts ↔ p = partitionInsert q 0 (Or.inl rfl) := by
      constructor
      · intro h
        apply Nat.Partition.ext
        simpa [partitionInsert] using h
      · intro h
        simpa [partitionInsert] using congrArg Nat.Partition.parts h
    simp_rw [he]
    simp
  have hgrow (j : ℕ) (hj : j ∈ q.parts.toFinset) :
      (∑ p : Nat.Partition (n + 1),
        if p.parts = (j + 1) ::ₘ q.parts.erase j
        then (j : ℝ) * q.parts.count j / (θ + n) else 0) =
      (j : ℝ) * q.parts.count j / (θ + n) := by
    have hmem := Multiset.mem_toFinset.mp hj
    have hn := (q.parts_pos hmem).ne'
    have he (p : Nat.Partition (n + 1)) :
        p.parts = (j + 1) ::ₘ q.parts.erase j ↔
          p = partitionInsert q j (Or.inr hmem) := by
      rw [← show (partitionInsert q j (Or.inr hmem)).parts =
        (j + 1) ::ₘ q.parts.erase j by simp [partitionInsert, hn]]
      exact ⟨Nat.Partition.ext, fun h => congrArg Nat.Partition.parts h⟩
    simp_rw [he]
    simp
  unfold ewensUrnStep
  rw [Finset.sum_add_distrib, hnew, Finset.sum_comm]
  rw [Finset.sum_congr rfl hgrow, ← Finset.sum_div]
  have hsum : ∑ j ∈ q.parts.toFinset, (j : ℝ) * q.parts.count j = n := by
    have h := Finset.sum_multiset_count q.parts
    simp only [smul_eq_mul, q.parts_sum] at h
    have hnat : ∑ j ∈ q.parts.toFinset, j * q.parts.count j = n := by
      simpa only [Nat.mul_comm] using h.symm
    exact_mod_cast hnat
  rw [hsum, ← add_div]
  exact div_self (by positivity)

noncomputable def ewensUrnStepPMF {n : ℕ} (θ : ℝ) (hθ : 0 < θ)
    (q : Nat.Partition n) : PMF (Nat.Partition (n + 1)) :=
  PMF.ofFintype (fun p => ENNReal.ofReal (ewensUrnStep θ q p)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun p _ => ewensUrnStep_nonneg hθ q p),
      sum_ewensUrnStep hθ q, ENNReal.ofReal_one])

noncomputable def ewensUrnLaw (θ : ℝ) (hθ : 0 < θ) :
    (n : ℕ) → PMF (Nat.Partition n)
  | 0 => PMF.pure default
  | n + 1 => (ewensUrnLaw θ hθ n).bind (ewensUrnStepPMF θ hθ)

end Rhone.Statistics

namespace Rhone.Palomar.EwensUrn

open Probability Statistics Rhone.Combinatorics Finset Polynomial

section Formula

variable {F : Type*} [Field F]

theorem sum_esf [CharZero F] (θ : F) (n : ℕ) (h : (ascPochhammer F n).eval θ ≠ 0) :
    ∑ p : Nat.Partition n, esf θ p = 1 := by
  sorry

theorem esf_eq_prod (θ : F) {n : ℕ} (p : Nat.Partition n) :
    esf θ p = (n.factorial : F) / (ascPochhammer F n).eval θ *
      ∏ j ∈ Icc 1 n, (θ / j) ^ p.parts.count j / (p.parts.count j).factorial := by
  sorry

end Formula

theorem ewensUrnLaw_apply (θ : ℝ) (hθ : 0 < θ) (n : ℕ)
    (p : Nat.Partition n) :
    ewensUrnLaw θ hθ n p = ENNReal.ofReal (esf θ p) := by
  sorry

theorem esf_conditional_card_real {n : ℕ} {θ : ℝ} (hθ : 0 < θ)
    (p : Nat.Partition n) :
    esf θ p /
        (∑ q ∈ (Finset.univ : Finset (Nat.Partition n)).filter
          (fun q => q.parts.card = p.parts.card), esf θ q) =
      (n.factorial : ℝ) * partWeight ℝ p.parts /
        (Nat.stirlingFirst n p.parts.card : ℝ) := by
  sorry

theorem esf_deletion_consistent_real {n : ℕ} {θ : ℝ} (hθ : 0 < θ)
    (q : Nat.Partition n) :
    ∑ p : Nat.Partition (n + 1), esf θ p * (deletionWeight p q : ℝ) = esf θ q := by
  sorry

end Rhone.Palomar.EwensUrn
