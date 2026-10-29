/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Statistics.EwensReal
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Ewens urn transition steps and the urn law

Source: hoppe1984, secs. 1–2, Thm, eq. (1), pp. 91–92; ewens1972, eq. (18), p. 94. -/

@[expose] public section
namespace Rhone.Statistics
open Finset Polynomial Rhone.Combinatorics Probability

/-- Source: hoppe1984, sec. 1, p. 91; ewens1972, eq. (18), p. 94. -/
noncomputable def ewensUrnStep {n : ℕ} (θ : ℝ)
    (q : Nat.Partition n) (p : Nat.Partition (n + 1)) : ℝ :=
  (if p.parts = 1 ::ₘ q.parts then θ / (θ + n) else 0) +
    ∑ j ∈ q.parts.toFinset,
      if p.parts = (j + 1) ::ₘ q.parts.erase j
      then (j : ℝ) * q.parts.count j / (θ + n) else 0

/-- Source: hoppe1984, sec. 1, p. 91; durrett2008, sec. 1.3.1. -/
theorem ewensUrnStep_nonneg {n : ℕ} {θ : ℝ} (hθ : 0 < θ)
    (q : Nat.Partition n) (p : Nat.Partition (n + 1)) :
    0 ≤ ewensUrnStep θ q p := by
  unfold ewensUrnStep
  apply add_nonneg
  · split_ifs <;> positivity
  · apply Finset.sum_nonneg
    intro j _
    split_ifs <;> positivity

/-- Source: hoppe1984, sec. 1, p. 91; durrett2008, sec. 1.3.1. -/
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

/-- Source: hoppe1984, sec. 2, Thm, eq. (1), p. 92; ewens1972, eq. (A3)–(A5), pp. 107–108. -/
theorem esf_urn_forward {n : ℕ} {θ : ℝ} (hθ : 0 < θ)
    (p : Nat.Partition (n + 1)) :
    ∑ q : Nat.Partition n, esf θ q * ewensUrnStep θ q p = esf θ p := by
  classical
  let mass (s : Multiset ℕ) : ℝ :=
    ((n + 1).factorial : ℝ) * θ ^ s.card * partWeight ℝ s /
      (ascPochhammer ℝ (n + 1)).eval θ
  let g (s : Multiset ℕ) (j : ℕ) : ℝ :=
    mass s * (j : ℝ) * s.count j / (n + 1) *
      (if s = p.parts then 1 else 0)
  have hlocal (q : Nat.Partition n) (j : ℕ) (hj : j = 0 ∨ j ∈ q.parts) :
      g (partitionInsert q j hj).parts (j + 1) =
      esf θ q * (if j = 0 then θ else (j : ℝ) * q.parts.count j) / (θ + n) *
        (if (partitionInsert q j hj).parts = p.parts then 1 else 0) := by
    change (esf θ (partitionInsert q j hj) * (j + 1 : ℕ) *
      (partitionInsert q j hj).parts.count (j + 1) / (n + 1)) * _ = _
    rw [esf_partitionInsert_balance_real hθ q j hj]
  have hright : (∑ q : Nat.Partition n,
      (g (1 ::ₘ q.parts) 1 +
        ∑ j ∈ q.parts.toFinset, g ((j + 1) ::ₘ q.parts.erase j) (j + 1))) =
      ∑ q : Nat.Partition n, esf θ q * ewensUrnStep θ q p := by
    apply Finset.sum_congr rfl
    intro q _
    have hnew := hlocal q 0 (Or.inl rfl)
    simp only [partitionInsert, ite_true, zero_add] at hnew
    rw [hnew]
    unfold ewensUrnStep
    rw [mul_add, mul_sum]
    congr 1
    · by_cases h : p.parts = 1 ::ₘ q.parts
      · simp [h, mul_div_assoc]
      · simp [h, Ne.symm h]
    · apply Finset.sum_congr rfl
      intro j hj
      have hmem := Multiset.mem_toFinset.mp hj
      have hn := (q.parts_pos hmem).ne'
      have hgrow := hlocal q j (Or.inr hmem)
      simp only [partitionInsert, hn, ite_false] at hgrow
      rw [hgrow]
      by_cases h : p.parts = (j + 1) ::ₘ q.parts.erase j
      · simp [h, mul_div_assoc]
      · simp [h, Ne.symm h]
  have hleft : (∑ q : Nat.Partition (n + 1),
      ∑ j ∈ q.parts.toFinset, g q.parts j) = esf θ p := by
    have heach (q : Nat.Partition (n + 1)) :
        (∑ j ∈ q.parts.toFinset, g q.parts j) =
          if q = p then esf θ p else 0 := by
      by_cases h : q = p
      · subst q
        simp only [g, ite_true, mul_one]
        rw [← Finset.sum_div]
        simp_rw [mul_assoc]
        rw [← Finset.mul_sum]
        have hn : ∑ j ∈ p.parts.toFinset, (j : ℝ) * p.parts.count j = n + 1 := by
          have ht := Finset.sum_multiset_count p.parts
          simp only [smul_eq_mul, p.parts_sum] at ht
          have ht' : ∑ j ∈ p.parts.toFinset, j * p.parts.count j = n + 1 := by
            simpa only [Nat.mul_comm] using ht.symm
          exact_mod_cast ht'
        rw [hn]
        change esf θ p * (n + 1 : ℝ) / (n + 1) = esf θ p
        field_simp
      · have hp : q.parts ≠ p.parts := fun hp => h (Nat.Partition.ext hp)
        simp [g, hp, h]
    simp_rw [heach]
    simp
  rw [← hright, ← sum_partition_individual_delete n g, hleft]

/-- Source: hoppe1984, sec. 1, p. 91. -/
noncomputable def ewensUrnStepPMF {n : ℕ} (θ : ℝ) (hθ : 0 < θ)
    (q : Nat.Partition n) : PMF (Nat.Partition (n + 1)) :=
  PMF.ofFintype (fun p => ENNReal.ofReal (ewensUrnStep θ q p)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun p _ => ewensUrnStep_nonneg hθ q p),
      sum_ewensUrnStep hθ q, ENNReal.ofReal_one])

/-- Source: hoppe1984, secs. 1–2, Thm, pp. 91–92. -/
noncomputable def ewensUrnLaw (θ : ℝ) (hθ : 0 < θ) :
    (n : ℕ) → PMF (Nat.Partition n)
  | 0 => PMF.pure default
  | n + 1 => (ewensUrnLaw θ hθ n).bind (ewensUrnStepPMF θ hθ)

/-- Source: hoppe1984, sec. 2, Thm, eq. (1), p. 92; ewens1972, eq. (A3)–(A5), pp. 107–108. -/
theorem ewensUrnLaw_apply (θ : ℝ) (hθ : 0 < θ) (n : ℕ)
    (p : Nat.Partition n) :
    ewensUrnLaw θ hθ n p = ENNReal.ofReal (esf θ p) := by
  induction n with
  | zero =>
    have hp : p = default := Subsingleton.elim _ _
    subst p
    simp [ewensUrnLaw, esf, partWeight]
  | succ n ih =>
    rw [ewensUrnLaw, PMF.bind_apply, tsum_fintype]
    simp_rw [ih, ewensUrnStepPMF, PMF.ofFintype_apply]
    simp_rw [← ENNReal.ofReal_mul (esf_nonneg hθ _)]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun q _ =>
      mul_nonneg (esf_nonneg hθ q) (ewensUrnStep_nonneg hθ q p)),
      esf_urn_forward hθ p]

end Rhone.Statistics
