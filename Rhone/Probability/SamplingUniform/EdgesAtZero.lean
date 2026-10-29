/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.SamplingUniform.RegularAtZero
public import Rhone.Probability.RareAlleleHierarchy.Alpha
public import Rhone.LinearAlgebra.SlotDeletion.Denom

/-! # The one-locus coefficients at the inverse-mutation origin -/

@[expose] public section

namespace Rhone.Probability.SamplingUniform
open Analysis.RareAlleleHierarchy RareAlleleHierarchy LinearAlgebra.SlotDeletion SlotDeletion
variable {K : Type*} [Field K]

private theorem coe_ne_zero_of_residue_ne_zero (f : Algebra.SamplingUniform.RegularAtZero K)
    (hf : Algebra.SamplingUniform.residueAtZero f ≠ 0) : (f : RatFunc K) ≠ 0 := by
  intro h
  have he : f = 0 := Subtype.ext h
  exact hf (by rw [he, map_zero])

noncomputable def edgeDenA (k : ℕ) : Algebra.SamplingUniform.RegularAtZero K :=
  1 + Algebra.SamplingUniform.regularC (k : K) * Algebra.SamplingUniform.regularZ

noncomputable def edgeDenB (θ : K) (k : ℕ) : Algebra.SamplingUniform.RegularAtZero K :=
  -1 + Algebra.SamplingUniform.regularC (θ + (k : K)) * Algebra.SamplingUniform.regularZ

@[simp] theorem residue_edgeDenA (k : ℕ) : Algebra.SamplingUniform.residueAtZero
    (edgeDenA (K := K) k) = 1 := by
  simp [edgeDenA]

@[simp] theorem residue_edgeDenB (θ : K) (k : ℕ) : Algebra.SamplingUniform.residueAtZero
    (edgeDenB θ k) = -1 := by
  simp [edgeDenB]

private theorem edgeDenA_ne_zero (k : ℕ) : (edgeDenA (K := K) k : RatFunc K) ≠ 0 :=
  coe_ne_zero_of_residue_ne_zero _ (by simp)

private theorem edgeDenB_ne_zero (θ : K) (k : ℕ) : (edgeDenB θ k : RatFunc K) ≠ 0 :=
  coe_ne_zero_of_residue_ne_zero _ (by simp)

theorem inverseMutation_add_nat_ne_zero (k : ℕ) :
    (RatFunc.X⁻¹ + (k : RatFunc K)) ≠ 0 := by
  have hprod : (RatFunc.X⁻¹ + (k : RatFunc K)) * (RatFunc.X : RatFunc K) =
      (edgeDenA (K := K) k : RatFunc K) := by
    simp [edgeDenA, add_mul, RatFunc.X_ne_zero]
  intro h
  exact edgeDenA_ne_zero (K := K) k (by rw [← hprod, h, zero_mul])

theorem complementaryMutation_add_nat_ne_zero (θ : K) (k : ℕ) :
    (RatFunc.C θ - RatFunc.X⁻¹ + (k : RatFunc K)) ≠ 0 := by
  have hprod : (RatFunc.C θ - RatFunc.X⁻¹ + (k : RatFunc K)) * (RatFunc.X : RatFunc K) =
      (edgeDenB θ k : RatFunc K) := by
    simp [edgeDenB, add_mul, sub_mul, RatFunc.X_ne_zero]
    ring
  intro h
  exact edgeDenB_ne_zero θ k (by rw [← hprod, h, zero_mul])

noncomputable def regularEdgeInvA (k : ℕ) : Algebra.SamplingUniform.RegularAtZero K :=
  Algebra.SamplingUniform.regularZ * Algebra.SamplingUniform.regularInv (edgeDenA k) (by simp)

noncomputable def regularEdgeInvB (θ : K) (k : ℕ) : Algebra.SamplingUniform.RegularAtZero K :=
  Algebra.SamplingUniform.regularZ * Algebra.SamplingUniform.regularInv (edgeDenB θ k) (by simp)

@[simp] theorem coe_regularEdgeInvA (k : ℕ) :
    (regularEdgeInvA (K := K) k : RatFunc K) = (RatFunc.X⁻¹ + (k : RatFunc K))⁻¹ := by
  have hd := edgeDenA_ne_zero (K := K) k
  simp only [edgeDenA, Subring.coe_add, Subring.coe_one, Subring.coe_mul,
    Algebra.SamplingUniform.coe_regularZ, map_natCast, Subring.coe_natCast] at hd
  simp only [regularEdgeInvA, Subring.coe_mul, Algebra.SamplingUniform.coe_regularZ,
      Algebra.SamplingUniform.coe_regularInv,
    edgeDenA, Subring.coe_add, Subring.coe_one, map_natCast, Subring.coe_natCast]
  field_simp [RatFunc.X_ne_zero]

@[simp] theorem coe_regularEdgeInvB (θ : K) (k : ℕ) :
    (regularEdgeInvB θ k : RatFunc K) =
      (RatFunc.C θ - RatFunc.X⁻¹ + (k : RatFunc K))⁻¹ := by
  have hd := edgeDenB_ne_zero θ k
  simp only [edgeDenB, Subring.coe_add, Subring.coe_neg, Subring.coe_one,
    Subring.coe_mul, Algebra.SamplingUniform.coe_regularC, Algebra.SamplingUniform.coe_regularZ,
        map_add, map_natCast, Subring.coe_natCast] at hd
  simp only [regularEdgeInvB, Subring.coe_mul, Algebra.SamplingUniform.coe_regularZ,
      Algebra.SamplingUniform.coe_regularInv,
    edgeDenB, Subring.coe_add, Subring.coe_neg, Subring.coe_one,
        Algebra.SamplingUniform.coe_regularC,
    map_add, map_natCast, Subring.coe_natCast]
  field_simp [RatFunc.X_ne_zero]
  ring

@[simp] theorem residue_regularEdgeInvA (k : ℕ) :
    Algebra.SamplingUniform.residueAtZero (regularEdgeInvA (K := K) k) = 0 := by
  simp [regularEdgeInvA]

@[simp] theorem residue_regularEdgeInvB (θ : K) (k : ℕ) :
    Algebra.SamplingUniform.residueAtZero (regularEdgeInvB θ k) = 0 := by
  simp [regularEdgeInvB]

noncomputable def regularAlphaA (i : ℕ) : Algebra.SamplingUniform.RegularAtZero K :=
  Algebra.SamplingUniform.regularC (Nat.factorial (i - 1) : K) * ∏ k ∈ Finset.Ico 1 i,
      regularEdgeInvA k

noncomputable def regularAlphaB (θ : K) (i : ℕ) : Algebra.SamplingUniform.RegularAtZero K :=
  Algebra.SamplingUniform.regularC (Nat.factorial (i - 1) : K) * ∏ k ∈ Finset.Ico 1 i,
      regularEdgeInvB θ k

@[simp] theorem coe_regularAlphaA (i : ℕ) :
    (regularAlphaA (K := K) i : RatFunc K) = alphaSeq RatFunc.X⁻¹ i := by
  simp [regularAlphaA, alphaSeq, div_eq_mul_inv, Finset.prod_inv_distrib]

@[simp] theorem coe_regularAlphaB (θ : K) (i : ℕ) :
    (regularAlphaB θ i : RatFunc K) = alphaSeq (RatFunc.C θ - RatFunc.X⁻¹) i := by
  simp [regularAlphaB, alphaSeq, div_eq_mul_inv, Finset.prod_inv_distrib]

theorem alphaSeq_A_mem_regular (i : ℕ) :
    alphaSeq (RatFunc.X⁻¹ : RatFunc K) i ∈ Algebra.SamplingUniform.regularAtZero K := by
  rw [← coe_regularAlphaA]
  exact (regularAlphaA i).property

theorem alphaSeq_B_mem_regular (θ : K) (i : ℕ) :
    alphaSeq (RatFunc.C θ - RatFunc.X⁻¹) i ∈ Algebra.SamplingUniform.regularAtZero K := by
  rw [← coe_regularAlphaB]
  exact (regularAlphaB θ i).property

theorem residue_regularAlphaA {i : ℕ} (hi : 2 ≤ i) :
    Algebra.SamplingUniform.residueAtZero (regularAlphaA (K := K) i) = 0 := by
  simp only [regularAlphaA, map_mul, map_prod, Algebra.SamplingUniform.residue_regularC,
      residue_regularEdgeInvA]
  rw [Finset.prod_eq_zero (Finset.mem_Ico.mpr (show 1 ≤ 1 ∧ 1 < i from ⟨by omega, by omega⟩)) rfl,
    mul_zero]

theorem residue_regularAlphaB (θ : K) {i : ℕ} (hi : 2 ≤ i) :
    Algebra.SamplingUniform.residueAtZero (regularAlphaB θ i) = 0 := by
  simp only [regularAlphaB, map_mul, map_prod, Algebra.SamplingUniform.residue_regularC,
      residue_regularEdgeInvB]
  rw [Finset.prod_eq_zero (Finset.mem_Ico.mpr (show 1 ≤ 1 ∧ 1 < i from ⟨by omega, by omega⟩)) rfl,
    mul_zero]

theorem residue_alphaSeq_A {i : ℕ} (hi : 2 ≤ i) :
    Algebra.SamplingUniform.residueAtZero (⟨alphaSeq (RatFunc.X⁻¹ : RatFunc K) i,
      alphaSeq_A_mem_regular i⟩ : Algebra.SamplingUniform.RegularAtZero K) = 0 := by
  have h : (⟨alphaSeq (RatFunc.X⁻¹ : RatFunc K) i,
      alphaSeq_A_mem_regular i⟩ : Algebra.SamplingUniform.RegularAtZero K) = regularAlphaA i :=
    Subtype.ext (coe_regularAlphaA i).symm
  rw [h, residue_regularAlphaA hi]

theorem residue_alphaSeq_B (θ : K) {i : ℕ} (hi : 2 ≤ i) :
    Algebra.SamplingUniform.residueAtZero (⟨alphaSeq (RatFunc.C θ - RatFunc.X⁻¹) i,
      alphaSeq_B_mem_regular θ i⟩ : Algebra.SamplingUniform.RegularAtZero K) = 0 := by
  have h : (⟨alphaSeq (RatFunc.C θ - RatFunc.X⁻¹) i,
      alphaSeq_B_mem_regular θ i⟩ : Algebra.SamplingUniform.RegularAtZero K) = regularAlphaB θ i :=
    Subtype.ext (coe_regularAlphaB θ i).symm
  rw [h, residue_regularAlphaB θ hi]

theorem poch_inverseMutation_ne_zero (i : ℕ) :
    poch (RatFunc.X⁻¹ : RatFunc K) i ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro k _
  exact inverseMutation_add_nat_ne_zero k

theorem poch_complementaryMutation_ne_zero (θ : K) (i : ℕ) :
    poch (RatFunc.C θ - RatFunc.X⁻¹) i ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro k _
  exact complementaryMutation_add_nat_ne_zero θ k

end Rhone.Probability.SamplingUniform
