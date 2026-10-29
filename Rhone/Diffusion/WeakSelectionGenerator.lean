/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Analysis.TruncationRemainder.Unbounded
public import Mathlib.Algebra.MvPolynomial.Derivation

/-! # The selection operator of the two-locus corpus as a generator identity -/

@[expose] public section

namespace Rhone.Diffusion

open MvPolynomial Finset LinearAlgebra.Recursion Analysis.TruncationRemainder

variable {KA KB : ℕ}

theorem derivation_prod {R A ι : Type*} [CommSemiring R] [CommRing A] [Algebra R A]
    [DecidableEq ι] (D : Derivation R A A) (s : Finset ι) (h : ι → A) :
    D (∏ k ∈ s, h k) = ∑ k ∈ s, D (h k) * ∏ l ∈ s.erase k, h l := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
    rw [prod_insert has, Derivation.leibniz, ih, sum_insert has, erase_insert has]
    simp only [smul_eq_mul]
    rw [mul_sum, add_comm]
    congr 1
    · ring
    · refine sum_congr rfl fun k hk => ?_
      have hka : k ≠ a := fun hka => has (hka ▸ hk)
      rw [erase_insert_of_ne hka.symm, prod_insert (fun ha => has (mem_of_mem_erase ha))]
      ring

theorem derivation_prod_pow_of_log {R A ι : Type*} [CommSemiring R] [CommRing A] [Algebra R A]
    (D : Derivation R A A) (s : Finset ι) (g α : ι → A) (e : ι → ℕ)
    (hg : ∀ k ∈ s, D (g k) = g k * α k) :
    D (∏ k ∈ s, g k ^ e k) = (∑ k ∈ s, (e k : A) * α k) * ∏ k ∈ s, g k ^ e k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
    rw [prod_insert has, Derivation.leibniz, ih (fun k hk => hg k (mem_insert_of_mem hk)),
      sum_insert has, Derivation.leibniz_pow, hg a (mem_insert_self a s)]
    simp only [smul_eq_mul, nsmul_eq_mul]
    rcases Nat.eq_zero_or_pos (e a) with h0 | hpos
    · simp [h0]
    · obtain ⟨m, hm⟩ : ∃ m, e a = m + 1 := ⟨e a - 1, by omega⟩
      rw [hm, Nat.add_sub_cancel]
      push_cast
      ring

noncomputable def margA (i : Fin KA) : MvPolynomial (Fin KA × Fin KB) ℝ := ∑ j, X (i, j)

noncomputable def margB (j : Fin KB) : MvPolynomial (Fin KA × Fin KB) ℝ := ∑ i, X (i, j)

noncomputable def selDrift (i₀ : Fin KA) :
    Derivation ℝ (MvPolynomial (Fin KA × Fin KB) ℝ) (MvPolynomial (Fin KA × Fin KB) ℝ) :=
  mkDerivation ℝ fun ij => X ij * (C (if ij.1 = i₀ then 1 else 0) - margA i₀)

noncomputable def partA (ξ : Config KA KB) : MvPolynomial (Fin KA × Fin KB) ℝ :=
  ∏ i, margA i ^ ξ.a i

noncomputable def partB (ξ : Config KA KB) : MvPolynomial (Fin KA × Fin KB) ℝ :=
  ∏ j, margB j ^ ξ.b j

noncomputable def partC (ξ : Config KA KB) : MvPolynomial (Fin KA × Fin KB) ℝ :=
  ∏ i, ∏ j, X (i, j) ^ ξ.c i j

noncomputable def sampleMonomial (ξ : Config KA KB) : MvPolynomial (Fin KA × Fin KB) ℝ :=
  partA ξ * partB ξ * partC ξ

theorem selDrift_X (i₀ : Fin KA) (i : Fin KA) (j : Fin KB) :
    selDrift i₀ (X (i, j)) = X (i, j) * (C (if i = i₀ then 1 else 0) - margA i₀) := by
  simp [selDrift, mkDerivation_X]

theorem selDrift_margA (i₀ i : Fin KA) :
    selDrift (KB := KB) i₀ (margA i) = margA i * (C (if i = i₀ then 1 else 0) - margA i₀) := by
  simp only [margA, map_sum, selDrift_X, sum_mul]

theorem selDrift_margB (i₀ : Fin KA) (j : Fin KB) :
    selDrift i₀ (margB j) = X (i₀, j) - margB j * margA i₀ := by
  simp only [margB, map_sum, selDrift_X, sum_mul, mul_sub, sum_sub_distrib]
  congr 1
  rw [sum_eq_single i₀]
  · simp
  · intro i _ hi; simp [hi]
  · simp

theorem partA_incA (ξ : Config KA KB) (i₀ : Fin KA) :
    partA (incA ξ i₀) = partA ξ * margA i₀ := by
  simp only [partA, incA]
  rw [← prod_erase_mul _ _ (mem_univ i₀), ← prod_erase_mul _ _ (mem_univ i₀)]
  rw [prod_congr rfl fun i hi => by rw [incf, Function.update_of_ne (ne_of_mem_erase hi)]]
  rw [incf, Function.update_self, pow_succ]
  ring

theorem prod_pow_incf {ι M : Type*} [Fintype ι] [DecidableEq ι] [CommMonoid M] (g : ι → M)
    (f : ι → ℕ) (j : ι) : ∏ l, g l ^ incf f j l = (∏ l, g l ^ f l) * g j := by
  have h : ∀ l, g l ^ incf f j l = g l ^ f l * (if l = j then g l else 1) := by
    intro l
    by_cases hl : l = j
    · subst hl; simp [incf, pow_succ]
    · simp [incf, hl]
  rw [prod_congr rfl fun l _ => h l, prod_mul_distrib]
  simp

theorem partC_bToC (ξ : Config KA KB) (i₀ : Fin KA) (j : Fin KB) :
    partC (bToC ξ i₀ j) = partC ξ * X (i₀, j) := by
  simp only [partC, bToC, Config.incC]
  have h : ∀ i, ∏ l, (X (i, l) : MvPolynomial (Fin KA × Fin KB) ℝ) ^
      Function.update ξ.c i₀ (incf (ξ.c i₀) j) i l =
      (∏ l, (X (i, l) : MvPolynomial (Fin KA × Fin KB) ℝ) ^ ξ.c i l) *
        (if i = i₀ then X (i₀, j) else 1) := by
    intro i
    by_cases hi : i = i₀
    · subst hi
      simp only [Function.update_self, ite_true]
      exact prod_pow_incf (fun l => (X (i, l) : MvPolynomial (Fin KA × Fin KB) ℝ)) _ j
    · simp [hi]
  rw [prod_congr rfl fun i _ => h i, prod_mul_distrib]
  simp

theorem partB_bToC (ξ : Config KA KB) (i₀ : Fin KA) (j : Fin KB) :
    partB (bToC ξ i₀ j) = (∏ l ∈ univ.erase j, margB l ^ ξ.b l) * margB j ^ (ξ.b j - 1) := by
  simp only [partB, bToC]
  rw [← prod_erase_mul _ _ (mem_univ j)]
  rw [prod_congr rfl fun l hl => by rw [decf, Function.update_of_ne (ne_of_mem_erase hl)]]
  rw [decf, Function.update_self]

theorem selDrift_partA (i₀ : Fin KA) (ξ : Config KA KB) :
    selDrift i₀ (partA ξ) =
      ((ξ.a i₀ : MvPolynomial (Fin KA × Fin KB) ℝ) - (ξ.sumA : MvPolynomial _ ℝ) * margA i₀) *
        partA ξ := by
  rw [partA, derivation_prod_pow_of_log _ _ _ (fun i => C (if i = i₀ then 1 else 0) - margA i₀) _
    (fun i _ => selDrift_margA i₀ i)]
  congr 1
  simp only [mul_sub, sum_sub_distrib, Config.sumA, Nat.cast_sum, ← sum_mul]
  congr 1
  rw [sum_eq_single i₀ (fun i _ hi => by simp [hi]) (by simp)]
  simp

theorem selDrift_partC (i₀ : Fin KA) (ξ : Config KA KB) :
    selDrift i₀ (partC ξ) =
      ((ξ.cRow i₀ : MvPolynomial (Fin KA × Fin KB) ℝ) - (ξ.t : MvPolynomial _ ℝ) * margA i₀) *
        partC ξ := by
  rw [partC, ← prod_product' (f := fun i j => (X (i, j) : MvPolynomial _ ℝ) ^ ξ.c i j)]
  rw [derivation_prod_pow_of_log _ (univ ×ˢ univ) (fun ij => X ij)
    (fun ij => C (if ij.1 = i₀ then 1 else 0) - margA i₀)
    (fun ij => ξ.c ij.1 ij.2) (fun ij _ => by rcases ij with ⟨i, j⟩; exact selDrift_X i₀ i j)]
  congr 1
  simp only [mul_sub, sum_sub_distrib, Config.t, Config.cRow, Nat.cast_sum, ← sum_mul]
  rw [sum_product, sum_product]
  congr 1
  rw [sum_eq_single i₀ (fun i _ hi => by simp [hi]) (by simp)]
  simp

theorem selDrift_partB (i₀ : Fin KA) (ξ : Config KA KB) :
    selDrift i₀ (partB ξ) =
      (∑ j, ((ξ.b j : ℕ) : MvPolynomial (Fin KA × Fin KB) ℝ) * (partB (bToC ξ i₀ j) * X (i₀, j))) -
        (ξ.sumB : MvPolynomial _ ℝ) * margA i₀ * partB ξ := by
  rw [partB, derivation_prod]
  simp only [Derivation.leibniz_pow, selDrift_margB, nsmul_eq_mul, smul_eq_mul]
  rw [Config.sumB, Nat.cast_sum, sum_mul, sum_mul, ← sum_sub_distrib]
  refine sum_congr rfl fun j _ => ?_
  rw [partB_bToC]
  rcases Nat.eq_zero_or_pos (ξ.b j) with h0 | hpos
  · simp [h0]
  · have hsplit : (∏ l, margB (KA := KA) l ^ ξ.b l) =
        margB j ^ (ξ.b j - 1) * margB j * ∏ l ∈ univ.erase j, margB l ^ ξ.b l := by
      rw [← prod_erase_mul _ _ (mem_univ j), ← pow_succ, Nat.sub_add_cancel hpos]; ring
    rw [hsplit]; ring

theorem selDrift_sampleMonomial (i₀ : Fin KA) (ξ : Config KA KB) :
    selDrift i₀ (sampleMonomial ξ) =
      ((ξ.mA i₀ : ℕ) : MvPolynomial (Fin KA × Fin KB) ℝ) * sampleMonomial ξ +
        (∑ j, ((ξ.b j : ℕ) : MvPolynomial (Fin KA × Fin KB) ℝ) * sampleMonomial (bToC ξ i₀ j)) -
        ((ξ.n : ℕ) : MvPolynomial (Fin KA × Fin KB) ℝ) * sampleMonomial (incA ξ i₀) := by
  have hAb : ∀ j, partA (bToC ξ i₀ j) = partA ξ := fun j => rfl
  have hBi : partB (incA ξ i₀) = partB ξ := rfl
  have hCi : partC (incA ξ i₀) = partC ξ := rfl
  have hsum : (∑ j, ((ξ.b j : ℕ) : MvPolynomial (Fin KA × Fin KB) ℝ) *
      sampleMonomial (bToC ξ i₀ j)) = partA ξ * partC ξ *
      ∑ j, ((ξ.b j : ℕ) : MvPolynomial (Fin KA × Fin KB) ℝ) *
        (partB (bToC ξ i₀ j) * X (i₀, j)) := by
    rw [mul_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [sampleMonomial, hAb, partC_bToC]
    ring
  have hinc : sampleMonomial (incA ξ i₀) = partA ξ * margA i₀ * partB ξ * partC ξ := by
    rw [sampleMonomial, partA_incA, hBi, hCi]
  rw [hsum, hinc, sampleMonomial, Derivation.leibniz, Derivation.leibniz, selDrift_partA,
    selDrift_partB, selDrift_partC]
  simp only [smul_eq_mul, Config.mA, Config.n, Nat.cast_add]
  ring

theorem selDrift_sampleMonomial_eq_sel (i₀ : Fin KA) (ξ : Config KA KB)
    (x : Fin KA × Fin KB → ℝ) :
    eval x (selDrift i₀ (sampleMonomial ξ)) = sel i₀ (fun η => eval x (sampleMonomial η)) ξ := by
  rw [selDrift_sampleMonomial, sel]
  simp [map_sum]

end Rhone.Diffusion
