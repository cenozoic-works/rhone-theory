/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Diffusion.WeakSelectionGenerator
public import Mathlib.Algebra.MvPolynomial.PDeriv

/-! # The neutral two-locus generator on sampling monomials -/

@[expose] public section

namespace Rhone.Diffusion

open MvPolynomial Finset LinearAlgebra.Recursion Analysis.TruncationRemainder

variable {KA KB : ℕ}

theorem incf_decf_of_ne_zero {ι : Type*} [DecidableEq ι] {f : ι → ℕ} {k : ι} (h : f k ≠ 0) :
    incf (decf f k) k = f := by
  funext l
  by_cases hl : l = k
  · subst hl
    rw [incf_self, decf_self]
    omega
  · rw [incf_of_ne _ hl, decf_of_ne _ hl]

theorem prod_pow_eq_prod_pow_decf_mul {ι M : Type*} [Fintype ι] [DecidableEq ι] [CommMonoid M]
    (g : ι → M) {f : ι → ℕ} {k : ι} (h : f k ≠ 0) :
    ∏ l, g l ^ f l = (∏ l, g l ^ decf f k l) * g k := by
  conv_lhs => rw [← incf_decf_of_ne_zero h]
  exact prod_pow_incf g _ k

theorem derivation_prod_pow {R A ι : Type*} [CommSemiring R] [CommRing A] [Algebra R A]
    [Fintype ι] [DecidableEq ι] (D : Derivation R A A) (g : ι → A) (f : ι → ℕ) :
    D (∏ l, g l ^ f l) = ∑ k, (f k : A) * D (g k) * ∏ l, g l ^ decf f k l := by
  rw [derivation_prod]
  refine sum_congr rfl fun k _ => ?_
  have hk : ∏ l, g l ^ decf f k l = (∏ l ∈ univ.erase k, g l ^ f l) * g k ^ (f k - 1) := by
    rw [← prod_erase_mul _ _ (mem_univ k), decf_self]
    congr 1
    exact prod_congr rfl fun l hl => by rw [decf_of_ne _ (ne_of_mem_erase hl)]
  rw [hk, Derivation.leibniz_pow]
  simp only [smul_eq_mul, nsmul_eq_mul]
  ring

theorem decC_apply_eq_decf (m : Fin KA → Fin KB → ℕ) (g p : Fin KA × Fin KB) :
    Config.decC m g.1 g.2 p.1 p.2 = decf (fun q : Fin KA × Fin KB => m q.1 q.2) g p := by
  rcases g with ⟨i, j⟩
  rcases p with ⟨i', j'⟩
  by_cases hi : i' = i
  · subst hi
    by_cases hj : j' = j
    · subst hj
      simp [Config.decC, decf]
    · have hne : ((i', j') : Fin KA × Fin KB) ≠ (i', j) := by simp [hj]
      simp [Config.decC, decf, Function.update_of_ne hj, Function.update_of_ne hne]
  · have hne : ((i', j') : Fin KA × Fin KB) ≠ (i, j) := by simp [hi]
    simp [Config.decC, decf, Function.update_of_ne hi, Function.update_of_ne hne]

theorem partC_eq_prod (ξ : Config KA KB) :
    partC ξ = ∏ p : Fin KA × Fin KB, X p ^ ξ.c p.1 p.2 := by
  rw [partC, ← Fintype.prod_prod_type' (fun i j => (X (i, j) : MvPolynomial _ ℝ) ^ ξ.c i j)]

theorem partC_dropC_eq_prod (ξ : Config KA KB) (g : Fin KA × Fin KB) :
    partC (ξ.dropC g.1 g.2) =
      ∏ p : Fin KA × Fin KB, X p ^ decf (fun q : Fin KA × Fin KB => ξ.c q.1 q.2) g p := by
  rw [partC_eq_prod]
  exact prod_congr rfl fun p _ => by rw [← decC_apply_eq_decf]; rfl

theorem sampleMonomial_eq_margA_mul (ξ : Config KA KB) {i : Fin KA} (h : ξ.a i ≠ 0) :
    sampleMonomial ξ = margA i * sampleMonomial (ξ.dropA i) := by
  have hB : partB (ξ.dropA i) = partB ξ := rfl
  have hC : partC (ξ.dropA i) = partC ξ := rfl
  rw [sampleMonomial, sampleMonomial, hB, hC, partA, partA,
    prod_pow_eq_prod_pow_decf_mul (fun l => margA (KB := KB) l) h]
  simp only [Config.dropA]
  ring

theorem sampleMonomial_eq_margB_mul (ξ : Config KA KB) {j : Fin KB} (h : ξ.b j ≠ 0) :
    sampleMonomial ξ = margB j * sampleMonomial (ξ.dropB j) := by
  have hA : partA (ξ.dropB j) = partA ξ := rfl
  have hC : partC (ξ.dropB j) = partC ξ := rfl
  rw [sampleMonomial, sampleMonomial, hA, hC, partB, partB,
    prod_pow_eq_prod_pow_decf_mul (fun l => margB (KA := KA) l) h]
  simp only [Config.dropB]
  ring

theorem sampleMonomial_eq_X_mul (ξ : Config KA KB) {i : Fin KA} {j : Fin KB}
    (h : ξ.c i j ≠ 0) :
    sampleMonomial ξ = X (i, j) * sampleMonomial (ξ.dropC i j) := by
  have hA : partA (ξ.dropC i j) = partA ξ := rfl
  have hB : partB (ξ.dropC i j) = partB ξ := rfl
  rw [sampleMonomial, sampleMonomial, hA, hB, partC_eq_prod,
    partC_dropC_eq_prod ξ (i, j),
    prod_pow_eq_prod_pow_decf_mul (fun p => (X p : MvPolynomial (Fin KA × Fin KB) ℝ))
      (f := fun q : Fin KA × Fin KB => ξ.c q.1 q.2) (k := (i, j)) h]
  ring

theorem sampleMonomial_mergeAB (ξ : Config KA KB) (i : Fin KA) (j : Fin KB) :
    sampleMonomial (ξ.mergeAB i j) = X (i, j) * sampleMonomial ((ξ.dropA i).dropB j) := by
  have hA : partA (ξ.mergeAB i j) = partA ((ξ.dropA i).dropB j) := rfl
  have hB : partB (ξ.mergeAB i j) = partB ((ξ.dropA i).dropB j) := rfl
  have hC : partC (ξ.mergeAB i j) = partC (bToC ξ i j) := rfl
  have hC' : partC ((ξ.dropA i).dropB j) = partC ξ := rfl
  rw [sampleMonomial, sampleMonomial, hA, hB, hC, hC', partC_bToC]
  ring

theorem sampleMonomial_killA (ξ : Config KA KB) (i : Fin KA) (j : Fin KB) :
    sampleMonomial (ξ.killA i j) = margB j * sampleMonomial (ξ.dropC i j) := by
  have hA : partA (ξ.killA i j) = partA (ξ.dropC i j) := rfl
  have hC : partC (ξ.killA i j) = partC (ξ.dropC i j) := rfl
  have hB : partB (ξ.killA i j) = partB (ξ.dropC i j) * margB j :=
    prod_pow_incf (fun l => margB (KA := KA) l) ξ.b j
  rw [sampleMonomial, sampleMonomial, hA, hB, hC]
  ring

theorem sampleMonomial_killB (ξ : Config KA KB) (i : Fin KA) (j : Fin KB) :
    sampleMonomial (ξ.killB i j) = margA i * sampleMonomial (ξ.dropC i j) := by
  have hB : partB (ξ.killB i j) = partB (ξ.dropC i j) := rfl
  have hC : partC (ξ.killB i j) = partC (ξ.dropC i j) := rfl
  have hA : partA (ξ.killB i j) = partA (ξ.dropC i j) * margA i :=
    prod_pow_incf (fun l => margA (KB := KB) l) ξ.a i
  rw [sampleMonomial, sampleMonomial, hA, hB, hC]
  ring

theorem sampleMonomial_split (ξ : Config KA KB) (i : Fin KA) (j : Fin KB) :
    sampleMonomial (ξ.split i j) = margA i * margB j * sampleMonomial (ξ.dropC i j) := by
  have hC : partC (ξ.split i j) = partC (ξ.dropC i j) := rfl
  have hA : partA (ξ.split i j) = partA (ξ.dropC i j) * margA i :=
    prod_pow_incf (fun l => margA (KB := KB) l) ξ.a i
  have hB : partB (ξ.split i j) = partB (ξ.dropC i j) * margB j :=
    prod_pow_incf (fun l => margB (KA := KA) l) ξ.b j
  rw [sampleMonomial, sampleMonomial, hA, hB, hC]
  ring

theorem pderiv_margA (g : Fin KA × Fin KB) (i : Fin KA) :
    pderiv g (margA (KB := KB) i) = if g.1 = i then 1 else 0 := by
  classical
  rcases g with ⟨i', j'⟩
  simp only [margA, map_sum, pderiv_X, Pi.single_apply, Prod.mk.injEq]
  by_cases h : i = i'
  · subst h
    simp
  · simp [h, Ne.symm h]

theorem pderiv_margB (g : Fin KA × Fin KB) (j : Fin KB) :
    pderiv g (margB (KA := KA) j) = if g.2 = j then 1 else 0 := by
  classical
  rcases g with ⟨i', j'⟩
  simp only [margB, map_sum, pderiv_X, Pi.single_apply, Prod.mk.injEq]
  by_cases h : j = j'
  · subst h
    simp
  · simp [h, Ne.symm h]

theorem pderiv_partA (g : Fin KA × Fin KB) (ξ : Config KA KB) :
    pderiv g (partA ξ) =
      ((ξ.a g.1 : ℕ) : MvPolynomial (Fin KA × Fin KB) ℝ) * partA (ξ.dropA g.1) := by
  rw [partA, derivation_prod_pow, sum_eq_single g.1]
  · simp only [pderiv_margA, ite_true, mul_one]
    rfl
  · intro k _ hk
    simp [pderiv_margA, Ne.symm hk]
  · simp

theorem pderiv_partB (g : Fin KA × Fin KB) (ξ : Config KA KB) :
    pderiv g (partB ξ) =
      ((ξ.b g.2 : ℕ) : MvPolynomial (Fin KA × Fin KB) ℝ) * partB (ξ.dropB g.2) := by
  rw [partB, derivation_prod_pow, sum_eq_single g.2]
  · simp only [pderiv_margB, ite_true, mul_one]
    rfl
  · intro k _ hk
    simp [pderiv_margB, Ne.symm hk]
  · simp

theorem pderiv_partC (g : Fin KA × Fin KB) (ξ : Config KA KB) :
    pderiv g (partC ξ) =
      ((ξ.c g.1 g.2 : ℕ) : MvPolynomial (Fin KA × Fin KB) ℝ) * partC (ξ.dropC g.1 g.2) := by
  classical
  rw [partC_eq_prod, partC_dropC_eq_prod, derivation_prod_pow, sum_eq_single g]
  · rw [pderiv_X_self, mul_one]
  · intro k _ hk
    simp [pderiv_X, hk]
  · simp

theorem pderiv_sampleMonomial (g : Fin KA × Fin KB) (ξ : Config KA KB) :
    pderiv g (sampleMonomial ξ) =
      ((ξ.a g.1 : ℕ) : MvPolynomial (Fin KA × Fin KB) ℝ) * sampleMonomial (ξ.dropA g.1) +
      ((ξ.b g.2 : ℕ) : MvPolynomial (Fin KA × Fin KB) ℝ) * sampleMonomial (ξ.dropB g.2) +
      ((ξ.c g.1 g.2 : ℕ) : MvPolynomial (Fin KA × Fin KB) ℝ) *
        sampleMonomial (ξ.dropC g.1 g.2) := by
  have h1 : partB (ξ.dropA g.1) = partB ξ := rfl
  have h2 : partC (ξ.dropA g.1) = partC ξ := rfl
  have h3 : partA (ξ.dropB g.2) = partA ξ := rfl
  have h4 : partC (ξ.dropB g.2) = partC ξ := rfl
  have h5 : partA (ξ.dropC g.1 g.2) = partA ξ := rfl
  have h6 : partB (ξ.dropC g.1 g.2) = partB ξ := rfl
  rw [sampleMonomial, Derivation.leibniz, Derivation.leibniz, pderiv_partA, pderiv_partB,
    pderiv_partC, sampleMonomial, sampleMonomial, sampleMonomial, h1, h2, h3, h4, h5, h6]
  simp only [smul_eq_mul]
  ring

theorem sum_X_mul_pderiv_sampleMonomial (ξ : Config KA KB) :
    ∑ g, X g * pderiv g (sampleMonomial ξ) =
      ((ξ.n : ℕ) : MvPolynomial (Fin KA × Fin KB) ℝ) * sampleMonomial ξ := by
  have hA : ∀ i, ((ξ.a i : ℕ) : MvPolynomial (Fin KA × Fin KB) ℝ) *
      (margA i * sampleMonomial (ξ.dropA i)) =
        ((ξ.a i : ℕ) : MvPolynomial (Fin KA × Fin KB) ℝ) * sampleMonomial ξ := by
    intro i
    by_cases h : ξ.a i = 0
    · simp [h]
    · rw [← sampleMonomial_eq_margA_mul ξ h]
  have hB : ∀ j, ((ξ.b j : ℕ) : MvPolynomial (Fin KA × Fin KB) ℝ) *
      (margB j * sampleMonomial (ξ.dropB j)) =
        ((ξ.b j : ℕ) : MvPolynomial (Fin KA × Fin KB) ℝ) * sampleMonomial ξ := by
    intro j
    by_cases h : ξ.b j = 0
    · simp [h]
    · rw [← sampleMonomial_eq_margB_mul ξ h]
  have hC : ∀ i j, ((ξ.c i j : ℕ) : MvPolynomial (Fin KA × Fin KB) ℝ) *
      (X (i, j) * sampleMonomial (ξ.dropC i j)) =
        ((ξ.c i j : ℕ) : MvPolynomial (Fin KA × Fin KB) ℝ) * sampleMonomial ξ := by
    intro i j
    by_cases h : ξ.c i j = 0
    · simp [h]
    · rw [← sampleMonomial_eq_X_mul ξ h]
  simp only [pderiv_sampleMonomial, mul_add, sum_add_distrib, Fintype.sum_prod_type]
  have e1 : ∑ i, ∑ j, (X (i, j) : MvPolynomial (Fin KA × Fin KB) ℝ) *
      (((ξ.a i : ℕ) : MvPolynomial _ ℝ) * sampleMonomial (ξ.dropA i)) =
      ∑ i, ((ξ.a i : ℕ) : MvPolynomial _ ℝ) * sampleMonomial ξ := by
    refine sum_congr rfl fun i _ => ?_
    rw [← hA i, margA, sum_mul, mul_sum]
    exact sum_congr rfl fun j _ => by ring
  have e2 : ∑ i, ∑ j, (X (i, j) : MvPolynomial (Fin KA × Fin KB) ℝ) *
      (((ξ.b j : ℕ) : MvPolynomial _ ℝ) * sampleMonomial (ξ.dropB j)) =
      ∑ j, ((ξ.b j : ℕ) : MvPolynomial _ ℝ) * sampleMonomial ξ := by
    rw [sum_comm]
    refine sum_congr rfl fun j _ => ?_
    rw [← hB j, margB, sum_mul, mul_sum]
    exact sum_congr rfl fun i _ => by ring
  have e3 : ∑ i, ∑ j, (X (i, j) : MvPolynomial (Fin KA × Fin KB) ℝ) *
      (((ξ.c i j : ℕ) : MvPolynomial _ ℝ) * sampleMonomial (ξ.dropC i j)) =
      ∑ i, ∑ j, ((ξ.c i j : ℕ) : MvPolynomial _ ℝ) * sampleMonomial ξ := by
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    rw [← hC i j]
    ring
  rw [e1, e2, e3]
  simp only [← sum_mul, ← add_mul]
  congr 1
  simp only [Config.n, Config.sumA, Config.sumB, Config.t, Nat.cast_add, Nat.cast_sum]

theorem pderiv_natCast_mul (g : Fin KA × Fin KB) (k : ℕ)
    (f : MvPolynomial (Fin KA × Fin KB) ℝ) :
    pderiv g ((k : MvPolynomial (Fin KA × Fin KB) ℝ) * f) =
      (k : MvPolynomial _ ℝ) * pderiv g f := by
  rw [Derivation.leibniz, Derivation.map_natCast, smul_eq_mul, smul_zero, add_zero]

theorem sum_X_mul_X_mul_pderiv_pderiv_sampleMonomial (ξ : Config KA KB) :
    ∑ g, ∑ h, X g * X h * pderiv g (pderiv h (sampleMonomial ξ)) =
      ((ξ.n : ℕ) : MvPolynomial (Fin KA × Fin KB) ℝ) * ((ξ.n : ℕ) - 1) * sampleMonomial ξ := by
  classical
  have hE := sum_X_mul_pderiv_sampleMonomial ξ
  have h2 : ∑ g, X g * pderiv g (∑ h, X h * pderiv h (sampleMonomial ξ)) =
      ∑ g, X g * pderiv g (((ξ.n : ℕ) : MvPolynomial (Fin KA × Fin KB) ℝ) *
        sampleMonomial ξ) := by rw [hE]
  simp only [map_sum, Derivation.leibniz, smul_eq_mul, pderiv_X, Derivation.map_natCast,
    Pi.single_apply, mul_zero, add_zero, mul_add, sum_add_distrib] at h2
  have h3 : ∑ g, X g * ∑ h, (X h : MvPolynomial (Fin KA × Fin KB) ℝ) *
      pderiv g (pderiv h (sampleMonomial ξ)) =
      ∑ g, ∑ h, X g * X h * pderiv g (pderiv h (sampleMonomial ξ)) := by
    refine sum_congr rfl fun g _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun h _ => by ring
  have h4 : ∑ g, (X g : MvPolynomial (Fin KA × Fin KB) ℝ) *
      ∑ h, pderiv h (sampleMonomial ξ) * (if h = g then 1 else 0) =
      ∑ g, X g * pderiv g (sampleMonomial ξ) := by
    refine sum_congr rfl fun g _ => ?_
    simp
  have h5 : ∑ g, (X g : MvPolynomial (Fin KA × Fin KB) ℝ) *
      (((ξ.n : ℕ) : MvPolynomial (Fin KA × Fin KB) ℝ) * pderiv g (sampleMonomial ξ)) =
      ((ξ.n : ℕ) : MvPolynomial (Fin KA × Fin KB) ℝ) * ∑ g, X g * pderiv g (sampleMonomial ξ) := by
    rw [mul_sum]
    exact sum_congr rfl fun g _ => by ring
  rw [h3, h4, h5, hE] at h2
  linear_combination h2

def gameteSimplex (KA KB : ℕ) : Set (Fin KA × Fin KB → ℝ) :=
  {x | (∀ g, 0 ≤ x g) ∧ ∑ g, x g = 1}

noncomputable def neutralDrift (θA θB ρ : ℝ) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ)
    (g : Fin KA × Fin KB) : MvPolynomial (Fin KA × Fin KB) ℝ :=
  C θA * (C (πA g.1) * margB g.2 - X g) + C θB * (C (πB g.2) * margA g.1 - X g) +
    C ρ * (margA g.1 * margB g.2 - X g)

noncomputable def neutralGenerator (θA θB ρ : ℝ) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ)
    (f : MvPolynomial (Fin KA × Fin KB) ℝ) : MvPolynomial (Fin KA × Fin KB) ℝ :=
  (∑ g, ∑ h, X g * (C (if g = h then 1 else 0) - X h) * pderiv g (pderiv h f)) +
    ∑ g, neutralDrift θA θB ρ πA πB g * pderiv g f

noncomputable def twoLocusGenerator (θA θB ρ : ℝ) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ)
    (i₀ : Fin KA) (σ : ℝ) (f : MvPolynomial (Fin KA × Fin KB) ℝ) :
    MvPolynomial (Fin KA × Fin KB) ℝ :=
  neutralGenerator θA θB ρ πA πB f + C σ * selDrift i₀ f

theorem eval_count_A (x : Fin KA × Fin KB → ℝ) (η : Config KA KB) (i : Fin KA) :
    ((η.a i : ℕ) : ℝ) * (eval x (margA i) * eval x (sampleMonomial (η.dropA i))) =
      ((η.a i : ℕ) : ℝ) * eval x (sampleMonomial η) := by
  by_cases h : η.a i = 0
  · simp [h]
  · rw [sampleMonomial_eq_margA_mul η h, map_mul]

theorem eval_count_B (x : Fin KA × Fin KB → ℝ) (η : Config KA KB) (j : Fin KB) :
    ((η.b j : ℕ) : ℝ) * (eval x (margB j) * eval x (sampleMonomial (η.dropB j))) =
      ((η.b j : ℕ) : ℝ) * eval x (sampleMonomial η) := by
  by_cases h : η.b j = 0
  · simp [h]
  · rw [sampleMonomial_eq_margB_mul η h, map_mul]

theorem eval_count_C (x : Fin KA × Fin KB → ℝ) (η : Config KA KB) (i : Fin KA) (j : Fin KB) :
    ((η.c i j : ℕ) : ℝ) * (x (i, j) * eval x (sampleMonomial (η.dropC i j))) =
      ((η.c i j : ℕ) : ℝ) * eval x (sampleMonomial η) := by
  by_cases h : η.c i j = 0
  · simp [h]
  · rw [sampleMonomial_eq_X_mul η h, map_mul, eval_X]

theorem eval_X_mul_pderiv_pderiv_self (x : Fin KA × Fin KB → ℝ) (ξ : Config KA KB)
    (i : Fin KA) (j : Fin KB) :
    x (i, j) * eval x (pderiv (i, j) (pderiv (i, j) (sampleMonomial ξ))) =
      x (i, j) * (((ξ.a i : ℕ) : ℝ) * (((ξ.dropA i).a i : ℕ) : ℝ) *
          eval x (sampleMonomial ((ξ.dropA i).dropA i))) +
        x (i, j) * (((ξ.b j : ℕ) : ℝ) * (((ξ.dropB j).b j : ℕ) : ℝ) *
          eval x (sampleMonomial ((ξ.dropB j).dropB j))) +
        2 * (((ξ.a i : ℕ) : ℝ) * ((ξ.b j : ℕ) : ℝ)) * eval x (sampleMonomial (ξ.mergeAB i j)) +
        2 * (((ξ.a i : ℕ) : ℝ) * ((ξ.c i j : ℕ) : ℝ)) * eval x (sampleMonomial (ξ.dropA i)) +
        2 * (((ξ.b j : ℕ) : ℝ) * ((ξ.c i j : ℕ) : ℝ)) * eval x (sampleMonomial (ξ.dropB j)) +
        ((ξ.c i j : ℕ) : ℝ) * (((ξ.dropC i j).c i j : ℕ) : ℝ) *
          eval x (sampleMonomial (ξ.dropC i j)) := by
  have hm := congrArg (eval x) (sampleMonomial_mergeAB ξ i j)
  have hAC := eval_count_C x (ξ.dropA i) i j
  have hBC := eval_count_C x (ξ.dropB j) i j
  have hCC := eval_count_C x (ξ.dropC i j) i j
  have e1 : (ξ.dropA i).b j = ξ.b j := rfl
  have e2 : (ξ.dropA i).c i j = ξ.c i j := rfl
  have e3 : (ξ.dropB j).a i = ξ.a i := rfl
  have e4 : (ξ.dropB j).c i j = ξ.c i j := rfl
  have e5 : (ξ.dropC i j).a i = ξ.a i := rfl
  have e6 : (ξ.dropC i j).b j = ξ.b j := rfl
  have f1 : (ξ.dropB j).dropA i = (ξ.dropA i).dropB j := rfl
  have f2 : (ξ.dropC i j).dropA i = (ξ.dropA i).dropC i j := rfl
  have f3 : (ξ.dropC i j).dropB j = (ξ.dropB j).dropC i j := rfl
  simp only [pderiv_sampleMonomial, map_add, pderiv_natCast_mul] at ⊢
  simp only [map_add, map_mul, map_natCast, eval_X, e1, e2, e3, e4, e5, e6, f1, f2,
    f3] at hm hAC hBC hCC ⊢
  linear_combination (-2 * ((ξ.a i : ℕ) : ℝ) * ((ξ.b j : ℕ) : ℝ)) * hm +
    (2 * ((ξ.a i : ℕ) : ℝ)) * hAC + (2 * ((ξ.b j : ℕ) : ℝ)) * hBC + ((ξ.c i j : ℕ) : ℝ) * hCC

theorem eval_sum_X_mul_pderiv_pderiv_self (x : Fin KA × Fin KB → ℝ) (ξ : Config KA KB) :
    ∑ g, x g * eval x (pderiv g (pderiv g (sampleMonomial ξ))) =
      (∑ i, ((ξ.coalA i : ℕ) : ℝ) * eval x (sampleMonomial (ξ.dropA i))) +
        (∑ j, ((ξ.coalB j : ℕ) : ℝ) * eval x (sampleMonomial (ξ.dropB j))) +
        (∑ i, ∑ j, ((ξ.coalC i j : ℕ) : ℝ) * eval x (sampleMonomial (ξ.dropC i j))) +
        (∑ i, ∑ j, ((ξ.coalAB i j : ℕ) : ℝ) * eval x (sampleMonomial (ξ.mergeAB i j))) := by
  rw [Fintype.sum_prod_type]
  simp only [eval_X_mul_pderiv_pderiv_self, sum_add_distrib]
  have hT1 : ∑ i, ∑ j, x (i, j) * (((ξ.a i : ℕ) : ℝ) * (((ξ.dropA i).a i : ℕ) : ℝ) *
      eval x (sampleMonomial ((ξ.dropA i).dropA i))) =
      ∑ i, ((ξ.a i : ℕ) : ℝ) * (((ξ.dropA i).a i : ℕ) : ℝ) *
        eval x (sampleMonomial (ξ.dropA i)) := by
    refine sum_congr rfl fun i _ => ?_
    have h := eval_count_A x (ξ.dropA i) i
    have hP : eval x (margA (KB := KB) i) = ∑ j, x (i, j) := by simp [margA]
    rw [hP] at h
    rw [← sum_mul]
    linear_combination ((ξ.a i : ℕ) : ℝ) * h
  have hT2 : ∑ i, ∑ j, x (i, j) * (((ξ.b j : ℕ) : ℝ) * (((ξ.dropB j).b j : ℕ) : ℝ) *
      eval x (sampleMonomial ((ξ.dropB j).dropB j))) =
      ∑ j, ((ξ.b j : ℕ) : ℝ) * (((ξ.dropB j).b j : ℕ) : ℝ) *
        eval x (sampleMonomial (ξ.dropB j)) := by
    rw [sum_comm]
    refine sum_congr rfl fun j _ => ?_
    have h := eval_count_B x (ξ.dropB j) j
    have hR : eval x (margB (KA := KA) j) = ∑ i, x (i, j) := by simp [margB]
    rw [hR] at h
    rw [← sum_mul]
    linear_combination ((ξ.b j : ℕ) : ℝ) * h
  have hR1 : ∑ i, ((ξ.coalA i : ℕ) : ℝ) * eval x (sampleMonomial (ξ.dropA i)) =
      ∑ i, ((ξ.a i : ℕ) : ℝ) * (((ξ.dropA i).a i : ℕ) : ℝ) *
        eval x (sampleMonomial (ξ.dropA i)) +
      ∑ i, ∑ j, 2 * (((ξ.a i : ℕ) : ℝ) * ((ξ.c i j : ℕ) : ℝ)) *
        eval x (sampleMonomial (ξ.dropA i)) := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    have hd : (ξ.dropA i).a i = ξ.a i - 1 := decf_self _ _
    simp only [Config.coalA, Config.cRow, hd, Nat.cast_mul, Nat.cast_add, Nat.cast_sum,
      Nat.cast_ofNat, ← sum_mul, ← mul_sum]
    ring
  have hR2 : ∑ j, ((ξ.coalB j : ℕ) : ℝ) * eval x (sampleMonomial (ξ.dropB j)) =
      ∑ j, ((ξ.b j : ℕ) : ℝ) * (((ξ.dropB j).b j : ℕ) : ℝ) *
        eval x (sampleMonomial (ξ.dropB j)) +
      ∑ i, ∑ j, 2 * (((ξ.b j : ℕ) : ℝ) * ((ξ.c i j : ℕ) : ℝ)) *
        eval x (sampleMonomial (ξ.dropB j)) := by
    rw [sum_comm (f := fun i j => 2 * (((ξ.b j : ℕ) : ℝ) * ((ξ.c i j : ℕ) : ℝ)) *
        eval x (sampleMonomial (ξ.dropB j))), ← sum_add_distrib]
    refine sum_congr rfl fun j _ => ?_
    have hd : (ξ.dropB j).b j = ξ.b j - 1 := decf_self _ _
    simp only [Config.coalB, Config.cCol, hd, Nat.cast_mul, Nat.cast_add, Nat.cast_sum,
      Nat.cast_ofNat, ← sum_mul, ← mul_sum]
    ring
  have hR3 : ∑ i, ∑ j, ((ξ.coalC i j : ℕ) : ℝ) * eval x (sampleMonomial (ξ.dropC i j)) =
      ∑ i, ∑ j, ((ξ.c i j : ℕ) : ℝ) * (((ξ.dropC i j).c i j : ℕ) : ℝ) *
        eval x (sampleMonomial (ξ.dropC i j)) := by
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    have hd : (ξ.dropC i j).c i j = ξ.c i j - 1 := by
      simp [Config.dropC, Config.decC, decf_self]
    rw [Config.coalC, hd, Nat.cast_mul]
  have hR4 : ∑ i, ∑ j, ((ξ.coalAB i j : ℕ) : ℝ) * eval x (sampleMonomial (ξ.mergeAB i j)) =
      ∑ i, ∑ j, 2 * (((ξ.a i : ℕ) : ℝ) * ((ξ.b j : ℕ) : ℝ)) *
        eval x (sampleMonomial (ξ.mergeAB i j)) := by
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    simp [Config.coalAB]
  rw [hT1, hT2, hR1, hR2, hR3, hR4]
  ring

theorem sum_eval_margB {x : Fin KA × Fin KB → ℝ} (hx : ∑ g, x g = 1) :
    ∑ j, eval x (margB (KA := KA) j) = 1 := by
  simp only [margB, map_sum, eval_X]
  rw [sum_comm, ← Fintype.sum_prod_type, hx]

theorem sum_eval_margA {x : Fin KA × Fin KB → ℝ} (hx : ∑ g, x g = 1) :
    ∑ i, eval x (margA (KB := KB) i) = 1 := by
  simp only [margA, map_sum, eval_X]
  rw [← Fintype.sum_prod_type, hx]

theorem eval_neutralDrift (θA θB ρ : ℝ) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ)
    (x : Fin KA × Fin KB → ℝ) (i : Fin KA) (j : Fin KB) :
    eval x (neutralDrift θA θB ρ πA πB (i, j)) =
      θA * (πA i * eval x (margB j) - x (i, j)) + θB * (πB j * eval x (margA i) - x (i, j)) +
        ρ * (eval x (margA i) * eval x (margB j) - x (i, j)) := by
  simp [neutralDrift]

theorem sum_eval_neutralDrift_row (θA θB ρ : ℝ) (πA : Fin KA → ℝ) {πB : Fin KB → ℝ}
    (hπB : ∑ j, πB j = 1) {x : Fin KA × Fin KB → ℝ} (hx : ∑ g, x g = 1) (i : Fin KA) :
    ∑ j, eval x (neutralDrift θA θB ρ πA πB (i, j)) = θA * (πA i - eval x (margA i)) := by
  have hP : eval x (margA (KB := KB) i) = ∑ j, x (i, j) := by simp [margA]
  have hR := sum_eval_margB (KA := KA) hx
  simp only [eval_neutralDrift, sum_add_distrib, sum_sub_distrib, ← mul_sum, ← sum_mul,
    ← hP, hR, hπB]
  ring

theorem sum_eval_neutralDrift_col (θA θB ρ : ℝ) {πA : Fin KA → ℝ} (πB : Fin KB → ℝ)
    (hπA : ∑ i, πA i = 1) {x : Fin KA × Fin KB → ℝ} (hx : ∑ g, x g = 1) (j : Fin KB) :
    ∑ i, eval x (neutralDrift θA θB ρ πA πB (i, j)) = θB * (πB j - eval x (margB j)) := by
  have hR : eval x (margB (KA := KA) j) = ∑ i, x (i, j) := by simp [margB]
  have hP := sum_eval_margA (KB := KB) hx
  simp only [eval_neutralDrift, sum_add_distrib, sum_sub_distrib, ← mul_sum, ← sum_mul,
    ← hR, hP, hπA]
  ring

theorem eval_sum_neutralDrift_mul_pderiv (θA θB ρ : ℝ) {πA : Fin KA → ℝ} {πB : Fin KB → ℝ}
    (hπA : ∑ i, πA i = 1) (hπB : ∑ j, πB j = 1) {x : Fin KA × Fin KB → ℝ}
    (hx : ∑ g, x g = 1) (ξ : Config KA KB) :
    ∑ g, eval x (neutralDrift θA θB ρ πA πB g) * eval x (pderiv g (sampleMonomial ξ)) =
      θA * ∑ i, πA i * (((ξ.a i : ℕ) : ℝ) * eval x (sampleMonomial (ξ.dropA i)) +
          ∑ j, ((ξ.c i j : ℕ) : ℝ) * eval x (sampleMonomial (ξ.killA i j))) +
        θB * ∑ j, πB j * (((ξ.b j : ℕ) : ℝ) * eval x (sampleMonomial (ξ.dropB j)) +
          ∑ i, ((ξ.c i j : ℕ) : ℝ) * eval x (sampleMonomial (ξ.killB i j))) +
        ρ * ∑ i, ∑ j, ((ξ.c i j : ℕ) : ℝ) * eval x (sampleMonomial (ξ.split i j)) -
        (θA * ((ξ.nA : ℕ) : ℝ) + θB * ((ξ.nB : ℕ) : ℝ) + ρ * ((ξ.t : ℕ) : ℝ)) *
          eval x (sampleMonomial ξ) := by
  rw [Fintype.sum_prod_type]
  simp only [pderiv_sampleMonomial, map_add, map_mul, map_natCast, mul_add, sum_add_distrib]
  have hD1 : ∑ i, ∑ j, eval x (neutralDrift θA θB ρ πA πB (i, j)) *
      (((ξ.a i : ℕ) : ℝ) * eval x (sampleMonomial (ξ.dropA i))) =
      θA * ∑ i, πA i * (((ξ.a i : ℕ) : ℝ) * eval x (sampleMonomial (ξ.dropA i))) -
        θA * ∑ i, ((ξ.a i : ℕ) : ℝ) * eval x (sampleMonomial ξ) := by
    rw [mul_sum, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [← sum_mul, sum_eval_neutralDrift_row θA θB ρ πA hπB hx i]
    linear_combination (-θA) * eval_count_A x ξ i
  have hD2 : ∑ i, ∑ j, eval x (neutralDrift θA θB ρ πA πB (i, j)) *
      (((ξ.b j : ℕ) : ℝ) * eval x (sampleMonomial (ξ.dropB j))) =
      θB * ∑ j, πB j * (((ξ.b j : ℕ) : ℝ) * eval x (sampleMonomial (ξ.dropB j))) -
        θB * ∑ j, ((ξ.b j : ℕ) : ℝ) * eval x (sampleMonomial ξ) := by
    rw [sum_comm, mul_sum, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun j _ => ?_
    rw [← sum_mul, sum_eval_neutralDrift_col θA θB ρ πB hπA hx j]
    linear_combination (-θB) * eval_count_B x ξ j
  have hD3 : ∀ i j, eval x (neutralDrift θA θB ρ πA πB (i, j)) *
      (((ξ.c i j : ℕ) : ℝ) * eval x (sampleMonomial (ξ.dropC i j))) =
      θA * (πA i * (((ξ.c i j : ℕ) : ℝ) * eval x (sampleMonomial (ξ.killA i j)))) +
        θB * (πB j * (((ξ.c i j : ℕ) : ℝ) * eval x (sampleMonomial (ξ.killB i j)))) +
        ρ * (((ξ.c i j : ℕ) : ℝ) * eval x (sampleMonomial (ξ.split i j))) -
        (θA + θB + ρ) * (((ξ.c i j : ℕ) : ℝ) * eval x (sampleMonomial ξ)) := by
    intro i j
    have hC := eval_count_C x ξ i j
    rw [eval_neutralDrift, sampleMonomial_killA, sampleMonomial_killB, sampleMonomial_split]
    simp only [map_mul]
    linear_combination (-(θA + θB + ρ)) * hC
  simp only [hD3, sum_add_distrib, sum_sub_distrib, ← mul_sum]
  rw [hD1, hD2]
  have hK : ∑ i, ∑ j, πB j * (((ξ.c i j : ℕ) : ℝ) * eval x (sampleMonomial (ξ.killB i j))) =
      ∑ j, πB j * ∑ i, ((ξ.c i j : ℕ) : ℝ) * eval x (sampleMonomial (ξ.killB i j)) := by
    rw [sum_comm]
    simp only [mul_sum]
  rw [hK]
  have hnA : ((ξ.nA : ℕ) : ℝ) = ∑ i, ((ξ.a i : ℕ) : ℝ) + ∑ i, ∑ j, ((ξ.c i j : ℕ) : ℝ) := by
    simp [Config.nA, Config.sumA, Config.t]
  have hnB : ((ξ.nB : ℕ) : ℝ) = ∑ j, ((ξ.b j : ℕ) : ℝ) + ∑ i, ∑ j, ((ξ.c i j : ℕ) : ℝ) := by
    simp [Config.nB, Config.sumB, Config.t]
  have ht : ((ξ.t : ℕ) : ℝ) = ∑ i, ∑ j, ((ξ.c i j : ℕ) : ℝ) := by simp [Config.t]
  rw [hnA, hnB, ht]
  simp only [mul_add, ← sum_mul]
  ring

theorem natCast_mul_sub_one (n : ℕ) : ((n * (n - 1) : ℕ) : ℝ) = (n : ℝ) * ((n : ℝ) - 1) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · simp [h]
  · rw [Nat.cast_mul, Nat.cast_sub h, Nat.cast_one]

theorem eval_neutralGenerator_sampleMonomial (θA θB ρ : ℝ) {πA : Fin KA → ℝ}
    {πB : Fin KB → ℝ} (hπA : ∑ i, πA i = 1) (hπB : ∑ j, πB j = 1) {x : Fin KA × Fin KB → ℝ}
    (hx : ∑ g, x g = 1) (ξ : Config KA KB) :
    eval x (neutralGenerator θA θB ρ πA πB (sampleMonomial ξ)) =
      rhs θA θB ρ πA πB (fun η => eval x (sampleMonomial η)) ξ -
        diag θA θB ρ ξ * eval x (sampleMonomial ξ) := by
  have h2 := congrArg (eval x) (sum_X_mul_X_mul_pderiv_pderiv_sampleMonomial ξ)
  simp only [map_sum, map_mul, map_sub, map_natCast, map_one, eval_X] at h2
  have hsplit : ∑ g, ∑ h, eval x (X g * (C (if g = h then (1 : ℝ) else 0) - X h) *
      pderiv g (pderiv h (sampleMonomial ξ))) =
      ∑ g, x g * eval x (pderiv g (pderiv g (sampleMonomial ξ))) -
        ∑ g, ∑ h, x g * x h * eval x (pderiv g (pderiv h (sampleMonomial ξ))) := by
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun g _ => ?_
    simp only [map_mul, map_sub, eval_X, eval_C, mul_sub, sub_mul, sum_sub_distrib]
    congr 1
    simp
  rw [neutralGenerator, map_add]
  simp only [map_sum]
  rw [hsplit, h2, eval_sum_X_mul_pderiv_pderiv_self]
  simp only [map_mul]
  rw [eval_sum_neutralDrift_mul_pderiv θA θB ρ hπA hπB hx ξ, rhs,
    Rhone.LinearAlgebra.Recursion.diag, natCast_mul_sub_one]
  ring

theorem eval_twoLocusGenerator_sampleMonomial (θA θB ρ : ℝ) {πA : Fin KA → ℝ}
    {πB : Fin KB → ℝ} (hπA : ∑ i, πA i = 1) (hπB : ∑ j, πB j = 1) (i₀ : Fin KA) (σ : ℝ)
    {x : Fin KA × Fin KB → ℝ} (hx : ∑ g, x g = 1) (ξ : Config KA KB) :
    eval x (twoLocusGenerator θA θB ρ πA πB i₀ σ (sampleMonomial ξ)) =
      rhs θA θB ρ πA πB (fun η => eval x (sampleMonomial η)) ξ -
        diag θA θB ρ ξ * eval x (sampleMonomial ξ) +
        σ * sel i₀ (fun η => eval x (sampleMonomial η)) ξ := by
  rw [twoLocusGenerator, map_add, map_mul, eval_C,
    eval_neutralGenerator_sampleMonomial θA θB ρ hπA hπB hx, selDrift_sampleMonomial_eq_sel]

end Rhone.Diffusion
