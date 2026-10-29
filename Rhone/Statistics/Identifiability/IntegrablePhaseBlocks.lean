/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.IntegrableInvariantSupport

/-! # Block propagation for arbitrary locally-L1 two-stage generator histories -/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory Matrix
open scoped Topology Matrix
namespace Rhone.Statistics.Identifiability.IntegrablePhase
variable {n m : ℕ}

lemma pre_transition
    (N : ℝ → Matrix (Fin (n + m)) (Fin (n + m)) ℝ)
    (A : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hN : ∀ i j, LocallyIntegrable (fun t => N t i j) volume)
    (hA : ∀ i j, LocallyIntegrable (fun t => A t i j) volume)
    (hpp : ∀ᵐ t, ∀ i j, N t (Fin.castAdd m i) (Fin.castAdd m j) = A t i j)
    (hlp : ∀ᵐ t, ∀ i j, N t (Fin.natAdd n i) (Fin.castAdd m j) = 0)
    (a b : ℝ) (i j : Fin n) :
    inhomogeneousTransition N a b (Fin.castAdd m i) (Fin.castAdd m j) =
      inhomogeneousTransition A a b i j := by
  let z : ℝ → Fin n → ℝ := fun t l =>
    inhomogeneousTransition N a t (Fin.castAdd m i) (Fin.castAdd m l)
  have hd : ∀ᵐ t, t ∈ uIcc a b → ∀ l,
      HasDerivAt (fun u => z u l) ((z t ᵥ* A t) l) t := by
    filter_upwards [integrableTransition_ae_hasDerivAt_right N hN, hpp, hlp]
      with t ht hpt hlt _ l
    have he := ht a (Fin.castAdd m i) (Fin.castAdd m l)
    simpa only [Matrix.mul_apply, Fin.sum_univ_add, hpt, hlt, mul_zero,
      Finset.sum_const_zero, add_zero, Matrix.vecMul, dotProduct, z] using he
  have he := finiteRow_integrable_homogeneous_eq_transition A hA z a b
    (fun l => integrableTransition_entry_ac_right N hN a a b _ _) hd
  have hz : z a = (1 : Matrix (Fin n) (Fin n) ℝ) i := by
    funext l
    simp [z, integrableTransition_self N hN, Matrix.one_apply]
  rw [hz] at he
  have hj := congrFun he j
  simpa only [Matrix.vecMul, dotProduct, Matrix.one_apply, ite_mul,
    one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true] using hj

lemma post_pre_transition
    (N : ℝ → Matrix (Fin (n + m)) (Fin (n + m)) ℝ)
    (A : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hN : ∀ i j, LocallyIntegrable (fun t => N t i j) volume)
    (hA : ∀ i j, LocallyIntegrable (fun t => A t i j) volume)
    (hpp : ∀ᵐ t, ∀ i j, N t (Fin.castAdd m i) (Fin.castAdd m j) = A t i j)
    (hlp : ∀ᵐ t, ∀ i j, N t (Fin.natAdd n i) (Fin.castAdd m j) = 0)
    (a b : ℝ) (i : Fin m) (j : Fin n) :
    inhomogeneousTransition N a b (Fin.natAdd n i) (Fin.castAdd m j) = 0 := by
  let z : ℝ → Fin n → ℝ := fun t l =>
    inhomogeneousTransition N a t (Fin.natAdd n i) (Fin.castAdd m l)
  have hd : ∀ᵐ t, t ∈ uIcc a b → ∀ l,
      HasDerivAt (fun u => z u l) (∑ k, z t k * A t k l) t := by
    filter_upwards [integrableTransition_ae_hasDerivAt_right N hN, hpp, hlp]
      with t ht hpt hlt _ l
    have he := ht a (Fin.natAdd n i) (Fin.castAdd m l)
    simpa only [Matrix.mul_apply, Fin.sum_univ_add, hpt, hlt, mul_zero,
      Finset.sum_const_zero, add_zero, z] using he
  have hz : z a = 0 := by
    funext l
    have hne : Fin.natAdd n i ≠ Fin.castAdd m l := by
      intro he
      have hv := congrArg Fin.val he
      simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
      omega
    simp [z, integrableTransition_self N hN, hne]
  exact congrFun (finiteRow_integrable_solution_eq_zero A z hA a b
    (fun l => integrableTransition_entry_ac_right N hN a a b _ _) hd hz) j

lemma post_transition
    (N : ℝ → Matrix (Fin (n + m)) (Fin (n + m)) ℝ)
    (A : ℝ → Matrix (Fin n) (Fin n) ℝ) (B : ℝ → Matrix (Fin m) (Fin m) ℝ)
    (hN : ∀ i j, LocallyIntegrable (fun t => N t i j) volume)
    (hA : ∀ i j, LocallyIntegrable (fun t => A t i j) volume)
    (hB : ∀ i j, LocallyIntegrable (fun t => B t i j) volume)
    (hpp : ∀ᵐ t, ∀ i j, N t (Fin.castAdd m i) (Fin.castAdd m j) = A t i j)
    (hlp : ∀ᵐ t, ∀ i j, N t (Fin.natAdd n i) (Fin.castAdd m j) = 0)
    (hll : ∀ᵐ t, ∀ i j, N t (Fin.natAdd n i) (Fin.natAdd n j) = B t i j)
    (a b : ℝ) (i j : Fin m) :
    inhomogeneousTransition N a b (Fin.natAdd n i) (Fin.natAdd n j) =
      inhomogeneousTransition B a b i j := by
  let z : ℝ → Fin m → ℝ := fun t l =>
    inhomogeneousTransition N a t (Fin.natAdd n i) (Fin.natAdd n l)
  have hd : ∀ᵐ t, t ∈ uIcc a b → ∀ l,
      HasDerivAt (fun u => z u l) ((z t ᵥ* B t) l) t := by
    filter_upwards [integrableTransition_ae_hasDerivAt_right N hN, hll]
      with t ht hlt _ l
    have he := ht a (Fin.natAdd n i) (Fin.natAdd n l)
    simpa only [Matrix.mul_apply, Fin.sum_univ_add,
      post_pre_transition N A hN hA hpp hlp, hlt, zero_mul,
      Finset.sum_const_zero, zero_add, Matrix.vecMul, dotProduct, z] using he
  have he := finiteRow_integrable_homogeneous_eq_transition B hB z a b
    (fun l => integrableTransition_entry_ac_right N hN a a b _ _) hd
  have hz : z a = (1 : Matrix (Fin m) (Fin m) ℝ) i := by
    funext l
    simp [z, integrableTransition_self N hN, Matrix.one_apply]
  rw [hz] at he
  have hj := congrFun he j
  simpa only [Matrix.vecMul, dotProduct, Matrix.one_apply, ite_mul,
    one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true] using hj

end Rhone.Statistics.Identifiability.IntegrablePhase
