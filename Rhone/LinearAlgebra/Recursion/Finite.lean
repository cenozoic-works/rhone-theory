/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.Recursion.Config

/-! # Finiteness of blocks, and the classification of the `n ≤ 1` configurations -/

@[expose] public section

namespace Rhone.LinearAlgebra.Recursion

open Finset

variable {KA KB : ℕ}

namespace Config

theorem a_eq_zero_of_sumA (ξ : Config KA KB) (h : ξ.sumA = 0) : ξ.a = fun _ => 0 :=
  funext fun i => Finset.sum_eq_zero_iff.mp h i (Finset.mem_univ i)

theorem b_eq_zero_of_sumB (ξ : Config KA KB) (h : ξ.sumB = 0) : ξ.b = fun _ => 0 :=
  funext fun j => Finset.sum_eq_zero_iff.mp h j (Finset.mem_univ j)

theorem c_eq_zero_of_t (ξ : Config KA KB) (h : ξ.t = 0) : ξ.c = fun _ _ => 0 := by
  refine funext fun i => funext fun j => ?_
  have h1 : ∑ j, ξ.c i j = 0 := Finset.sum_eq_zero_iff.mp h i (Finset.mem_univ i)
  exact Finset.sum_eq_zero_iff.mp h1 j (Finset.mem_univ j)

theorem eq_zero_of_n_eq_zero (ξ : Config KA KB) (h : ξ.n = 0) : ξ = 0 := by
  have h1 : ξ.sumA = 0 := by simp only [n] at h; omega
  have h2 : ξ.sumB = 0 := by simp only [n] at h; omega
  have h3 : ξ.t = 0 := by simp only [n] at h; omega
  exact Config.ext (ξ.a_eq_zero_of_sumA h1) (ξ.b_eq_zero_of_sumB h2) (ξ.c_eq_zero_of_t h3)

theorem exists_incf_of_sum_eq_one {ι : Type*} [Fintype ι] [DecidableEq ι] {f : ι → ℕ}
    (h : ∑ x, f x = 1) : ∃ i, f = incf (fun _ => 0) i := by
  obtain ⟨i, hi⟩ : ∃ i, f i ≠ 0 := by
    by_contra hc
    have hz : ∀ x, f x = 0 := fun x => not_not.mp fun hx => hc ⟨x, hx⟩
    rw [Finset.sum_eq_zero fun x _ => hz x] at h
    exact one_ne_zero h.symm
  have hfi : f i = 1 := by
    have := Finset.single_le_sum (f := f) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  have hsplit := sum_eq_add_erase f i
  have h0 : ∑ x ∈ Finset.univ.erase i, f x = 0 := by omega
  refine ⟨i, funext fun k => ?_⟩
  by_cases hk : k = i
  · subst hk; rw [incf_self, hfi]
  · rw [incf_of_ne _ hk]
    exact Finset.sum_eq_zero_iff.mp h0 k (Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩)

theorem exists_incC_of_sum_eq_one {m : Fin KA → Fin KB → ℕ} (h : ∑ i, ∑ j, m i j = 1) :
    ∃ i j, m = incC (fun _ _ => 0) i j := by
  obtain ⟨i, hi⟩ := exists_incf_of_sum_eq_one (f := fun i => ∑ j, m i j) h
  have hrow : ∑ j, m i j = 1 := by
    have := congrFun hi i
    simpa [incf_self] using this
  obtain ⟨j, hj⟩ := exists_incf_of_sum_eq_one hrow
  refine ⟨i, j, funext fun k => ?_⟩
  by_cases hk : k = i
  · subst hk
    simp only [incC, Function.update_self]
    exact hj
  · have hk0 : ∑ j, m k j = 0 := by
      have := congrFun hi k
      simpa [incf_of_ne _ hk] using this
    have : m k = fun _ => 0 :=
      funext fun j' => Finset.sum_eq_zero_iff.mp hk0 j' (Finset.mem_univ j')
    simp only [incC, Function.update_of_ne hk]
    exact this

theorem exists_e_of_n_eq_one (ξ : Config KA KB) (h : ξ.n = 1) :
    (∃ i, ξ = eA i) ∨ (∃ j, ξ = eB j) ∨ (∃ i j, ξ = eC i j) := by
  simp only [n] at h
  rcases Nat.lt_or_ge ξ.sumA 1 with h1 | h1
  · rcases Nat.lt_or_ge ξ.sumB 1 with h2 | h2
    · have hA : ξ.sumA = 0 := by omega
      have hB : ξ.sumB = 0 := by omega
      have hT : ξ.t = 1 := by omega
      obtain ⟨i, j, hij⟩ := exists_incC_of_sum_eq_one (m := ξ.c) hT
      exact Or.inr (Or.inr ⟨i, j, Config.ext (ξ.a_eq_zero_of_sumA hA)
        (ξ.b_eq_zero_of_sumB hB) hij⟩)
    · have hA : ξ.sumA = 0 := by omega
      have hB : ξ.sumB = 1 := by omega
      have hT : ξ.t = 0 := by omega
      obtain ⟨j, hj⟩ := exists_incf_of_sum_eq_one (f := ξ.b) hB
      exact Or.inr (Or.inl ⟨j, Config.ext (ξ.a_eq_zero_of_sumA hA) hj (ξ.c_eq_zero_of_t hT)⟩)
  · have hA : ξ.sumA = 1 := by omega
    have hB : ξ.sumB = 0 := by omega
    have hT : ξ.t = 0 := by omega
    obtain ⟨i, hi⟩ := exists_incf_of_sum_eq_one (f := ξ.a) hA
    exact Or.inl ⟨i, Config.ext hi (ξ.b_eq_zero_of_sumB hB) (ξ.c_eq_zero_of_t hT)⟩

def equivPi : Config KA KB ≃ (Fin KA → ℕ) × (Fin KB → ℕ) × (Fin KA → Fin KB → ℕ) where
  toFun ξ := (ξ.a, ξ.b, ξ.c)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem finite_pi_le (M : ℕ) (K : ℕ) : {f : Fin K → ℕ | ∀ i, f i ≤ M}.Finite :=
  Set.Finite.pi' fun _ => Set.finite_Iic M

private theorem finite_pi2_le (M : ℕ) :
    {m : Fin KA → Fin KB → ℕ | ∀ i j, m i j ≤ M}.Finite :=
  Set.Finite.pi' fun _ => finite_pi_le M KB

private theorem finite_bounded (M : ℕ) :
    {ξ : Config KA KB |
      (∀ i, ξ.a i ≤ M) ∧ (∀ j, ξ.b j ≤ M) ∧ (∀ i j, ξ.c i j ≤ M)}.Finite := by
  have hfin :
      ((({f : Fin KA → ℕ | ∀ i, f i ≤ M} ×ˢ
        ({g : Fin KB → ℕ | ∀ j, g j ≤ M} ×ˢ
          {m : Fin KA → Fin KB → ℕ | ∀ i j, m i j ≤ M})) : Set _)).Finite :=
    (finite_pi_le M KA).prod ((finite_pi_le M KB).prod (finite_pi2_le M))
  have := Set.Finite.preimage (f := (equivPi : Config KA KB ≃ _))
    (Function.Injective.injOn equivPi.injective) hfin
  exact this

theorem finite_le (N : ℕ) : {ξ : Config KA KB | ξ.nA + ξ.nB ≤ N}.Finite := by
  refine (finite_bounded N).subset ?_
  rintro ξ hξ
  have hlev : ξ.nA + ξ.nB ≤ N := hξ
  refine ⟨fun i => ?_, fun j => ?_, fun i j => ?_⟩
  · have h1 : ξ.a i ≤ ξ.sumA :=
      Finset.single_le_sum (f := ξ.a) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have h2 := ξ.sumA_le_nA
    omega
  · have h1 : ξ.b j ≤ ξ.sumB :=
      Finset.single_le_sum (f := ξ.b) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    have h2 := ξ.sumB_le_nB
    omega
  · have h1 : ξ.c i j ≤ ∑ j', ξ.c i j' :=
      Finset.single_le_sum (f := ξ.c i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    have h2 : (∑ j', ξ.c i j') ≤ ξ.t :=
      Finset.single_le_sum (f := fun i' => ∑ j', ξ.c i' j') (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i)
    have h3 := ξ.t_le_nA
    omega

theorem finite_level (N : ℕ) : {ξ : Config KA KB | ξ.nA + ξ.nB = N}.Finite :=
  (finite_le N).subset fun _ h => le_of_eq h

end Config

end Rhone.LinearAlgebra.Recursion
