/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.Denominator.Source
public import Rhone.LinearAlgebra.Recursion.Exist

/-! # The product family and the scoped defect -/

@[expose] public section

namespace Rhone.Probability.Denominator

open Finset LinearAlgebra.Recursion

variable {KA KB : ℕ} {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {πA : Fin KA → F} {πB : Fin KB → F}

theorem mul_pred_eq_zero_of_le_one {x : ℕ} (h : x ≤ 1) : x * (x - 1) = 0 := by
  interval_cases x <;> rfl

theorem cRow_le_t (ξ : Config KA KB) (i : Fin KA) : ξ.cRow i ≤ ξ.t :=
  Finset.single_le_sum (f := ξ.cRow) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

theorem cCol_le_t (ξ : Config KA KB) (j : Fin KB) : ξ.cCol j ≤ ξ.t := by
  rw [ξ.t_eq_sum_cCol]
  exact Finset.single_le_sum (f := ξ.cCol) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)

theorem twoQ1_eq_zero_of_t_le_one (ξ : Config KA KB) (ht : ξ.t ≤ 1) :
    twoQ1 θA θB πA πB ξ = 0 := by
  have h0 : ξ.t * (ξ.t - 1) = 0 := mul_pred_eq_zero_of_le_one ht
  have h1 : ∀ i : Fin KA, ξ.cRow i * (ξ.cRow i - 1) = 0 := fun i =>
    mul_pred_eq_zero_of_le_one (le_trans (cRow_le_t ξ i) ht)
  have h2 : ∀ j : Fin KB, ξ.cCol j * (ξ.cCol j - 1) = 0 := fun j =>
    mul_pred_eq_zero_of_le_one (le_trans (cCol_le_t ξ j) ht)
  have h3 : ∀ (i : Fin KA) (j : Fin KB), ξ.c i j * (ξ.c i j - 1) = 0 := by
    intro i j
    have hle : ξ.c i j ≤ ξ.cRow i :=
      Finset.single_le_sum (f := ξ.c i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    exact mul_pred_eq_zero_of_le_one (le_trans hle (le_trans (cRow_le_t ξ i) ht))
  simp [twoQ1, h0, h1, h2, h3]

omit [IsStrictOrderedRing F] in
theorem eq_qHat_of_n_le_one (hθA : 0 < θA) (hθB : 0 < θB) {q : Config KA KB → F}
    (hq : IsSolution θA θB ρ πA πB q) (ξ : Config KA KB) (hn : ξ.n ≤ 1) :
    q ξ = qHat θA θB πA πB ξ := by
  rcases Nat.lt_or_ge ξ.n 1 with h | h
  · have hz : ξ = 0 := ξ.eq_zero_of_n_eq_zero (by omega)
    subst hz
    rw [hq.empty, qHat, Config.mA_zero, Config.mB_zero, qOne_zero, qOne_zero, one_mul]
  · rcases ξ.exists_e_of_n_eq_one (by omega) with ⟨i, rfl⟩ | ⟨j, rfl⟩ | ⟨i, j, rfl⟩
    · rw [hq.bdryA, qHat, Config.mA_eA, Config.mB_eA, qOne_zero, qOne_eA hθA.ne' i,
        mul_one]
    · rw [hq.bdryB, qHat, Config.mA_eB, Config.mB_eB, qOne_zero, qOne_eA hθB.ne' j,
        one_mul]
    · rw [hq.bdryC, qHat, Config.mA_eC, Config.mB_eC, qOne_eA hθA.ne' i,
        qOne_eA hθB.ne' j]

def scopedDefect (θA θB : F) (πA : Fin KA → F) (πB : Fin KB → F) (q : Config KA KB → F)
    (ξ : Config KA KB) : F :=
  if ξ.nA ≤ 1 ∨ ξ.nB ≤ 1 then q ξ - qHat θA θB πA πB ξ else 0

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem scopedDefect_of_min_le_one {q : Config KA KB → F} {ξ : Config KA KB}
    (h : ξ.nA ≤ 1 ∨ ξ.nB ≤ 1) :
    scopedDefect θA θB πA πB q ξ = q ξ - qHat θA θB πA πB ξ := ite_eq_left h

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem scopedDefect_of_two_le {q : Config KA KB → F} {ξ : Config KA KB}
    (hA : 2 ≤ ξ.nA) (hB : 2 ≤ ξ.nB) : scopedDefect θA θB πA πB q ξ = 0 :=
  ite_eq_right (by omega)

theorem eq_qHat_of_min_le_one (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    {q : Config KA KB → F} (hq : IsSolution θA θB ρ πA πB q) (ξ : Config KA KB)
    (hmin : ξ.nA ≤ 1 ∨ ξ.nB ≤ 1) : q ξ = qHat θA θB πA πB ξ := by
  have hzero : ∀ η : Config KA KB, scopedDefect θA θB πA πB q η = 0 := by
    intro η
    refine within_block_eq_zero (θA := θA) (θB := θB) (ρ := ρ)
      (h := scopedDefect θA θB πA πB q) (D := diag θA θB ρ) (N := η.nA + η.nB)
      hθA hθB hρ (fun _ => le_rfl) ?_ ?_ η le_rfl
    · intro ζ hn _
      have h1 : ζ.nA ≤ 1 := le_trans ζ.nA_le_n hn
      rw [scopedDefect_of_min_le_one (Or.inl h1),
        eq_qHat_of_n_le_one hθA hθB hq ζ hn, sub_self]
    · intro ζ hn2 _ hbelow
      by_cases hsc : ζ.nA ≤ 1 ∨ ζ.nB ≤ 1
      · have hval : ∀ η : Config KA KB, η.nA ≤ ζ.nA → η.nB ≤ ζ.nB →
            (fun η => q η - qHat θA θB πA πB η) η = scopedDefect θA θB πA πB q η := by
          intro η h1 h2
          refine (scopedDefect_of_min_le_one ?_).symm
          rcases hsc with h | h
          · exact Or.inl (le_trans h1 h)
          · exact Or.inr (le_trans h2 h)
        have ht : ζ.t ≤ 1 := by
          rcases hsc with h | h
          · exact le_trans ζ.t_le_nA h
          · exact le_trans ζ.t_le_nB h
        have hsrc := source_identity (ρ := ρ) (πA := πA) (πB := πB) hθA hθB ζ
        have hΔ : diag θA θB ρ ζ * (q ζ - qHat θA θB πA πB ζ)
            = rhs θA θB ρ πA πB (fun η => q η - qHat θA θB πA πB η) ζ := by
          rw [rhs_sub, mul_sub, hq.recursion ζ hn2, hsrc,
            twoQ1_eq_zero_of_t_le_one (θA := θA) (θB := θB) (πA := πA) (πB := πB) ζ ht]
          ring
        rw [scopedDefect_of_min_le_one hsc, hΔ, rhs_congr θA θB ρ πA πB ζ hval]
        exact rhs_of_vanishing_below θA θB ρ πA πB ζ fun η h1 h2 _ => hbelow η (by omega)
      · have hA2 : 2 ≤ ζ.nA := by omega
        have hB2 : 2 ≤ ζ.nB := by omega
        have m1 : (∑ i, ∑ j, ((ζ.coalAB i j : ℕ) : F)
            * scopedDefect θA θB πA πB q (ζ.mergeAB i j)) = 0 := by
          refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
          by_cases ha : ζ.a i = 0
          · rw [ζ.coalAB_eq_zero_left j ha]; simp
          by_cases hb : ζ.b j = 0
          · rw [ζ.coalAB_eq_zero_right i hb]; simp
          obtain ⟨e1, e2⟩ := ζ.mergeAB_same ha hb
          rw [scopedDefect_of_two_le (by omega) (by omega), mul_zero]
        have m2 : (∑ i, ∑ j, ((ζ.c i j : ℕ) : F)
            * scopedDefect θA θB πA πB q (ζ.split i j)) = 0 := by
          refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
          by_cases hc : ζ.c i j = 0
          · rw [hc]; simp
          obtain ⟨e1, e2⟩ := ζ.split_same hc
          rw [scopedDefect_of_two_le (by omega) (by omega), mul_zero]
        rw [scopedDefect_of_two_le hA2 hB2, m1, m2, mul_zero, mul_zero, add_zero]
  have := hzero ξ
  rw [scopedDefect_of_min_le_one hmin] at this
  linarith

theorem qOne_eq_one_of_K_one {θ : F} {π : Fin 1 → F} (hθ : 0 < θ) (hπ : ∑ i, π i = 1)
    (m : Fin 1 → ℕ) : qOne θ π m = 1 := by
  have hπ0 : π 0 = 1 := by simpa using hπ
  have hsum : (∑ i, m i) = m 0 := by simp
  rw [qOne, hsum, Fin.prod_univ_one, hπ0, mul_one]
  exact div_self (rising_ne_zero hθ (m 0))

theorem twoQ1_eq_zero_of_KA_one {πA : Fin 1 → F} (hθA : 0 < θA) (hπA : ∑ i, πA i = 1)
    (ξ : Config 1 KB) : twoQ1 θA θB πA πB ξ = 0 := by
  have hone : ∀ m : Fin 1 → ℕ, qOne θA πA m = 1 := qOne_eq_one_of_K_one hθA hπA
  have hrow : ξ.cRow 0 = ξ.t := by simp [Config.cRow, Config.t]
  have hcol : ∀ j, ξ.cCol j = ξ.c 0 j := by intro j; simp [Config.cCol]
  simp only [twoQ1, hone, hrow, hcol, Fin.sum_univ_one, one_mul, mul_one]
  ring

theorem twoQ1_eq_zero_of_KB_one {πB : Fin 1 → F} (hθB : 0 < θB) (hπB : ∑ j, πB j = 1)
    (ξ : Config KA 1) : twoQ1 θA θB πA πB ξ = 0 := by
  have hone : ∀ m : Fin 1 → ℕ, qOne θB πB m = 1 := qOne_eq_one_of_K_one hθB hπB
  have hcol : ξ.cCol 0 = ξ.t := by simp [Config.cCol, Config.t]
  have hrow : ∀ i, ξ.cRow i = ξ.c i 0 := by intro i; simp [Config.cRow]
  simp only [twoQ1, hone, hrow, hcol, Fin.sum_univ_one, one_mul, mul_one]
  ring

theorem eq_qHat_of_source_eq_zero (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    {q : Config KA KB → F} (hq : IsSolution θA θB ρ πA πB q)
    (hsrc0 : ∀ ξ : Config KA KB, twoQ1 θA θB πA πB ξ = 0) :
    q = qHat θA θB πA πB := by
  have hbd : ∀ ξ : Config KA KB, ξ.n ≤ 1 → q ξ - qHat θA θB πA πB ξ = 0 := fun ξ hn =>
    sub_eq_zero_of_eq (eq_qHat_of_n_le_one hθA hθB hq ξ hn)
  have hrec : ∀ ξ : Config KA KB, 2 ≤ ξ.n →
      diag θA θB ρ ξ * (q ξ - qHat θA θB πA πB ξ)
        = rhs θA θB ρ πA πB (fun η => q η - qHat θA θB πA πB η) ξ := by
    intro ξ hn
    rw [rhs_sub, mul_sub, hq.recursion ξ hn,
      source_identity (ρ := ρ) (πA := πA) (πB := πB) hθA hθB ξ, hsrc0 ξ]
    ring
  funext ξ
  have := homogeneous_eq_zero (πA := πA) (πB := πB) hθA hθB hρ hbd hrec ξ
  linarith

theorem eq_qHat_of_KA_one {πA : Fin 1 → F} (hθA : 0 < θA) (hθB : 0 < θB)
    (hρ : 0 ≤ ρ) (hπA : ∑ i, πA i = 1) {q : Config 1 KB → F}
    (hq : IsSolution θA θB ρ πA πB q) : q = qHat θA θB πA πB :=
  eq_qHat_of_source_eq_zero hθA hθB hρ hq (twoQ1_eq_zero_of_KA_one hθA hπA)

theorem eq_qHat_of_KB_one {πB : Fin 1 → F} (hθA : 0 < θA) (hθB : 0 < θB)
    (hρ : 0 ≤ ρ) (hπB : ∑ j, πB j = 1) {q : Config KA 1 → F}
    (hq : IsSolution θA θB ρ πA πB q) : q = qHat θA θB πA πB :=
  eq_qHat_of_source_eq_zero hθA hθB hρ hq (twoQ1_eq_zero_of_KB_one hθB hπB)

theorem q_eq_qHat_of_min_le_one (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (ξ : Config KA KB) (hmin : ξ.nA ≤ 1 ∨ ξ.nB ≤ 1) :
    q (πA := πA) (πB := πB) hθA hθB hρ ξ = qHat θA θB πA πB ξ :=
  eq_qHat_of_min_le_one hθA hθB hρ (q_isSolution hθA hθB hρ) ξ hmin

end Rhone.Probability.Denominator
