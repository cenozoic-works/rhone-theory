/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.Recursion.Unique

/-! # The one-locus PIM marginal, and the edge blocks of the two-locus recursion -/

@[expose] public section

namespace Rhone.LinearAlgebra.Recursion

open Finset Config

section Rising

variable {F : Type*} [Field F]

def rising (x : F) (k : ℕ) : F := ∏ r ∈ Finset.range k, (x + (r : ℕ))

@[simp] theorem rising_zero (x : F) : rising x 0 = 1 := by simp [rising]

theorem rising_succ (x : F) (k : ℕ) : rising x (k + 1) = rising x k * (x + (k : ℕ)) := by
  simp [rising, Finset.prod_range_succ]

@[simp] theorem rising_one (x : F) : rising x 1 = x := by simp [rising_succ]

theorem rising_pos [LinearOrder F] [IsStrictOrderedRing F] {x : F} (hx : 0 < x) (k : ℕ) :
    0 < rising x k :=
  Finset.prod_pos fun r _ => by positivity

theorem rising_ne_zero [LinearOrder F] [IsStrictOrderedRing F] {x : F} (hx : 0 < x) (k : ℕ) :
    rising x k ≠ 0 := (rising_pos hx k).ne'

end Rising

section QOne

variable {K : ℕ} {F : Type*} [Field F] {θ : F} {π : Fin K → F}

def qOne (θ : F) (π : Fin K → F) (m : Fin K → ℕ) : F :=
  (∏ i, rising (θ * π i) (m i)) / rising θ (∑ i, m i)

@[simp] theorem qOne_zero : qOne θ π (fun _ => 0) = 1 := by simp [qOne]

theorem qOne_eA (hθ : θ ≠ 0) (i : Fin K) : qOne θ π (incf (fun _ => 0) i) = π i := by
  have h1 : ∑ k, incf (fun _ => (0 : ℕ)) i k = 1 := by simp [sum_incf]
  have h2 : ∏ k, rising (θ * π k) (incf (fun _ => 0) i k) = θ * π i := by
    rw [Finset.prod_eq_single_of_mem i (Finset.mem_univ i)]
    · rw [incf_self]; simp
    · intro k _ hk; rw [incf_of_ne _ hk]; simp
  rw [qOne, h1, h2, rising_one]
  field_simp

theorem prod_rising_decf (f : Fin K → F) {m : Fin K → ℕ} {i : Fin K} (h : m i ≠ 0) :
    ∏ k, rising (f k) (m k)
      = (∏ k, rising (f k) (decf m i k)) * (f i + ((m i : ℕ) : F) - 1) := by
  have hsplit : ∀ g : Fin K → ℕ,
      (∏ k, rising (f k) (g k))
        = rising (f i) (g i) * ∏ k ∈ Finset.univ.erase i, rising (f k) (g k) :=
    fun g => (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
  have herase : ∀ k ∈ Finset.univ.erase i, rising (f k) (decf m i k) = rising (f k) (m k) := by
    intro k hk
    rw [decf_of_ne _ (Finset.mem_erase.mp hk).1]
  obtain ⟨p, hp⟩ : ∃ p, m i = p + 1 := ⟨m i - 1, by omega⟩
  rw [hsplit m, hsplit (decf m i), Finset.prod_congr rfl herase, decf_self, hp]
  simp only [Nat.add_sub_cancel]
  rw [rising_succ]
  push_cast
  ring

theorem natCast_mul_pred {F : Type*} [Field F] (a : ℕ) :
    ((a * (a - 1) : ℕ) : F) = (a : F) * ((a : F) - 1) := by
  cases a with
  | zero => simp
  | succ k => push_cast [Nat.add_sub_cancel]; ring

theorem qOne_step_of_ne_zero (m : Fin K → ℕ) {i : Fin K} (hi : m i ≠ 0)
    (hden : rising θ (∑ k, m k) ≠ 0) :
    (θ * π i + ((m i : ℕ) : F) - 1) * qOne θ π (decf m i)
      = (θ + ((∑ k, m k : ℕ) : F) - 1) * qOne θ π m := by
  have hsd := sum_decf hi
  obtain ⟨M, hM⟩ : ∃ M, (∑ k, m k) = M + 1 := ⟨∑ k, decf m i k, hsd.symm⟩
  have hdec : ∑ k, decf m i k = M := by omega
  have hnum := prod_rising_decf (fun k => θ * π k) hi
  have hsplit : rising θ (∑ k, m k) = rising θ M * (θ + ((∑ k, m k : ℕ) : F) - 1) := by
    rw [hM, rising_succ]
    push_cast
    ring
  have hMne : rising θ M ≠ 0 := fun h => hden (by rw [hsplit, h, zero_mul])
  have hlast : θ + ((∑ k, m k : ℕ) : F) - 1 ≠ 0 := fun h => hden (by rw [hsplit, h, mul_zero])
  simp only [qOne]
  rw [hdec, hnum, hsplit]
  field_simp

theorem qOne_step_gen (m : Fin K → ℕ) (i : Fin K) (hden : rising θ (∑ k, m k) ≠ 0) :
    ((m i : ℕ) : F) * (θ * π i + ((m i : ℕ) : F) - 1) * qOne θ π (decf m i)
      = ((m i : ℕ) : F) * (θ + ((∑ k, m k : ℕ) : F) - 1) * qOne θ π m := by
  by_cases hi : m i = 0
  · rw [hi]; simp
  · rw [mul_assoc, mul_assoc, qOne_step_of_ne_zero m hi hden]

theorem qOne_recursion_gen (m : Fin K → ℕ) (hden : rising θ (∑ k, m k) ≠ 0) :
    (((∑ k, m k) * ((∑ k, m k) - 1) : ℕ) + θ * ((∑ k, m k : ℕ) : F)) * qOne θ π m
      = ∑ i, (((m i * (m i - 1) : ℕ) : F) + θ * π i * ((m i : ℕ) : F))
          * qOne θ π (decf m i) := by
  have hterm : ∀ i : Fin K,
      (((m i * (m i - 1) : ℕ) : F) + θ * π i * ((m i : ℕ) : F)) * qOne θ π (decf m i)
        = ((m i : ℕ) : F) * (θ + ((∑ k, m k : ℕ) : F) - 1) * qOne θ π m := by
    intro i
    rw [← qOne_step_gen (θ := θ) (π := π) m i hden, natCast_mul_pred]
    ring
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hterm i]
  rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum]
  rw [natCast_mul_pred]
  ring

variable [LinearOrder F] [IsStrictOrderedRing F]

theorem qOne_step (hθ : 0 < θ) (m : Fin K → ℕ) (i : Fin K) :
    ((m i : ℕ) : F) * (θ * π i + ((m i : ℕ) : F) - 1) * qOne θ π (decf m i)
      = ((m i : ℕ) : F) * (θ + ((∑ k, m k : ℕ) : F) - 1) * qOne θ π m :=
  qOne_step_gen m i (rising_ne_zero hθ _)

theorem qOne_recursion (hθ : 0 < θ) (m : Fin K → ℕ) :
    (((∑ k, m k) * ((∑ k, m k) - 1) : ℕ) + θ * ((∑ k, m k : ℕ) : F)) * qOne θ π m
      = ∑ i, (((m i * (m i - 1) : ℕ) : F) + θ * π i * ((m i : ℕ) : F))
          * qOne θ π (decf m i) :=
  qOne_recursion_gen m (rising_ne_zero hθ _)

end QOne

section Edge

variable {KA KB : ℕ} {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {πA : Fin KA → F} {πB : Fin KB → F}

theorem diag_of_nB_eq_zero (ξ : Config KA KB) (h : ξ.nB = 0) :
    diag θA θB ρ ξ = ((ξ.n * (ξ.n - 1) : ℕ) : F) + θA * ((ξ.n : ℕ) : F) := by
  have h1 : ξ.sumB = 0 := by simp only [nB] at h; omega
  have h2 : ξ.t = 0 := by simp only [nB] at h; omega
  have h3 : ξ.nA = ξ.n := by simp only [nA, n]; omega
  simp only [diag, h, h3, h2]
  simp

theorem rhs_of_nB_eq_zero (q : Config KA KB → F) (ξ : Config KA KB) (h : ξ.nB = 0) :
    rhs θA θB ρ πA πB q ξ
      = (∑ i, ((ξ.a i * (ξ.a i - 1) : ℕ) : F) * q (ξ.dropA i))
        + θA * ∑ i, πA i * (((ξ.a i : ℕ) : F) * q (ξ.dropA i)) := by
  have h1 : ξ.sumB = 0 := by simp only [nB] at h; omega
  have h2 : ξ.t = 0 := by simp only [nB] at h; omega
  have hb : ξ.b = fun _ => 0 := ξ.b_eq_zero_of_sumB h1
  have hc : ξ.c = fun _ _ => 0 := ξ.c_eq_zero_of_t h2
  simp only [rhs, Config.coalA, Config.coalB, Config.coalC, Config.coalAB, Config.cRow,
    Config.cCol, hb, hc]
  simp

theorem IsSolution.eq_qOne_of_nB (hθA : 0 < θA) {q : Config KA KB → F}
    (hq : IsSolution θA θB ρ πA πB q) :
    ∀ ξ : Config KA KB, ξ.nB = 0 → q ξ = qOne θA πA ξ.a := by
  intro ξ₀
  induction hn : ξ₀.n using Nat.strong_induction_on generalizing ξ₀ with
  | _ N IH =>
    intro h0
    rcases Nat.lt_or_ge N 2 with hlt | hge
    · rcases Nat.lt_or_ge N 1 with h1 | h1
      · have hz : ξ₀ = 0 := ξ₀.eq_zero_of_n_eq_zero (by omega)
        subst hz
        rw [hq.empty]
        exact qOne_zero.symm
      · have hone : ξ₀.n = 1 := by omega
        rcases ξ₀.exists_e_of_n_eq_one hone with ⟨i, rfl⟩ | ⟨j, rfl⟩ | ⟨i, j, rfl⟩
        · rw [hq.bdryA]
          exact (qOne_eA hθA.ne' i).symm
        · exfalso
          have : (eB j : Config KA KB).nB = 1 := by
            simp [nB, sumB, Config.t, eB, sum_incf]
          omega
        · exfalso
          have : (eC i j : Config KA KB).nB = 1 := by
            simp [nB, sumB, Config.t, eC, sum_incC]
          omega
    · have hsumA : ξ₀.sumA = ξ₀.n := by
        have h1 : ξ₀.sumB = 0 := by simp only [nB] at h0; omega
        have h2 : ξ₀.t = 0 := by simp only [nB] at h0; omega
        simp only [n]; omega
      have hrec := hq.recursion ξ₀ (by omega)
      rw [diag_of_nB_eq_zero ξ₀ h0, rhs_of_nB_eq_zero q ξ₀ h0] at hrec
      have hone := qOne_recursion (π := πA) hθA ξ₀.a
      rw [show (∑ k, ξ₀.a k) = ξ₀.n from hsumA] at hone
      have hstep : ∀ i : Fin KA, q (ξ₀.dropA i) = qOne θA πA (decf ξ₀.a i)
          ∨ ξ₀.a i = 0 := by
        intro i
        by_cases hai : ξ₀.a i = 0
        · exact Or.inr hai
        · refine Or.inl (IH (ξ₀.dropA i).n ?_ (ξ₀.dropA i) rfl ?_)
          · have := ξ₀.n_dropA i hai; omega
          · have := ξ₀.nB_dropA i; omega
      have hsum : (∑ i, ((ξ₀.a i * (ξ₀.a i - 1) : ℕ) : F) * q (ξ₀.dropA i))
            + θA * ∑ i, πA i * (((ξ₀.a i : ℕ) : F) * q (ξ₀.dropA i))
          = ∑ i, (((ξ₀.a i * (ξ₀.a i - 1) : ℕ) : F) + θA * πA i * ((ξ₀.a i : ℕ) : F))
              * qOne θA πA (decf ξ₀.a i) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rcases hstep i with hq0 | hq0
        · rw [hq0]; ring
        · rw [hq0]; simp
      rw [hsum, ← hone] at hrec
      have hD : (0 : F) < ((ξ₀.n * (ξ₀.n - 1) : ℕ) : F) + θA * ((ξ₀.n : ℕ) : F) := by
        have h1 : (0 : F) ≤ ((ξ₀.n * (ξ₀.n - 1) : ℕ) : F) := Nat.cast_nonneg _
        have h2 : (0 : F) < ((ξ₀.n : ℕ) : F) := by
          have : 0 < ξ₀.n := by omega
          exact_mod_cast this
        nlinarith
      exact mul_left_cancel₀ hD.ne' hrec

theorem diag_of_nA_eq_zero (ξ : Config KA KB) (h : ξ.nA = 0) :
    diag θA θB ρ ξ = ((ξ.n * (ξ.n - 1) : ℕ) : F) + θB * ((ξ.n : ℕ) : F) := by
  have h1 : ξ.sumA = 0 := by simp only [nA] at h; omega
  have h2 : ξ.t = 0 := by simp only [nA] at h; omega
  have h3 : ξ.nB = ξ.n := by simp only [nB, n]; omega
  simp only [diag, h, h3, h2]
  simp

theorem rhs_of_nA_eq_zero (q : Config KA KB → F) (ξ : Config KA KB) (h : ξ.nA = 0) :
    rhs θA θB ρ πA πB q ξ
      = (∑ j, ((ξ.b j * (ξ.b j - 1) : ℕ) : F) * q (ξ.dropB j))
        + θB * ∑ j, πB j * (((ξ.b j : ℕ) : F) * q (ξ.dropB j)) := by
  have h1 : ξ.sumA = 0 := by simp only [nA] at h; omega
  have h2 : ξ.t = 0 := by simp only [nA] at h; omega
  have ha : ξ.a = fun _ => 0 := ξ.a_eq_zero_of_sumA h1
  have hc : ξ.c = fun _ _ => 0 := ξ.c_eq_zero_of_t h2
  simp only [rhs, Config.coalA, Config.coalB, Config.coalC, Config.coalAB, Config.cRow,
    Config.cCol, ha, hc]
  simp

theorem IsSolution.eq_qOne_of_nA (hθB : 0 < θB) {q : Config KA KB → F}
    (hq : IsSolution θA θB ρ πA πB q) :
    ∀ ξ : Config KA KB, ξ.nA = 0 → q ξ = qOne θB πB ξ.b := by
  intro ξ₀
  induction hn : ξ₀.n using Nat.strong_induction_on generalizing ξ₀ with
  | _ N IH =>
    intro h0
    rcases Nat.lt_or_ge N 2 with hlt | hge
    · rcases Nat.lt_or_ge N 1 with h1 | h1
      · have hz : ξ₀ = 0 := ξ₀.eq_zero_of_n_eq_zero (by omega)
        subst hz
        rw [hq.empty]
        exact qOne_zero.symm
      · have hone : ξ₀.n = 1 := by omega
        rcases ξ₀.exists_e_of_n_eq_one hone with ⟨i, rfl⟩ | ⟨j, rfl⟩ | ⟨i, j, rfl⟩
        · exfalso
          have : (eA i : Config KA KB).nA = 1 := by
            simp [nA, sumA, Config.t, eA, sum_incf]
          omega
        · rw [hq.bdryB]
          exact (qOne_eA hθB.ne' j).symm
        · exfalso
          have : (eC i j : Config KA KB).nA = 1 := by
            simp [nA, sumA, Config.t, eC, sum_incC]
          omega
    · have hsumB : ξ₀.sumB = ξ₀.n := by
        have h1 : ξ₀.sumA = 0 := by simp only [nA] at h0; omega
        have h2 : ξ₀.t = 0 := by simp only [nA] at h0; omega
        simp only [n]; omega
      have hrec := hq.recursion ξ₀ (by omega)
      rw [diag_of_nA_eq_zero ξ₀ h0, rhs_of_nA_eq_zero q ξ₀ h0] at hrec
      have hone := qOne_recursion (π := πB) hθB ξ₀.b
      rw [show (∑ k, ξ₀.b k) = ξ₀.n from hsumB] at hone
      have hstep : ∀ j : Fin KB, q (ξ₀.dropB j) = qOne θB πB (decf ξ₀.b j)
          ∨ ξ₀.b j = 0 := by
        intro j
        by_cases hbj : ξ₀.b j = 0
        · exact Or.inr hbj
        · refine Or.inl (IH (ξ₀.dropB j).n ?_ (ξ₀.dropB j) rfl ?_)
          · have := ξ₀.n_dropB j hbj; omega
          · have := ξ₀.nA_dropB j; omega
      have hsum : (∑ j, ((ξ₀.b j * (ξ₀.b j - 1) : ℕ) : F) * q (ξ₀.dropB j))
            + θB * ∑ j, πB j * (((ξ₀.b j : ℕ) : F) * q (ξ₀.dropB j))
          = ∑ j, (((ξ₀.b j * (ξ₀.b j - 1) : ℕ) : F) + θB * πB j * ((ξ₀.b j : ℕ) : F))
              * qOne θB πB (decf ξ₀.b j) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rcases hstep j with hq0 | hq0
        · rw [hq0]; ring
        · rw [hq0]; simp
      rw [hsum, ← hone] at hrec
      have hD : (0 : F) < ((ξ₀.n * (ξ₀.n - 1) : ℕ) : F) + θB * ((ξ₀.n : ℕ) : F) := by
        have h1 : (0 : F) ≤ ((ξ₀.n * (ξ₀.n - 1) : ℕ) : F) := Nat.cast_nonneg _
        have h2 : (0 : F) < ((ξ₀.n : ℕ) : F) := by
          have : 0 < ξ₀.n := by omega
          exact_mod_cast this
        nlinarith
      exact mul_left_cancel₀ hD.ne' hrec

end Edge

end Rhone.LinearAlgebra.Recursion
