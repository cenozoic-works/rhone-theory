/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.Denominator.CommuteUp
public import Rhone.Probability.Denominator.Product

/-! # Marginalization: a test vector `1` deletes its slot -/

@[expose] public section

namespace Rhone.Probability.Denominator

open Finset LinearAlgebra.Recursion

variable {KA KB : ℕ} {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {πA : Fin KA → F} {πB : Fin KB → F}

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem diag_addA (θA θB ρ : F) (ξ : Config KA KB) (i : Fin KA) :
    diag θA θB ρ (addA ξ i) = diag θA θB ρ ξ + ((2 * ξ.n : ℕ) : F) + θA := by
  have h1 : (addA ξ i).n = ξ.n + 1 := n_addA ξ i
  have h2 : (addA ξ i).nA = ξ.nA + 1 := nA_addA ξ i
  have hn : (ξ.n + 1) * ((ξ.n + 1) - 1) = ξ.n * (ξ.n - 1) + 2 * ξ.n := by
    cases hc : ξ.n with
    | zero => rfl
    | succ m => simp only [Nat.add_sub_cancel]; ring
  simp only [LinearAlgebra.Recursion.diag, h1, h2, hn, nB_addA, t_addA, Nat.cast_add, Nat.cast_one]
  ring

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem diag_up (θA θB ρ : F) (ξ : Config KA KB) (i : Fin KA) (j : Fin KB) (hb : ξ.b j ≠ 0) :
    diag θA θB ρ (up ξ i j) = diag θA θB ρ ξ + θA + ρ := by
  have h1 : (up ξ i j).n = ξ.n := n_up ξ i j hb
  have h2 : (up ξ i j).nA = ξ.nA + 1 := nA_up ξ i j
  have h3 : (up ξ i j).nB = ξ.nB := nB_up ξ i j hb
  have h4 : (up ξ i j).t = ξ.t + 1 := t_up ξ i j
  simp only [LinearAlgebra.Recursion.diag, h1, h2, h3, h4, Nat.cast_add, Nat.cast_one]
  ring

theorem recursion_all (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    {q : Config KA KB → F} (hq : IsSolution θA θB ρ πA πB q) (ξ : Config KA KB) :
    diag θA θB ρ ξ * q ξ = rhs θA θB ρ πA πB q ξ := by
  rcases Nat.lt_or_ge ξ.n 2 with hn | hn
  · have h1 : ξ.nA ≤ 1 := le_trans ξ.nA_le_n (by omega)
    have heq : ∀ η : Config KA KB, η.nA ≤ ξ.nA → η.nB ≤ ξ.nB → q η = qHat θA θB πA πB η :=
      fun η ha _ => eq_qHat_of_min_le_one hθA hθB hρ hq η (Or.inl (le_trans ha h1))
    have ht : ξ.t ≤ 1 := le_trans ξ.t_le_nA h1
    rw [rhs_congr θA θB ρ πA πB ξ heq, source_identity (ρ := ρ) hθA hθB ξ,
      twoQ1_eq_zero_of_t_le_one (θA := θA) (θB := θB) (πA := πA) (πB := πB) ξ ht, add_zero,
      heq ξ le_rfl le_rfl]
  · exact hq.recursion ξ hn

def hA (q : Config KA KB → F) : Config KA KB → F := fun ξ => sumAddA q ξ - q ξ

def hC (q : Config KA KB → F) (j : Fin KB) : Config KA KB → F := fun ξ => sumUp q j ξ - q ξ

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem hA_apply (q : Config KA KB → F) (ξ : Config KA KB) : hA q ξ = sumAddA q ξ - q ξ := rfl

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem hC_apply (q : Config KA KB → F) (j : Fin KB) (ξ : Config KA KB) :
    hC q j ξ = sumUp q j ξ - q ξ := rfl

theorem hA_eq (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (hπA : ∑ i, πA i = 1)
    {q : Config KA KB → F} (hq : IsSolution θA θB ρ πA πB q) (ξ : Config KA KB) :
    (diag θA θB ρ ξ + ((2 * ξ.n : ℕ) : F) + θA) * hA q ξ
      = rhs θA θB ρ πA πB (hA q) ξ + 2 * ∑ l, ((ξ.b l : ℕ) : F) * hC q l ξ := by
  have hall := recursion_all hθA hθB hρ hq
  have key : (diag θA θB ρ ξ + ((2 * ξ.n : ℕ) : F) + θA) * sumAddA q ξ
      = ∑ i, rhs θA θB ρ πA πB q (addA ξ i) := by
    rw [sumAddA, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [← diag_addA θA θB ρ ξ i, hall (addA ξ i)]
  rw [sum_rhs_addA θA θB ρ πA πB q ξ, hπA] at key
  have hrhsA : rhs θA θB ρ πA πB (hA q) ξ
      = rhs θA θB ρ πA πB (sumAddA q) ξ - rhs θA θB ρ πA πB q ξ :=
    rhs_sub θA θB ρ πA πB (sumAddA q) q ξ
  have hb2 : (∑ l, ((ξ.b l : ℕ) : F) * hC q l ξ)
      = (∑ l, ((ξ.b l : ℕ) : F) * sumUp q l ξ) - ((ξ.sumB : ℕ) : F) * q ξ := by
    have h1 : ((ξ.sumB : ℕ) : F) * q ξ = ∑ l, ((ξ.b l : ℕ) : F) * q ξ := by
      rw [← Finset.sum_mul, ← Nat.cast_sum]
      rfl
    rw [h1, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun l _ => by rw [hC_apply]; ring
  have hnumN : 2 * ξ.nA + 2 * ξ.sumB = 2 * ξ.n := by
    simp only [Config.nA, Config.n]; omega
  have hnum : ((2 * ξ.nA : ℕ) : F) + 2 * ((ξ.sumB : ℕ) : F) = ((2 * ξ.n : ℕ) : F) := by
    rw [← hnumN]; push_cast; ring
  rw [hb2, hrhsA, ← hall ξ]
  simp only [hA_apply]
  linear_combination key + q ξ * hnum

theorem hC_eq (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (hπA : ∑ i, πA i = 1)
    {q : Config KA KB → F} (hq : IsSolution θA θB ρ πA πB q) (ξ : Config KA KB) (j : Fin KB)
    (hb : ξ.b j ≠ 0) :
    (diag θA θB ρ ξ + θA + ρ) * hC q j ξ
      = rhs θA θB ρ πA πB (hC q j) ξ
        - 2 * (∑ k, ((ξ.a k : ℕ) : F) * hC q j (ξ.mergeAB k j))
        - 2 * ((ξ.cCol j : ℕ) : F) * hC q j (ξ.dropB j)
        + θB * πB j * (hA q (ξ.dropB j) - hC q j (ξ.dropB j))
        + ρ * hA q ξ := by
  have hall := recursion_all hθA hθB hρ hq
  have key : (diag θA θB ρ ξ + θA + ρ) * sumUp q j ξ
      = ∑ i, rhs θA θB ρ πA πB q (up ξ i j) := by
    rw [sumUp, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [← diag_up θA θB ρ ξ i j hb, hall (up ξ i j)]
  rw [sum_rhs_up θA θB ρ πA πB q ξ j hb, hπA] at key
  have hrhsC : rhs θA θB ρ πA πB (hC q j) ξ
      = rhs θA θB ρ πA πB (sumUp q j) ξ - rhs θA θB ρ πA πB q ξ :=
    rhs_sub θA θB ρ πA πB (sumUp q j) q ξ
  have hm : (∑ k, ((ξ.a k : ℕ) : F) * hC q j (ξ.mergeAB k j))
      = (∑ k, ((ξ.a k : ℕ) : F) * sumUp q j (ξ.mergeAB k j))
        - ∑ k, ((ξ.a k : ℕ) : F) * q (ξ.mergeAB k j) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by rw [hC_apply]; ring
  rw [hm, hrhsC, ← hall ξ]
  simp only [hA_apply, hC_apply]
  linear_combination key

theorem rhs_regroup_C (θA θB ρ : F) (πA : Fin KA → F) (πB : Fin KB → F)
    {ζ : Config KA KB} {j : Fin KB} (hbj : ζ.b j ≠ 0) {h : Config KA KB → F}
    (hbelow : ∀ η : Config KA KB, η.nA + η.nB < ζ.nA + ζ.nB → η.b j ≠ 0 → h η = 0) :
    rhs θA θB ρ πA πB h ζ
      = 2 * (∑ k, ((ζ.a k : ℕ) : F) * h (ζ.mergeAB k j))
        + (2 * ((ζ.cCol j : ℕ) : F) + θB * πB j) * h (ζ.dropB j)
        + (∑ k, ∑ l, ((2 * (ζ.a k * decf ζ.b j l) : ℕ) : F) * h (ζ.mergeAB k l))
        + ρ * ∑ k, ∑ l, ((ζ.c k l : ℕ) : F) * h (ζ.split k l) := by
  have hdropB : ∀ l : Fin KB, l ≠ j → h (ζ.dropB l) = 0 ∨ ζ.b l = 0 := by
    intro l hl
    by_cases hbl : ζ.b l = 0
    · exact Or.inr hbl
    · obtain ⟨h1, h2⟩ := ζ.dropB_lt hbl
      refine Or.inl (hbelow _ (by omega) ?_)
      change decf ζ.b l j ≠ 0
      rw [decf_of_ne _ (fun hc => hl (hc.symm))]
      exact hbj
  have hdropA : ∀ k : Fin KA, h (ζ.dropA k) = 0 ∨ ζ.a k = 0 := by
    intro k
    by_cases hak : ζ.a k = 0
    · exact Or.inr hak
    · obtain ⟨h1, h2⟩ := ζ.dropA_lt hak
      exact Or.inl (hbelow _ (by omega) hbj)
  have hdropC : ∀ (k : Fin KA) (l : Fin KB), h (ζ.dropC k l) = 0 ∨ ζ.c k l = 0 := by
    intro k l
    by_cases hc : ζ.c k l = 0
    · exact Or.inr hc
    · obtain ⟨h1, h2⟩ := ζ.dropC_lt hc
      exact Or.inl (hbelow _ (by omega) hbj)
  have hkillA : ∀ (k : Fin KA) (l : Fin KB), h (ζ.killA k l) = 0 ∨ ζ.c k l = 0 := by
    intro k l
    by_cases hc : ζ.c k l = 0
    · exact Or.inr hc
    · obtain ⟨h1, h2⟩ := ζ.killA_lt hc
      refine Or.inl (hbelow _ (by omega) ?_)
      change incf ζ.b l j ≠ 0
      simp only [incf_apply]
      omega
  have hkillB : ∀ (k : Fin KA) (l : Fin KB), h (ζ.killB k l) = 0 ∨ ζ.c k l = 0 := by
    intro k l
    by_cases hc : ζ.c k l = 0
    · exact Or.inr hc
    · obtain ⟨h1, h2⟩ := ζ.killB_lt hc
      exact Or.inl (hbelow _ (by omega) hbj)
  have e1 : (∑ k, ((ζ.coalA k : ℕ) : F) * h (ζ.dropA k)) = 0 := by
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases hdropA k with h0 | h0
    · rw [h0, mul_zero]
    · rw [ζ.coalA_eq_zero_of h0]; simp
  have e3 : (∑ k, ∑ l, ((ζ.coalC k l : ℕ) : F) * h (ζ.dropC k l)) = 0 := by
    refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun l _ => ?_
    rcases hdropC k l with h0 | h0
    · rw [h0, mul_zero]
    · rw [ζ.coalC_eq_zero_of h0]; simp
  have e5 : (θA * ∑ k, πA k * (((ζ.a k : ℕ) : F) * h (ζ.dropA k)
      + ∑ l, ((ζ.c k l : ℕ) : F) * h (ζ.killA k l))) = 0 := by
    have : (∑ k, πA k * (((ζ.a k : ℕ) : F) * h (ζ.dropA k)
        + ∑ l, ((ζ.c k l : ℕ) : F) * h (ζ.killA k l))) = 0 := by
      refine Finset.sum_eq_zero fun k _ => ?_
      have t1 : ((ζ.a k : ℕ) : F) * h (ζ.dropA k) = 0 := by
        rcases hdropA k with h0 | h0
        · rw [h0, mul_zero]
        · rw [h0]; simp
      have t2 : (∑ l, ((ζ.c k l : ℕ) : F) * h (ζ.killA k l)) = 0 := by
        refine Finset.sum_eq_zero fun l _ => ?_
        rcases hkillA k l with h0 | h0
        · rw [h0, mul_zero]
        · rw [h0]; simp
      rw [t1, t2, add_zero, mul_zero]
    rw [this, mul_zero]
  have e2 : (∑ l, ((ζ.coalB l : ℕ) : F) * h (ζ.dropB l))
      = ((ζ.coalB j : ℕ) : F) * h (ζ.dropB j) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    have : (∑ l ∈ Finset.univ.erase j, ((ζ.coalB l : ℕ) : F) * h (ζ.dropB l)) = 0 := by
      refine Finset.sum_eq_zero fun l hl => ?_
      rcases hdropB l (Finset.mem_erase.mp hl).1 with h0 | h0
      · rw [h0, mul_zero]
      · rw [ζ.coalB_eq_zero_of h0]; simp
    rw [this, add_zero]
  have e6 : (θB * ∑ l, πB l * (((ζ.b l : ℕ) : F) * h (ζ.dropB l)
      + ∑ k, ((ζ.c k l : ℕ) : F) * h (ζ.killB k l)))
      = θB * (πB j * (((ζ.b j : ℕ) : F) * h (ζ.dropB j))) := by
    congr 1
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    have hk : ∀ l : Fin KB, (∑ k, ((ζ.c k l : ℕ) : F) * h (ζ.killB k l)) = 0 := by
      intro l
      refine Finset.sum_eq_zero fun k _ => ?_
      rcases hkillB k l with h0 | h0
      · rw [h0, mul_zero]
      · rw [h0]; simp
    have hrest : (∑ l ∈ Finset.univ.erase j, πB l * (((ζ.b l : ℕ) : F) * h (ζ.dropB l)
        + ∑ k, ((ζ.c k l : ℕ) : F) * h (ζ.killB k l))) = 0 := by
      refine Finset.sum_eq_zero fun l hl => ?_
      have t1 : ((ζ.b l : ℕ) : F) * h (ζ.dropB l) = 0 := by
        rcases hdropB l (Finset.mem_erase.mp hl).1 with h0 | h0
        · rw [h0, mul_zero]
        · rw [h0]; simp
      rw [t1, hk l, add_zero, mul_zero]
    rw [hrest, add_zero, hk j, add_zero]
  have edrop : ((ζ.coalB j : ℕ) : F) * h (ζ.dropB j)
      + θB * (πB j * (((ζ.b j : ℕ) : F) * h (ζ.dropB j)))
      = (2 * ((ζ.cCol j : ℕ) : F) + θB * πB j) * h (ζ.dropB j) := by
    rcases Nat.lt_or_ge (ζ.b j) 2 with h1 | h1
    · have hb1 : ζ.b j = 1 := by omega
      have hcb : ζ.coalB j = 2 * ζ.cCol j := by
        simp only [Config.coalB, hb1]
        omega
      rw [hcb, hb1]
      push_cast
      ring
    · have hz : h (ζ.dropB j) = 0 := by
        obtain ⟨g1, g2⟩ := ζ.dropB_lt hbj
        refine hbelow _ (by omega) ?_
        change decf ζ.b j j ≠ 0
        rw [decf_self]
        omega
      rw [hz]
      ring
  have e4 : (∑ k, ∑ l, ((ζ.coalAB k l : ℕ) : F) * h (ζ.mergeAB k l))
      = 2 * (∑ k, ((ζ.a k : ℕ) : F) * h (ζ.mergeAB k j))
        + ∑ k, ∑ l, ((2 * (ζ.a k * decf ζ.b j l) : ℕ) : F) * h (ζ.mergeAB k l) := by
    have hsplit : ∀ (k : Fin KA) (l : Fin KB),
        ((ζ.coalAB k l : ℕ) : F) * h (ζ.mergeAB k l)
          = (if l = j then 2 * ((ζ.a k : ℕ) : F) * h (ζ.mergeAB k j) else 0)
            + ((2 * (ζ.a k * decf ζ.b j l) : ℕ) : F) * h (ζ.mergeAB k l) := by
      intro k l
      by_cases hl : l = j
      · subst hl
        have hn : ζ.coalAB k l = 2 * ζ.a k + 2 * (ζ.a k * decf ζ.b l l) := by
          simp only [Config.coalAB, decf_self]
          obtain ⟨pp, hpp⟩ : ∃ pp, ζ.b l = pp + 1 := ⟨ζ.b l - 1, by omega⟩
          rw [hpp]
          simp only [Nat.add_sub_cancel]
          ring
        rw [ite_eq_left rfl, hn]
        push_cast
        ring
      · have hn : ζ.coalAB k l = 2 * (ζ.a k * decf ζ.b j l) := by
          simp only [Config.coalAB, decf_of_ne _ hl]
        rw [ite_eq_right hl, hn, zero_add]
    rw [Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) =>
      Finset.sum_congr rfl fun l (_ : l ∈ Finset.univ) => hsplit k l]
    rw [Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) => Finset.sum_add_distrib,
      Finset.sum_add_distrib]
    congr 1
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by simp [mul_assoc]
  simp only [rhs]
  rw [e1, e2, e3, e4, e5, e6]
  linear_combination edrop

def defect (q : Config KA KB → F) : Option (Fin KB) → Config KA KB → F
  | none, ξ => hA q ξ
  | some j, ξ => if ξ.b j = 0 then 0 else hC q j ξ

theorem abs_sum_le_cast {ι : Type*} [Fintype ι] (w : ι → ℕ) (g : ι → F) (M : F)
    (hM : ∀ x : ι, w x ≠ 0 → |g x| ≤ M) :
    |∑ x, ((w x : ℕ) : F) * g x| ≤ ((∑ x, w x : ℕ) : F) * M := by
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  rw [Nat.cast_sum, Finset.sum_mul]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
  by_cases hw : w x = 0
  · rw [hw]; simp
  · exact mul_le_mul_of_nonneg_left (hM x hw) (Nat.cast_nonneg _)

theorem abs_sum2_le_cast (w : Fin KA → Fin KB → ℕ) (g : Fin KA → Fin KB → F) (M : F)
    (hM : ∀ (k : Fin KA) (l : Fin KB), w k l ≠ 0 → |g k l| ≤ M) :
    |∑ k, ∑ l, ((w k l : ℕ) : F) * g k l| ≤ ((∑ k, ∑ l, w k l : ℕ) : F) * M := by
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  rw [Nat.cast_sum, Finset.sum_mul]
  exact Finset.sum_le_sum fun k _ => abs_sum_le_cast (w k) (g k) M (hM k)

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem defect_none (q : Config KA KB → F) (ξ : Config KA KB) : defect q none ξ = hA q ξ := rfl

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem defect_some (q : Config KA KB → F) (j : Fin KB) (ξ : Config KA KB) :
    defect q (some j) ξ = if ξ.b j = 0 then 0 else hC q j ξ := rfl

theorem defect_eq_zero (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hπA : ∑ i, πA i = 1) {q : Config KA KB → F} (hq : IsSolution θA θB ρ πA πB q) :
    ∀ (L : ℕ) (o : Option (Fin KB)) (ξ : Config KA KB), ξ.nA + ξ.nB = L →
      defect q o ξ = 0 := by
  intro L
  induction L using Nat.strong_induction_on with
  | _ L IH =>
    intro o0 ξ0 hξ0
    have hbelowA : ∀ η : Config KA KB, η.nA + η.nB < L → hA q η = 0 :=
      fun η hη => IH _ hη none η rfl
    have hbelowC : ∀ (jj : Fin KB) (η : Config KA KB), η.nA + η.nB < L → η.b jj ≠ 0 →
        hC q jj η = 0 := by
      intro jj η hη hbb
      have hz := IH _ hη (some jj) η rfl
      rw [defect_some, ite_eq_right hbb] at hz
      exact hz
    have hfin : {p : Option (Fin KB) × Config KA KB | p.2.nA + p.2.nB = L}.Finite := by
      have h1 : (Set.univ : Set (Option (Fin KB))).Finite := Set.finite_univ
      exact (h1.prod (Config.finite_level (KA := KA) (KB := KB) L)).subset
        (fun p hp => ⟨Set.mem_univ _, hp⟩)
    obtain ⟨p, hpS, hpmax⟩ := Set.exists_max_image
      {p : Option (Fin KB) × Config KA KB | p.2.nA + p.2.nB = L}
      (fun p => |defect q p.1 p.2|) hfin ⟨(o0, ξ0), hξ0⟩
    have hmem : ∀ (o : Option (Fin KB)) (x : Config KA KB), x.nA + x.nB = L →
        (o, x) ∈ {p : Option (Fin KB) × Config KA KB | p.2.nA + p.2.nB = L} :=
      fun o x hx => hx
    have hMzero : |defect q p.1 p.2| = 0 := by
      obtain ⟨o, ζ⟩ := p
      have hζ : ζ.nA + ζ.nB = L := hpS
      have hP : (0 : F) ≤ θA * ((ζ.nA : ℕ) : F) + θB * ((ζ.nB : ℕ) : F) :=
        add_nonneg (mul_nonneg hθA.le (Nat.cast_nonneg _))
          (mul_nonneg hθB.le (Nat.cast_nonneg _))
      have hrt : (0 : F) ≤ ρ * ((ζ.t : ℕ) : F) := mul_nonneg hρ (Nat.cast_nonneg _)
      have hnn : (0 : F) ≤ ((ζ.n * (ζ.n - 1) : ℕ) : F) := Nat.cast_nonneg _
      have hcoal : ((2 * (ζ.sumA * ζ.sumB) : ℕ) : F) ≤ ((ζ.n * (ζ.n - 1) : ℕ) : F) := by
        exact_mod_cast ζ.two_mul_sumA_mul_sumB_le
      cases o with
      | none =>
        rw [defect_none]
        set M : F := |hA q ζ| with hMdef
        have hMnn : (0 : F) ≤ M := abs_nonneg _
        have heq := hA_eq hθA hθB hρ hπA hq ζ
        rw [rhs_of_vanishing_below θA θB ρ πA πB ζ
          (fun η h1 h2 _ => hbelowA η (by omega))] at heq
        have hb1 : |∑ k, ∑ l, ((ζ.coalAB k l : ℕ) : F) * hA q (ζ.mergeAB k l)|
            ≤ ((∑ k, ∑ l, ζ.coalAB k l : ℕ) : F) * M := by
          refine abs_sum2_le_cast _ _ M ?_
          intro k l hw
          have hak : ζ.a k ≠ 0 := fun hz => hw (by simp [Config.coalAB, hz])
          have hbl : ζ.b l ≠ 0 := fun hz => hw (by simp [Config.coalAB, hz])
          obtain ⟨e1, e2⟩ := ζ.mergeAB_same hak hbl
          have hm := hpmax (none, ζ.mergeAB k l) (hmem none _ (by omega))
          rw [defect_none, defect_none] at hm
          exact hm
        have hb2 : |∑ k, ∑ l, ((ζ.c k l : ℕ) : F) * hA q (ζ.split k l)|
            ≤ ((ζ.t : ℕ) : F) * M := by
          have hx := abs_sum2_le_cast (fun k l => ζ.c k l)
            (fun k l => hA q (ζ.split k l)) M ?_
          · rw [ζ.sum_c] at hx
            exact hx
          · intro k l hw
            obtain ⟨e1, e2⟩ := ζ.split_same hw
            have hm := hpmax (none, ζ.split k l) (hmem none _ (by omega))
            rw [defect_none, defect_none] at hm
            exact hm
        have hb3 : |∑ l, ((ζ.b l : ℕ) : F) * hC q l ζ| ≤ ((ζ.sumB : ℕ) : F) * M := by
          refine abs_sum_le_cast (fun l => ζ.b l) (fun l => hC q l ζ) M ?_
          intro l hw
          have hm := hpmax (some l, ζ) (hmem _ _ hζ)
          rw [defect_some, ite_eq_right hw, defect_none] at hm
          exact hm
        have hDpos : (0 : F) < diag θA θB ρ ζ + ((2 * ζ.n : ℕ) : F) + θA := by
          have h0 : (0 : F) ≤ ((2 * ζ.n : ℕ) : F) := Nat.cast_nonneg _
          simp only [LinearAlgebra.Recursion.diag]
          linarith
        have habs : (diag θA θB ρ ζ + ((2 * ζ.n : ℕ) : F) + θA) * M
            = |(∑ k, ∑ l, ((ζ.coalAB k l : ℕ) : F) * hA q (ζ.mergeAB k l))
                + ρ * ∑ k, ∑ l, ((ζ.c k l : ℕ) : F) * hA q (ζ.split k l)
                + 2 * ∑ l, ((ζ.b l : ℕ) : F) * hC q l ζ| := by
          rw [hMdef, ← abs_of_pos hDpos, ← abs_mul, heq]
        have hchain : (diag θA θB ρ ζ + ((2 * ζ.n : ℕ) : F) + θA) * M
            ≤ ((∑ k, ∑ l, ζ.coalAB k l : ℕ) : F) * M + ρ * (((ζ.t : ℕ) : F) * M)
              + 2 * (((ζ.sumB : ℕ) : F) * M) := by
          rw [habs]
          refine le_trans (abs_add_le _ _) ?_
          refine add_le_add (le_trans (abs_add_le _ _) (add_le_add hb1 ?_)) ?_
          · rw [abs_mul, abs_of_nonneg hρ]
            exact mul_le_mul_of_nonneg_left hb2 hρ
          · rw [abs_mul, abs_of_nonneg (by norm_num : (0 : F) ≤ 2)]
            exact mul_le_mul_of_nonneg_left hb3 (by norm_num)
        rw [ζ.sum_coalAB] at hchain
        have hsbN : 2 * ζ.sumB ≤ 2 * ζ.n := by have := ζ.sumA_add_sumB_le_n; omega
        have hsb : ((2 * ζ.sumB : ℕ) : F) ≤ ((2 * ζ.n : ℕ) : F) := by exact_mod_cast hsbN
        have hsb2 : 2 * (((ζ.sumB : ℕ) : F) * M) ≤ ((2 * ζ.n : ℕ) : F) * M := by
          have h2 : 2 * (((ζ.sumB : ℕ) : F) * M) = ((2 * ζ.sumB : ℕ) : F) * M := by
            push_cast
            ring
          rw [h2]
          exact mul_le_mul_of_nonneg_right hsb hMnn
        simp only [LinearAlgebra.Recursion.diag] at hchain
        by_contra hne
        have hMpos : (0 : F) < M := lt_of_le_of_ne hMnn (Ne.symm hne)
        have hc2 : ((2 * (ζ.sumA * ζ.sumB) : ℕ) : F) * M
            ≤ ((ζ.n * (ζ.n - 1) : ℕ) : F) * M := mul_le_mul_of_nonneg_right hcoal hMnn
        have hc3 : (0 : F) ≤ (θA * ((ζ.nA : ℕ) : F) + θB * ((ζ.nB : ℕ) : F)) * M :=
          mul_nonneg hP hMnn
        have hc4 : (0 : F) < θA * M := mul_pos hθA hMpos
        linarith [hchain, hc2, hc3, hc4, hsb2]
      | some jj =>
        by_cases hbb : ζ.b jj = 0
        · rw [defect_some, ite_eq_left hbb, abs_zero]
        rw [defect_some, ite_eq_right hbb]
        set M : F := |hC q jj ζ| with hMdef
        have hMnn : (0 : F) ≤ M := abs_nonneg _
        have heq := hC_eq hθA hθB hρ hπA hq ζ jj hbb
        rw [rhs_regroup_C θA θB ρ πA πB hbb
          (fun η hη hbjj => hbelowC jj η (by omega) hbjj)] at heq
        have hAdrop : hA q (ζ.dropB jj) = 0 := by
          obtain ⟨g1, g2⟩ := ζ.dropB_lt hbb
          exact hbelowA _ (by omega)
        rw [hAdrop] at heq
        have heq2 : (diag θA θB ρ ζ + θA + ρ) * hC q jj ζ
            = (∑ k, ∑ l, ((2 * (ζ.a k * decf ζ.b jj l) : ℕ) : F)
                * hC q jj (ζ.mergeAB k l))
              + ρ * (∑ k, ∑ l, ((ζ.c k l : ℕ) : F) * hC q jj (ζ.split k l))
              + ρ * hA q ζ := by
          linear_combination heq
        have hb1 : |∑ k, ∑ l, ((2 * (ζ.a k * decf ζ.b jj l) : ℕ) : F)
              * hC q jj (ζ.mergeAB k l)|
            ≤ ((∑ k, ∑ l, 2 * (ζ.a k * decf ζ.b jj l) : ℕ) : F) * M := by
          refine abs_sum2_le_cast _ _ M ?_
          intro k l hw
          have hak : ζ.a k ≠ 0 := fun hz => hw (by simp [hz])
          have hdl : decf ζ.b jj l ≠ 0 := fun hz => hw (by simp [hz])
          have hbl : ζ.b l ≠ 0 := fun hz => hdl (by simp [decf_apply, hz])
          obtain ⟨e1, e2⟩ := ζ.mergeAB_same hak hbl
          have hbjj : (ζ.mergeAB k l).b jj ≠ 0 := by
            change decf ζ.b l jj ≠ 0
            by_cases hlj : l = jj
            · rw [hlj]; rw [hlj] at hdl; exact hdl
            · rw [decf_of_ne _ (fun hc => hlj hc.symm)]; exact hbb
          have hm := hpmax (some jj, ζ.mergeAB k l) (hmem _ _ (by omega))
          rw [defect_some, ite_eq_right hbjj, defect_some, ite_eq_right hbb] at hm
          exact hm
        have hb2 : |∑ k, ∑ l, ((ζ.c k l : ℕ) : F) * hC q jj (ζ.split k l)|
            ≤ ((ζ.t : ℕ) : F) * M := by
          have hx := abs_sum2_le_cast (fun k l => ζ.c k l)
            (fun k l => hC q jj (ζ.split k l)) M ?_
          · rw [ζ.sum_c] at hx
            exact hx
          · intro k l hw
            obtain ⟨e1, e2⟩ := ζ.split_same hw
            have hbjj : (ζ.split k l).b jj ≠ 0 := by
              change incf ζ.b l jj ≠ 0
              simp only [incf_apply]
              omega
            have hm := hpmax (some jj, ζ.split k l) (hmem _ _ (by omega))
            rw [defect_some, ite_eq_right hbjj, defect_some, ite_eq_right hbb] at hm
            exact hm
        have hb3 : |hA q ζ| ≤ M := by
          have hm := hpmax (none, ζ) (hmem _ _ hζ)
          rw [defect_none, defect_some, ite_eq_right hbb] at hm
          exact hm
        have hDpos : (0 : F) < diag θA θB ρ ζ + θA + ρ := by
          simp only [LinearAlgebra.Recursion.diag]
          linarith
        have habs : (diag θA θB ρ ζ + θA + ρ) * M
            = |(∑ k, ∑ l, ((2 * (ζ.a k * decf ζ.b jj l) : ℕ) : F)
                  * hC q jj (ζ.mergeAB k l))
                + ρ * (∑ k, ∑ l, ((ζ.c k l : ℕ) : F) * hC q jj (ζ.split k l))
                + ρ * hA q ζ| := by
          rw [hMdef, ← abs_of_pos hDpos, ← abs_mul, heq2]
        have hchain : (diag θA θB ρ ζ + θA + ρ) * M
            ≤ ((∑ k, ∑ l, 2 * (ζ.a k * decf ζ.b jj l) : ℕ) : F) * M
              + ρ * (((ζ.t : ℕ) : F) * M) + ρ * M := by
          rw [habs]
          refine le_trans (abs_add_le _ _) ?_
          refine add_le_add (le_trans (abs_add_le _ _) (add_le_add hb1 ?_)) ?_
          · rw [abs_mul, abs_of_nonneg hρ]
            exact mul_le_mul_of_nonneg_left hb2 hρ
          · rw [abs_mul, abs_of_nonneg hρ]
            exact mul_le_mul_of_nonneg_left hb3 hρ
        have hwtN : (∑ k, ∑ l, 2 * (ζ.a k * decf ζ.b jj l))
            ≤ 2 * (ζ.sumA * ζ.sumB) := by
          rw [← ζ.sum_coalAB]
          refine Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => ?_
          simp only [Config.coalAB]
          exact Nat.mul_le_mul_left 2
            (Nat.mul_le_mul_left _ (by simp only [decf_apply]; omega))
        have hwt : ((∑ k, ∑ l, 2 * (ζ.a k * decf ζ.b jj l) : ℕ) : F)
            ≤ ((2 * (ζ.sumA * ζ.sumB) : ℕ) : F) := by exact_mod_cast hwtN
        simp only [LinearAlgebra.Recursion.diag] at hchain
        by_contra hne
        have hMpos : (0 : F) < M := lt_of_le_of_ne hMnn (Ne.symm hne)
        have hc2 : ((∑ k, ∑ l, 2 * (ζ.a k * decf ζ.b jj l) : ℕ) : F) * M
            ≤ ((ζ.n * (ζ.n - 1) : ℕ) : F) * M :=
          mul_le_mul_of_nonneg_right (le_trans hwt hcoal) hMnn
        have hc3 : (0 : F) ≤ (θA * ((ζ.nA : ℕ) : F) + θB * ((ζ.nB : ℕ) : F)) * M :=
          mul_nonneg hP hMnn
        have hc4 : (0 : F) < θA * M := mul_pos hθA hMpos
        linarith [hchain, hc2, hc3, hc4]
    have hfinal := hpmax (o0, ξ0) hξ0
    rw [hMzero] at hfinal
    exact abs_eq_zero.mp (le_antisymm hfinal (abs_nonneg _))

theorem marginalise_A (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hπA : ∑ i, πA i = 1) {q : Config KA KB → F} (hq : IsSolution θA θB ρ πA πB q)
    (ξ : Config KA KB) : (∑ i, q (addA ξ i)) = q ξ := by
  have hz := defect_eq_zero hθA hθB hρ hπA hq (ξ.nA + ξ.nB) none ξ rfl
  rw [defect_none, hA_apply, sumAddA] at hz
  linarith [hz]

theorem marginalise_C (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hπA : ∑ i, πA i = 1) {q : Config KA KB → F} (hq : IsSolution θA θB ρ πA πB q)
    (ξ : Config KA KB) (j : Fin KB) :
    (∑ i, q (addC ξ i j)) = q (addB ξ j) := by
  have hb : (addB ξ j).b j ≠ 0 := by simp [addB, incf_apply]
  have hz := defect_eq_zero hθA hθB hρ hπA hq ((addB ξ j).nA + (addB ξ j).nB)
    (some j) (addB ξ j) rfl
  rw [defect_some, ite_eq_right hb, hC_apply, sumUp] at hz
  simp only [up_addB] at hz
  linarith [hz]

theorem q_marginalise_A (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hπA : ∑ i, πA i = 1) (ξ : Config KA KB) :
    (∑ i, q (πA := πA) (πB := πB) hθA hθB hρ (addA ξ i))
      = q (πA := πA) (πB := πB) hθA hθB hρ ξ :=
  marginalise_A hθA hθB hρ hπA (q_isSolution hθA hθB hρ) ξ

theorem q_marginalise_C (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hπA : ∑ i, πA i = 1) (ξ : Config KA KB) (j : Fin KB) :
    (∑ i, q (πA := πA) (πB := πB) hθA hθB hρ (addC ξ i j))
      = q (πA := πA) (πB := πB) hθA hθB hρ (addB ξ j) :=
  marginalise_C hθA hθB hρ hπA (q_isSolution hθA hθB hρ) ξ j

end Rhone.Probability.Denominator
