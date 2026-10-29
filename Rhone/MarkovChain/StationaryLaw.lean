/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.Semigroup
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-! # Stationary laws of a finite-state continuous-time chain -/

@[expose] public section

namespace Rhone.MarkovChain.RateChain

open Finset Matrix

variable {S : Type*} [Fintype S] (R : RateChain S)

structure IsStationary (π : S → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ π x
  sum_eq_one : ∑ x, π x = 1
  vecMul_Q : π ᵥ* R.Q = 0

def Adj (x y : S) : Prop := x ≠ y ∧ 0 < R.Q x y

def IsIrreducible : Prop := ∀ x y, Relation.ReflTransGen R.Adj x y

variable {R}

theorem IsStationary.vecMul_semigroup [DecidableEq S] {π : S → ℝ} (hπ : R.IsStationary π)
    (t : ℝ) : π ᵥ* R.semigroup t = π := by
  funext y
  have hd : ∀ s, HasDerivAt (fun s => ∑ x, π x * R.semigroup s x y) 0 s := by
    intro s
    have h := HasDerivAt.fun_sum (u := univ)
      fun x _ => (R.hasDerivAt_semigroup' s x y).const_mul (π x)
    have h0 : ∑ x, π x * (R.Q * R.semigroup s) x y = 0 := by
      have h1 : (π ᵥ* (R.Q * R.semigroup s)) y = 0 := by
        rw [← vecMul_vecMul, hπ.vecMul_Q, zero_vecMul]
        rfl
      simpa [vecMul, dotProduct] using h1
    rwa [h0] at h
  have hconst := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
    (fun s => (hd s).deriv) t 0
  change ∑ x, π x * R.semigroup t x y = π y
  rw [hconst]
  simp [semigroup_zero, Matrix.one_apply]

section Analysis

theorem rate_mul_eq [DecidableEq S] {u : S → ℝ} (hu : u ᵥ* R.Q = 0) (y : S) :
    u y * R.rate y = ∑ x ∈ univ.erase y, u x * R.Q x y := by
  have h := congrFun hu y
  simp only [vecMul, dotProduct, Pi.zero_apply] at h
  rw [← Finset.add_sum_erase univ _ (mem_univ y)] at h
  have hq : R.Q y y = -R.rate y := by simp [rate]
  rw [hq] at h
  linarith

theorem mul_Q_le_mul_rate {u : S → ℝ} (hu : u ᵥ* R.Q = 0) (hu0 : ∀ x, 0 ≤ u x) {x y : S}
    (hxy : x ≠ y) : u x * R.Q x y ≤ u y * R.rate y := by
  classical
  rw [rate_mul_eq hu y]
  exact Finset.single_le_sum (f := fun z => u z * R.Q z y)
    (fun z hz => mul_nonneg (hu0 z) (R.off_diag_nonneg z y (Finset.ne_of_mem_erase hz)))
    (mem_erase.2 ⟨hxy, mem_univ x⟩)

theorem pos_of_adj {u : S → ℝ} (hu : u ᵥ* R.Q = 0) (hu0 : ∀ x, 0 ≤ u x) {x y : S}
    (hxy : R.Adj x y) (hx : 0 < u x) : 0 < u y := by
  classical
  have h := mul_Q_le_mul_rate hu hu0 hxy.1
  have h2 : 0 < u x * R.Q x y := mul_pos hx hxy.2
  rcases (hu0 y).lt_or_eq with h3 | h3
  · exact h3
  · rw [← h3, zero_mul] at h
    linarith

theorem eq_zero_of_adj {u : S → ℝ} (hu : u ᵥ* R.Q = 0) (hu0 : ∀ x, 0 ≤ u x) {x y : S}
    (hxy : R.Adj x y) (hy : u y = 0) : u x = 0 := by
  classical
  have h := mul_Q_le_mul_rate hu hu0 hxy.1
  rw [hy, zero_mul] at h
  by_contra hne
  have hpos : 0 < u x := lt_of_le_of_ne (hu0 x) (Ne.symm hne)
  have := mul_pos hpos hxy.2
  linarith

theorem exists_isStationary [Nonempty S] : ∃ π, R.IsStationary π := by
  classical
  obtain ⟨v, hv0, hv⟩ : ∃ v : S → ℝ, v ≠ 0 ∧ v ᵥ* R.Q = 0 := by
    have hdet : R.Q.det = 0 := by
      refine Matrix.exists_mulVec_eq_zero_iff.1 ⟨fun _ => 1, ?_, ?_⟩
      · exact fun h => one_ne_zero (congrFun h (Classical.arbitrary S))
      · funext x
        simp [mulVec, dotProduct, R.row_sum x]
    exact Matrix.exists_vecMul_eq_zero_iff.2 hdet
  set w : S → ℝ := fun x => |v x| with hw
  have hw0 : ∀ x, 0 ≤ w x := fun x => abs_nonneg _
  have hwQ : ∀ y, 0 ≤ (w ᵥ* R.Q) y := by
    intro y
    have h1 : |v y| * R.rate y ≤ ∑ x ∈ univ.erase y, |v x| * R.Q x y := by
      have h2 : |v y * R.rate y| = |v y| * R.rate y := by
        rw [abs_mul, abs_of_nonneg (R.rate_nonneg y)]
      rw [← h2, rate_mul_eq hv y]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x hx => ?_)
      rw [abs_mul, abs_of_nonneg (R.off_diag_nonneg x y (Finset.ne_of_mem_erase hx))]
    simp only [vecMul, dotProduct, hw]
    rw [← Finset.add_sum_erase univ _ (mem_univ y)]
    have hq : R.Q y y = -R.rate y := by simp [rate]
    rw [hq]
    linarith
  have hsum : ∑ y, (w ᵥ* R.Q) y = 0 := by
    simp only [vecMul, dotProduct]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [← Finset.mul_sum, R.row_sum x, mul_zero]
  have hwQ0 : w ᵥ* R.Q = 0 := by
    funext y
    exact (Finset.sum_eq_zero_iff_of_nonneg fun y _ => hwQ y).1 hsum y (mem_univ y)
  have hspos : 0 < ∑ x, w x := by
    obtain ⟨x, hx⟩ : ∃ x, v x ≠ 0 := by
      by_contra h
      exact hv0 (funext fun x => not_not.1 fun hx => h ⟨x, hx⟩)
    exact Finset.sum_pos' (fun x _ => hw0 x) ⟨x, mem_univ x, abs_pos.2 hx⟩
  refine ⟨(∑ x, w x)⁻¹ • w, ⟨fun x => ?_, ?_, ?_⟩⟩
  · exact mul_nonneg (inv_nonneg.2 hspos.le) (hw0 x)
  · simp only [Pi.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum, inv_mul_cancel₀ hspos.ne']
  · rw [smul_vecMul, hwQ0, smul_zero]

theorem IsStationary.pos_of_irreducible (hirr : R.IsIrreducible) {π : S → ℝ}
    (hπ : R.IsStationary π) (x : S) : 0 < π x := by
  classical
  obtain ⟨x0, hx0⟩ : ∃ x0, 0 < π x0 := by
    by_contra hcon
    have : ∑ x, π x ≤ 0 := Finset.sum_nonpos fun x _ => not_lt.1 fun h => hcon ⟨x, h⟩
    linarith [hπ.sum_eq_one]
  induction hirr x0 x with
  | refl => exact hx0
  | tail _ hab ih => exact pos_of_adj hπ.vecMul_Q hπ.nonneg hab ih

theorem IsStationary.eq_of_irreducible (hirr : R.IsIrreducible) {π ρ : S → ℝ}
    (hπ : R.IsStationary π) (hρ : R.IsStationary ρ) : π = ρ := by
  classical
  have hne : Nonempty S := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := hπ.sum_eq_one
    simp at this
  obtain ⟨x0, -, hmin⟩ := Finset.exists_min_image univ (fun x => π x / ρ x)
    (Finset.univ_nonempty_iff.2 hne)
  set c : ℝ := π x0 / ρ x0 with hc
  set v : S → ℝ := π - c • ρ with hv
  have hvQ : v ᵥ* R.Q = 0 := by
    rw [hv, sub_vecMul, smul_vecMul, hπ.vecMul_Q, hρ.vecMul_Q, smul_zero, sub_zero]
  have hv0 : ∀ x, 0 ≤ v x := by
    intro x
    have h1 : c ≤ π x / ρ x := hmin x (mem_univ x)
    have h2 := (le_div_iff₀ (hρ.pos_of_irreducible hirr x)).1 h1
    simp only [hv, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  have hvx0 : v x0 = 0 := by
    have : ρ x0 ≠ 0 := (hρ.pos_of_irreducible hirr x0).ne'
    simp only [hv, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hc]
    field_simp
    ring
  have hall : ∀ x, v x = 0 := by
    intro x
    induction hirr x x0 using Relation.ReflTransGen.head_induction_on with
    | refl => exact hvx0
    | head hab _ ih => exact eq_zero_of_adj hvQ hv0 hab ih
  have hπρ : ∀ x, π x = c * ρ x := by
    intro x
    have := hall x
    simp only [hv, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at this
    linarith
  have hc1 : c = 1 := by
    have h1 := hπ.sum_eq_one
    simp only [hπρ, ← Finset.mul_sum, hρ.sum_eq_one, mul_one] at h1
    exact h1
  funext x
  rw [hπρ x, hc1, one_mul]

end Analysis

end Rhone.MarkovChain.RateChain
