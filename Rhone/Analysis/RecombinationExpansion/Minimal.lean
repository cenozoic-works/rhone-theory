/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Analysis.RecombinationExpansion.CFinite
public import Mathlib.RingTheory.PowerSeries.Trunc
public import Mathlib.RingTheory.Coprime.Basic
public import Mathlib.Algebra.Polynomial.Degree.Domain
public import Mathlib.Algebra.Polynomial.Div

/-! # Minimal C-finite order of a sequence given in lowest terms -/

@[expose] public section

namespace Rhone.Analysis.RecombinationExpansion

open Polynomial

variable {F : Type*} [Field F]

def IsCFinite (U : ℕ) (B : Polynomial F) (G : PowerSeries F) : Prop :=
  ∀ k : ℕ, U < k → ∑ m ∈ Finset.range (U + 1), B.coeff m * PowerSeries.coeff (k - m) G = 0

theorem coeff_zero_reflect (M : ℕ) (D : Polynomial F) : (D.reflect M).coeff 0 = D.coeff M := by
  rw [Polynomial.coeff_reflect, revAt_le (Nat.zero_le M), Nat.sub_zero]

theorem isCFinite_reflect_iff (M : ℕ) (D : Polynomial F) (G : PowerSeries F) :
    IsCFinite M (D.reflect M) G ↔
      ∀ k : ℕ, M < k →
        ∑ m ∈ Finset.range (M + 1),
          D.coeff (M - m) * PowerSeries.coeff (k - m) G = 0 := by
  have hsum : ∀ k : ℕ,
      ∑ m ∈ Finset.range (M + 1), (D.reflect M).coeff m * PowerSeries.coeff (k - m) G
        = ∑ m ∈ Finset.range (M + 1),
            D.coeff (M - m) * PowerSeries.coeff (k - m) G := by
    intro k
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.mem_range] at hm
    rw [Polynomial.coeff_reflect, revAt_le (by omega)]
  exact ⟨fun h k hk => (hsum k) ▸ h k hk, fun h k hk => (hsum k).symm ▸ h k hk⟩

theorem coeff_mul_poly {U : ℕ} (B : Polynomial F) (G : PowerSeries F) (hB : B.natDegree ≤ U)
    {k : ℕ} (hk : U < k) :
    PowerSeries.coeff k ((B : PowerSeries F) * G)
      = ∑ m ∈ Finset.range (U + 1), B.coeff m * PowerSeries.coeff (k - m) G := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [Polynomial.coeff_coe]
  refine (Finset.sum_subset ?_ ?_).symm
  · intro x hx
    rw [Finset.mem_range] at hx ⊢
    omega
  · intro x _ hx
    have hxU : U < x := by
      by_contra hc
      exact hx (Finset.mem_range.2 (by omega))
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]

theorem cfinite_iff (U : ℕ) (B : Polynomial F) (hB : B.natDegree ≤ U) (G : PowerSeries F) :
    IsCFinite U B G ↔
      ∃ A : Polynomial F, A.natDegree ≤ U ∧ (A : PowerSeries F) = (B : PowerSeries F) * G := by
  constructor
  · intro h
    refine ⟨PowerSeries.trunc (U + 1) ((B : PowerSeries F) * G), ?_, ?_⟩
    · exact Nat.lt_succ_iff.mp (PowerSeries.natDegree_trunc_lt _ U)
    · refine PowerSeries.ext fun k => ?_
      rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
      split_ifs with hk
      · rfl
      · rw [coeff_mul_poly B G hB (by omega)]
        exact (h k (by omega)).symm
  · rintro ⟨A, hA, hAeq⟩ k hk
    exact RecombinationExpansion.cfinite_aux A B hA hB G hAeq hk

def IsCFiniteOrder (U : ℕ) (G : PowerSeries F) : Prop :=
  ∃ A B : Polynomial F, B ≠ 0 ∧ A.natDegree ≤ U ∧ B.natDegree ≤ U ∧
    (A : PowerSeries F) = (B : PowerSeries F) * G

theorem isCFiniteOrder_iff (U : ℕ) (G : PowerSeries F) :
    IsCFiniteOrder U G ↔
      ∃ B : Polynomial F, B ≠ 0 ∧ B.natDegree ≤ U ∧ IsCFinite U B G := by
  constructor
  · rintro ⟨A, B, hB0, hA, hB, hAB⟩
    exact ⟨B, hB0, hB, (cfinite_iff U B hB G).mpr ⟨A, hA, hAB⟩⟩
  · rintro ⟨B, hB0, hB, hcf⟩
    obtain ⟨A, hA, hAB⟩ := (cfinite_iff U B hB G).mp hcf
    exact ⟨A, B, hB0, hA, hB, hAB⟩

theorem exists_cofactor {A B A' B' : Polynomial F} {G : PowerSeries F}
    (hAB : (A : PowerSeries F) = (B : PowerSeries F) * G) (hcop : IsCoprime A B) (hB0 : B ≠ 0)
    (hA'B' : (A' : PowerSeries F) = (B' : PowerSeries F) * G) :
    ∃ C : Polynomial F, B' = B * C ∧ A' = A * C := by
  have hpoly : B' * A = B * A' := by
    refine Polynomial.coe_inj.mp ?_
    push_cast
    rw [hAB, hA'B']
    ring
  obtain ⟨C, hC⟩ := hcop.symm.dvd_of_dvd_mul_right ⟨A', hpoly⟩
  refine ⟨C, hC, mul_left_cancel₀ hB0 ?_⟩
  rw [← hpoly, hC]
  ring

theorem isLeast_cfiniteOrder {A B : Polynomial F} {G : PowerSeries F}
    (hAB : (A : PowerSeries F) = (B : PowerSeries F) * G) (hcop : IsCoprime A B) (hB0 : B ≠ 0) :
    IsLeast {U : ℕ | IsCFiniteOrder U G} (max A.natDegree B.natDegree) := by
  constructor
  · exact ⟨A, B, hB0, le_max_left _ _, le_max_right _ _, hAB⟩
  · rintro U ⟨A', B', hB'0, hA', hB', hA'B'⟩
    obtain ⟨C, hCB, hCA⟩ := exists_cofactor hAB hcop hB0 hA'B'
    have hC0 : C ≠ 0 := by
      intro h
      rw [h, mul_zero] at hCB
      exact hB'0 hCB
    have hBle : B.natDegree ≤ U :=
      le_trans (Polynomial.natDegree_le_of_dvd ⟨C, hCB⟩ hB'0) hB'
    have hAle : A.natDegree ≤ U := by
      rcases eq_or_ne A 0 with hA0 | hA0
      · rw [hA0]
        simp
      · have hA'0 : A' ≠ 0 := by
          rw [hCA]
          exact mul_ne_zero hA0 hC0
        exact le_trans (Polynomial.natDegree_le_of_dvd ⟨C, hCA⟩ hA'0) hA'
    exact max_le hAle hBle

theorem not_isCFinite_of_lt {A B : Polynomial F} {G : PowerSeries F}
    (hAB : (A : PowerSeries F) = (B : PowerSeries F) * G) (hcop : IsCoprime A B) (hB0 : B ≠ 0)
    {U : ℕ} (hU : U < max A.natDegree B.natDegree) (B' : Polynomial F) (hB'0 : B' ≠ 0)
    (hB'deg : B'.natDegree ≤ U) : ¬ IsCFinite U B' G := by
  intro hcf
  have hmem : IsCFiniteOrder U G := (isCFiniteOrder_iff U G).mpr ⟨B', hB'0, hB'deg, hcf⟩
  exact absurd ((isLeast_cfiniteOrder hAB hcop hB0).2 hmem) (by omega)

theorem natDegree_reflect_eq {M : ℕ} {p : Polynomial F} (hp : p.natDegree ≤ M)
    (h0 : p.coeff 0 ≠ 0) : (p.reflect M).natDegree = M := by
  refine le_antisymm (le_trans natDegree_reflect_le (max_le (le_refl M) hp)) ?_
  refine Polynomial.le_natDegree_of_ne_zero ?_
  rwa [Polynomial.coeff_reflect, revAt_le (le_refl M), Nat.sub_self]

theorem coeff_zero_ne_zero_of_isCoprime {N D : Polynomial F} (hcop : IsCoprime N D) :
    N.coeff 0 ≠ 0 ∨ D.coeff 0 ≠ 0 := by
  by_contra hc
  have h1 : N.coeff 0 = 0 := by
    by_contra h
    exact hc (Or.inl h)
  have h2 : D.coeff 0 = 0 := by
    by_contra h
    exact hc (Or.inr h)
  exact Polynomial.not_isUnit_X
    (hcop.isUnit_of_dvd' (Polynomial.X_dvd_iff.mpr h1) (Polynomial.X_dvd_iff.mpr h2))

theorem max_natDegree_reflect_eq {M : ℕ} {N D : Polynomial F} (hN : N.natDegree ≤ M)
    (hD : D.natDegree ≤ M) (hcop : IsCoprime N D) :
    max (N.reflect M).natDegree (D.reflect M).natDegree = M := by
  rcases coeff_zero_ne_zero_of_isCoprime hcop with h | h
  · rw [natDegree_reflect_eq hN h]
    exact max_eq_left (le_trans natDegree_reflect_le (max_le (le_refl M) hD))
  · rw [natDegree_reflect_eq hD h]
    exact max_eq_right (le_trans natDegree_reflect_le (max_le (le_refl M) hN))

theorem isLeast_order_reflect {M : ℕ} {N D : Polynomial F} {G : PowerSeries F}
    (hN : N.natDegree ≤ M) (hD : D.natDegree ≤ M) (hcop : IsCoprime N D)
    (hcop' : IsCoprime (N.reflect M) (D.reflect M)) (hD0 : D.reflect M ≠ 0)
    (hG : ((N.reflect M : Polynomial F) : PowerSeries F)
      = ((D.reflect M : Polynomial F) : PowerSeries F) * G) :
    IsLeast {U : ℕ | IsCFiniteOrder U G} M := by
  have h := isLeast_cfiniteOrder hG hcop' hD0
  rwa [max_natDegree_reflect_eq hN hD hcop] at h

end Rhone.Analysis.RecombinationExpansion
