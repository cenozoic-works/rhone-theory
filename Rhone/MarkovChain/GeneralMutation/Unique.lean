/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.GeneralMutation.WithinBounds

/-! # Well-posedness of the general-mutation-matrix system: uniqueness -/

@[expose] public section

namespace Rhone.MarkovChain.GeneralMutation

open Finset LinearAlgebra.Recursion

variable {KA KB : ℕ} {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {νA : Fin KA → F} {νB : Fin KB → F}
variable {PA : Fin KA → Fin KA → F} {PB : Fin KB → Fin KB → F}

private theorem abs_add6 (x1 x2 x3 x4 x5 x6 : F) :
    |x1 + x2 + x3 + x4 + x5 + x6| ≤ |x1| + |x2| + |x3| + |x4| + |x5| + |x6| := by
  have h6 := abs_add_le (x1 + x2 + x3 + x4 + x5) x6
  have h5 := abs_add_le (x1 + x2 + x3 + x4) x5
  have h4 := abs_add_le (x1 + x2 + x3) x4
  have h3 := abs_add_le (x1 + x2) x3
  have h2 := abs_add_le x1 x2
  linarith

set_option maxHeartbeats 400000 in
theorem homogeneous_eq_zero_le (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hPA : ∀ k i, 0 ≤ PA k i) (hPB : ∀ l j, 0 ≤ PB l j)
    (hνA : ∀ i, 0 < νA i) (hνB : ∀ j, 0 < νB j)
    (hstA : ∀ i, ∑ k, νA k * PA k i = νA i) (hstB : ∀ j, ∑ l, νB l * PB l j = νB j)
    {h : Config KA KB → F} {N : ℕ}
    (hbd : ∀ ξ : Config KA KB, ξ.n ≤ 1 → ξ.nA + ξ.nB ≤ N → h ξ = 0)
    (hrec : ∀ ξ : Config KA KB, 2 ≤ ξ.n → ξ.nA + ξ.nB ≤ N →
      diag θA θB ρ ξ * h ξ = rhsGen θA θB ρ PA PB h ξ) :
    ∀ ξ : Config KA KB, ξ.nA + ξ.nB ≤ N → h ξ = 0 := by
  suffices H : ∀ L : ℕ, L ≤ N → ∀ ξ : Config KA KB, ξ.nA + ξ.nB = L → h ξ = 0 from
    fun ξ hξ => H _ hξ ξ rfl
  intro L
  induction L using Nat.strong_induction_on with
  | _ L IH =>
    intro hLN ξ hξ
    have hbelow : ∀ η : Config KA KB, η.nA + η.nB < L → h η = 0 :=
      fun η hη => IH _ hη (by omega) η rfl
    obtain ⟨ζ, hζS, hζmax⟩ :=
      Set.exists_max_image {ζ : Config KA KB | ζ.nA + ζ.nB = L}
        (fun ζ => |h ζ| / wtC νA νB ζ) (Config.finite_level L) ⟨ξ, hξ⟩
    have hζlev : ζ.nA + ζ.nB = L := hζS
    set M : F := |h ζ| / wtC νA νB ζ with hMdef
    have hW : 0 < wtC νA νB ζ := wtC_pos hνA hνB ζ
    have hMnn : 0 ≤ M := div_nonneg (abs_nonneg _) hW.le
    have hMW : M * wtC νA νB ζ = |h ζ| := by
      rw [hMdef]; field_simp
    have hmax : ∀ η : Config KA KB, η.nA + η.nB = L → |h η| ≤ M * wtC νA νB η :=
      fun η hη => (div_le_iff₀ (wtC_pos hνA hνB η)).mp (hζmax η hη)
    have hzero : |h ζ| = 0 := by
      by_cases hn : ζ.n ≤ 1
      · rw [hbd ζ hn (by omega), abs_zero]
      have hn2 : 2 ≤ ζ.n := by omega
      have hlev2 : 2 ≤ ζ.nA + ζ.nB := by have := ζ.n_add_t; omega
      have heq := hrec ζ hn2 (by omega)
      rw [rhsGen_of_vanishing_below ζ (fun η h1 h2 _ => hbelow η (by omega))] at heq
      have hb1 := coalAB_sum_bound ζ M (fun η hη => hmax η (by omega)) hn2
        (fun η hη hlev => hbd η hη (by omega))
      have hb2 := mutA_sum_bound hPA hνA hstA ζ M (fun η hη => hmax η (by omega))
      have hb3 := mutCA_sum_bound hPA hνA hstA ζ M (fun η hη => hmax η (by omega))
      have hb4 := mutB_sum_bound hPB hνB hstB ζ M (fun η hη => hmax η (by omega))
      have hb5 := mutCB_sum_bound hPB hνB hstB ζ M (fun η hη => hmax η (by omega))
      have hb6 := split_sum_bound ζ M (fun η hη => hmax η (by omega))
      set S1 := ∑ i, ∑ j, ((ζ.coalAB i j : ℕ) : F) * h (ζ.mergeAB i j)
      set S2 := ∑ i, ∑ k, PA k i * ((ζ.a i : ℕ) : F) * h (mutA ζ i k)
      set S3 := ∑ i, ∑ j, ∑ k, PA k i * ((ζ.c i j : ℕ) : F) * h (mutCA ζ i j k)
      set S4 := ∑ j, ∑ l, PB l j * ((ζ.b j : ℕ) : F) * h (mutB ζ j l)
      set S5 := ∑ i, ∑ j, ∑ l, PB l j * ((ζ.c i j : ℕ) : F) * h (mutCB ζ i j l)
      set S6 := ∑ i, ∑ j, ((ζ.c i j : ℕ) : F) * h (ζ.split i j)
      set W := wtC νA νB ζ
      have hDpos : 0 < diag θA θB ρ ζ := diag_pos hθA hθB hρ (by omega)
      have habs : diag θA θB ρ ζ * (M * W)
          ≤ ((cab ζ : ℕ) : F) * (M * W)
            + θA * (((ζ.sumA : ℕ) : F) * (M * W)) + θA * (((ζ.t : ℕ) : F) * (M * W))
            + θB * (((ζ.sumB : ℕ) : F) * (M * W)) + θB * (((ζ.t : ℕ) : F) * (M * W))
            + ρ * (((ζ.t : ℕ) : F) * (M * W)) := by
        have hstart : diag θA θB ρ ζ * (M * W) = |diag θA θB ρ ζ * h ζ| := by
          rw [hMW, abs_mul, abs_of_pos hDpos]
        rw [hstart, heq]
        have h6 := abs_add6 S1 (θA * S2) (θA * S3) (θB * S4) (θB * S5) (ρ * S6)
        simp only [abs_mul] at h6
        rw [abs_of_pos hθA, abs_of_pos hθB, abs_of_nonneg hρ] at h6
        have e2 := mul_le_mul_of_nonneg_left hb2 hθA.le
        have e3 := mul_le_mul_of_nonneg_left hb3 hθA.le
        have e4 := mul_le_mul_of_nonneg_left hb4 hθB.le
        have e5 := mul_le_mul_of_nonneg_left hb5 hθB.le
        have e6 := mul_le_mul_of_nonneg_left hb6 hρ
        linarith
      have hdiag : diag θA θB ρ ζ = ((ζ.n * (ζ.n - 1) : ℕ) : F) + θA * ((ζ.nA : ℕ) : F)
          + θB * ((ζ.nB : ℕ) : F) + ρ * ((ζ.t : ℕ) : F) := rfl
      have hnA : ((ζ.nA : ℕ) : F) = ((ζ.sumA : ℕ) : F) + ((ζ.t : ℕ) : F) := by
        rw [show ζ.nA = ζ.sumA + ζ.t from rfl]; push_cast; ring
      have hnB : ((ζ.nB : ℕ) : F) = ((ζ.sumB : ℕ) : F) + ((ζ.t : ℕ) : F) := by
        rw [show ζ.nB = ζ.sumB + ζ.t from rfl]; push_cast; ring
      have hcablt : ((cab ζ : ℕ) : F) < ((ζ.n * (ζ.n - 1) : ℕ) : F) := by
        exact_mod_cast cab_lt ζ hn2
      rw [hdiag, hnA, hnB] at habs
      have hfinal : ((ζ.n * (ζ.n - 1) : ℕ) : F) * (M * W) ≤ ((cab ζ : ℕ) : F) * (M * W) := by
        nlinarith [habs]
      have hMzero : M = 0 := by
        by_contra hne
        have hMpos : 0 < M := lt_of_le_of_ne hMnn (Ne.symm hne)
        nlinarith [hfinal, hcablt, mul_pos hMpos hW]
      rw [← hMW, hMzero, zero_mul]
    have hM0 : M = 0 := by rw [hMdef, hzero, zero_div]
    have hle := hζmax ξ hξ
    rw [hM0] at hle
    have hw1 : 0 < wtC νA νB ξ := wtC_pos hνA hνB ξ
    have hfin : |h ξ| ≤ 0 := by
      have := (div_le_iff₀ hw1).mp hle
      linarith
    exact abs_eq_zero.mp (le_antisymm hfin (abs_nonneg _))

theorem homogeneous_eq_zero (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hPA : ∀ k i, 0 ≤ PA k i) (hPB : ∀ l j, 0 ≤ PB l j)
    (hνA : ∀ i, 0 < νA i) (hνB : ∀ j, 0 < νB j)
    (hstA : ∀ i, ∑ k, νA k * PA k i = νA i) (hstB : ∀ j, ∑ l, νB l * PB l j = νB j)
    {h : Config KA KB → F}
    (hbd : ∀ ξ : Config KA KB, ξ.n ≤ 1 → h ξ = 0)
    (hrec : ∀ ξ : Config KA KB, 2 ≤ ξ.n →
      diag θA θB ρ ξ * h ξ = rhsGen θA θB ρ PA PB h ξ) :
    ∀ ξ : Config KA KB, h ξ = 0 := fun ξ =>
  homogeneous_eq_zero_le (νA := νA) (νB := νB) (N := ξ.nA + ξ.nB) hθA hθB hρ hPA hPB hνA hνB
    hstA hstB (fun η hη _ => hbd η hη) (fun η hη _ => hrec η hη) ξ le_rfl

theorem IsSolutionGen.unique (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hPA : ∀ k i, 0 ≤ PA k i) (hPB : ∀ l j, 0 ≤ PB l j)
    (hνA : ∀ i, 0 < νA i) (hνB : ∀ j, 0 < νB j)
    (hstA : ∀ i, ∑ k, νA k * PA k i = νA i) (hstB : ∀ j, ∑ l, νB l * PB l j = νB j)
    {q₁ q₂ : Config KA KB → F} (h₁ : IsSolutionGen θA θB ρ νA νB PA PB q₁)
    (h₂ : IsSolutionGen θA θB ρ νA νB PA PB q₂) : q₁ = q₂ := by
  have hbd : ∀ ξ : Config KA KB, ξ.n ≤ 1 → q₁ ξ - q₂ ξ = 0 := by
    intro ξ hn
    rcases Nat.lt_or_ge ξ.n 1 with hlt | hge
    · have hz : ξ = 0 := ξ.eq_zero_of_n_eq_zero (by omega)
      subst hz
      rw [h₁.empty, h₂.empty, sub_self]
    · rcases ξ.exists_e_of_n_eq_one (by omega) with ⟨i, rfl⟩ | ⟨j, rfl⟩ | ⟨i, j, rfl⟩
      · rw [h₁.bdryA, h₂.bdryA, sub_self]
      · rw [h₁.bdryB, h₂.bdryB, sub_self]
      · rw [h₁.bdryC, h₂.bdryC, sub_self]
  have hrec : ∀ ξ : Config KA KB, 2 ≤ ξ.n →
      diag θA θB ρ ξ * (q₁ ξ - q₂ ξ) = rhsGen θA θB ρ PA PB (fun η => q₁ η - q₂ η) ξ := by
    intro ξ hn
    rw [rhsGen_sub, mul_sub, h₁.recursion ξ hn, h₂.recursion ξ hn]
  funext ξ
  have := homogeneous_eq_zero (νA := νA) (νB := νB) hθA hθB hρ hPA hPB hνA hνB hstA hstB
    hbd hrec ξ
  linarith [this]

end Rhone.MarkovChain.GeneralMutation
