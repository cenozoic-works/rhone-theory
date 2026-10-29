/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.SlotDeletion.BiallelicDenominator
public import Rhone.Probability.SamplingNumerators.Basic

/-! # Sampling correlations through block (3,3) -/

@[expose] public section

namespace Rhone.Probability.SamplingNumerators

open Matrix LinearAlgebra.Recursion LinearAlgebra.Multilinear Multilinear LinearAlgebra.SlotDeletion
    SlotDeletion

section Actual

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {a b ρ : F} {πA πB : Fin 2 → F} {q : Config 2 2 → F}
variable (ha : 0 < a) (hb : 0 < b) (hr : 0 ≤ ρ)
variable (hq : IsSolution a b ρ πA πB q)
variable (hπA : πA 0 + πA 1 = 1) (hπB : πB 0 + πB 1 = 1)

omit [LinearOrder F] [IsStrictOrderedRing F] in
private theorem phi_edge_A_level (i t : ℕ) :
    Phi q πA πB i 0 t = Phi q πA πB i 0 0 := by
  simpa using Phi_of_min_le q πA πB (i := i) (j := 0) (t := t) (by simp)

omit [LinearOrder F] [IsStrictOrderedRing F] in
private theorem phi_edge_B_level (j t : ℕ) :
    Phi q πA πB 0 j t = Phi q πA πB 0 j 0 := by
  simpa using Phi_of_min_le q πA πB (i := 0) (j := j) (t := t) (by simp)

include ha hb hr hq hπA hπB

theorem phi20_cleared (t : ℕ) :
    (a + 1) * Phi q πA πB 2 0 t = kap πA := by
  rw [phi_edge_A_level]
  have h := phi_A_rec ha hb hr hq hπA hπB (i := 2) (by omega)
  have h1 := Phi_i_one ha hb hr hq hπA 0 0
  have h0 := Phi_zero_zero hq (t := 0)
  norm_num [h1, h0] at h
  simpa [add_comm] using h

theorem phi02_cleared (t : ℕ) :
    (b + 1) * Phi q πA πB 0 2 t = kap πB := by
  rw [phi_edge_B_level]
  have h := phi_B_rec ha hb hr hq hπA hπB (j := 2) (by omega)
  have h1 := Phi_j_one ha hb hr hq hπA hπB 0 0
  have h0 := Phi_zero_zero hq (t := 0)
  norm_num [h1, h0] at h
  simpa [add_comm] using h

theorem phi30_cleared (t : ℕ) :
    ((a + 1) * (a + 2)) * Phi q πA πB 3 0 t = 2 * kap πA * gam πA := by
  rw [phi_edge_A_level]
  have h := phi_A_rec ha hb hr hq hπA hπB (i := 3) (by omega)
  have h1 := Phi_i_one ha hb hr hq hπA 0 0
  norm_num [h1] at h
  have h2 := phi20_cleared ha hb hr hq hπA hπB 0
  linear_combination (norm := ring!) (a + 1) * h + 2 * gam πA * h2

theorem phi03_cleared (t : ℕ) :
    ((b + 1) * (b + 2)) * Phi q πA πB 0 3 t = 2 * kap πB * gam πB := by
  rw [phi_edge_B_level]
  have h := phi_B_rec ha hb hr hq hπA hπB (j := 3) (by omega)
  have h1 := Phi_j_one ha hb hr hq hπA hπB 0 0
  norm_num [h1] at h
  have h2 := phi02_cleared ha hb hr hq hπA hπB 0
  linear_combination (norm := ring!) (b + 1) * h + 2 * gam πB * h2

theorem phiRecursionSource22 :
    (fun t : Fin 3 => phiRecursionSource q πA πB 2 2 t) =
      ![2 * kap πA * Phi q πA πB 0 2 0 + 2 * kap πB * Phi q πA πB 2 0 0,
        2 * kap πA * Phi q πA πB 0 2 0 + 2 * kap πB * Phi q πA πB 2 0 0,
        2 * kap πA * kap πB] := by
  have hzA := Phi_i_one ha hb hr hq hπA
  have hzB := Phi_j_one ha hb hr hq hπA hπB
  have hz0 := Phi_zero_zero hq
  funext t
  fin_cases t <;>
    norm_num [phiRecursionSource, hzA, hzB, hz0, phi_edge_A_level, phi_edge_B_level] <;> ring

theorem phiRecursionSource23 :
    (fun t : Fin 3 => phiRecursionSource q πA πB 2 3 t) =
      ![2 * kap πA * Phi q πA πB 0 3 0 + 6 * gam πB * Phi q πA πB 2 2 0,
        2 * kap πA * Phi q πA πB 0 3 0 + 6 * gam πB * Phi q πA πB 2 2 1,
        2 * kap πA * gam πB * Phi q πA πB 0 2 0 +
          4 * gam πB * Phi q πA πB 2 2 2] := by
  have hzA := Phi_i_one ha hb hr hq hπA
  have hzB := Phi_j_one ha hb hr hq hπA hπB
  funext t
  fin_cases t <;>
    norm_num [phiRecursionSource, hzA, hzB, phi_edge_A_level, phi_edge_B_level] <;> ring

theorem phiRecursionSource32 :
    (fun t : Fin 3 => phiRecursionSource q πA πB 3 2 t) =
      ![6 * gam πA * Phi q πA πB 2 2 0 + 2 * kap πB * Phi q πA πB 3 0 0,
        6 * gam πA * Phi q πA πB 2 2 1 + 2 * kap πB * Phi q πA πB 3 0 0,
        4 * gam πA * Phi q πA πB 2 2 2 +
          2 * gam πA * kap πB * Phi q πA πB 2 0 0] := by
  have hzA := Phi_i_one ha hb hr hq hπA
  have hzB := Phi_j_one ha hb hr hq hπA hπB
  funext t
  fin_cases t <;>
    norm_num [phiRecursionSource, hzA, hzB, phi_edge_A_level, phi_edge_B_level] <;> ring

theorem phiRecursionSource33 :
    (fun t : Fin 4 => phiRecursionSource q πA πB 3 3 t) =
      ![6 * gam πA * Phi q πA πB 2 3 0 + 6 * gam πB * Phi q πA πB 3 2 0,
        6 * gam πA * Phi q πA πB 2 3 1 + 6 * gam πB * Phi q πA πB 3 2 1,
        4 * gam πA * Phi q πA πB 2 3 2 + 4 * gam πB * Phi q πA πB 3 2 2 +
          2 * gam πA * gam πB * Phi q πA πB 2 2 1,
        6 * gam πA * gam πB * Phi q πA πB 2 2 2] := by
  have hzA := Phi_i_one ha hb hr hq hπA
  have hzB := Phi_j_one ha hb hr hq hπA hπB
  funext t
  fin_cases t <;> norm_num [phiRecursionSource, hzA, hzB] <;> ring

theorem usmani_cleared (i j : ℕ) (C f : F)
    (B : Fin (min i j + 1) → F)
    (hsource : ∀ t : Fin (min i j + 1),
      C * phiRecursionSource q πA πB i j t = f * B t)
    (t : Fin (min i j + 1)) :
    (C * LinearAlgebra.Tridiag.E F i j a b ρ) * Phi q πA πB i j t =
      f * ((Analysis.DenominatorEquation.U F i j a b ρ) *ᵥ B) t := by
  have hc' := congrFun (DenominatorEquation.E_smul_Phi ha hb hr hq hπA hπB i j) t
  change LinearAlgebra.Tridiag.E F i j a b ρ * Phi q πA πB i j t =
    ((Analysis.DenominatorEquation.U F i j a b ρ) *ᵥ
      (fun u : Fin (min i j + 1) => phiRecursionSource q πA πB i j u)) t at hc'
  calc
    (C * LinearAlgebra.Tridiag.E F i j a b ρ) * Phi q πA πB i j t =
        C * (LinearAlgebra.Tridiag.E F i j a b ρ * Phi q πA πB i j t) := by ring
    _ = C * ((Analysis.DenominatorEquation.U F i j a b ρ) *ᵥ
        (fun u : Fin (min i j + 1) => phiRecursionSource q πA πB i j u)) t := by rw [hc']
    _ = f * ((Analysis.DenominatorEquation.U F i j a b ρ) *ᵥ B) t := by
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      calc
        C * ((Analysis.DenominatorEquation.U F i j a b ρ) t u * phiRecursionSource q πA πB i j u) =
            (Analysis.DenominatorEquation.U F i j a b ρ) t u *
                (C * phiRecursionSource q πA πB i j u) := by ring
        _ = (Analysis.DenominatorEquation.U F i j a b ρ) t u * (f * B u) := by rw [hsource]
        _ = f * ((Analysis.DenominatorEquation.U F i j a b ρ) t u * B u) := by ring

theorem phiRecursionSource22_cleared (t : Fin 3) :
    c22 a b * phiRecursionSource q πA πB 2 2 t = kap πA * kap πB * s22 a b t := by
  rw [congrFun (phiRecursionSource22 ha hb hr hq hπA hπB) t]
  have h20 := phi20_cleared ha hb hr hq hπA hπB 0
  have h02 := phi02_cleared ha hb hr hq hπA hπB 0
  fin_cases t <;> norm_num [s22, c22]
  · linear_combination (norm := ring!) 2 * kap πA * (a + 1) * h02 + 2 * kap πB * (b + 1) * h20
  · linear_combination (norm := ring!) 2 * kap πA * (a + 1) * h02 + 2 * kap πB * (b + 1) * h20
  · ring

theorem phi22_cleared (t : Fin 3) :
    d22 a b ρ * Phi q πA πB 2 2 t = kap πA * kap πB * n22 a b ρ t := by
  exact usmani_cleared ha hb hr hq hπA hπB 2 2 (c22 a b)
    (kap πA * kap πB) (s22 a b) (phiRecursionSource22_cleared ha hb hr hq hπA hπB) t

theorem phiRecursionSource23_cleared (t : Fin 3) :
    c23 a b ρ * phiRecursionSource q πA πB 2 3 t =
      kap πA * kap πB * gam πB * s23 a b ρ t := by
  rw [congrFun (phiRecursionSource23 ha hb hr hq hπA hπB) t]
  have he3 := phi03_cleared ha hb hr hq hπA hπB 0
  have he2 := phi02_cleared ha hb hr hq hπA hπB 0
  have h22 := phi22_cleared ha hb hr hq hπA hπB t
  simp only [d22, c22] at h22
  fin_cases t <;> norm_num [c23, s23] at h22 ⊢
  · linear_combination (norm := ring!) 2 * kap πA * (a + 1) * LinearAlgebra.Tridiag.E F 2 2 a b ρ *
      he3 +
      6 * gam πB * (b + 2) * h22
  · linear_combination (norm := ring!) 2 * kap πA * (a + 1) * LinearAlgebra.Tridiag.E F 2 2 a b ρ *
      he3 +
      6 * gam πB * (b + 2) * h22
  · linear_combination (norm := ring!) 2 * kap πA * gam πB * (a + 1) * (b + 2) *
      LinearAlgebra.Tridiag.E F 2 2 a b ρ * he2 + 4 * gam πB * (b + 2) * h22

theorem phi23_cleared (t : Fin 3) :
    d23 a b ρ * Phi q πA πB 2 3 t =
      kap πA * kap πB * gam πB * n23 a b ρ t := by
  exact usmani_cleared ha hb hr hq hπA hπB 2 3 (c23 a b ρ)
    (kap πA * kap πB * gam πB) (s23 a b ρ)
    (phiRecursionSource23_cleared ha hb hr hq hπA hπB) t

theorem phiRecursionSource32_cleared (t : Fin 3) :
    c32 a b ρ * phiRecursionSource q πA πB 3 2 t =
      kap πA * kap πB * gam πA * s32 a b ρ t := by
  rw [congrFun (phiRecursionSource32 ha hb hr hq hπA hπB) t]
  have he3 := phi30_cleared ha hb hr hq hπA hπB 0
  have he2 := phi20_cleared ha hb hr hq hπA hπB 0
  have h22 := phi22_cleared ha hb hr hq hπA hπB t
  simp only [d22, c22] at h22
  fin_cases t <;> norm_num [c32, s32] at h22 ⊢
  · linear_combination (norm := ring!) 2 * kap πB * (b + 1) * LinearAlgebra.Tridiag.E F 2 2 a b ρ *
      he3 +
      6 * gam πA * (a + 2) * h22
  · linear_combination (norm := ring!) 2 * kap πB * (b + 1) * LinearAlgebra.Tridiag.E F 2 2 a b ρ *
      he3 +
      6 * gam πA * (a + 2) * h22
  · linear_combination (norm := ring!) 2 * kap πB * gam πA * (b + 1) * (a + 2) *
      LinearAlgebra.Tridiag.E F 2 2 a b ρ * he2 + 4 * gam πA * (a + 2) * h22

theorem phi32_cleared (t : Fin 3) :
    d32 a b ρ * Phi q πA πB 3 2 t =
      kap πA * kap πB * gam πA * n32 a b ρ t := by
  exact usmani_cleared ha hb hr hq hπA hπB 3 2 (c32 a b ρ)
    (kap πA * kap πB * gam πA) (s32 a b ρ)
    (phiRecursionSource32_cleared ha hb hr hq hπA hπB) t

theorem phiRecursionSource33_cleared (t : Fin 4) :
    c33 a b ρ * phiRecursionSource q πA πB 3 3 t =
      kap πA * kap πB * gam πA * gam πB * s33 a b ρ t := by
  rw [congrFun (phiRecursionSource33 ha hb hr hq hπA hπB) t]
  have h23 := phi23_cleared ha hb hr hq hπA hπB
  have h32 := phi32_cleared ha hb hr hq hπA hπB
  have h22 := phi22_cleared ha hb hr hq hπA hπB
  simp only [d23, c23] at h23
  simp only [d32, c32] at h32
  simp only [d22, c22] at h22
  fin_cases t <;> norm_num [c33, s33]
  · linear_combination
      (norm := (norm_num only [Fin.val_zero, Fin.val_one, Fin.val_two]; ring))
      6 * gam πA * (a + 2) * LinearAlgebra.Tridiag.E F 3 2 a b ρ * h23 0 +
      6 * gam πB * (b + 2) * LinearAlgebra.Tridiag.E F 2 3 a b ρ * h32 0
  · linear_combination
      (norm := (norm_num only [Fin.val_zero, Fin.val_one, Fin.val_two]; ring))
      6 * gam πA * (a + 2) * LinearAlgebra.Tridiag.E F 3 2 a b ρ * h23 1 +
      6 * gam πB * (b + 2) * LinearAlgebra.Tridiag.E F 2 3 a b ρ * h32 1
  · linear_combination
      (norm := (norm_num only [Fin.val_zero, Fin.val_one, Fin.val_two]; ring))
      4 * gam πA * (a + 2) * LinearAlgebra.Tridiag.E F 3 2 a b ρ * h23 2 +
      4 * gam πB * (b + 2) * LinearAlgebra.Tridiag.E F 2 3 a b ρ * h32 2 +
      2 * gam πA * gam πB * (a + 2) * (b + 2) * LinearAlgebra.Tridiag.E F 2 3 a b ρ *
      LinearAlgebra.Tridiag.E F 3 2 a b ρ * h22 1
  · linear_combination
      (norm := (norm_num only [Fin.val_zero, Fin.val_one, Fin.val_two]; ring))
      6 * gam πA * gam πB * (a + 2) * (b + 2) *
      LinearAlgebra.Tridiag.E F 2 3 a b ρ * LinearAlgebra.Tridiag.E F 3 2 a b ρ * h22 2

theorem phi33_cleared (t : Fin 4) :
    d33 a b ρ * Phi q πA πB 3 3 t =
      kap πA * kap πB * gam πA * gam πB * n33 a b ρ t := by
  exact usmani_cleared ha hb hr hq hπA hπB 3 3 (c33 a b ρ)
    (kap πA * kap πB * gam πA * gam πB) (s33 a b ρ)
    (phiRecursionSource33_cleared ha hb hr hq hπA hπB) t

theorem Dfull_phi33 (t : Fin 4) :
    Dfull a b ρ 3 3 * Phi q πA πB 3 3 t =
      kap πA * kap πB * gam πA * gam πB * n33 a b ρ t := by
  rw [← d33_eq_Dfull]
  exact phi33_cleared ha hb hr hq hπA hπB t

end Actual

end Rhone.Probability.SamplingNumerators
