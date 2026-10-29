/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.Spectral.Floor

/-! # The sector basis carries `T^{(i,j)}` -/

@[expose] public section

namespace Rhone.LinearAlgebra.Spectral

open Matrix

variable (thA thB rho : ℝ)

noncomputable def C_2_2 :
    Matrix (Fin (min 2 2 + 1)) (Fin (min 2 2 + 1)) ℝ :=
  !![12 + 2 * thA + 2 * thB, -8, 0;
    -rho, 6 + 2 * thA + 2 * thB + rho, -2;
    0, -2 * rho, 2 + 2 * thA + 2 * thB + 2 * rho
  ]

theorem C_2_2_eq_T : C_2_2 thA thB rho = T 2 2 thA thB rho := by
  ext t s
  fin_cases t <;> fin_cases s <;>
    simp [C_2_2, T, Tdiag, Tsup, Tsub] <;> ring

theorem C_2_2_eigen_ge_floor (hrho : 0 ≤ rho) {mu : ℝ}
    {v : Fin (min 2 2 + 1) → ℝ} (hv : v ≠ 0)
    (heig : C_2_2 thA thB rho *ᵥ v = mu • v) :
    floorMu 2 2 thA thB ≤ mu := by
  rw [C_2_2_eq_T] at heig
  exact T_eigen_ge_floor hrho hv heig

noncomputable def C_2_3 :
    Matrix (Fin (min 2 3 + 1)) (Fin (min 2 3 + 1)) ℝ :=
  !![20 + 2 * thA + 3 * thB, -12, 0;
    -rho, 12 + 2 * thA + 3 * thB + rho, -4;
    0, -2 * rho, 6 + 2 * thA + 3 * thB + 2 * rho
  ]

theorem C_2_3_eq_T : C_2_3 thA thB rho = T 2 3 thA thB rho := by
  ext t s
  fin_cases t <;> fin_cases s <;>
    simp [C_2_3, T, Tdiag, Tsup, Tsub] <;> ring

theorem C_2_3_eigen_ge_floor (hrho : 0 ≤ rho) {mu : ℝ}
    {v : Fin (min 2 3 + 1) → ℝ} (hv : v ≠ 0)
    (heig : C_2_3 thA thB rho *ᵥ v = mu • v) :
    floorMu 2 3 thA thB ≤ mu := by
  rw [C_2_3_eq_T] at heig
  exact T_eigen_ge_floor hrho hv heig

noncomputable def C_2_4 :
    Matrix (Fin (min 2 4 + 1)) (Fin (min 2 4 + 1)) ℝ :=
  !![30 + 2 * thA + 4 * thB, -16, 0;
    -rho, 20 + 2 * thA + 4 * thB + rho, -6;
    0, -2 * rho, 12 + 2 * thA + 4 * thB + 2 * rho
  ]

theorem C_2_4_eq_T : C_2_4 thA thB rho = T 2 4 thA thB rho := by
  ext t s
  fin_cases t <;> fin_cases s <;>
    simp [C_2_4, T, Tdiag, Tsup, Tsub] <;> ring

theorem C_2_4_eigen_ge_floor (hrho : 0 ≤ rho) {mu : ℝ}
    {v : Fin (min 2 4 + 1) → ℝ} (hv : v ≠ 0)
    (heig : C_2_4 thA thB rho *ᵥ v = mu • v) :
    floorMu 2 4 thA thB ≤ mu := by
  rw [C_2_4_eq_T] at heig
  exact T_eigen_ge_floor hrho hv heig

noncomputable def C_3_2 :
    Matrix (Fin (min 3 2 + 1)) (Fin (min 3 2 + 1)) ℝ :=
  !![20 + 3 * thA + 2 * thB, -12, 0;
    -rho, 12 + 3 * thA + 2 * thB + rho, -4;
    0, -2 * rho, 6 + 3 * thA + 2 * thB + 2 * rho
  ]

theorem C_3_2_eq_T : C_3_2 thA thB rho = T 3 2 thA thB rho := by
  ext t s
  fin_cases t <;> fin_cases s <;>
    simp [C_3_2, T, Tdiag, Tsup, Tsub] <;> ring

theorem C_3_2_eigen_ge_floor (hrho : 0 ≤ rho) {mu : ℝ}
    {v : Fin (min 3 2 + 1) → ℝ} (hv : v ≠ 0)
    (heig : C_3_2 thA thB rho *ᵥ v = mu • v) :
    floorMu 3 2 thA thB ≤ mu := by
  rw [C_3_2_eq_T] at heig
  exact T_eigen_ge_floor hrho hv heig

noncomputable def C_3_3 :
    Matrix (Fin (min 3 3 + 1)) (Fin (min 3 3 + 1)) ℝ :=
  !![30 + 3 * thA + 3 * thB, -18, 0, 0;
    -rho, 20 + 3 * thA + 3 * thB + rho, -8, 0;
    0, -2 * rho, 12 + 3 * thA + 3 * thB + 2 * rho, -2;
    0, 0, -3 * rho, 6 + 3 * thA + 3 * thB + 3 * rho
  ]

theorem C_3_3_eq_T : C_3_3 thA thB rho = T 3 3 thA thB rho := by
  ext t s
  fin_cases t <;> fin_cases s <;>
    simp [C_3_3, T, Tdiag, Tsup, Tsub] <;> ring

theorem C_3_3_eigen_ge_floor (hrho : 0 ≤ rho) {mu : ℝ}
    {v : Fin (min 3 3 + 1) → ℝ} (hv : v ≠ 0)
    (heig : C_3_3 thA thB rho *ᵥ v = mu • v) :
    floorMu 3 3 thA thB ≤ mu := by
  rw [C_3_3_eq_T] at heig
  exact T_eigen_ge_floor hrho hv heig

noncomputable def C_3_4 :
    Matrix (Fin (min 3 4 + 1)) (Fin (min 3 4 + 1)) ℝ :=
  !![42 + 3 * thA + 4 * thB, -24, 0, 0;
    -rho, 30 + 3 * thA + 4 * thB + rho, -12, 0;
    0, -2 * rho, 20 + 3 * thA + 4 * thB + 2 * rho, -4;
    0, 0, -3 * rho, 12 + 3 * thA + 4 * thB + 3 * rho
  ]

theorem C_3_4_eq_T : C_3_4 thA thB rho = T 3 4 thA thB rho := by
  ext t s
  fin_cases t <;> fin_cases s <;>
    simp [C_3_4, T, Tdiag, Tsup, Tsub] <;> ring

theorem C_3_4_eigen_ge_floor (hrho : 0 ≤ rho) {mu : ℝ}
    {v : Fin (min 3 4 + 1) → ℝ} (hv : v ≠ 0)
    (heig : C_3_4 thA thB rho *ᵥ v = mu • v) :
    floorMu 3 4 thA thB ≤ mu := by
  rw [C_3_4_eq_T] at heig
  exact T_eigen_ge_floor hrho hv heig

noncomputable def C_4_2 :
    Matrix (Fin (min 4 2 + 1)) (Fin (min 4 2 + 1)) ℝ :=
  !![30 + 4 * thA + 2 * thB, -16, 0;
    -rho, 20 + 4 * thA + 2 * thB + rho, -6;
    0, -2 * rho, 12 + 4 * thA + 2 * thB + 2 * rho
  ]

theorem C_4_2_eq_T : C_4_2 thA thB rho = T 4 2 thA thB rho := by
  ext t s
  fin_cases t <;> fin_cases s <;>
    simp [C_4_2, T, Tdiag, Tsup, Tsub] <;> ring

theorem C_4_2_eigen_ge_floor (hrho : 0 ≤ rho) {mu : ℝ}
    {v : Fin (min 4 2 + 1) → ℝ} (hv : v ≠ 0)
    (heig : C_4_2 thA thB rho *ᵥ v = mu • v) :
    floorMu 4 2 thA thB ≤ mu := by
  rw [C_4_2_eq_T] at heig
  exact T_eigen_ge_floor hrho hv heig

noncomputable def C_4_3 :
    Matrix (Fin (min 4 3 + 1)) (Fin (min 4 3 + 1)) ℝ :=
  !![42 + 4 * thA + 3 * thB, -24, 0, 0;
    -rho, 30 + 4 * thA + 3 * thB + rho, -12, 0;
    0, -2 * rho, 20 + 4 * thA + 3 * thB + 2 * rho, -4;
    0, 0, -3 * rho, 12 + 4 * thA + 3 * thB + 3 * rho
  ]

theorem C_4_3_eq_T : C_4_3 thA thB rho = T 4 3 thA thB rho := by
  ext t s
  fin_cases t <;> fin_cases s <;>
    simp [C_4_3, T, Tdiag, Tsup, Tsub] <;> ring

theorem C_4_3_eigen_ge_floor (hrho : 0 ≤ rho) {mu : ℝ}
    {v : Fin (min 4 3 + 1) → ℝ} (hv : v ≠ 0)
    (heig : C_4_3 thA thB rho *ᵥ v = mu • v) :
    floorMu 4 3 thA thB ≤ mu := by
  rw [C_4_3_eq_T] at heig
  exact T_eigen_ge_floor hrho hv heig

noncomputable def C_4_4 :
    Matrix (Fin (min 4 4 + 1)) (Fin (min 4 4 + 1)) ℝ :=
  !![56 + 4 * thA + 4 * thB, -32, 0, 0, 0;
    -rho, 42 + 4 * thA + 4 * thB + rho, -18, 0, 0;
    0, -2 * rho, 30 + 4 * thA + 4 * thB + 2 * rho, -8, 0;
    0, 0, -3 * rho, 20 + 4 * thA + 4 * thB + 3 * rho, -2;
    0, 0, 0, -4 * rho, 12 + 4 * thA + 4 * thB + 4 * rho
  ]

theorem C_4_4_eq_T : C_4_4 thA thB rho = T 4 4 thA thB rho := by
  ext t s
  fin_cases t <;> fin_cases s <;>
    simp [C_4_4, T, Tdiag, Tsup, Tsub] <;> ring

theorem C_4_4_eigen_ge_floor (hrho : 0 ≤ rho) {mu : ℝ}
    {v : Fin (min 4 4 + 1) → ℝ} (hv : v ≠ 0)
    (heig : C_4_4 thA thB rho *ᵥ v = mu • v) :
    floorMu 4 4 thA thB ≤ mu := by
  rw [C_4_4_eq_T] at heig
  exact T_eigen_ge_floor hrho hv heig

end Rhone.LinearAlgebra.Spectral
