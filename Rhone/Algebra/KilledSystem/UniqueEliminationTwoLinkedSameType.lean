/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.KilledSystem.UniqueScalars

/-! # Uniqueness of the killed-PIM system: elimination for a doubly linked state -/

@[expose] public section

set_option linter.unusedSimpArgs false

namespace Rhone.Algebra.KilledSystem

theorem unique_piece_k70 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (s270 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ ⟨1,
      0, 0, 1, 1, 0, 0, 0⟩ - (2 + 2 * thA + 2 * thB + 2 * rhoL) * rhoL * Δ ⟨2, 0, 1, 1, 0, 0, 0, 0⟩
      = 0)
    (z79 : Δ ⟨2, 0, 1, 1, 0, 0, 0, 0⟩ = 0)
    : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ ⟨1, 0, 0,
      1, 1, 0, 0, 0⟩ = 0 := by
  linear_combination (1) * s270 + (2 * rhoL ^ 2 + 2 * rhoL * thA + 2 * rhoL * thB + 2 * rhoL) *
    z79

theorem unique_piece_k71 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (s271 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ ⟨1,
      0, 1, 0, 0, 0, 0, 1⟩ - (2 + 2 * thA + 2 * thB + 2 * rhoL) * rhoL * Δ ⟨1, 1, 1, 1, 0, 0, 0, 0⟩
      = 0)
    (z76 : Δ ⟨1, 1, 1, 1, 0, 0, 0, 0⟩ = 0)
    : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ ⟨1, 0, 1,
      0, 0, 0, 0, 1⟩ = 0 := by
  linear_combination (1) * s271 + (2 * rhoL ^ 2 + 2 * rhoL * thA + 2 * rhoL * thB + 2 * rhoL) *
    z76

theorem unique_piece_k72 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (s272 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ ⟨1,
      0, 1, 0, 0, 0, 1, 0⟩ - (2 + 2 * thA + 2 * thB + 2 * rhoL) * rhoL * Δ ⟨1, 1, 2, 0, 0, 0, 0, 0⟩
      = 0)
    (z77 : Δ ⟨1, 1, 2, 0, 0, 0, 0, 0⟩ = 0)
    : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ ⟨1, 0, 1,
      0, 0, 0, 1, 0⟩ = 0 := by
  linear_combination (1) * s272 + (2 * rhoL ^ 2 + 2 * rhoL * thA + 2 * rhoL * thB + 2 * rhoL) *
    z77

theorem unique_piece_k73 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (s273 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ ⟨1,
      0, 1, 0, 0, 1, 0, 0⟩ - (2 + 2 * thA + 2 * thB + 2 * rhoL) * rhoL * Δ ⟨2, 0, 1, 1, 0, 0, 0, 0⟩
      = 0)
    (z79 : Δ ⟨2, 0, 1, 1, 0, 0, 0, 0⟩ = 0)
    : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ ⟨1, 0, 1,
      0, 0, 1, 0, 0⟩ = 0 := by
  linear_combination (1) * s273 + (2 * rhoL ^ 2 + 2 * rhoL * thA + 2 * rhoL * thB + 2 * rhoL) *
    z79

theorem unique_piece_k74 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (s274 : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ ⟨1,
      0, 1, 0, 1, 0, 0, 0⟩ - (2 + 2 * thA + 2 * thB + 2 * rhoL) * rhoL * Δ ⟨2, 0, 2, 0, 0, 0, 0, 0⟩
      = 0)
    (z80 : Δ ⟨2, 0, 2, 0, 0, 0, 0, 0⟩ = 0)
    : ((6 + 2 * thA + 2 * thB + rhoL) * (2 + 2 * thA + 2 * thB + 2 * rhoL) - 4 * rhoL) * Δ ⟨1, 0, 1,
      0, 1, 0, 0, 0⟩ = 0 := by
  linear_combination (1) * s274 + (2 * rhoL ^ 2 + 2 * rhoL * thA + 2 * rhoL * thB + 2 * rhoL) *
    z80

theorem unique_piece_k46 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (h46 : (2 * rhoL + 2 * thA + 2 * thB + 2) * Δ ⟨0, 0, 0, 0, 0, 0, 0, 2⟩ + (-2 * rhoL) * Δ ⟨0, 1,
      0, 1, 0, 0, 0, 1⟩ = 0)
    (z56 : Δ ⟨0, 1, 0, 1, 0, 0, 0, 1⟩ = 0)
    : (2 + 2 * thA + 2 * thB + 2 * rhoL) * Δ ⟨0, 0, 0, 0, 0, 0, 0, 2⟩ = 0 := by
  linear_combination (1) * h46 + (2 * rhoL) * z56

theorem unique_piece_k47 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (h47 : (2 * rhoL + 2 * thA + 2 * thB + 2) * Δ ⟨0, 0, 0, 0, 0, 0, 1, 1⟩ + (-rhoL) * Δ ⟨0, 1, 0,
      1, 0, 0, 1, 0⟩ + (-rhoL) * Δ ⟨0, 1, 1, 0, 0, 0, 0, 1⟩ = 0)
    (z57 : Δ ⟨0, 1, 0, 1, 0, 0, 1, 0⟩ = 0)
    (z60 : Δ ⟨0, 1, 1, 0, 0, 0, 0, 1⟩ = 0)
    : (2 + 2 * thA + 2 * thB + 2 * rhoL) * Δ ⟨0, 0, 0, 0, 0, 0, 1, 1⟩ = 0 := by
  linear_combination (1) * h47 + (rhoL) * z57 + (rhoL) * z60

theorem unique_piece_k48 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (h48 : (2 * rhoL + 2 * thA + 2 * thB + 2) * Δ ⟨0, 0, 0, 0, 0, 0, 2, 0⟩ + (-2 * rhoL) * Δ ⟨0, 1,
      1, 0, 0, 0, 1, 0⟩ = 0)
    (z61 : Δ ⟨0, 1, 1, 0, 0, 0, 1, 0⟩ = 0)
    : (2 + 2 * thA + 2 * thB + 2 * rhoL) * Δ ⟨0, 0, 0, 0, 0, 0, 2, 0⟩ = 0 := by
  linear_combination (1) * h48 + (2 * rhoL) * z61

theorem unique_piece_k49 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (h49 : (2 * rhoL + 2 * thA + 2 * thB + 2) * Δ ⟨0, 0, 0, 0, 0, 1, 0, 1⟩ + (-rhoL) * Δ ⟨0, 1, 0,
      1, 0, 1, 0, 0⟩ + (-rhoL) * Δ ⟨1, 0, 0, 1, 0, 0, 0, 1⟩ = 0)
    (z58 : Δ ⟨0, 1, 0, 1, 0, 1, 0, 0⟩ = 0)
    (z67 : Δ ⟨1, 0, 0, 1, 0, 0, 0, 1⟩ = 0)
    : (2 + 2 * thA + 2 * thB + 2 * rhoL) * Δ ⟨0, 0, 0, 0, 0, 1, 0, 1⟩ = 0 := by
  linear_combination (1) * h49 + (rhoL) * z58 + (rhoL) * z67

theorem unique_piece_k50 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (h50 : (2 * rhoL + 2 * thA + 2 * thB + 2) * Δ ⟨0, 0, 0, 0, 0, 1, 1, 0⟩ + (-rhoL) * Δ ⟨0, 1, 1,
      0, 0, 1, 0, 0⟩ + (-rhoL) * Δ ⟨1, 0, 0, 1, 0, 0, 1, 0⟩ = 0)
    (z62 : Δ ⟨0, 1, 1, 0, 0, 1, 0, 0⟩ = 0)
    (z68 : Δ ⟨1, 0, 0, 1, 0, 0, 1, 0⟩ = 0)
    : (2 + 2 * thA + 2 * thB + 2 * rhoL) * Δ ⟨0, 0, 0, 0, 0, 1, 1, 0⟩ = 0 := by
  linear_combination (1) * h50 + (rhoL) * z62 + (rhoL) * z68

theorem unique_piece_k51 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (h51 : (2 * rhoL + 2 * thA + 2 * thB + 2) * Δ ⟨0, 0, 0, 0, 0, 2, 0, 0⟩ + (-2 * rhoL) * Δ ⟨1, 0,
      0, 1, 0, 1, 0, 0⟩ = 0)
    (z69 : Δ ⟨1, 0, 0, 1, 0, 1, 0, 0⟩ = 0)
    : (2 + 2 * thA + 2 * thB + 2 * rhoL) * Δ ⟨0, 0, 0, 0, 0, 2, 0, 0⟩ = 0 := by
  linear_combination (1) * h51 + (2 * rhoL) * z69

theorem unique_piece_k52 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (h52 : (2 * rhoL + 2 * thA + 2 * thB + 2) * Δ ⟨0, 0, 0, 0, 1, 0, 0, 1⟩ + (-rhoL) * Δ ⟨0, 1, 0,
      1, 1, 0, 0, 0⟩ + (-rhoL) * Δ ⟨1, 0, 1, 0, 0, 0, 0, 1⟩ = 0)
    (z59 : Δ ⟨0, 1, 0, 1, 1, 0, 0, 0⟩ = 0)
    (z71 : Δ ⟨1, 0, 1, 0, 0, 0, 0, 1⟩ = 0)
    : (2 + 2 * thA + 2 * thB + 2 * rhoL) * Δ ⟨0, 0, 0, 0, 1, 0, 0, 1⟩ = 0 := by
  linear_combination (1) * h52 + (rhoL) * z59 + (rhoL) * z71

theorem unique_piece_k53 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (h53 : (2 * rhoL + 2 * thA + 2 * thB + 2) * Δ ⟨0, 0, 0, 0, 1, 0, 1, 0⟩ + (-rhoL) * Δ ⟨0, 1, 1,
      0, 1, 0, 0, 0⟩ + (-rhoL) * Δ ⟨1, 0, 1, 0, 0, 0, 1, 0⟩ = 0)
    (z63 : Δ ⟨0, 1, 1, 0, 1, 0, 0, 0⟩ = 0)
    (z72 : Δ ⟨1, 0, 1, 0, 0, 0, 1, 0⟩ = 0)
    : (2 + 2 * thA + 2 * thB + 2 * rhoL) * Δ ⟨0, 0, 0, 0, 1, 0, 1, 0⟩ = 0 := by
  linear_combination (1) * h53 + (rhoL) * z63 + (rhoL) * z72

theorem unique_piece_k54 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (h54 : (2 * rhoL + 2 * thA + 2 * thB + 2) * Δ ⟨0, 0, 0, 0, 1, 1, 0, 0⟩ + (-rhoL) * Δ ⟨1, 0, 0,
      1, 1, 0, 0, 0⟩ + (-rhoL) * Δ ⟨1, 0, 1, 0, 0, 1, 0, 0⟩ = 0)
    (z70 : Δ ⟨1, 0, 0, 1, 1, 0, 0, 0⟩ = 0)
    (z73 : Δ ⟨1, 0, 1, 0, 0, 1, 0, 0⟩ = 0)
    : (2 + 2 * thA + 2 * thB + 2 * rhoL) * Δ ⟨0, 0, 0, 0, 1, 1, 0, 0⟩ = 0 := by
  linear_combination (1) * h54 + (rhoL) * z70 + (rhoL) * z73

theorem unique_piece_k55 {F : Type*} [Field F] (thA thB rhoL : F) (Δ : St → F)
    (h55 : (2 * rhoL + 2 * thA + 2 * thB + 2) * Δ ⟨0, 0, 0, 0, 2, 0, 0, 0⟩ + (-2 * rhoL) * Δ ⟨1, 0,
      1, 0, 1, 0, 0, 0⟩ = 0)
    (z74 : Δ ⟨1, 0, 1, 0, 1, 0, 0, 0⟩ = 0)
    : (2 + 2 * thA + 2 * thB + 2 * rhoL) * Δ ⟨0, 0, 0, 0, 2, 0, 0, 0⟩ = 0 := by
  linear_combination (1) * h55 + (2 * rhoL) * z74

end Rhone.Algebra.KilledSystem
