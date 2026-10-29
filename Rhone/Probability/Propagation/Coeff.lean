/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.Propagation.SourceOffsets
public import Rhone.Probability.SlotDeletion.Source

/-! # The recursion source as an abstract linear operator, and the `κ_A = 0` collapse -/

@[expose] public section

namespace Rhone.Probability.Propagation

open LinearAlgebra.Multilinear Multilinear SlotDeletion

variable {K : Type*} [Field K]

def src (κA γA κB γB : K) (f : ℕ → ℕ → ℕ → K) (i j t : ℕ) : K :=
  κA * ((((i - t) * (i - t - 1) : ℕ) : K) * f (i - 2) j t
      + 2 * (((i - t) * t : ℕ) : K) * f (i - 2) j (t - 1))
    + γA * (((i - t) * (i + t - 1) : ℕ) : K) * f (i - 1) j t
    + κB * ((((j - t) * (j - t - 1) : ℕ) : K) * f i (j - 2) t
      + 2 * (((j - t) * t : ℕ) : K) * f i (j - 2) (t - 1))
    + γB * (((j - t) * (j + t - 1) : ℕ) : K) * f i (j - 1) t
    + ((t * (t - 1) : ℕ) : K) * (κA * κB * f (i - 2) (j - 2) (t - 2)
      + κA * γB * f (i - 2) (j - 1) (t - 2)
      + γA * κB * f (i - 1) (j - 2) (t - 2)
      + γA * γB * f (i - 1) (j - 1) (t - 1))

def srcVal (κA γA κB γB : K) (g20 g10 g02 g01 g22 g21 g12 g11 : ℕ → K) (i j t : ℕ) : K :=
  κA * ((((i - t) * (i - t - 1) : ℕ) : K) * g20 t
      + 2 * (((i - t) * t : ℕ) : K) * g20 (t - 1))
    + γA * (((i - t) * (i + t - 1) : ℕ) : K) * g10 t
    + κB * ((((j - t) * (j - t - 1) : ℕ) : K) * g02 t
      + 2 * (((j - t) * t : ℕ) : K) * g02 (t - 1))
    + γB * (((j - t) * (j + t - 1) : ℕ) : K) * g01 t
    + ((t * (t - 1) : ℕ) : K) * (κA * κB * g22 (t - 2)
      + κA * γB * g21 (t - 2)
      + γA * κB * g12 (t - 2)
      + γA * γB * g11 (t - 1))

theorem src_eq_srcVal (κA γA κB γB : K) (f : ℕ → ℕ → ℕ → K) (i j t : ℕ) :
    src κA γA κB γB f i j t
      = srcVal κA γA κB γB (fun u => f (i - 2) j u) (fun u => f (i - 1) j u)
          (fun u => f i (j - 2) u) (fun u => f i (j - 1) u) (fun u => f (i - 2) (j - 2) u)
          (fun u => f (i - 2) (j - 1) u) (fun u => f (i - 1) (j - 2) u)
          (fun u => f (i - 1) (j - 1) u) i j t := rfl

theorem src_eq_phiRecursionSource {F : Type*} [Field F]
    (q : Rhone.LinearAlgebra.Recursion.Config 2 2 → F)
    (πA πB : Fin 2 → F) (i j t : ℕ) :
    src (kap πA) (gam πA) (kap πB) (gam πB) (Phi q πA πB) i j t = phiRecursionSource q πA πB i j
        t := rfl

theorem src_smul (κA γA κB γB c : K) (f : ℕ → ℕ → ℕ → K) (i j t : ℕ) :
    src κA γA κB γB (fun a b s => c * f a b s) i j t = c * src κA γA κB γB f i j t := by
  simp only [src]
  ring

theorem src_range_congr (κA γA κB γB : K) (f g : ℕ → ℕ → ℕ → K) {i j t : ℕ}
    (hi : 1 ≤ i) (hj : 1 ≤ j)
    (h : ∀ a b u, u ≤ min a b → a + b < i + j → f a b u = g a b u) (ht : t ≤ min i j) :
    src κA γA κB γB f i j t = src κA γA κB γB g i j t := by
  have e1 : (((i - t) * (i - t - 1) : ℕ) : K) * f (i - 2) j t
      = (((i - t) * (i - t - 1) : ℕ) : K) * g (i - 2) j t := by
    by_cases hr : t ≤ min (i - 2) j
    · rw [h _ _ _ hr (by omega)]
    · rw [show ((i - t) * (i - t - 1) : ℕ) = 0 from Nat.mul_eq_zero.2 (by omega)]
      simp
  have e2 : (((i - t) * t : ℕ) : K) * f (i - 2) j (t - 1)
      = (((i - t) * t : ℕ) : K) * g (i - 2) j (t - 1) := by
    by_cases hr : t - 1 ≤ min (i - 2) j
    · rw [h _ _ _ hr (by omega)]
    · rw [show ((i - t) * t : ℕ) = 0 from Nat.mul_eq_zero.2 (by omega)]
      simp
  have e3 : (((i - t) * (i + t - 1) : ℕ) : K) * f (i - 1) j t
      = (((i - t) * (i + t - 1) : ℕ) : K) * g (i - 1) j t := by
    by_cases hr : t ≤ min (i - 1) j
    · rw [h _ _ _ hr (by omega)]
    · rw [show ((i - t) * (i + t - 1) : ℕ) = 0 from Nat.mul_eq_zero.2 (by omega)]
      simp
  have e4 : (((j - t) * (j - t - 1) : ℕ) : K) * f i (j - 2) t
      = (((j - t) * (j - t - 1) : ℕ) : K) * g i (j - 2) t := by
    by_cases hr : t ≤ min i (j - 2)
    · rw [h _ _ _ hr (by omega)]
    · rw [show ((j - t) * (j - t - 1) : ℕ) = 0 from Nat.mul_eq_zero.2 (by omega)]
      simp
  have e5 : (((j - t) * t : ℕ) : K) * f i (j - 2) (t - 1)
      = (((j - t) * t : ℕ) : K) * g i (j - 2) (t - 1) := by
    by_cases hr : t - 1 ≤ min i (j - 2)
    · rw [h _ _ _ hr (by omega)]
    · rw [show ((j - t) * t : ℕ) = 0 from Nat.mul_eq_zero.2 (by omega)]
      simp
  have e6 : (((j - t) * (j + t - 1) : ℕ) : K) * f i (j - 1) t
      = (((j - t) * (j + t - 1) : ℕ) : K) * g i (j - 1) t := by
    by_cases hr : t ≤ min i (j - 1)
    · rw [h _ _ _ hr (by omega)]
    · rw [show ((j - t) * (j + t - 1) : ℕ) = 0 from Nat.mul_eq_zero.2 (by omega)]
      simp
  have e7 : f (i - 2) (j - 2) (t - 2) = g (i - 2) (j - 2) (t - 2) := h _ _ _ (by omega) (by omega)
  have e8 : f (i - 2) (j - 1) (t - 2) = g (i - 2) (j - 1) (t - 2) := h _ _ _ (by omega) (by omega)
  have e9 : f (i - 1) (j - 2) (t - 2) = g (i - 1) (j - 2) (t - 2) := h _ _ _ (by omega) (by omega)
  have e10 : f (i - 1) (j - 1) (t - 1) = g (i - 1) (j - 1) (t - 1) := h _ _ _ (by omega) (by omega)
  simp only [src]
  linear_combination κA * e1 + 2 * κA * e2 + γA * e3 + κB * e4 + 2 * κB * e5 + γB * e6
    + ((t * (t - 1) : ℕ) : K) * κA * κB * e7 + ((t * (t - 1) : ℕ) : K) * κA * γB * e8
    + ((t * (t - 1) : ℕ) : K) * γA * κB * e9 + ((t * (t - 1) : ℕ) : K) * γA * γB * e10

def lamA (i t : ℕ) : ℕ := (i - t) * (i + t - 1)

def lamB (j t : ℕ) : ℕ := (j - t) * (j + t - 1)

theorem lamA_ne_zero [CharZero K] {i t : ℕ} (hi : 2 ≤ i) (ht : t ≤ i - 1) :
    ((lamA i t : ℕ) : K) ≠ 0 := by
  refine Nat.cast_ne_zero.2 ?_
  rw [lamA]
  exact Nat.mul_ne_zero (by omega) (by omega)

theorem lamB_ne_zero [CharZero K] {j t : ℕ} (hj : 2 ≤ j) (ht : t ≤ j - 1) :
    ((lamB j t : ℕ) : K) ≠ 0 := by
  refine Nat.cast_ne_zero.2 ?_
  rw [lamB]
  exact Nat.mul_ne_zero (by omega) (by omega)

theorem src_row_collapse (γA κB γB : K) (f : ℕ → ℕ → ℕ → K) {p q i : ℕ} (hq : 2 ≤ q)
    (hoff : ∀ a b s, ¬(p ≤ a ∧ q ≤ b) → f a b s = 0) (t : ℕ) :
    src 0 γA κB γB f i q t = γA * ((lamA i t : ℕ) : K) * f (i - 1) q t := by
  have h1 : ∀ a s, f a (q - 2) s = 0 := fun a s => hoff a (q - 2) s (by omega)
  have h2 : ∀ a s, f a (q - 1) s = 0 := fun a s => hoff a (q - 1) s (by omega)
  simp only [src, h1, h2, lamA]
  ring

theorem src_col_collapse (κA γA γB : K) (f : ℕ → ℕ → ℕ → K) {p q j : ℕ} (hp : 2 ≤ p)
    (hoff : ∀ a b s, ¬(p ≤ a ∧ q ≤ b) → f a b s = 0) (t : ℕ) :
    src κA γA 0 γB f p j t = γB * ((lamB j t : ℕ) : K) * f p (j - 1) t := by
  have h1 : ∀ b s, f (p - 2) b s = 0 := fun b s => hoff (p - 2) b s (by omega)
  have h2 : ∀ b s, f (p - 1) b s = 0 := fun b s => hoff (p - 1) b s (by omega)
  simp only [src, h1, h2, lamB]
  ring

end Rhone.Probability.Propagation
