/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.RareAlleleHierarchy.Coeff
public import Rhone.Analysis.DenominatorEquation.Basic
public import Rhone.LinearAlgebra.SlotDeletion.Denom

/-! # Universal cleared centred correlations -/

@[expose] public section

namespace Rhone.Probability.SamplingUniform

open Matrix LinearAlgebra.SlotDeletion SlotDeletion RareAlleleHierarchy

variable {R : Type*} [CommRing R]

def edgeFactor (a : R) (n : ℕ) : R := if 2 ≤ n then a + (n - 1 : ℕ) else 1

theorem poch_edgeFactor (a : R) (n : ℕ) :
    poch a n = poch a (n - 1) * edgeFactor a n := by
  by_cases hn : 2 ≤ n
  · simpa [edgeFactor, hn] using poch_succ_top a hn
  · have hn' : n = 0 ∨ n = 1 := by omega
    rcases hn' with rfl | rfl <;> simp [edgeFactor]

def edgeNumerator (a κ γ : R) : ℕ → R
  | 0 => 1
  | 1 => 0
  | n + 2 => (n + 1 : ℕ) *
      (κ * edgeFactor a (n + 1) * edgeNumerator a κ γ n +
        γ * edgeNumerator a κ γ (n + 1))

noncomputable def cutRatio (a b ρ : R) (i j x y : ℕ) : R :=
  if h : x ≤ i ∧ y ≤ j ∧ (x < i ∨ y < j) ∧ 2 ≤ i then
    Classical.choose (Dfull_dvd_Dcut a b ρ h.1 h.2.1 h.2.2.1 h.2.2.2)
  else 0

theorem Dfull_mul_cutRatio (a b ρ : R) {i j x y : ℕ}
    (hx : x ≤ i) (hy : y ≤ j) (hlt : x < i ∨ y < j) (hi : 2 ≤ i) :
    Dfull a b ρ x y * cutRatio a b ρ i j x y = Dcut a b ρ i j := by
  rw [cutRatio, dite_eq_left ⟨hx, hy, hlt, hi⟩]
  exact (Classical.choose_spec (Dfull_dvd_Dcut a b ρ hx hy hlt hi)).symm

theorem recursionSource_congr_lower (κA γA κB γB : R) {f g : ℕ → ℕ → ℕ → R}
    {i j : ℕ} (hi : 2 ≤ i) (hj : 2 ≤ j)
    (h : ∀ x y u, x ≤ i → y ≤ j → x + y < i + j → f x y u = g x y u)
    (t : ℕ) : recursionSource κA γA κB γB f i j t = recursionSource κA γA κB γB g i j t := by
  unfold recursionSource
  rw [h (i - 2) j t (by omega) (by omega) (by omega),
    h (i - 2) j (t - 1) (by omega) (by omega) (by omega),
    h (i - 1) j t (by omega) (by omega) (by omega),
    h i (j - 2) t (by omega) (by omega) (by omega),
    h i (j - 2) (t - 1) (by omega) (by omega) (by omega),
    h i (j - 1) t (by omega) (by omega) (by omega),
    h (i - 2) (j - 2) (t - 2) (by omega) (by omega) (by omega),
    h (i - 2) (j - 1) (t - 2) (by omega) (by omega) (by omega),
    h (i - 1) (j - 2) (t - 2) (by omega) (by omega) (by omega),
    h (i - 1) (j - 1) (t - 1) (by omega) (by omega) (by omega)]

theorem recursionSource_mul (κA γA κB γB c : R) (f : ℕ → ℕ → ℕ → R) (i j t : ℕ) :
    recursionSource κA γA κB γB (fun x y u => c * f x y u) i j t =
      c * recursionSource κA γA κB γB f i j t := by
  unfold recursionSource
  ring

theorem recursionSource_map {S : Type*} [CommRing S] (φ : R →+* S)
    (κA γA κB γB : R) (f : ℕ → ℕ → ℕ → R) (i j t : ℕ) :
    φ (recursionSource κA γA κB γB f i j t) =
      recursionSource (φ κA) (φ γA) (φ κB) (φ γB) (fun x y u => φ (f x y u)) i j t := by
  simp [recursionSource, map_ofNat]

def blockLevel (i j t : ℕ) : Fin (min i j + 1) :=
  ⟨min t (min i j), by omega⟩

noncomputable def clearedPhi (a b ρ κA γA κB γB : R) (i j t : ℕ) : R :=
  if j = 0 then edgeNumerator a κA γA i
  else if i = 0 then edgeNumerator b κB γB j
  else if i = 1 ∨ j = 1 then 0
  else
    ((Analysis.DenominatorEquation.U R i j a b ρ) *ᵥ
      (fun s : Fin (min i j + 1) =>
        recursionSource κA γA κB γB
          (fun x y u => if _h : x + y < i + j then
            cutRatio a b ρ i j x y * clearedPhi a b ρ κA γA κB γB x y u else 0)
          i j s)) (blockLevel i j t)
termination_by i + j

theorem clearedPhi_A (a b ρ κA γA κB γB : R) (i t : ℕ) :
    clearedPhi a b ρ κA γA κB γB i 0 t = edgeNumerator a κA γA i := by
  rw [clearedPhi]
  simp

theorem clearedPhi_B (a b ρ κA γA κB γB : R) (j t : ℕ) :
    clearedPhi a b ρ κA γA κB γB 0 j t = edgeNumerator b κB γB j := by
  rw [clearedPhi]
  by_cases hj : j = 0
  · subst j
    simp [edgeNumerator]
  · simp [hj]

theorem clearedPhi_one_left (a b ρ κA γA κB γB : R) (j t : ℕ) :
    clearedPhi a b ρ κA γA κB γB 1 j t = 0 := by
  rw [clearedPhi]
  by_cases hj : j = 0 <;> simp [hj, edgeNumerator]

theorem clearedPhi_one_right (a b ρ κA γA κB γB : R) (i t : ℕ) :
    clearedPhi a b ρ κA γA κB γB i 1 t = 0 := by
  rw [clearedPhi]
  by_cases hi : i = 0 <;> simp [hi, edgeNumerator]

theorem clearedPhi_interior (a b ρ κA γA κB γB : R) {i j : ℕ}
    (hi : 2 ≤ i) (hj : 2 ≤ j) (t : ℕ) :
    clearedPhi a b ρ κA γA κB γB i j t =
      ((Analysis.DenominatorEquation.U R i j a b ρ) *ᵥ
        (fun s : Fin (min i j + 1) =>
          recursionSource κA γA κB γB
            (fun x y u => cutRatio a b ρ i j x y *
              clearedPhi a b ρ κA γA κB γB x y u) i j s)) (blockLevel i j t) := by
  rw [clearedPhi]
  simp only [show j ≠ 0 by omega, show i ≠ 0 by omega,
    show ¬(i = 1 ∨ j = 1) by omega, ↓reduceIte]
  congr 2
  funext s
  apply recursionSource_congr_lower κA γA κB γB hi hj
  intro x y u _ _ hxy
  simp only [dite_eq_left hxy]

end Rhone.Probability.SamplingUniform
