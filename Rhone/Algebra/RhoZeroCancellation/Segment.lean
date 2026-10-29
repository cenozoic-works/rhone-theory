/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.RhoZero.Blocking

/-! # The segment calculus: the four families, their increment sums, and the margin -/

@[expose] public section

namespace Rhone.Algebra.RhoZeroCancellation

open RhoZero

def moveEffect : MoveClass → ℤ × ℤ × ℤ
  | .M1 => (-1, 0, 0)
  | .M2 => (0, -1, 0)
  | .M3 => (-1, -1, -1)
  | .M4 => (0, 0, 1)
  | .M5 => (-1, 0, -1)
  | .M6 => (0, -1, -1)

def nEffect (m : MoveClass) : ℤ :=
  (moveEffect m).1 + (moveEffect m).2.1 - (moveEffect m).2.2

theorem nEffect_levelCrossing :
    nEffect .M1 = -1 ∧ nEffect .M2 = -1 ∧ nEffect .M3 = -1 ∧ nEffect .M4 = -1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl

theorem nEffect_kill : nEffect .M5 = 0 ∧ nEffect .M6 = 0 := ⟨rfl, rfl⟩

theorem families_of_shape {di dj n1 n2 n3 n4 n5 n6 : ℕ}
    (hA : n1 + n3 + n5 = di) (hB : n2 + n3 + n6 = dj) (hn : n1 + n2 + n3 + n4 = 1) :
    (n1 = 0 ∧ n2 = 0 ∧ n3 = 1 ∧ n4 = 0 ∧ n5 + 1 = di ∧ n6 + 1 = dj)
      ∨ (n1 = 1 ∧ n2 = 0 ∧ n3 = 0 ∧ n4 = 0 ∧ n5 + 1 = di ∧ n6 = dj)
      ∨ (n1 = 0 ∧ n2 = 1 ∧ n3 = 0 ∧ n4 = 0 ∧ n5 = di ∧ n6 + 1 = dj)
      ∨ (n1 = 0 ∧ n2 = 0 ∧ n3 = 0 ∧ n4 = 1 ∧ n5 = di ∧ n6 = dj) := by
  have hcase : n3 = 1 ∨ n1 = 1 ∨ n2 = 1 ∨ n4 = 1 := by omega
  rcases hcase with h | h | h | h
  · exact Or.inl ⟨by omega, by omega, h, by omega, by omega, by omega⟩
  · exact Or.inr (Or.inl ⟨h, by omega, by omega, by omega, by omega, by omega⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨by omega, h, by omega, by omega, by omega, by omega⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega, by omega, h, by omega, by omega⟩))

theorem family_card {di dj n1 n2 n3 n4 n5 n6 : ℕ}
    (hA : n1 + n3 + n5 = di) (hB : n2 + n3 + n6 = dj) (hn : n1 + n2 + n3 + n4 = 1) :
    (n3 = 1 ∧ n1 + n2 + n3 + n4 + n5 + n6 + 1 = di + dj)
      ∨ (n1 = 1 ∧ n1 + n2 + n3 + n4 + n5 + n6 = di + dj)
      ∨ (n2 = 1 ∧ n1 + n2 + n3 + n4 + n5 + n6 = di + dj)
      ∨ (n4 = 1 ∧ n1 + n2 + n3 + n4 + n5 + n6 = di + dj + 1) := by
  have hcase : n3 = 1 ∨ n1 = 1 ∨ n2 = 1 ∨ n4 = 1 := by omega
  rcases hcase with h | h | h | h
  · exact Or.inl ⟨h, by omega⟩
  · exact Or.inr (Or.inl ⟨h, by omega⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h, by omega⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨h, by omega⟩))

theorem margin_iff_four_le (di dj : ℕ) :
    (2 < di + dj - 1 ∧ 3 < di + dj ∧ 4 < di + dj + 1) ↔ 4 ≤ di + dj := by
  omega

theorem margin_iff_fullyTyped {di dj : ℕ} (hdi : 1 ≤ di) (hdj : 1 ≤ dj) (hdi' : di ≤ 2)
    (hdj' : dj ≤ 2) : 4 ≤ di + dj ↔ (di = 2 ∧ dj = 2) := by
  omega

variable {F : Type*} [CommRing F]

def deltaSum (θA θB : F) (k : ℕ) (m1 m2 m3 m4 m5 m6 : ℕ) : F :=
  (m1 : F) * delta θA θB k .M1 + (m2 : F) * delta θA θB k .M2 + (m3 : F) * delta θA θB k .M3
    + (m4 : F) * delta θA θB k .M4 + (m5 : F) * delta θA θB k .M5 + (m6 : F) * delta θA θB k .M6

theorem deltaSum_eq (θA θB : F) (k : ℕ) (hu : (k : F) - 1 = -(θA + θB)) (m1 m2 m3 m4 m5 m6 : ℕ) :
    deltaSum θA θB k m1 m2 m3 m4 m5 m6
      = (((m2 : F) + m3 + m6) - 2 * ((m1 : F) + m2 + m3 + m4)) * ((k : F) - 1)
        + (((m2 : F) + m3 + m6) - ((m1 : F) + m3 + m5)) * θA := by
  simp only [deltaSum, delta]
  linear_combination (-((m2 : F) + m3 + m6)) * hu

def IsBlockedFamily (n1 n2 n3 n4 n5 n6 : ℕ) : Prop :=
  (n1 = 0 ∧ n2 = 0 ∧ n3 = 1 ∧ n4 = 0 ∧ n5 = 1 ∧ n6 = 1)
    ∨ (n1 = 1 ∧ n2 = 0 ∧ n3 = 0 ∧ n4 = 0 ∧ n5 = 1 ∧ n6 = 2)
    ∨ (n1 = 0 ∧ n2 = 1 ∧ n3 = 0 ∧ n4 = 0 ∧ n5 = 2 ∧ n6 = 1)
    ∨ (n1 = 0 ∧ n2 = 0 ∧ n3 = 0 ∧ n4 = 1 ∧ n5 = 2 ∧ n6 = 2)

theorem isBlockedFamily_iff {n1 n2 n3 n4 n5 n6 : ℕ} :
    IsBlockedFamily n1 n2 n3 n4 n5 n6
      ↔ (n1 + n3 + n5 = 2 ∧ n2 + n3 + n6 = 2 ∧ n1 + n2 + n3 + n4 = 1) := by
  unfold IsBlockedFamily
  constructor
  · rintro (⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2, h3, h4, h5, h6⟩ |
      ⟨h1, h2, h3, h4, h5, h6⟩) <;> exact ⟨by omega, by omega, by omega⟩
  · rintro ⟨hA, hB, hn⟩
    have hcase : n3 = 1 ∨ n1 = 1 ∨ n2 = 1 ∨ n4 = 1 := by omega
    rcases hcase with h | h | h | h
    · exact Or.inl ⟨by omega, by omega, h, by omega, by omega, by omega⟩
    · exact Or.inr (Or.inl ⟨h, by omega, by omega, by omega, by omega, by omega⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨by omega, h, by omega, by omega, by omega, by omega⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega, by omega, h, by omega, by omega⟩))

theorem isBlockedFamily_card {n1 n2 n3 n4 n5 n6 : ℕ} (h : IsBlockedFamily n1 n2 n3 n4 n5 n6) :
    n1 + n2 + n3 + n4 + n5 + n6 = 3 ∨ n1 + n2 + n3 + n4 + n5 + n6 = 4
      ∨ n1 + n2 + n3 + n4 + n5 + n6 = 5 := by
  unfold IsBlockedFamily at h
  rcases h with ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2, h3, h4, h5, h6⟩ |
    ⟨h1, h2, h3, h4, h5, h6⟩
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl (by omega))
  · exact Or.inr (Or.inl (by omega))
  · exact Or.inr (Or.inr (by omega))

theorem deltaSum_family_eq_zero (θA θB : F) (k : ℕ) (hu : (k : F) - 1 = -(θA + θB))
    {n1 n2 n3 n4 n5 n6 : ℕ} (h : IsBlockedFamily n1 n2 n3 n4 n5 n6) :
    deltaSum θA θB k n1 n2 n3 n4 n5 n6 = 0 := by
  rw [deltaSum_eq θA θB k hu]
  unfold IsBlockedFamily at h
  rcases h with ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2, h3, h4, h5, h6⟩ |
    ⟨h1, h2, h3, h4, h5, h6⟩ <;>
    subst h1 <;> subst h2 <;> subst h3 <;> subst h4 <;> subst h5 <;> subst h6 <;>
    push_cast <;> ring

theorem coeff_ne_zero_of_proper {n1 n2 n3 n4 n5 n6 m1 m2 m3 m4 m5 m6 : ℕ}
    (h : IsBlockedFamily n1 n2 n3 n4 n5 n6)
    (hle : m1 ≤ n1 ∧ m2 ≤ n2 ∧ m3 ≤ n3 ∧ m4 ≤ n4 ∧ m5 ≤ n5 ∧ m6 ≤ n6)
    (hpos : 0 < m1 + m2 + m3 + m4 + m5 + m6)
    (hlt : m1 + m2 + m3 + m4 + m5 + m6 < n1 + n2 + n3 + n4 + n5 + n6) :
    ¬(m2 + m3 + m6 = 2 * (m1 + m2 + m3 + m4) ∧ m2 + m3 + m6 = m1 + m3 + m5) := by
  unfold IsBlockedFamily at h
  rcases h with ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2, h3, h4, h5, h6⟩ | ⟨h1, h2, h3, h4, h5, h6⟩ |
    ⟨h1, h2, h3, h4, h5, h6⟩ <;> omega

theorem deltaSum_proper_ne_zero {F : Type*} [Field F] (θA θB : F) (k : ℕ)
    (hu : (k : F) - 1 = -(θA + θB))
    (hind : ∀ a b : ℤ, ¬(a = 0 ∧ b = 0) → (a : F) * ((k : F) - 1) + (b : F) * θA ≠ 0)
    {n1 n2 n3 n4 n5 n6 m1 m2 m3 m4 m5 m6 : ℕ} (h : IsBlockedFamily n1 n2 n3 n4 n5 n6)
    (h1 : m1 ≤ n1) (h2 : m2 ≤ n2) (h3 : m3 ≤ n3) (h4 : m4 ≤ n4) (h5 : m5 ≤ n5) (h6 : m6 ≤ n6)
    (hpos : 0 < m1 + m2 + m3 + m4 + m5 + m6)
    (hlt : m1 + m2 + m3 + m4 + m5 + m6 < n1 + n2 + n3 + n4 + n5 + n6) :
    deltaSum θA θB k m1 m2 m3 m4 m5 m6 ≠ 0 := by
  rw [deltaSum_eq θA θB k hu]
  have hcoeff := coeff_ne_zero_of_proper h ⟨h1, h2, h3, h4, h5, h6⟩ hpos hlt
  have hne : ¬(((m2 : ℤ) + m3 + m6) - 2 * ((m1 : ℤ) + m2 + m3 + m4) = 0
      ∧ ((m2 : ℤ) + m3 + m6) - ((m1 : ℤ) + m3 + m5) = 0) := by
    intro hh
    exact hcoeff ⟨by omega, by omega⟩
  have key : (((m2 : F) + m3 + m6) - 2 * ((m1 : F) + m2 + m3 + m4)) * ((k : F) - 1)
      + (((m2 : F) + m3 + m6) - ((m1 : F) + m3 + m5)) * θA
      = ((((m2 : ℤ) + m3 + m6) - 2 * ((m1 : ℤ) + m2 + m3 + m4) : ℤ) : F) * ((k : F) - 1)
        + ((((m2 : ℤ) + m3 + m6) - ((m1 : ℤ) + m3 + m5) : ℤ) : F) * θA := by
    push_cast
    ring
  rw [key]
  exact hind _ _ hne

end Rhone.Algebra.RhoZeroCancellation
