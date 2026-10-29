/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith

/-!
# Additive and dominance decomposition of genotypic value at one locus

Source: fisher1918, pp. 403–404, eq. V–VII; falconer_mackay1996, ch. 7. -/

@[expose] public section

namespace Rhone.Statistics

variable {F : Type*} [Field F] [CharZero F]

def hwExp (p : F) (f : Fin 3 → F) : F :=
  (1 - p) ^ 2 * f 0 + 2 * p * (1 - p) * f 1 + p ^ 2 * f 2

def count : Fin 3 → F := ![0, 1, 2]

def addParam (G : Fin 3 → F) : F := (G 2 - G 0) / 2

def domParam (G : Fin 3 → F) : F := G 1 - (G 2 + G 0) / 2

def genoMean (p : F) (G : Fin 3 → F) : F := hwExp p G

def avgEffect (p : F) (G : Fin 3 → F) : F :=
  addParam G + domParam G * ((1 - p) - p)

def breedingValue (p : F) (G : Fin 3 → F) (k : Fin 3) : F := (count k - 2 * p) * avgEffect p G

def domDev (p : F) (G : Fin 3 → F) (k : Fin 3) : F :=
  G k - genoMean p G - breedingValue p G k

def hwCov (p : F) (f g : Fin 3 → F) : F :=
  hwExp p (fun k => f k * g k) - hwExp p f * hwExp p g

def varG (p : F) (G : Fin 3 → F) : F := hwExp p (fun k => (G k - genoMean p G) ^ 2)

def varA (p : F) (G : Fin 3 → F) : F := hwExp p (fun k => breedingValue p G k ^ 2)

def varD (p : F) (G : Fin 3 → F) : F := hwExp p (fun k => domDev p G k ^ 2)

theorem domDev_eq (p : F) (G : Fin 3 → F) :
    domDev p G 0 = -(2 * p ^ 2 * domParam G) ∧ domDev p G 1 = 2 * p * (1 - p) * domParam G
      ∧ domDev p G 2 = -(2 * (1 - p) ^ 2 * domParam G) := by
  simp only [domDev, genoMean, hwExp, breedingValue, avgEffect, addParam, domParam, count]
  refine ⟨?_, ?_, ?_⟩ <;> simp <;> ring

omit [CharZero F] in
theorem hwExp_breedingValue (p : F) (G : Fin 3 → F) : hwExp p (breedingValue p G) = 0 := by
  simp only [hwExp, breedingValue, count]; simp; ring

theorem hwExp_domDev (p : F) (G : Fin 3 → F) : hwExp p (domDev p G) = 0 := by
  simp only [hwExp, domDev, genoMean, breedingValue, avgEffect, addParam, domParam, count]
  simp; ring

theorem hwExp_domDev_mul_count (p : F) (G : Fin 3 → F) :
    hwExp p (fun k => domDev p G k * count k) = 0 := by
  simp only [hwExp, domDev, genoMean, breedingValue, avgEffect, addParam, domParam, count]
  simp; ring

theorem hwExp_breedingValue_mul_domDev (p : F) (G : Fin 3 → F) :
    hwExp p (fun k => breedingValue p G k * domDev p G k) = 0 := by
  simp only [hwExp, domDev, genoMean, breedingValue, avgEffect, addParam, domParam, count]
  simp; ring

theorem hwCov_count_eq (p : F) (G : Fin 3 → F) :
    hwCov p G count = 2 * p * (1 - p) * avgEffect p G := by
  simp only [hwCov, hwExp, avgEffect, addParam, domParam, count]
  simp; ring

omit [CharZero F] in
theorem hwCov_count_count (p : F) : hwCov p count count = 2 * p * (1 - p) := by
  simp only [hwCov, hwExp, count]
  simp; ring

omit [CharZero F] in
theorem varA_eq (p : F) (G : Fin 3 → F) : varA p G = 2 * p * (1 - p) * avgEffect p G ^ 2 := by
  simp only [varA, hwExp, breedingValue, count]
  simp; ring

theorem varD_eq (p : F) (G : Fin 3 → F) : varD p G = (2 * p * (1 - p) * domParam G) ^ 2 := by
  simp only [varD, hwExp, domDev, genoMean, breedingValue, avgEffect, addParam, domParam, count]
  simp; ring

theorem varG_eq (p : F) (G : Fin 3 → F) : varG p G = varA p G + varD p G := by
  simp only [varG, varA, varD, hwExp, domDev, genoMean, breedingValue, avgEffect, addParam,
    domParam, count]
  simp; ring

section Order

variable [LinearOrder F] [IsStrictOrderedRing F]

theorem domDev_least_squares {p : F} (h0 : 0 ≤ p) (h1 : p ≤ 1) (G : Fin 3 → F) (c₀ c₁ : F) :
    varD p G ≤ hwExp p (fun k => (G k - c₀ - c₁ * count k) ^ 2) := by
  have hq : 0 ≤ 1 - p := sub_nonneg.mpr h1
  have key : hwExp p (fun k => (G k - c₀ - c₁ * count k) ^ 2) - varD p G
      = (1 - p) ^ 2 * ((genoMean p G - 2 * p * avgEffect p G - c₀) + (avgEffect p G - c₁) * 0) ^ 2
        + 2 * p * (1 - p) *
          ((genoMean p G - 2 * p * avgEffect p G - c₀) + (avgEffect p G - c₁) * 1) ^ 2
        + p ^ 2 *
          ((genoMean p G - 2 * p * avgEffect p G - c₀) + (avgEffect p G - c₁) * 2) ^ 2 := by
    simp only [varD, hwExp, domDev, genoMean, breedingValue, avgEffect, addParam, domParam, count]
    simp; ring
  have : 0 ≤ hwExp p (fun k => (G k - c₀ - c₁ * count k) ^ 2) - varD p G := by
    rw [key]; positivity
  linarith

end Order

end Rhone.Statistics
