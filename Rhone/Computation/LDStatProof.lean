/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.LDStat
public import Rhone.Dynamics.LDMeasures
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.Field.Rat

/-!
# Executable linkage disequilibrium measures equal the specification

Source: lewontin_kojima1960, eq. (2), p. 459; lewontin1964, p. 50; lewontin1964, pp. 54–55;
hill_robertson1968, p. 226; hill1981, p. 210. -/

@[expose] public section
namespace Rhone.Computation.LDStat

def toGametes (g : Hap) : Rhone.Dynamics.Gametes ℝ :=
  ⟨(g.x11 : ℝ), (g.x12 : ℝ), (g.x21 : ℝ), (g.x22 : ℝ)⟩

theorem pA_eq (g : Hap) : ((pA g : Rat) : ℝ) = (toGametes g).pA := by
  simp [pA, toGametes, Rhone.Dynamics.Gametes.pA]

theorem pB_eq (g : Hap) : ((pB g : Rat) : ℝ) = (toGametes g).pB := by
  simp [pB, toGametes, Rhone.Dynamics.Gametes.pB]

theorem total_eq (g : Hap) : ((total g : Rat) : ℝ) = (toGametes g).total := by
  simp [total, toGametes, Rhone.Dynamics.Gametes.total]

theorem ldD_eq (g : Hap) : ((ldD g : Rat) : ℝ) = (toGametes g).D := by
  simp [ldD, toGametes, Rhone.Dynamics.Gametes.D]

theorem dMax_eq (pA pB D : Rat) :
    ((dMax pA pB D : Rat) : ℝ) = Rhone.Dynamics.Gametes.dMax (pA : ℝ) (pB : ℝ) (D : ℝ) := by
  unfold dMax Rhone.Dynamics.Gametes.dMax
  have h : (0 : ℝ) ≤ (D : ℝ) ↔ (0 : Rat) ≤ D := by exact_mod_cast Iff.rfl
  by_cases hD : (0 : Rat) ≤ D
  · have h' : (0 : ℝ) ≤ (D : ℝ) := h.2 hD
    simp only [hD, h', ite_true]
    rw [Rat.cast_min]
    push_cast
    rfl
  · have h' : ¬ (0 : ℝ) ≤ (D : ℝ) := fun hh => hD (h.1 hh)
    simp only [hD, h', ite_false]
    rw [Rat.cast_min]
    push_cast
    rfl

theorem lewontinD'_eq (pA pB D : Rat) :
    ((lewontinD' pA pB D : Rat) : ℝ) =
      Rhone.Dynamics.Gametes.lewontinD' (pA : ℝ) (pB : ℝ) (D : ℝ) := by
  unfold lewontinD' Rhone.Dynamics.Gametes.lewontinD'
  rw [Rat.cast_div, dMax_eq]

theorem rSq_eq (pA pB D : Rat) :
    ((rSq pA pB D : Rat) : ℝ) = Rhone.Dynamics.Gametes.rSq (pA : ℝ) (pB : ℝ) (D : ℝ) := by
  simp [rSq, Rhone.Dynamics.Gametes.rSq, sq]

theorem ldDPrime_eq (g : Hap) :
    ((ldDPrime g : Rat) : ℝ) =
      Rhone.Dynamics.Gametes.lewontinD' (toGametes g).pA (toGametes g).pB (toGametes g).D := by
  rw [ldDPrime, lewontinD'_eq, pA_eq, pB_eq, ldD_eq]

theorem ldRSq_eq (g : Hap) :
    ((ldRSq g : Rat) : ℝ) =
      Rhone.Dynamics.Gametes.rSq (toGametes g).pA (toGametes g).pB (toGametes g).D := by
  rw [ldRSq, rSq_eq, pA_eq, pB_eq, ldD_eq]

theorem ldD_eq_x11_sub (g : Hap) (h : total g = 1) :
    ((ldD g : Rat) : ℝ) = (g.x11 : ℝ) - (pA g : ℝ) * (pB g : ℝ) := by
  have ht : (toGametes g).total = 1 := by rw [← total_eq, h]; simp
  rw [ldD_eq, Rhone.Dynamics.Gametes.D_eq_x11_sub ht, pA_eq, pB_eq]
  rfl

theorem abs_ldDPrime_le_one (g : Hap) (h11 : 0 ≤ g.x11) (h12 : 0 ≤ g.x12) (h21 : 0 ≤ g.x21)
    (h22 : 0 ≤ g.x22) (h : total g = 1) : |((ldDPrime g : Rat) : ℝ)| ≤ 1 := by
  have hd : (toGametes g).IsDist :=
    ⟨by simpa [toGametes] using h11, by simpa [toGametes] using h12,
      by simpa [toGametes] using h21, by simpa [toGametes] using h22,
      by rw [← total_eq, h]; simp⟩
  rw [ldDPrime_eq]
  exact Rhone.Dynamics.Gametes.abs_lewontinD'_le_one hd

end Rhone.Computation.LDStat
