/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.Rational.Spec

/-! # `q` as a rational function of `ρ` -/

@[expose] public section

namespace Rhone.Algebra.Rational

open Finset LinearAlgebra.Recursion LinearAlgebra.Recursion.Config

variable {KA KB : ℕ}

variable {θA θB : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ}

theorem det_bMat_polyX_ne_zero (hθA : 0 < θA) (hθB : 0 < θB) (N : ℕ) :
    (bMat (Polynomial.C θA) (Polynomial.C θB) (Polynomial.X : Polynomial ℝ)
      (fun i => Polynomial.C (πA i)) (fun j => Polynomial.C (πB j)) N).det ≠ 0 :=
  det_bMat_ne_zero_of_hom (Polynomial.evalRingHom (1 : ℝ)) (by simpa using hθA)
    (by simpa using hθB) (by simp) N

theorem detNeZero_rho (hθA : 0 < θA) (hθB : 0 < θB) :
    DetNeZero (RatFunc.C θA) (RatFunc.C θB) RatFunc.X
      (fun i => RatFunc.C (πA i)) (fun j => RatFunc.C (πB j)) := by
  intro N
  have hmap : bMat (RatFunc.C θA) (RatFunc.C θB) (RatFunc.X : RatFunc ℝ)
        (fun i => RatFunc.C (πA i)) (fun j => RatFunc.C (πB j)) N
      = (bMat (Polynomial.C θA) (Polynomial.C θB) (Polynomial.X : Polynomial ℝ)
          (fun i => Polynomial.C (πA i)) (fun j => Polynomial.C (πB j)) N).map
          (algebraMap (Polynomial ℝ) (RatFunc ℝ)) := by
    rw [bMat_map]
    simp only [RatFunc.algebraMap_C, RatFunc.algebraMap_X]
  rw [hmap, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  intro h
  exact det_bMat_polyX_ne_zero hθA hθB N
    (IsFractionRing.injective (Polynomial ℝ) (RatFunc ℝ) (by rw [h, map_zero]))

noncomputable def qRho (hθA : 0 < θA) (hθB : 0 < θB) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ) :
    Config KA KB → RatFunc ℝ :=
  qOfDet (detNeZero_rho (πA := πA) (πB := πB) hθA hθB)

theorem qRho_isSolution (hθA : 0 < θA) (hθB : 0 < θB) :
    IsSolution (RatFunc.C θA) (RatFunc.C θB) RatFunc.X
      (fun i => RatFunc.C (πA i)) (fun j => RatFunc.C (πB j)) (qRho hθA hθB πA πB) :=
  qOfDet_isSolution _

theorem qRho_isSolution' (hθA : 0 < θA) (hθB : 0 < θB) :
    IsSolution (algebraMap (Polynomial ℝ) (RatFunc ℝ) (Polynomial.C θA))
      (algebraMap (Polynomial ℝ) (RatFunc ℝ) (Polynomial.C θB))
      (algebraMap (Polynomial ℝ) (RatFunc ℝ) Polynomial.X)
      (fun i => algebraMap (Polynomial ℝ) (RatFunc ℝ) (Polynomial.C (πA i)))
      (fun j => algebraMap (Polynomial ℝ) (RatFunc ℝ) (Polynomial.C (πB j)))
      (qRho hθA hθB πA πB) := by
  simpa only [RatFunc.algebraMap_C, RatFunc.algebraMap_X] using qRho_isSolution hθA hθB

theorem exists_ratio (hθA : 0 < θA) (hθB : 0 < θB) (Lv : ℕ) :
    ∃ (d : Polynomial ℝ) (P : Config KA KB → Polynomial ℝ), d ≠ 0 ∧
      (∀ ξ : Config KA KB, ξ.nA + ξ.nB ≤ Lv →
        algebraMap (Polynomial ℝ) (RatFunc ℝ) (P ξ)
          = qRho hθA hθB πA πB ξ * algebraMap (Polynomial ℝ) (RatFunc ℝ) d) ∧
      ∀ (ρ₀ : ℝ) (hρ₀ : 0 ≤ ρ₀), Polynomial.eval ρ₀ d ≠ 0 →
        ∀ ξ : Config KA KB, ξ.nA + ξ.nB ≤ Lv →
          LinearAlgebra.Recursion.q (πA := πA) (πB := πB) hθA hθB hρ₀ ξ
            = Polynomial.eval ρ₀ (P ξ) / Polynomial.eval ρ₀ d := by
  classical
  obtain ⟨d, P, hd, hPs⟩ := exists_common_denom (R := Polynomial ℝ) (L := RatFunc ℝ)
    (qRho hθA hθB πA πB) (Config.finite_le Lv).toFinset
  have hP : ∀ ξ : Config KA KB, ξ.nA + ξ.nB ≤ Lv →
      algebraMap (Polynomial ℝ) (RatFunc ℝ) (P ξ)
        = qRho hθA hθB πA πB ξ * algebraMap (Polynomial ℝ) (RatFunc ℝ) d := by
    intro ξ hξ
    exact hPs ξ (by simp only [Set.Finite.mem_toFinset]; exact hξ)
  refine ⟨d, P, hd, hP, ?_⟩
  intro ρ₀ hρ₀ hdρ ξ hξ
  have hspec := solvesUpTo_specialize (Polynomial.evalRingHom ρ₀) (qRho_isSolution' hθA hθB)
    (by simpa using hdρ) hP
  simp only [Polynomial.coe_evalRingHom, Polynomial.eval_C, Polynomial.eval_X] at hspec
  have heq := LinearAlgebra.Recursion.SolvesUpTo.eq_of_le hθA hθB hρ₀
    (solvesUpTo_of_isSolution
        (LinearAlgebra.Recursion.q_isSolution (πA := πA) (πB := πB) hθA hθB hρ₀) Lv)
    hspec ξ hξ
  rw [heq, specVal_of_le _ d P _ _ hξ]
  simp

theorem exists_ratio_config (hθA : 0 < θA) (hθB : 0 < θB) (ξ : Config KA KB) :
    ∃ p d : Polynomial ℝ, d ≠ 0 ∧
      algebraMap (Polynomial ℝ) (RatFunc ℝ) p
        = qRho hθA hθB πA πB ξ * algebraMap (Polynomial ℝ) (RatFunc ℝ) d ∧
      ∀ (ρ₀ : ℝ) (hρ₀ : 0 ≤ ρ₀), Polynomial.eval ρ₀ d ≠ 0 →
        LinearAlgebra.Recursion.q (πA := πA) (πB := πB) hθA hθB hρ₀ ξ
          = Polynomial.eval ρ₀ p / Polynomial.eval ρ₀ d := by
  obtain ⟨d, P, hd, hlink, hPs⟩ := exists_ratio (πA := πA) (πB := πB) hθA hθB (ξ.nA + ξ.nB)
  exact ⟨P ξ, d, hd, hlink ξ le_rfl, fun ρ₀ hρ₀ hdρ => hPs ρ₀ hρ₀ hdρ ξ le_rfl⟩

end Rhone.Algebra.Rational
