/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.Rational.Spec

/-! # `q` at the generic parameter point: a rational function of `θ_A, θ_B, ρ, π` -/

@[expose] public section

namespace Rhone.Algebra.Rational

open Finset LinearAlgebra.Recursion LinearAlgebra.Recursion.Config

variable {KA KB : ℕ}

abbrev Par (KA KB : ℕ) := Fin 3 ⊕ Fin KA ⊕ Fin KB

abbrev PRing (KA KB : ℕ) := MvPolynomial (Par KA KB) ℚ

abbrev PField (KA KB : ℕ) := FractionRing (PRing KA KB)

noncomputable def thA : PRing KA KB := MvPolynomial.X (Sum.inl 0)

noncomputable def thB : PRing KA KB := MvPolynomial.X (Sum.inl 1)

noncomputable def rhoP : PRing KA KB := MvPolynomial.X (Sum.inl 2)

noncomputable def piA (i : Fin KA) : PRing KA KB := MvPolynomial.X (Sum.inr (Sum.inl i))

noncomputable def piB (j : Fin KB) : PRing KA KB := MvPolynomial.X (Sum.inr (Sum.inr j))

noncomputable def evalOne : PRing KA KB →+* ℝ :=
  ((MvPolynomial.aeval fun _ => (1 : ℝ)) : PRing KA KB →ₐ[ℚ] ℝ).toRingHom

@[simp] theorem evalOne_thA : evalOne (thA : PRing KA KB) = 1 := by
  simp [evalOne, thA]

@[simp] theorem evalOne_thB : evalOne (thB : PRing KA KB) = 1 := by
  simp [evalOne, thB]

@[simp] theorem evalOne_rhoP : evalOne (rhoP : PRing KA KB) = 1 := by
  simp [evalOne, rhoP]

theorem det_bMat_gen_ne_zero (N : ℕ) :
    (bMat (thA : PRing KA KB) thB rhoP piA piB N).det ≠ 0 :=
  det_bMat_ne_zero_of_hom evalOne (by simp) (by simp) (by simp) N

theorem detNeZero_gen :
    DetNeZero (algebraMap (PRing KA KB) (PField KA KB) thA)
      (algebraMap (PRing KA KB) (PField KA KB) thB)
      (algebraMap (PRing KA KB) (PField KA KB) rhoP)
      (fun i => algebraMap (PRing KA KB) (PField KA KB) (piA i))
      (fun j => algebraMap (PRing KA KB) (PField KA KB) (piB j)) := by
  intro N
  rw [← bMat_map (algebraMap (PRing KA KB) (PField KA KB)), ← RingHom.mapMatrix_apply,
    ← RingHom.map_det]
  intro h
  exact det_bMat_gen_ne_zero N
    (IsFractionRing.injective (PRing KA KB) (PField KA KB) (by rw [h, map_zero]))

noncomputable def qRat : Config KA KB → PField KA KB := qOfDet detNeZero_gen

theorem qRat_isSolution :
    IsSolution (algebraMap (PRing KA KB) (PField KA KB) thA)
      (algebraMap (PRing KA KB) (PField KA KB) thB)
      (algebraMap (PRing KA KB) (PField KA KB) rhoP)
      (fun i => algebraMap (PRing KA KB) (PField KA KB) (piA i))
      (fun j => algebraMap (PRing KA KB) (PField KA KB) (piB j))
      (qRat : Config KA KB → PField KA KB) :=
  qOfDet_isSolution _

theorem qRat_unique {q' : Config KA KB → PField KA KB}
    (hq : IsSolution (algebraMap (PRing KA KB) (PField KA KB) thA)
      (algebraMap (PRing KA KB) (PField KA KB) thB)
      (algebraMap (PRing KA KB) (PField KA KB) rhoP)
      (fun i => algebraMap (PRing KA KB) (PField KA KB) (piA i))
      (fun j => algebraMap (PRing KA KB) (PField KA KB) (piB j)) q') : q' = qRat :=
  qOfDet_unique _ hq

theorem exists_specialization (Lv : ℕ) :
    ∃ (D : PRing KA KB) (P : Config KA KB → PRing KA KB), D ≠ 0 ∧
      (∀ ξ : Config KA KB, ξ.nA + ξ.nB ≤ Lv →
        algebraMap (PRing KA KB) (PField KA KB) (P ξ)
          = qRat ξ * algebraMap (PRing KA KB) (PField KA KB) D) ∧
      ∀ (φ : PRing KA KB →+* ℝ) (hA : 0 < φ thA) (hB : 0 < φ thB) (hρ : 0 ≤ φ rhoP),
        φ D ≠ 0 → ∀ ξ : Config KA KB, ξ.nA + ξ.nB ≤ Lv →
          LinearAlgebra.Recursion.q (πA := fun i => φ (piA i)) (πB := fun j => φ (piB j)) hA hB hρ ξ
            = φ (P ξ) / φ D := by
  classical
  obtain ⟨D, P, hD, hPs⟩ := exists_common_denom (R := PRing KA KB) (L := PField KA KB)
    qRat (Config.finite_le Lv).toFinset
  have hP : ∀ ξ : Config KA KB, ξ.nA + ξ.nB ≤ Lv →
      algebraMap (PRing KA KB) (PField KA KB) (P ξ)
        = qRat ξ * algebraMap (PRing KA KB) (PField KA KB) D := by
    intro ξ hξ
    exact hPs ξ (by simp only [Set.Finite.mem_toFinset]; exact hξ)
  refine ⟨D, P, hD, hP, ?_⟩
  intro φ hA hB hρ hDφ ξ hξ
  have hspec := solvesUpTo_specialize φ qRat_isSolution hDφ hP
  have heq := LinearAlgebra.Recursion.SolvesUpTo.eq_of_le hA hB hρ
    (solvesUpTo_of_isSolution (LinearAlgebra.Recursion.q_isSolution hA hB hρ) Lv) hspec ξ hξ
  rw [heq, specVal_of_le _ D P _ _ hξ]

end Rhone.Algebra.Rational
