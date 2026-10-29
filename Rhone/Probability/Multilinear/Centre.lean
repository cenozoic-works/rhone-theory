/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.Multilinear.MultilinearRecursion

/-! # §3 — Centring, and why `K = 2` is one-dimensional -/

@[expose] public section

namespace Rhone

open Finset LinearAlgebra.Recursion Probability.Denominator

variable {F : Type*} [Field F]

section Centre

variable {K : ℕ} (π x : Fin K → F)

def Probability.Multilinear.centre : Fin K → F := x - Probability.Multilinear.mean π x • 1

@[simp] theorem Probability.Multilinear.mean_one : Probability.Multilinear.mean π (1 : Fin K → F) =
    ∑ i, π i := by simp [Probability.Multilinear.mean]

theorem Probability.Multilinear.mean_centre (hπ : ∑ i, π i = 1) : Probability.Multilinear.mean π
    (Probability.Multilinear.centre π x) = 0 := by
  have h : Probability.Multilinear.mean π (Probability.Multilinear.centre π x) =
      Probability.Multilinear.mean π x - Probability.Multilinear.mean π x *
      Probability.Multilinear.mean π (1 : Fin K → F) := by
    simp only [Probability.Multilinear.centre, Probability.Multilinear.mean, Pi.sub_apply,
        Pi.smul_apply, smul_eq_mul, Pi.one_apply,
      mul_sub, mul_one]
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
    ring_nf
  rw [h, Probability.Multilinear.mean_one, hπ, mul_one, sub_self]

theorem Probability.Multilinear.centre_add_mean : Probability.Multilinear.centre π x +
    Probability.Multilinear.mean π x • (1 : Fin K → F) = x := by
  simp [Probability.Multilinear.centre]

end Centre

section Expansion

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : ℕ}

theorem LinearAlgebra.Multilinear.IsMulti.centred_expansion {G : (ι → Fin K → F) → F}
    (hG : LinearAlgebra.Multilinear.IsMulti G)
    (π : Fin K → F) (s : ι → Fin K → F) :
    G s = ∑ S : Finset ι, (∏ u ∈ Sᶜ, Probability.Multilinear.mean π (s u))
        * G (fun u => if u ∈ S then Probability.Multilinear.centre π (s u) else 1) := by
  have h0 : ∀ t : ι → Fin K → F, hG.toML t = G t := fun _ => rfl
  have hdec : s = (fun u => Probability.Multilinear.centre π (s u)) + fun u =>
      Probability.Multilinear.mean π (s u) • (1 : Fin K → F) := by
    funext u
    exact (Probability.Multilinear.centre_add_mean π (s u)).symm
  calc G s
      = hG.toML ((fun u => Probability.Multilinear.centre π (s u)) + fun u =>
          Probability.Multilinear.mean π (s u) • (1 : Fin K → F)) := by
        rw [← hdec]; rfl
    _ = ∑ S : Finset ι, hG.toML (S.piecewise (fun u => Probability.Multilinear.centre π (s u))
          fun u => Probability.Multilinear.mean π (s u) • (1 : Fin K → F)) :=
              MultilinearMap.map_add_univ _ _ _
    _ = ∑ S : Finset ι, (∏ u ∈ Sᶜ, Probability.Multilinear.mean π (s u))
          * G (fun u => if u ∈ S then Probability.Multilinear.centre π (s u) else 1) := by
        refine Finset.sum_congr rfl fun S _ => ?_
        have hpw : S.piecewise (fun u => Probability.Multilinear.centre π (s u))
              (fun u => Probability.Multilinear.mean π (s u) • (1 : Fin K → F))
            = Sᶜ.piecewise
                (fun u => Probability.Multilinear.mean π (s u) •
                    (fun u => if u ∈ S then Probability.Multilinear.centre π (s u) else 1) u)
                fun u => if u ∈ S then Probability.Multilinear.centre π (s u) else 1 := by
          funext u
          by_cases h : u ∈ S <;> simp [Finset.piecewise, h]
        rw [hpw, MultilinearMap.map_piecewise_smul, h0, smul_eq_mul]

end Expansion

section Biallelic

variable (π : Fin 2 → F)

def Probability.Multilinear.fvec : Fin 2 → F := Pi.single 0 1 - (π 0) • 1

@[simp] theorem Probability.Multilinear.fvec_zero : Probability.Multilinear.fvec π 0 = 1 - π 0 :=
    by simp [Probability.Multilinear.fvec]

@[simp] theorem Probability.Multilinear.fvec_one : Probability.Multilinear.fvec π 1 = -(π 0) :=
    by simp [Probability.Multilinear.fvec]

def Probability.Multilinear.kap : F := π 0 * π 1

def Probability.Multilinear.gam : F := π 1 - π 0

theorem Probability.Multilinear.single_zero_eq : (Pi.single 0 1 : Fin 2 → F) = π 0 • 1 +
    Probability.Multilinear.fvec π := by
  funext i
  fin_cases i
  · change (Pi.single 0 1 : Fin 2 → F) 0 = π 0 * 1 + Probability.Multilinear.fvec π 0
    rw [Pi.single_eq_same, Probability.Multilinear.fvec_zero]; ring
  · change (Pi.single 0 1 : Fin 2 → F) 1 = π 0 * 1 + Probability.Multilinear.fvec π 1
    rw [Pi.single_eq_of_ne (by decide), Probability.Multilinear.fvec_one]; ring

variable {π} (hπ : π 0 + π 1 = 1)
include hπ

theorem Probability.Multilinear.fvec_zero' : Probability.Multilinear.fvec π 0 = π 1 := by
  rw [Probability.Multilinear.fvec_zero]; linear_combination (-1 : F) * hπ

theorem Probability.Multilinear.mean_fvec : Probability.Multilinear.mean π
    (Probability.Multilinear.fvec π) = 0 := by
  simp only [Probability.Multilinear.mean, Fin.sum_univ_two, Probability.Multilinear.fvec_zero,
      Probability.Multilinear.fvec_one]
  linear_combination (-(π 0)) * hπ

theorem Probability.Multilinear.fvec_mul_fvec : Probability.Multilinear.fvec π *
    Probability.Multilinear.fvec π = Probability.Multilinear.kap π • (1 : Fin 2 → F) +
    Probability.Multilinear.gam π • Probability.Multilinear.fvec π := by
  funext i
  fin_cases i
  · change Probability.Multilinear.fvec π 0 * Probability.Multilinear.fvec π 0 =
      Probability.Multilinear.kap π * 1 + Probability.Multilinear.gam π *
      Probability.Multilinear.fvec π 0
    rw [Probability.Multilinear.fvec_zero, Probability.Multilinear.kap,
        Probability.Multilinear.gam]; linear_combination (-1 : F) * hπ
  · change Probability.Multilinear.fvec π 1 * Probability.Multilinear.fvec π 1 =
      Probability.Multilinear.kap π * 1 + Probability.Multilinear.gam π *
      Probability.Multilinear.fvec π 1
    rw [Probability.Multilinear.fvec_one, Probability.Multilinear.kap, Probability.Multilinear.gam];
        ring

theorem Probability.Multilinear.single_one_eq : (Pi.single 1 1 : Fin 2 → F) = π 1 • 1 -
    Probability.Multilinear.fvec π := by
  funext i
  fin_cases i
  · change (Pi.single 1 1 : Fin 2 → F) 0 = π 1 * 1 - Probability.Multilinear.fvec π 0
    rw [Pi.single_eq_of_ne
        (by decide), Probability.Multilinear.fvec_zero]; linear_combination (-1 : F) * hπ
  · change (Pi.single 1 1 : Fin 2 → F) 1 = π 1 * 1 - Probability.Multilinear.fvec π 1
    rw [Pi.single_eq_same, Probability.Multilinear.fvec_one]; linear_combination (-1 : F) * hπ

end Biallelic

end Rhone
