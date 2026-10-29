/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.Denominator.Basic

/-! # Transfer of reduced denominators across a split `x = cΦ + Ψ` -/

@[expose] public section

namespace Rhone.Algebra.Denominator

variable {F : Type*} [Field F]

theorem clears_of_split {A : Subring F} {x c Φ Ψ Dc d : F}
    (hx : x = c * Φ + Ψ) (hcc : c * c = 1) (hc : c ∈ A)
    (hΨ : Clears A Ψ Dc) (hd : Clears A x d) :
    Clears A Φ (d * Dc) := by
  refine ⟨A.mul_mem hd.1 hΨ.1, ?_⟩
  have key : d * Dc * Φ = c * (Dc * (d * x) - d * (Dc * Ψ)) := by
    rw [hx]
    linear_combination (-(d * Dc * Φ)) * hcc
  rw [key]
  exact A.mul_mem hc (A.sub_mem (A.mul_mem hΨ.1 hd.2) (A.mul_mem hd.1 hΨ.2))

theorem dvdIn_of_split_clears {A : Subring F} {x c Φ Ψ D Dc E : F}
    (hx : x = c * Φ + Ψ) (hcc : c * c = 1) (hc : c ∈ A)
    (hΨ : Clears A Ψ Dc) (hDc : Dc ≠ 0) (hD : D = Dc * E)
    (hH : IsRedDenom A Φ D) {d : F} (hd : Clears A x d) :
    DvdIn A E d := by
  obtain ⟨k, hk, hkey⟩ := hH.min (d * Dc) (clears_of_split hx hcc hc hΨ hd)
  refine ⟨k, hk, ?_⟩
  refine mul_right_cancel₀ hDc ?_
  rw [hkey, hD]
  ring

theorem dvdIn_of_split_isRedDenom {A : Subring F} {x c Φ Ψ D Dc E δ : F}
    (hx : x = c * Φ + Ψ) (hcc : c * c = 1) (hc : c ∈ A)
    (hΨ : Clears A Ψ Dc) (hDc : Dc ≠ 0) (hD : D = Dc * E)
    (hH : IsRedDenom A Φ D) (hδ : IsRedDenom A x δ) :
    DvdIn A E δ :=
  (dvdIn_of_isRedDenom_iff hδ).mp fun _ hd => dvdIn_of_split_clears hx hcc hc hΨ hDc hD hH hd

theorem dvdIn_of_split_clears_converse {A : Subring F} {x c Φ Ψ Dc E : F}
    (hx : x = c * Φ + Ψ) (hc : c ∈ A) (hΨ : Clears A Ψ Dc)
    (hcop : ∀ y : F, DvdIn A E (y * Dc) → DvdIn A E y)
    (hE : ∀ d, Clears A x d → DvdIn A E d)
    {d : F} (hd : Clears A Φ d) :
    DvdIn A E d := by
  refine hcop d (hE (d * Dc) ⟨A.mul_mem hd.1 hΨ.1, ?_⟩)
  have key : d * Dc * x = Dc * (c * (d * Φ)) + d * (Dc * Ψ) := by
    rw [hx]
    ring
  rw [key]
  exact A.add_mem (A.mul_mem hΨ.1 (A.mul_mem hc hd.2)) (A.mul_mem hd.1 hΨ.2)

theorem num_identity {c Φ Ψ D Dc E x : F} (hx : x = c * Φ + Ψ) (hD : D = Dc * E) :
    D * x = c * (D * Φ) + E * (Dc * Ψ) := by
  rw [hx, hD]
  ring

end Rhone.Algebra.Denominator
