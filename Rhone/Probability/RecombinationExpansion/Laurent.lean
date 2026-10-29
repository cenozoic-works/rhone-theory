/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.RecombinationExpansion.Transport
public import Mathlib.RingTheory.LaurentSeries

/-! # The transport of `LΔ = 2q₁` from `F((x))` into `F⟦x⟧` -/

@[expose] public section

namespace Rhone.Probability.RecombinationExpansion

open LinearAlgebra.Recursion LinearAlgebra.Recursion.Config Analysis.RecombinationExpansion

section Ring

variable {KA KB : ℕ} {F : Type*} [CommRing F]
variable {θA θB : F} {πA : Fin KA → F} {πB : Fin KB → F}

noncomputable def xL (F : Type*) [CommRing F] : LaurentSeries F := HahnSeries.single (1 : ℤ) 1

noncomputable def rhoL (F : Type*) [CommRing F] : LaurentSeries F :=
  HahnSeries.single (-1 : ℤ) 1

noncomputable def incl (F : Type*) [CommRing F] : PowerSeries F →+* LaurentSeries F :=
  HahnSeries.ofPowerSeries ℤ F

theorem rhoL_mul_xL : rhoL F * xL F = 1 := by
  have h : ((-1 : ℤ) + 1) = 0 := by norm_num
  rw [rhoL, xL, HahnSeries.single_mul_single, one_mul, h, HahnSeries.single_zero_one]

theorem incl_injective : Function.Injective (incl F) :=
  HahnSeries.ofPowerSeries_injective

@[simp] theorem incl_X : incl F PowerSeries.X = xL F := HahnSeries.ofPowerSeries_X

@[simp] theorem incl_C (r : F) : incl F (PowerSeries.C r) = HahnSeries.C r :=
  HahnSeries.ofPowerSeries_C r

theorem rhoL_eq_inv {F : Type*} [Field F] : rhoL F = (xL F)⁻¹ := by
  rw [xL, HahnSeries.inv_single, inv_one, rhoL]

theorem Lop_laurent (G : Config KA KB → PowerSeries F) (ξ : Config KA KB) :
    Lop (HahnSeries.C θA) (HahnSeries.C θB) (rhoL F)
        (fun i => HahnSeries.C (πA i)) (fun j => HahnSeries.C (πB j))
        (fun η => xL F * incl F (G η)) ξ
      = incl F (LTrans θA θB πA πB G ξ) := by
  have e0 : L0 (HahnSeries.C θA) (HahnSeries.C θB) (fun i => HahnSeries.C (πA i))
      (fun j => HahnSeries.C (πB j)) (fun η => xL F * incl F (G η)) ξ
      = xL F * L0 (HahnSeries.C θA) (HahnSeries.C θB) (fun i => HahnSeries.C (πA i))
          (fun j => HahnSeries.C (πB j)) (fun η : Config KA KB => incl F (G η)) ξ := by
    rw [L0, L0, Lop_smul]
  have e1 : L1 (fun η => xL F * incl F (G η)) ξ
      = xL F * L1 (fun η : Config KA KB => incl F (G η)) ξ := L1_smul _ _ ξ
  have key : incl F (LTrans θA θB πA πB G ξ)
      = xL F * L0 (HahnSeries.C θA) (HahnSeries.C θB) (fun i => HahnSeries.C (πA i))
          (fun j => HahnSeries.C (πB j)) (fun η : Config KA KB => incl F (G η)) ξ
        + L1 (fun η : Config KA KB => incl F (G η)) ξ := by
    rw [LTrans, map_add, map_mul, incl_X, map_L0, map_L1]
    simp only [incl_C]
  rw [key, Lop_split, e0, e1, ← mul_assoc, rhoL_mul_xL, one_mul]

theorem laurent_transport_iff (G : Config KA KB → PowerSeries F) (S : PowerSeries F)
    (ξ : Config KA KB) :
    Lop (HahnSeries.C θA) (HahnSeries.C θB) (rhoL F)
        (fun i => HahnSeries.C (πA i)) (fun j => HahnSeries.C (πB j))
        (fun η => xL F * incl F (G η)) ξ = incl F S
      ↔ LTrans θA θB πA πB G ξ = S := by
  rw [Lop_laurent]
  exact ⟨fun h => incl_injective h, fun h => congrArg _ h⟩

theorem families_of_LTrans (G : Config KA KB → PowerSeries F) (src : Config KA KB → F)
    (ξ : Config KA KB) (h : LTrans θA θB πA πB G ξ = PowerSeries.C (src ξ)) :
    L1 (fun η => PowerSeries.coeff 0 (G η)) ξ = src ξ ∧
      ∀ m : ℕ, L1 (fun η => PowerSeries.coeff (m + 1) (G η)) ξ
        = -L0 θA θB πA πB (fun η => PowerSeries.coeff m (G η)) ξ := by
  constructor
  · have h0 := congrArg (PowerSeries.coeff 0) h
    rwa [coeff_zero_LTrans, PowerSeries.coeff_zero_C] at h0
  · intro m
    have hm := congrArg (PowerSeries.coeff (m + 1)) h
    rw [coeff_succ_LTrans, PowerSeries.coeff_C, ite_eq_right (Nat.succ_ne_zero m)] at hm
    linear_combination hm

theorem order_matching_laurent (G : Config KA KB → PowerSeries F) (src : Config KA KB → F)
    (ξ : Config KA KB)
    (h : Lop (HahnSeries.C θA) (HahnSeries.C θB) (rhoL F)
        (fun i => HahnSeries.C (πA i)) (fun j => HahnSeries.C (πB j))
        (fun η => xL F * incl F (G η)) ξ = HahnSeries.C (src ξ)) :
    L1 (fun η => PowerSeries.coeff 0 (G η)) ξ = src ξ ∧
      ∀ m : ℕ, L1 (fun η => PowerSeries.coeff (m + 1) (G η)) ξ
        = -L0 θA θB πA πB (fun η => PowerSeries.coeff m (G η)) ξ := by
  refine families_of_LTrans G src ξ ?_
  rw [← laurent_transport_iff G (PowerSeries.C (src ξ)) ξ, incl_C]
  exact h

end Ring

section Naturality

variable {K KA KB : ℕ} {F F' : Type*} [Field F] [Field F']

theorem map_rising (φ : F →+* F') (x : F) (k : ℕ) : φ (rising x k) = rising (φ x) k := by
  simp only [rising, map_prod, map_add, map_natCast]

theorem map_qOne (φ : F →+* F') (θ : F) (π : Fin K → F) (m : Fin K → ℕ) :
    φ (qOne θ π m) = qOne (φ θ) (fun i => φ (π i)) m := by
  simp only [qOne, map_div₀, map_prod, map_rising, map_mul]

theorem map_qHat (φ : F →+* F') (θA θB : F) (πA : Fin KA → F) (πB : Fin KB → F)
    (ξ : Config KA KB) :
    φ (qHat θA θB πA πB ξ)
      = qHat (φ θA) (φ θB) (fun i => φ (πA i)) (fun j => φ (πB j)) ξ := by
  simp only [qHat, map_mul, map_qOne]

theorem map_twoQ1 (φ : F →+* F') (θA θB : F) (πA : Fin KA → F) (πB : Fin KB → F)
    (ξ : Config KA KB) :
    φ (twoQ1 θA θB πA πB ξ)
      = twoQ1 (φ θA) (φ θB) (fun i => φ (πA i)) (fun j => φ (πB j)) ξ := by
  simp only [twoQ1, map_add, map_sub, map_mul, map_sum, map_natCast, map_qOne]

end Naturality

section Solution

variable {KA KB : ℕ} {F : Type*} [Field F]
variable {θA θB : F} {πA : Fin KA → F} {πB : Fin KB → F}

theorem LDelta_gen {ρ : F} {q : Config KA KB → F} (hq : IsSolution θA θB ρ πA πB q)
    (ξ : Config KA KB) (hn : 2 ≤ ξ.n) (hdenA : rising θA ξ.nA ≠ 0)
    (hdenB : rising θB ξ.nB ≠ 0) :
    Lop θA θB ρ πA πB (fun η => q η - qHat θA θB πA πB η) ξ = twoQ1 θA θB πA πB ξ := by
  rw [Lop_sub, Lop_eq_zero_of_isSolution hq ξ hn, Lop,
    Rhone.Probability.Denominator.source_identity_gen (ρ := ρ) ξ hdenA hdenB]
  ring

theorem order_matching_of_solution (Q : Config KA KB → LaurentSeries F)
    (G : Config KA KB → PowerSeries F)
    (hQ : IsSolution (HahnSeries.C θA) (HahnSeries.C θB) (rhoL F)
      (fun i => HahnSeries.C (πA i)) (fun j => HahnSeries.C (πB j)) Q)
    (hΔ : ∀ η : Config KA KB,
      Q η - HahnSeries.C (qHat θA θB πA πB η) = xL F * incl F (G η))
    (ξ : Config KA KB) (hn : 2 ≤ ξ.n) (hdenA : rising θA ξ.nA ≠ 0)
    (hdenB : rising θB ξ.nB ≠ 0) :
    L1 (fun η => PowerSeries.coeff 0 (G η)) ξ = twoQ1 θA θB πA πB ξ ∧
      ∀ m : ℕ, L1 (fun η => PowerSeries.coeff (m + 1) (G η)) ξ
        = -L0 θA θB πA πB (fun η => PowerSeries.coeff m (G η)) ξ := by
  have hCinj : Function.Injective (HahnSeries.C (Γ := ℤ) (R := F)) := HahnSeries.C_injective
  have hrA : rising (HahnSeries.C θA : LaurentSeries F) ξ.nA ≠ 0 := by
    rw [← map_rising (HahnSeries.C (Γ := ℤ)) θA ξ.nA]
    exact fun h => hdenA ((map_eq_zero_iff _ hCinj).mp h)
  have hrB : rising (HahnSeries.C θB : LaurentSeries F) ξ.nB ≠ 0 := by
    rw [← map_rising (HahnSeries.C (Γ := ℤ)) θB ξ.nB]
    exact fun h => hdenB ((map_eq_zero_iff _ hCinj).mp h)
  have hL := LDelta_gen hQ ξ hn hrA hrB
  have hfun : (fun η : Config KA KB => Q η
        - qHat (HahnSeries.C θA) (HahnSeries.C θB) (fun i => HahnSeries.C (πA i))
            (fun j => HahnSeries.C (πB j)) η)
      = fun η : Config KA KB => xL F * incl F (G η) := by
    funext η
    rw [← map_qHat (HahnSeries.C (Γ := ℤ)) θA θB πA πB η]
    exact hΔ η
  rw [hfun, Lop_laurent, ← map_twoQ1 (HahnSeries.C (Γ := ℤ)) θA θB πA πB ξ, ← incl_C] at hL
  exact families_of_LTrans G (twoQ1 θA θB πA πB) ξ (incl_injective hL)

end Solution

end Rhone.Probability.RecombinationExpansion
