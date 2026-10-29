/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.RecombinationExpansion.Expansion

/-! # The transported operator `x·L₀ + L₁` on `F⟦x⟧`, and order matching as a ring identity -/

@[expose] public section

namespace Rhone.Probability.RecombinationExpansion

open LinearAlgebra.Recursion LinearAlgebra.Recursion.Config Analysis.RecombinationExpansion

section Map

variable {KA KB : ℕ} {F F' : Type*} [CommRing F] [CommRing F']

theorem map_diag (φ : F →+* F') (θA θB ρ : F) (ξ : Config KA KB) :
    φ (diag θA θB ρ ξ) = diag (φ θA) (φ θB) (φ ρ) ξ := by
  simp only [diag, map_add, map_mul, map_natCast]

theorem map_rhs (φ : F →+* F') (θA θB ρ : F) (πA : Fin KA → F) (πB : Fin KB → F)
    (f : Config KA KB → F) (ξ : Config KA KB) :
    φ (rhs θA θB ρ πA πB f ξ)
      = rhs (φ θA) (φ θB) (φ ρ) (fun i => φ (πA i)) (fun j => φ (πB j))
          (fun η => φ (f η)) ξ := by
  simp only [rhs, map_add, map_mul, map_sum, map_natCast]

theorem map_Lop (φ : F →+* F') (θA θB ρ : F) (πA : Fin KA → F) (πB : Fin KB → F)
    (f : Config KA KB → F) (ξ : Config KA KB) :
    φ (Lop θA θB ρ πA πB f ξ)
      = Lop (φ θA) (φ θB) (φ ρ) (fun i => φ (πA i)) (fun j => φ (πB j))
          (fun η => φ (f η)) ξ := by
  rw [Lop, Lop, map_sub, map_mul, map_diag, map_rhs]

theorem map_L0 (φ : F →+* F') (θA θB : F) (πA : Fin KA → F) (πB : Fin KB → F)
    (f : Config KA KB → F) (ξ : Config KA KB) :
    φ (L0 θA θB πA πB f ξ)
      = L0 (φ θA) (φ θB) (fun i => φ (πA i)) (fun j => φ (πB j)) (fun η => φ (f η)) ξ := by
  rw [L0, L0, map_Lop, map_zero]

theorem map_L1 (φ : F →+* F') (f : Config KA KB → F) (ξ : Config KA KB) :
    φ (L1 f ξ) = L1 (fun η => φ (f η)) ξ := by
  simp only [L1, map_sub, map_mul, map_sum, map_natCast]

end Map

section Trans

open PowerSeries

variable {KA KB : ℕ} {F : Type*} [CommRing F]
variable {θA θB : F} {πA : Fin KA → F} {πB : Fin KB → F}

noncomputable def LTrans (θA θB : F) (πA : Fin KA → F) (πB : Fin KB → F)
    (Q : Config KA KB → PowerSeries F) (ξ : Config KA KB) : PowerSeries F :=
  PowerSeries.X * L0 (PowerSeries.C θA) (PowerSeries.C θB) (fun i => PowerSeries.C (πA i))
      (fun j => PowerSeries.C (πB j)) Q ξ
    + L1 Q ξ

theorem coeff_zero_LTrans (Q : Config KA KB → PowerSeries F) (ξ : Config KA KB) :
    PowerSeries.coeff 0 (LTrans θA θB πA πB Q ξ)
      = L1 (fun η => PowerSeries.coeff 0 (Q η)) ξ := by
  rw [LTrans, map_add, PowerSeries.coeff_zero_X_mul, coeff_L1, zero_add]

theorem coeff_succ_LTrans (k : ℕ) (Q : Config KA KB → PowerSeries F) (ξ : Config KA KB) :
    PowerSeries.coeff (k + 1) (LTrans θA θB πA πB Q ξ)
      = L0 θA θB πA πB (fun η => PowerSeries.coeff k (Q η)) ξ
        + L1 (fun η => PowerSeries.coeff (k + 1) (Q η)) ξ := by
  rw [LTrans, map_add, PowerSeries.coeff_succ_X_mul, coeff_L0, coeff_L1]

theorem LTrans_gen (qk : ℕ → Config KA KB → F) (src : Config KA KB → F) (ξ : Config KA KB)
    (h0 : L1 (qk 1) ξ = src ξ)
    (hs : ∀ m : ℕ, L1 (qk (m + 2)) ξ = -L0 θA θB πA πB (qk (m + 1)) ξ) :
    LTrans θA θB πA πB (gen qk) ξ = PowerSeries.C (src ξ) := by
  refine PowerSeries.ext fun k => ?_
  match k with
  | 0 =>
    rw [coeff_zero_LTrans, PowerSeries.coeff_zero_C]
    rw [show (fun η => PowerSeries.coeff 0 (gen qk η)) = qk 1 from
      funext fun η => coeff_gen qk η 0]
    exact h0
  | k + 1 =>
    rw [coeff_succ_LTrans, PowerSeries.coeff_C, ite_eq_right (Nat.succ_ne_zero k)]
    rw [show (fun η => PowerSeries.coeff k (gen qk η)) = qk (k + 1) from
      funext fun η => coeff_gen qk η k]
    rw [show (fun η => PowerSeries.coeff (k + 1) (gen qk η)) = qk (k + 2) from
      funext fun η => coeff_gen qk η (k + 1)]
    rw [hs k, add_neg_cancel]

theorem order_matching_iff (qk : ℕ → Config KA KB → F) (src : Config KA KB → F)
    (ξ : Config KA KB) :
    LTrans θA θB πA πB (gen qk) ξ = PowerSeries.C (src ξ)
      ↔ (L1 (qk 1) ξ = src ξ ∧
          ∀ m : ℕ, L1 (qk (m + 2)) ξ = -L0 θA θB πA πB (qk (m + 1)) ξ) := by
  constructor
  · intro h
    exact order_matching qk src ξ h
  · rintro ⟨h0, hs⟩
    exact LTrans_gen qk src ξ h0 hs

end Trans

end Rhone.Probability.RecombinationExpansion
