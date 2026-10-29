/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.BlockTwoSymbolic.Bridge
public import Rhone.Algebra.SymbolicFrequencies.Q22

/-! # The killed-PIM system over `ℚ(π_A, π_B)(u,v)(ρ)`: solution and uniqueness -/
set_option linter.style.longLine false

@[expose] public section

namespace Rhone.Algebra.BlockTwoSymbolic

open Polynomial

open KilledSystem

local notation "uPi" => (Polynomial.C (GenericField.uu SymbolicFrequencies.Kpi) : GenericField.P SymbolicFrequencies.Kpi)
local notation "vPi" => (Polynomial.C (GenericField.vv SymbolicFrequencies.Kpi) : GenericField.P SymbolicFrequencies.Kpi)
local notation "aPi"
    => (Polynomial.C SymbolicFrequencies.piAF : GenericField.P SymbolicFrequencies.Kpi)
local notation "bPi"
    => (Polynomial.C SymbolicFrequencies.piBF : GenericField.P SymbolicFrequencies.Kpi)

@[simp] theorem algebraMap_uPi :
    algebraMap (GenericField.P SymbolicFrequencies.Kpi) (GenericField.L SymbolicFrequencies.Kpi)
        uPi = GenericField.thA SymbolicFrequencies.Kpi + GenericField.thB SymbolicFrequencies.Kpi :=
        by
  rw [algebraMap_P_C, uu_eq, map_add, algebraMap_thAF, algebraMap_thBF]

@[simp] theorem algebraMap_vPi :
    algebraMap (GenericField.P SymbolicFrequencies.Kpi) (GenericField.L SymbolicFrequencies.Kpi)
        vPi = GenericField.thA SymbolicFrequencies.Kpi - GenericField.thB SymbolicFrequencies.Kpi :=
        by
  rw [algebraMap_P_C, vv_eq, map_sub, algebraMap_thAF, algebraMap_thBF]

@[simp] theorem algebraMap_aPi :
    algebraMap (GenericField.P SymbolicFrequencies.Kpi) (GenericField.L SymbolicFrequencies.Kpi)
        aPi = piAL := algebraMap_P_C _

@[simp] theorem algebraMap_bPi :
    algebraMap (GenericField.P SymbolicFrequencies.Kpi) (GenericField.L SymbolicFrequencies.Kpi)
        bPi = piBL := algebraMap_P_C _

def IsSolutionπ (q : St → GenericField.L SymbolicFrequencies.Kpi) : Prop :=
  (∀ s ∈ recStates, lhsC (GenericField.thA SymbolicFrequencies.Kpi)
      (GenericField.thB SymbolicFrequencies.Kpi) (GenericField.rhoL SymbolicFrequencies.Kpi) s * q s
      = rhsC 1 (GenericField.thA SymbolicFrequencies.Kpi * piAL)
          (GenericField.thA SymbolicFrequencies.Kpi * (1 - piAL))
        (GenericField.thB SymbolicFrequencies.Kpi * piBL)
            (GenericField.thB SymbolicFrequencies.Kpi * (1 - piBL))
            (GenericField.rhoL SymbolicFrequencies.Kpi) q s) ∧
  (∀ s ∈ bdryStates, q s = bdryC piAL (1 - piAL) piBL (1 - piBL) s)

theorem lhsW_map (s : St) :
    algebraMap (GenericField.P SymbolicFrequencies.Kpi) (GenericField.L SymbolicFrequencies.Kpi)
        (lhsW uPi vPi X s)
      = 2 * lhsC (GenericField.thA SymbolicFrequencies.Kpi)
          (GenericField.thB SymbolicFrequencies.Kpi) (GenericField.rhoL SymbolicFrequencies.Kpi)
          s := by
  rw [← lhsW_eq]
  simp only [lhsW, map_add, map_sub, map_mul, map_ofNat, map_natCast, algebraMap_uPi,
    algebraMap_vPi, algebraMap_X_L]

theorem rhsW_map (N : St → GenericField.P SymbolicFrequencies.Kpi) (s : St) :
    algebraMap (GenericField.P SymbolicFrequencies.Kpi) (GenericField.L SymbolicFrequencies.Kpi)
        (rhsW uPi vPi aPi bPi X N s)
      = 2 * rhsC 1 (GenericField.thA SymbolicFrequencies.Kpi * piAL)
          (GenericField.thA SymbolicFrequencies.Kpi * (1 - piAL))
          (GenericField.thB SymbolicFrequencies.Kpi * piBL)
              (GenericField.thB SymbolicFrequencies.Kpi * (1 - piBL))
              (GenericField.rhoL SymbolicFrequencies.Kpi)
          (fun z => algebraMap (GenericField.P SymbolicFrequencies.Kpi)
              (GenericField.L SymbolicFrequencies.Kpi) (N z)) s := by
  have e0 : algebraMap (GenericField.P SymbolicFrequencies.Kpi)
      (GenericField.L SymbolicFrequencies.Kpi) 2 = 2 * 1 := by
    rw [map_ofNat, mul_one]
  have e1 : algebraMap (GenericField.P SymbolicFrequencies.Kpi)
      (GenericField.L SymbolicFrequencies.Kpi) ((uPi + vPi) * aPi)
      = 2 * (GenericField.thA SymbolicFrequencies.Kpi * piAL) := by
    simp only [map_mul, map_add, algebraMap_uPi, algebraMap_vPi, algebraMap_aPi]; ring
  have e2 : algebraMap (GenericField.P SymbolicFrequencies.Kpi)
      (GenericField.L SymbolicFrequencies.Kpi) ((uPi + vPi) * (1 - aPi))
      = 2 * (GenericField.thA SymbolicFrequencies.Kpi * (1 - piAL)) := by
    simp only [map_mul, map_add, map_sub, map_one, algebraMap_uPi, algebraMap_vPi,
      algebraMap_aPi]
    ring
  have e3 : algebraMap (GenericField.P SymbolicFrequencies.Kpi)
      (GenericField.L SymbolicFrequencies.Kpi) ((uPi - vPi) * bPi)
      = 2 * (GenericField.thB SymbolicFrequencies.Kpi * piBL) := by
    simp only [map_mul, map_sub, algebraMap_uPi, algebraMap_vPi, algebraMap_bPi]; ring
  have e4 : algebraMap (GenericField.P SymbolicFrequencies.Kpi)
      (GenericField.L SymbolicFrequencies.Kpi) ((uPi - vPi) * (1 - bPi))
      = 2 * (GenericField.thB SymbolicFrequencies.Kpi * (1 - piBL)) := by
    simp only [map_mul, map_sub, map_one, algebraMap_uPi, algebraMap_vPi, algebraMap_bPi]
    ring
  have e5 : algebraMap (GenericField.P SymbolicFrequencies.Kpi)
      (GenericField.L SymbolicFrequencies.Kpi) (2 * X) = 2 * GenericField.rhoL
      SymbolicFrequencies.Kpi := by
    rw [map_mul, map_ofNat, algebraMap_X_L]
  rw [rhsW, rhsC_map, e0, e1, e2, e3, e4, e5, rhsC_scale]

theorem isSolutionπ_of_poly (N : St → GenericField.P SymbolicFrequencies.Kpi)
    (Dc : GenericField.P SymbolicFrequencies.Kpi) (hD : Dc ≠ 0)
    (hrec : ∀ s ∈ recStates, lhsW uPi vPi X s * N s = rhsW uPi vPi aPi bPi X N s)
    (hbd : ∀ s ∈ bdryStates, N s = bdryC aPi (1 - aPi) bPi (1 - bPi) s * Dc) :
    IsSolutionπ (fun s => algebraMap (GenericField.P SymbolicFrequencies.Kpi)
        (GenericField.L SymbolicFrequencies.Kpi) (N s)
      * (algebraMap (GenericField.P SymbolicFrequencies.Kpi)
          (GenericField.L SymbolicFrequencies.Kpi) Dc)⁻¹) := by
  have hDL : algebraMap (GenericField.P SymbolicFrequencies.Kpi)
      (GenericField.L SymbolicFrequencies.Kpi) Dc ≠ 0 := polyL_ne_zero hD
  constructor
  · intro s hs
    have h := congrArg
        (algebraMap (GenericField.P SymbolicFrequencies.Kpi)
        (GenericField.L SymbolicFrequencies.Kpi)) (hrec s hs)
    rw [map_mul, lhsW_map, rhsW_map] at h
    change lhsC (GenericField.thA SymbolicFrequencies.Kpi)
        (GenericField.thB SymbolicFrequencies.Kpi) (GenericField.rhoL SymbolicFrequencies.Kpi) s
      * (algebraMap (GenericField.P SymbolicFrequencies.Kpi)
          (GenericField.L SymbolicFrequencies.Kpi) (N s)
        * (algebraMap (GenericField.P SymbolicFrequencies.Kpi)
            (GenericField.L SymbolicFrequencies.Kpi) Dc)⁻¹) = _
    rw [rhsC_mul_const]
    linear_combination
        ((algebraMap (GenericField.P SymbolicFrequencies.Kpi)
        (GenericField.L SymbolicFrequencies.Kpi) Dc)⁻¹ / 2) * h
  · intro s hs
    have h := congrArg
        (algebraMap (GenericField.P SymbolicFrequencies.Kpi)
        (GenericField.L SymbolicFrequencies.Kpi)) (hbd s hs)
    rw [map_mul, bdryC_map] at h
    simp only [map_sub, map_one, algebraMap_aPi, algebraMap_bPi] at h
    change algebraMap (GenericField.P SymbolicFrequencies.Kpi)
        (GenericField.L SymbolicFrequencies.Kpi) (N s)
      * (algebraMap (GenericField.P SymbolicFrequencies.Kpi)
          (GenericField.L SymbolicFrequencies.Kpi) Dc)⁻¹ = _
    rw [h]
    exact mul_inv_cancel_right₀ hDL _

noncomputable def Wπ (s : St) : GenericField.P SymbolicFrequencies.Kpi := Wval uPi vPi aPi bPi X s

noncomputable def Dcmπ : GenericField.P SymbolicFrequencies.Kpi := Dcm uPi vPi X

theorem Dcm_eq_qD {R : Type*} [CommRing R] (u v a b r : R) :
    Dcm u v r = SymbolicFrequencies.qD2 u v a b * r ^ 2 + SymbolicFrequencies.qD1 u v a b * r +
        SymbolicFrequencies.qD0 u v a b := by
  simp only [Dcm, SymbolicFrequencies.qD2, SymbolicFrequencies.qD1, SymbolicFrequencies.qD0]
  ring

theorem Dcmπ_eq : Dcmπ = SymbolicFrequencies.Dqπ := by
  have h2 := SymbolicFrequencies.qD2_map
      (Polynomial.C : GenericField.Fuv SymbolicFrequencies.Kpi →+* GenericField.P
      SymbolicFrequencies.Kpi)
    (GenericField.uu SymbolicFrequencies.Kpi) (GenericField.vv SymbolicFrequencies.Kpi)
        SymbolicFrequencies.piAF SymbolicFrequencies.piBF
  have h1 := SymbolicFrequencies.qD1_map
      (Polynomial.C : GenericField.Fuv SymbolicFrequencies.Kpi →+* GenericField.P
      SymbolicFrequencies.Kpi)
    (GenericField.uu SymbolicFrequencies.Kpi) (GenericField.vv SymbolicFrequencies.Kpi)
        SymbolicFrequencies.piAF SymbolicFrequencies.piBF
  have h0 := SymbolicFrequencies.qD0_map
      (Polynomial.C : GenericField.Fuv SymbolicFrequencies.Kpi →+* GenericField.P
      SymbolicFrequencies.Kpi)
    (GenericField.uu SymbolicFrequencies.Kpi) (GenericField.vv SymbolicFrequencies.Kpi)
        SymbolicFrequencies.piAF SymbolicFrequencies.piBF
  rw [Dcmπ, Dcm_eq_qD uPi vPi aPi bPi X, SymbolicFrequencies.Dqπ, SymbolicFrequencies.DqOf, h2, h1,
      h0]

theorem Dcmπ_ne_zero : Dcmπ ≠ 0 := by rw [Dcmπ_eq]; exact SymbolicFrequencies.Dqπ_ne_zero

noncomputable def qSolπ (s : St) : GenericField.L SymbolicFrequencies.Kpi :=
  algebraMap (GenericField.P SymbolicFrequencies.Kpi) (GenericField.L SymbolicFrequencies.Kpi)
      (Wπ s)
    * (algebraMap (GenericField.P SymbolicFrequencies.Kpi) (GenericField.L SymbolicFrequencies.Kpi)
        Dcmπ)⁻¹

theorem qSolπ_isSolutionπ : IsSolutionπ qSolπ :=
  isSolutionπ_of_poly Wπ Dcmπ Dcmπ_ne_zero
    (fun s hs => Wval_rec uPi vPi aPi bPi X s hs)
    (fun s hs => Wval_bd uPi vPi aPi bPi X s hs)

theorem unique_auxπ (Δ : St → GenericField.L SymbolicFrequencies.Kpi)
    (hrec : ∀ s ∈ recStates,
      lhsC (GenericField.thA SymbolicFrequencies.Kpi) (GenericField.thB SymbolicFrequencies.Kpi)
          (GenericField.rhoL SymbolicFrequencies.Kpi) s * Δ s
        = rhsC 1 (GenericField.thA SymbolicFrequencies.Kpi * piAL)
            (GenericField.thA SymbolicFrequencies.Kpi * (1 - piAL))
          (GenericField.thB SymbolicFrequencies.Kpi * piBL)
              (GenericField.thB SymbolicFrequencies.Kpi * (1 - piBL))
              (GenericField.rhoL SymbolicFrequencies.Kpi) Δ s)
    (hbd : ∀ s ∈ bdryStates, Δ s = 0) :
    ∀ s ∈ closureList, Δ s = 0 :=
  unique_auxF (GenericField.thA SymbolicFrequencies.Kpi) (GenericField.thB SymbolicFrequencies.Kpi)
      (GenericField.rhoL SymbolicFrequencies.Kpi) piAL (1 - piAL) piBL
    (1 - piBL) Δ ne_lhs02 ne_lhs20 ne_lhs11 ne_d1_12 ne_d1_21 ne_E12 ne_E21 ne_d2_22 ne_W22
    ne_W4_22 ne_D22 hrec hbd

theorem unique_of_isSolutionπ {q q2 : St → GenericField.L SymbolicFrequencies.Kpi}
    (h : IsSolutionπ q)
    (h2 : IsSolutionπ q2) : ∀ s ∈ closureList, q s = q2 s := by
  intro s hs
  have key := unique_auxπ (fun z => q z - q2 z) ?_ ?_ s hs
  · exact sub_eq_zero.mp key
  · intro t ht
    have e := congrArg₂ (· - ·) (h.1 t ht) (h2.1 t ht)
    rw [rhsC_sub] at e
    change lhsC (GenericField.thA SymbolicFrequencies.Kpi)
        (GenericField.thB SymbolicFrequencies.Kpi) (GenericField.rhoL SymbolicFrequencies.Kpi) t *
        (q t - q2 t) = _
    rw [mul_sub]
    exact e
  · intro t ht
    rw [h.2 t ht, h2.2 t ht, sub_self]

theorem W46_eq_Nq {R : Type*} [CommRing R] (u v a b r : R) :
    W46 u v a b r
      = (a - 1) * (b - 1)
        * (SymbolicFrequencies.qM2 u v a b * r ^ 2 + SymbolicFrequencies.qM1 u v a b * r +
            SymbolicFrequencies.qM0 u v a b) := by
  simp only [W46, SymbolicFrequencies.qM2, SymbolicFrequencies.qM1, SymbolicFrequencies.qM0]
  ring

theorem Wπ_s22 : Wπ s22 = SymbolicFrequencies.Nqπ := by
  have h2 := SymbolicFrequencies.qM2_map
      (Polynomial.C : GenericField.Fuv SymbolicFrequencies.Kpi →+* GenericField.P
      SymbolicFrequencies.Kpi)
    (GenericField.uu SymbolicFrequencies.Kpi) (GenericField.vv SymbolicFrequencies.Kpi)
        SymbolicFrequencies.piAF SymbolicFrequencies.piBF
  have h1 := SymbolicFrequencies.qM1_map
      (Polynomial.C : GenericField.Fuv SymbolicFrequencies.Kpi →+* GenericField.P
      SymbolicFrequencies.Kpi)
    (GenericField.uu SymbolicFrequencies.Kpi) (GenericField.vv SymbolicFrequencies.Kpi)
        SymbolicFrequencies.piAF SymbolicFrequencies.piBF
  have h0 := SymbolicFrequencies.qM0_map
      (Polynomial.C : GenericField.Fuv SymbolicFrequencies.Kpi →+* GenericField.P
      SymbolicFrequencies.Kpi)
    (GenericField.uu SymbolicFrequencies.Kpi) (GenericField.vv SymbolicFrequencies.Kpi)
        SymbolicFrequencies.piAF SymbolicFrequencies.piBF
  have hc : (Polynomial.C ((SymbolicFrequencies.piAF - 1) * (SymbolicFrequencies.piBF - 1)) :
      GenericField.P SymbolicFrequencies.Kpi)
      = (aPi - 1) * (bPi - 1) := by
    rw [map_mul, map_sub, map_sub, map_one]
  rw [Wπ, s22, Wval_46, W46_eq_Nq, SymbolicFrequencies.Nqπ, SymbolicFrequencies.NqOf,
      SymbolicFrequencies.MqOf, h2, h1, h0, hc]

theorem qSolπ_s22 : qSolπ s22 = SymbolicFrequencies.q22π := by
  rw [qSolπ, Wπ_s22, Dcmπ_eq, SymbolicFrequencies.q22π, SymbolicFrequencies.q22Of, div_eq_mul_inv]
  rfl

theorem eq_q22π_of_isSolutionπ {q : St → GenericField.L SymbolicFrequencies.Kpi}
    (hq : IsSolutionπ q) :
    q s22 = SymbolicFrequencies.q22π :=
  (unique_of_isSolutionπ hq qSolπ_isSolutionπ s22 s22_mem_closureList).trans qSolπ_s22

theorem exists_unique_isSolutionπ :
    IsSolutionπ qSolπ ∧ ∀ q : St → GenericField.L SymbolicFrequencies.Kpi, IsSolutionπ q →
      ∀ s ∈ closureList, q s = qSolπ s :=
  ⟨qSolπ_isSolutionπ, fun _q hq => unique_of_isSolutionπ hq qSolπ_isSolutionπ⟩

end Rhone.Algebra.BlockTwoSymbolic
