/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.BlockTwoSymbolic.Bridge
public import Rhone.Algebra.BlockTwoSymbolic.BlockU
public import Rhone.Algebra.BlockTwoSymbolic.DataU

/-! # The killed-PIM system over `ℚ(π_A,π_B)(v,ρ)(u)`, with `u` adjoined last -/

@[expose] public section

namespace Rhone.Algebra.BlockTwoSymbolic

open Polynomial

open KilledSystem

noncomputable def WUπ (s : St) : GenericField.P SymbolicFrequencies.Kpi :=
  Wval X (C (GenericField.vv SymbolicFrequencies.Kpi)) (C SymbolicFrequencies.piAF)
      (C SymbolicFrequencies.piBF) (C rhoMπ) s

noncomputable def DcmUπ : GenericField.P SymbolicFrequencies.Kpi := Dcm X
    (C (GenericField.vv SymbolicFrequencies.Kpi)) (C rhoMπ)

theorem huU : algebraMap (GenericField.P SymbolicFrequencies.Kpi)
    (GenericField.L SymbolicFrequencies.Kpi)
    ((X : GenericField.P SymbolicFrequencies.Kpi) + C (GenericField.vv SymbolicFrequencies.Kpi)) =
        2 * thAuπ := algebraMap_tAUπ

theorem hvU : algebraMap (GenericField.P SymbolicFrequencies.Kpi)
    (GenericField.L SymbolicFrequencies.Kpi)
    ((X : GenericField.P SymbolicFrequencies.Kpi) - C (GenericField.vv SymbolicFrequencies.Kpi)) =
        2 * thBuπ := algebraMap_tBUπ

theorem hrU : algebraMap (GenericField.P SymbolicFrequencies.Kpi)
    (GenericField.L SymbolicFrequencies.Kpi) (C rhoMπ) = rhoUπ := algebraMap_rhoPUπ

theorem haU : algebraMap (GenericField.P SymbolicFrequencies.Kpi)
    (GenericField.L SymbolicFrequencies.Kpi) (C SymbolicFrequencies.piAF) = piAL := algebraMap_P_C _

theorem hbU : algebraMap (GenericField.P SymbolicFrequencies.Kpi)
    (GenericField.L SymbolicFrequencies.Kpi) (C SymbolicFrequencies.piBF) = piBL := algebraMap_P_C _

theorem Dcm_eq_gfacU {R : Type*} [CommRing R] (u v r : R) :
    Dcm u v r = (u + v + 2) * ((u - v + 2) * E22uOf u r) := by
  simp only [Dcm, E22uOf]
  ring

theorem E22uOf_eq : E22uOf (X : GenericField.P SymbolicFrequencies.Kpi) (C rhoMπ) = E22uπ := by
  simp only [E22uOf, E22uπ, map_add, map_mul, map_pow, map_ofNat]

theorem DcmUπ_eq : DcmUπ =
    ((X : GenericField.P SymbolicFrequencies.Kpi) + C (GenericField.vv SymbolicFrequencies.Kpi) + 2)
    * (((X : GenericField.P SymbolicFrequencies.Kpi) - C (GenericField.vv SymbolicFrequencies.Kpi) +
        2) * E22uπ) := by
  rw [DcmUπ, Dcm_eq_gfacU, E22uOf_eq]

theorem E22uπ_dvd_DcmUπ : E22uπ ∣ DcmUπ :=
  ⟨((X : GenericField.P SymbolicFrequencies.Kpi) + C (GenericField.vv SymbolicFrequencies.Kpi) +
      2) * ((X : GenericField.P SymbolicFrequencies.Kpi)
    - C (GenericField.vv SymbolicFrequencies.Kpi) + 2), by rw [DcmUπ_eq]; ring⟩

theorem DcmUπ_ne_zero : DcmUπ ≠ 0 := by
  rw [DcmUπ_eq]
  refine mul_ne_zero
      (linU_ne_zero (a := 1) (b := GenericField.vv SymbolicFrequencies.Kpi + 2) one_ne_zero ?_)
    (mul_ne_zero (linU_ne_zero (a := 1) (b := 2 - GenericField.vv SymbolicFrequencies.Kpi)
        one_ne_zero ?_) E22uπ_ne_zero)
  · simp only [map_add, map_ofNat, map_one]; ring
  · simp only [map_sub, map_ofNat, map_one]; ring

noncomputable def qSolUπ (s : St) : GenericField.L SymbolicFrequencies.Kpi :=
  algebraMap (GenericField.P SymbolicFrequencies.Kpi) (GenericField.L SymbolicFrequencies.Kpi)
      (WUπ s)
    * (algebraMap (GenericField.P SymbolicFrequencies.Kpi) (GenericField.L SymbolicFrequencies.Kpi)
        DcmUπ)⁻¹

theorem qSolUπ_isSolutionUπ : IsSolutionG thAuπ thBuπ rhoUπ piAL piBL qSolUπ :=
  isSolutionG_of_poly X (C (GenericField.vv SymbolicFrequencies.Kpi)) (C SymbolicFrequencies.piAF)
      (C SymbolicFrequencies.piBF) (C rhoMπ)
    thAuπ thBuπ rhoUπ piAL piBL huU hvU hrU haU hbU WUπ DcmUπ DcmUπ_ne_zero
    (fun s hs => Wval_rec X (C (GenericField.vv SymbolicFrequencies.Kpi))
        (C SymbolicFrequencies.piAF) (C SymbolicFrequencies.piBF) (C rhoMπ) s hs)
    (fun s hs => Wval_bd X (C (GenericField.vv SymbolicFrequencies.Kpi))
        (C SymbolicFrequencies.piAF) (C SymbolicFrequencies.piBF) (C rhoMπ) s hs)

theorem unique_of_isSolutionUπ {q q2 : St → GenericField.L SymbolicFrequencies.Kpi}
    (h : IsSolutionG thAuπ thBuπ rhoUπ piAL piBL q)
    (h2 : IsSolutionG thAuπ thBuπ rhoUπ piAL piBL q2) : ∀ s ∈ closureList, q s = q2 s :=
  unique_of_isSolutionG neU_lhs02 neU_lhs20 neU_lhs11 neU_d1_12 neU_d1_21 neU_E12 neU_E21
    neU_d2_22 neU_W22 neU_W4_22 neU_D22 h h2

noncomputable def q22πU : GenericField.L SymbolicFrequencies.Kpi :=
  algebraMap (GenericField.P SymbolicFrequencies.Kpi) (GenericField.L SymbolicFrequencies.Kpi)
      (WUπ s22)
    / algebraMap (GenericField.P SymbolicFrequencies.Kpi) (GenericField.L SymbolicFrequencies.Kpi)
        DcmUπ

theorem qSolUπ_s22 : qSolUπ s22 = q22πU := by rw [qSolUπ, q22πU, div_eq_mul_inv]

theorem eq_q22πU_of_isSolutionUπ {q : St → GenericField.L SymbolicFrequencies.Kpi}
    (hq : IsSolutionG thAuπ thBuπ rhoUπ piAL piBL q) : q s22 = q22πU :=
  (unique_of_isSolutionUπ hq qSolUπ_isSolutionUπ s22 s22_mem_closureList).trans qSolUπ_s22

theorem exists_unique_isSolutionUπ :
    IsSolutionG thAuπ thBuπ rhoUπ piAL piBL qSolUπ ∧ ∀ q : St → GenericField.L
        SymbolicFrequencies.Kpi,
      IsSolutionG thAuπ thBuπ rhoUπ piAL piBL q → ∀ s ∈ closureList, q s = qSolUπ s :=
  ⟨qSolUπ_isSolutionUπ, fun _q hq => unique_of_isSolutionUπ hq qSolUπ_isSolutionUπ⟩

theorem WUπ_s22_eq : WUπ s22
    = W46 X (C (GenericField.vv SymbolicFrequencies.Kpi)) (C SymbolicFrequencies.piAF)
        (C SymbolicFrequencies.piBF) (C rhoMπ) := by
  rw [WUπ, s22, Wval_46]

theorem W46_modU {R : Type*} [CommRing R] (u v a b r : R) :
    W46 u v a b r = HqU u v a b r * E22uOf u r + RemU u v a b r := by
  simp only [W46, HqU, RemU, RemU2, RemU1, RemU0, E22uOf]
  ring

theorem RemUπ_eq :
    RemU (X : GenericField.P SymbolicFrequencies.Kpi) (C (GenericField.vv SymbolicFrequencies.Kpi))
        (C SymbolicFrequencies.piAF) (C SymbolicFrequencies.piBF) (C rhoMπ)
      = C (RemU2 (GenericField.vv SymbolicFrequencies.Kpi) SymbolicFrequencies.piAF
          SymbolicFrequencies.piBF rhoMπ) * X ^ 2
        + C (RemU1 (GenericField.vv SymbolicFrequencies.Kpi) SymbolicFrequencies.piAF
            SymbolicFrequencies.piBF rhoMπ) * X
        + C (RemU0 (GenericField.vv SymbolicFrequencies.Kpi) SymbolicFrequencies.piAF
            SymbolicFrequencies.piBF rhoMπ) := by
  rw [RemU, ← RemU2_map
      (Polynomial.C : GenericField.Fuv SymbolicFrequencies.Kpi →+* GenericField.P
      SymbolicFrequencies.Kpi),
    ← RemU1_map (Polynomial.C : GenericField.Fuv SymbolicFrequencies.Kpi →+* GenericField.P
        SymbolicFrequencies.Kpi),
    ← RemU0_map (Polynomial.C : GenericField.Fuv SymbolicFrequencies.Kpi →+* GenericField.P
        SymbolicFrequencies.Kpi)]

theorem RemU2π_ne_zero : RemU2 (GenericField.vv SymbolicFrequencies.Kpi) SymbolicFrequencies.piAF
    SymbolicFrequencies.piBF rhoMπ ≠ 0 := by
  have hb : algebraMap (GenericField.Fv SymbolicFrequencies.Kpi)
      (GenericField.Fuv SymbolicFrequencies.Kpi) (3 : GenericField.Fv SymbolicFrequencies.Kpi)
      = (3 : GenericField.Fuv SymbolicFrequencies.Kpi) := map_ofNat _ 3
  have hc : algebraMap (GenericField.Fv SymbolicFrequencies.Kpi)
      (GenericField.Fuv SymbolicFrequencies.Kpi) (1 - RatFunc.X ^ 2)
      = 1 - GenericField.vv SymbolicFrequencies.Kpi ^ 2 := by rw [map_sub, map_one, map_pow]; rfl
  have h := middle_monic_quadratic_ne_zero (3 : GenericField.Fv SymbolicFrequencies.Kpi)
      (1 - RatFunc.X ^ 2)
  rw [hb, hc] at h
  have hEq : RemU2 (GenericField.vv SymbolicFrequencies.Kpi) SymbolicFrequencies.piAF
      SymbolicFrequencies.piBF rhoMπ
      = 2 * SymbolicFrequencies.piAF * SymbolicFrequencies.piBF * (SymbolicFrequencies.piAF - 1) *
          (SymbolicFrequencies.piBF - 1)
        * (rhoMπ ^ 2 + 3 * rhoMπ + (1 - GenericField.vv SymbolicFrequencies.Kpi ^ 2)) := by
    simp only [RemU2]; ring
  rw [hEq]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
    SymbolicFrequencies.piAF_ne_zero) SymbolicFrequencies.piBF_ne_zero)
        SymbolicFrequencies.piAF_sub_one_ne_zero) SymbolicFrequencies.piBF_sub_one_ne_zero) h

theorem RemUπ_ne_zero :
    RemU (X : GenericField.P SymbolicFrequencies.Kpi) (C (GenericField.vv SymbolicFrequencies.Kpi))
        (C SymbolicFrequencies.piAF) (C SymbolicFrequencies.piBF) (C rhoMπ) ≠ 0 := by
  rw [RemUπ_eq]
  exact quadP_ne_zero RemU2π_ne_zero

theorem RemUπ_natDegree_le :
    (RemU (X : GenericField.P SymbolicFrequencies.Kpi) (C (GenericField.vv SymbolicFrequencies.Kpi))
        (C SymbolicFrequencies.piAF) (C SymbolicFrequencies.piBF) (C rhoMπ)).natDegree
      ≤ 2 := by
  rw [RemUπ_eq]
  exact Polynomial.natDegree_quadratic_le

theorem E22uπ_not_dvd_WUs22 : ¬ E22uπ ∣ WUπ s22 := by
  intro hdvd
  rw [WUπ_s22_eq] at hdvd
  have hR : RemU (X : GenericField.P SymbolicFrequencies.Kpi)
      (C (GenericField.vv SymbolicFrequencies.Kpi)) (C SymbolicFrequencies.piAF)
      (C SymbolicFrequencies.piBF) (C rhoMπ)
      = W46 X (C (GenericField.vv SymbolicFrequencies.Kpi)) (C SymbolicFrequencies.piAF)
          (C SymbolicFrequencies.piBF) (C rhoMπ)
        - HqU X (C (GenericField.vv SymbolicFrequencies.Kpi)) (C SymbolicFrequencies.piAF)
            (C SymbolicFrequencies.piBF) (C rhoMπ) * E22uπ := by
    rw [← E22uOf_eq, W46_modU]; ring
  have h1 : E22uπ ∣ RemU (X : GenericField.P SymbolicFrequencies.Kpi)
      (C (GenericField.vv SymbolicFrequencies.Kpi)) (C SymbolicFrequencies.piAF)
      (C SymbolicFrequencies.piBF)
      (C rhoMπ) := by
    rw [hR]
    exact dvd_sub hdvd (Dvd.intro_left _ rfl)
  have h2 := Polynomial.natDegree_le_of_dvd h1 RemUπ_ne_zero
  rw [E22uπ_natDegree] at h2
  exact absurd (le_trans h2 RemUπ_natDegree_le) (by norm_num)

theorem E22uπ_dvd_q22πU_denom : E22uπ ∣ q22πU.denom :=
  _root_.Rhone.Algebra.prime_dvd_denom DcmUπ_ne_zero rfl E22uπ_prime E22uπ_dvd_DcmUπ
    E22uπ_not_dvd_WUs22

end Rhone.Algebra.BlockTwoSymbolic
