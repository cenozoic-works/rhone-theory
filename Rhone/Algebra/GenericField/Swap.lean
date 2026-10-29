/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.GenericField.E22
public import Rhone.Algebra.Q22
public import Rhone.Algebra.NoDegreeTwoFormula

/-! # The variable swap between the two encodings -/

@[expose] public section

namespace Rhone.Algebra.GenericField

open Polynomial

abbrev FV := _root_.Rhone.Algebra.Fv
abbrev FUV := _root_.Rhone.Algebra.Fuv
abbrev PP := _root_.Rhone.Algebra.P
abbrev LL := _root_.Rhone.Algebra.L

noncomputable abbrev ι : PP →+* LL := algebraMap PP LL

noncomputable def vL : LL := algebraMap FUV LL _root_.Rhone.Algebra.vv
noncomputable def uL : LL := algebraMap FUV LL _root_.Rhone.Algebra.uu
noncomputable def rL : LL := RatFunc.X

noncomputable def swapNum : Polynomial FV →+* LL :=
  ι.comp (Polynomial.mapRingHom (algebraMap FV FUV))

theorem swapNum_injective : Function.Injective swapNum := by
  rw [swapNum, RingHom.coe_comp]
  exact (IsFractionRing.injective PP LL).comp
    (Polynomial.map_injective _ (algebraMap FV FUV).injective)

set_option maxSynthPendingDepth 3 in
theorem swapNum_nonZeroDivisors :
    nonZeroDivisors (Polynomial FV) ≤ (nonZeroDivisors LL).comap swapNum := by
  intro x hx
  rw [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
  intro h
  exact (mem_nonZeroDivisors_iff_ne_zero.mp hx) (swapNum_injective (by rw [h, map_zero]))

noncomputable def swapC : FUV →+* LL := RatFunc.liftRingHom swapNum swapNum_nonZeroDivisors

@[simp] theorem swapC_uu : swapC _root_.Rhone.Algebra.uu = rL := by
  rw [_root_.Rhone.Algebra.uu, swapC, RatFunc.liftRingHom_X, swapNum]
  simp [rL]

@[simp] theorem swapC_vv : swapC _root_.Rhone.Algebra.vv = vL := by
  have h : _root_.Rhone.Algebra.vv = RatFunc.C (RatFunc.X : FV) := rfl
  rw [h, swapC, RatFunc.liftRingHom_C, swapNum]
  simp [vL, _root_.Rhone.Algebra.vv]

noncomputable def swapP : PP →+* LL := Polynomial.eval₂RingHom swapC uL

@[simp] theorem swapP_C (c : FUV) : swapP (C c) = swapC c := by
  simp [swapP]

@[simp] theorem swapP_X : swapP X = uL := by simp [swapP]

theorem map_uu : ι (C _root_.Rhone.Algebra.uu) = uL := by
  rw [uL]; exact RatFunc.algebraMap_C _

theorem map_vv : ι (C _root_.Rhone.Algebra.vv) = vL := by
  rw [vL]; exact RatFunc.algebraMap_C _

theorem map_X : ι X = rL := by
  rw [rL]; exact RatFunc.algebraMap_X

theorem swapP_E22u : swapP _root_.Rhone.Algebra.E22u = ι _root_.Rhone.Algebra.E22 := by
  simp only [_root_.Rhone.Algebra.E22u, _root_.Rhone.Algebra.E22, _root_.Rhone.Algebra.E22a,
    _root_.Rhone.Algebra.E22b, _root_.Rhone.Algebra.E22c, _root_.Rhone.Algebra.rhoM,
    map_add, map_mul, map_pow, map_ofNat, map_one, swapP_C, swapP_X, swapC_uu,
    map_uu, map_X]
  ring

theorem swapP_NqU : swapP _root_.Rhone.Algebra.NqU = ι _root_.Rhone.Algebra.Nq := by
  simp only [_root_.Rhone.Algebra.NqU, _root_.Rhone.Algebra.Nq, _root_.Rhone.Algebra.nuU0,
    _root_.Rhone.Algebra.nuU1, _root_.Rhone.Algebra.nuU2, _root_.Rhone.Algebra.nuU3,
        _root_.Rhone.Algebra.nuU4,
    _root_.Rhone.Algebra.nuU5, _root_.Rhone.Algebra.qN0, _root_.Rhone.Algebra.qN1,
        _root_.Rhone.Algebra.qN2,
    _root_.Rhone.Algebra.rhoM, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat,
    swapP_C, swapP_X, swapC_uu, swapC_vv, map_uu, map_vv, map_X]
  ring

theorem swapP_DqU : swapP _root_.Rhone.Algebra.DqU = ι _root_.Rhone.Algebra.Dq := by
  simp only [_root_.Rhone.Algebra.DqU, _root_.Rhone.Algebra.Dq, _root_.Rhone.Algebra.duU0,
    _root_.Rhone.Algebra.duU1, _root_.Rhone.Algebra.duU2, _root_.Rhone.Algebra.duU3,
        _root_.Rhone.Algebra.duU4,
    _root_.Rhone.Algebra.duU5, _root_.Rhone.Algebra.qD0, _root_.Rhone.Algebra.qD1,
        _root_.Rhone.Algebra.qD2,
    _root_.Rhone.Algebra.rhoM, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat,
    swapP_C, swapP_X, swapC_uu, swapC_vv, map_uu, map_vv, map_X]
  ring

theorem q22_eq_swap :
    _root_.Rhone.Algebra.q22 = swapP _root_.Rhone.Algebra.NqU / swapP _root_.Rhone.Algebra.DqU := by
  rw [swapP_NqU, swapP_DqU]
  rfl

theorem q22_num_den_swap :
    _root_.Rhone.Algebra.q22 * swapP _root_.Rhone.Algebra.DqU = swapP _root_.Rhone.Algebra.NqU := by
  have hD : ι _root_.Rhone.Algebra.Dq ≠ 0 :=
    _root_.Rhone.Algebra.algebraMap_ne_zero _root_.Rhone.Algebra.Dq_ne_zero
  rw [swapP_NqU, swapP_DqU, _root_.Rhone.Algebra.q22]
  field_simp

abbrev Bi := Polynomial (Polynomial FV)

noncomputable def emb : Bi →+* PP :=
  Polynomial.mapRingHom (algebraMap (Polynomial FV) FUV)

theorem emb_injective : Function.Injective emb :=
  Polynomial.map_injective _ (IsFractionRing.injective (Polynomial FV) FUV)

noncomputable def swapBiC : Polynomial FV →+* Bi :=
  Polynomial.eval₂RingHom (Polynomial.C.comp Polynomial.C) Polynomial.X

noncomputable def swapBi : Bi →+* Bi :=
  Polynomial.eval₂RingHom swapBiC (Polynomial.C Polynomial.X)

theorem swapBi_comp_swapBi : swapBi.comp swapBi = RingHom.id Bi := by
  ext <;> simp [swapBi, swapBiC]

theorem swapBi_involutive : Function.Involutive swapBi := fun x => by
  have h := RingHom.congr_fun swapBi_comp_swapBi x
  simpa using h

theorem swapBi_injective : Function.Injective swapBi := swapBi_involutive.injective

theorem swapP_comp_emb : swapP.comp emb = ι.comp (emb.comp swapBi) := by
  ext a
  · change swapP (emb (Polynomial.C (Polynomial.C a))) = _
    simp [emb, swapBi, swapBiC, swapC, RatFunc.liftRingHom_C, swapNum]
  · change swapP (emb (Polynomial.C Polynomial.X)) = _
    simp [emb, swapBi, swapBiC, swapC, RatFunc.liftRingHom_X, swapNum]
  · change swapP (emb Polynomial.X) = _
    simp [emb, swapBi, swapBiC, uL, _root_.Rhone.Algebra.uu]

theorem swapP_emb_injective : Function.Injective (swapP.comp emb) := by
  rw [swapP_comp_emb, RingHom.coe_comp, RingHom.coe_comp]
  exact ((IsFractionRing.injective PP LL).comp emb_injective).comp swapBi_injective

set_option maxSynthPendingDepth 3 in
theorem swapP_injective : Function.Injective swapP := by
  rw [injective_iff_map_eq_zero]
  intro q hq
  obtain ⟨b, hbM, hb⟩ :=
    IsLocalization.integerNormalization_spec (nonZeroDivisors (Polynomial FV)) q
  set Q := IsLocalization.integerNormalization (nonZeroDivisors (Polynomial FV)) q with hQ
  have hsm : (b : Polynomial FV) • q = C (algebraMap (Polynomial FV) FUV b) * q := by
    rw [← algebraMap_smul FUV b q, Polynomial.smul_eq_C_mul]
  have h1 : emb Q = C (algebraMap (Polynomial FV) FUV b) * q := by
    rw [emb]; rw [Polynomial.coe_mapRingHom, hb, hsm]
  have h2 : swapP (emb Q) = 0 := by rw [h1, map_mul, hq, mul_zero]
  have h3 : Q = 0 := by
    have := swapP_emb_injective (a₁ := Q) (a₂ := 0) (by simpa using h2)
    exact this
  exact (IsLocalization.integerNormalization_eq_zero_iff le_rfl q).mp (hQ ▸ h3)

noncomputable def swapL : LL →+* LL := IsFractionRing.lift swapP_injective

theorem swapL_injective : Function.Injective swapL := swapL.injective

theorem swapL_algebraMap (p : PP) : swapL (ι p) = swapP p :=
  IsFractionRing.lift_algebraMap swapP_injective p

theorem swapL_q22u : swapL _root_.Rhone.Algebra.q22u = _root_.Rhone.Algebra.q22 := by
  rw [_root_.Rhone.Algebra.q22u, map_div₀, swapL_algebraMap, swapL_algebraMap,
    swapP_NqU, swapP_DqU]
  rfl

theorem swapL_E22u : swapL (ι _root_.Rhone.Algebra.E22u) = ι _root_.Rhone.Algebra.E22 := by
  rw [swapL_algebraMap, swapP_E22u]

end Rhone.Algebra.GenericField
