/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.SymbolicFrequencies.Q22Data
public import Rhone.Algebra.SymbolicFrequencies.Tower

/-! # `E_{2,2}` is a factor of `den(q22)` with symbolic mutant frequencies -/

@[expose] public section

namespace Rhone.Algebra.SymbolicFrequencies

open Polynomial

section Naturality

variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (u v a b : R)

theorem qM2_map : f (qM2 u v a b) = qM2 (f u) (f v) (f a) (f b) := by
  simp only [qM2, map_add, map_sub, map_mul, map_pow, map_ofNat]

theorem qM1_map : f (qM1 u v a b) = qM1 (f u) (f v) (f a) (f b) := by
  simp only [qM1, map_add, map_sub, map_mul, map_pow, map_ofNat]

theorem qM0_map : f (qM0 u v a b) = qM0 (f u) (f v) (f a) (f b) := by
  simp only [qM0, map_add, map_sub, map_mul, map_pow, map_ofNat]

theorem qD2_map : f (qD2 u v a b) = qD2 (f u) (f v) (f a) (f b) := by
  simp only [qD2, map_add, map_sub, map_mul, map_pow, map_ofNat]

theorem qD1_map : f (qD1 u v a b) = qD1 (f u) (f v) (f a) (f b) := by
  simp only [qD1, map_add, map_sub, map_mul, map_pow, map_ofNat]

theorem qD0_map : f (qD0 u v a b) = qD0 (f u) (f v) (f a) (f b) := by
  simp only [qD0, map_add, map_sub, map_mul, map_pow, map_ofNat]

theorem MqOf_map : (MqOf u v a b).map f = MqOf (f u) (f v) (f a) (f b) := by
  simp only [MqOf, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_C, Polynomial.map_X]
  rw [qM2_map, qM1_map, qM0_map]

theorem NqOf_map : (NqOf u v a b).map f = NqOf (f u) (f v) (f a) (f b) := by
  simp only [NqOf, Polynomial.map_mul, Polynomial.map_C, MqOf_map]
  congr 2
  rw [map_mul, map_sub, map_sub, map_one]

theorem DqOf_map : (DqOf u v a b).map f = DqOf (f u) (f v) (f a) (f b) := by
  simp only [DqOf, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_C, Polynomial.map_X]
  rw [qD2_map, qD1_map, qD0_map]

end Naturality

noncomputable def Mqπ : GenericField.P Kpi := MqOf (GenericField.uu Kpi) (GenericField.vv Kpi) piAF
    piBF

noncomputable def Nqπ : GenericField.P Kpi := NqOf (GenericField.uu Kpi) (GenericField.vv Kpi) piAF
    piBF

noncomputable def Dqπ : GenericField.P Kpi := DqOf (GenericField.uu Kpi) (GenericField.vv Kpi) piAF
    piBF

noncomputable def Sqπ : GenericField.P Kpi := SqOf (GenericField.uu Kpi) (GenericField.vv Kpi) piAF
    piBF

noncomputable def nfacπ : GenericField.Fuv Kpi := (piAF - 1) * (piBF - 1)

noncomputable def gfacπ : GenericField.Fuv Kpi :=
  (GenericField.uu Kpi - GenericField.vv Kpi + 2) * (GenericField.uu Kpi + GenericField.vv Kpi + 2)

noncomputable def q22Of {F : Type*} [Field F] (u v a b : F) : RatFunc F :=
  algebraMap (Polynomial F) (RatFunc F) (NqOf u v a b)
    / algebraMap (Polynomial F) (RatFunc F) (DqOf u v a b)

noncomputable def q22π : GenericField.L Kpi := q22Of (GenericField.uu Kpi) (GenericField.vv Kpi)
    piAF piBF

theorem Nqπ_eq : Nqπ = C nfacπ * Mqπ := rfl

theorem Dqπ_eq : Dqπ = C gfacπ * GenericField.E22 Kpi := by
  simp only [Dqπ, DqOf, qD2, qD1, qD0, gfacπ, GenericField.E22, GenericField.E22a,
      GenericField.E22b, GenericField.E22c,
    map_add, map_sub, map_mul, map_pow, map_ofNat, map_one]
  ring

theorem gfacπ_ne_zero : gfacπ ≠ 0 :=
  mul_ne_zero (uu_sub_vv_add_two_ne_zero Kpi) (uu_add_vv_add_two_ne_zero Kpi)

theorem Dqπ_ne_zero : Dqπ ≠ 0 := by
  rw [Dqπ_eq]
  exact mul_ne_zero (fun h => gfacπ_ne_zero (Polynomial.C_eq_zero.mp h))
      (GenericField.E22_ne_zero Kpi)

theorem E22_dvd_Dqπ : GenericField.E22 Kpi ∣ Dqπ := ⟨C gfacπ, by rw [Dqπ_eq]; ring⟩

theorem Mqπ_mod :
    Mqπ = C (qQ (GenericField.uu Kpi) (GenericField.vv Kpi) piAF piBF) * GenericField.E22 Kpi +
        Sqπ := by
  simp only [Mqπ, MqOf, qM2, qM1, qM0, Sqπ, SqOf, qS1, qS0, qQ,
    GenericField.E22, GenericField.E22a, GenericField.E22b, GenericField.E22c,
    map_add, map_sub, map_mul, map_pow, map_ofNat, map_one]
  ring

theorem qS1π_ne_zero : qS1 (GenericField.uu Kpi) (GenericField.vv Kpi) piAF piBF ≠ 0 := by
  have h : qS1 (GenericField.uu Kpi) (GenericField.vv Kpi) piAF piBF
      = piAF * piBF * ((GenericField.uu Kpi + 2) * ((GenericField.uu Kpi - GenericField.vv Kpi)
        * (GenericField.uu Kpi + GenericField.vv Kpi))) := by
    simp only [qS1]; ring
  rw [h]
  exact mul_ne_zero (mul_ne_zero piAF_ne_zero piBF_ne_zero)
    (mul_ne_zero (GenericField.uu_add_two_ne_zero Kpi)
      (mul_ne_zero (uu_sub_vv_ne_zero Kpi) (uu_add_vv_ne_zero Kpi)))

theorem Sqπ_ne_zero : Sqπ ≠ 0 := by
  intro h
  apply qS1π_ne_zero
  have h1 := congrArg (fun p => Polynomial.coeff p 1) h
  simpa [Sqπ, SqOf] using h1

theorem Sqπ_natDegree_le : Sqπ.natDegree ≤ 1 := by
  rw [Sqπ, SqOf]; exact Polynomial.natDegree_linear_le

theorem E22_not_dvd_Mqπ : ¬ GenericField.E22 Kpi ∣ Mqπ := by
  intro hdvd
  have h1 : GenericField.E22 Kpi ∣ Sqπ := by
    have hS : Sqπ = Mqπ - C (qQ (GenericField.uu Kpi) (GenericField.vv Kpi) piAF piBF) *
        GenericField.E22 Kpi := by
      rw [Mqπ_mod]; ring
    rw [hS]
    exact dvd_sub hdvd (Dvd.intro_left _ rfl)
  have h2 := Polynomial.natDegree_le_of_dvd h1 Sqπ_ne_zero
  rw [GenericField.E22_natDegree] at h2
  exact absurd (le_trans h2 Sqπ_natDegree_le) (by norm_num)

theorem nfacπ_ne_zero : nfacπ ≠ 0 :=
  mul_ne_zero piAF_sub_one_ne_zero piBF_sub_one_ne_zero

theorem E22_not_dvd_Nqπ : ¬ GenericField.E22 Kpi ∣ Nqπ := by
  intro hdvd
  rw [Nqπ_eq] at hdvd
  rcases (GenericField.E22_prime Kpi two_ne_zero_Kpi).dvd_mul.mp hdvd with h | h
  · have hne : (C nfacπ : GenericField.P Kpi) ≠ 0 := fun h0 => nfacπ_ne_zero
      (Polynomial.C_eq_zero.mp h0)
    have h2 := Polynomial.natDegree_le_of_dvd h hne
    rw [GenericField.E22_natDegree, Polynomial.natDegree_C] at h2
    exact absurd h2 (by norm_num)
  · exact E22_not_dvd_Mqπ h

theorem E22_dvd_q22π_denom : GenericField.E22 Kpi ∣ q22π.denom :=
  _root_.Rhone.Algebra.prime_dvd_denom Dqπ_ne_zero rfl (GenericField.E22_prime Kpi two_ne_zero_Kpi)
    E22_dvd_Dqπ E22_not_dvd_Nqπ

end Rhone.Algebra.SymbolicFrequencies
