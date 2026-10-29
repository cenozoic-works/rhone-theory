/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.Galois.Basic
public import Mathlib.RingTheory.Polynomial.GaussLemma

/-! # Irreducibility tools for degree `7`, and the specialization principle in reusable form -/

@[expose] public section

namespace Rhone.Algebra.GaloisDegreeSeven

open Polynomial

section CommRing

variable {K : Type*} [CommRing K]

theorem monic_natDegree_three_eq {q : K[X]} (hq : q.Monic) (h : q.natDegree = 3) :
    q = X ^ 3 + C (q.coeff 2) * X ^ 2 + C (q.coeff 1) * X + C (q.coeff 0) := by
  have h3 : q.coeff 3 = 1 := by
    have := hq.coeff_natDegree
    rwa [h] at this
  ext n
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
  rcases lt_or_ge n 4 with hn | hn
  · interval_cases n <;> norm_num [h3]
  · have hz : q.coeff n = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    rw [hz]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega)]
    ring

end CommRing

section Domain

variable {K : Type*} [CommRing K] [IsDomain K]

theorem not_dvd_of_rem_triple {f q s : K[X]} {r2 r1 r0 : K}
    (h : f = q * s + C r2 * X ^ 2 + C r1 * X + C r0) (hq : q.natDegree = 3)
    (hne : r2 ≠ 0 ∨ r1 ≠ 0 ∨ r0 ≠ 0) : ¬ q ∣ f := by
  refine Rhone.Algebra.Galois.not_dvd_of_remainder (s := s) (r := C r2 * X ^ 2 + C r1 * X + C r0)
    (by rw [h]; ring) ?_ ?_
  · intro h0
    have c2 : (C r2 * X ^ 2 + C r1 * X + C r0 : K[X]).coeff 2 = r2 := by
      simp [coeff_X_pow]
    have c1 : (C r2 * X ^ 2 + C r1 * X + C r0 : K[X]).coeff 1 = r1 := by
      simp [coeff_X_pow]
    have c0 : (C r2 * X ^ 2 + C r1 * X + C r0 : K[X]).coeff 0 = r0 := by
      simp [coeff_X_pow]
    rw [h0, coeff_zero] at c2 c1 c0
    rcases hne with hh | hh | hh
    · exact hh c2.symm
    · exact hh c1.symm
    · exact hh c0.symm
  · have h1 : (C r2 * X ^ 2 + C r1 * X + C r0 : K[X]).natDegree ≤ 2 := by compute_degree
    omega

end Domain

section Field

variable {K : Type*} [Field K]

theorem no_monic_dvd_one {f : K[X]} (h : ∀ x : K, f.eval x ≠ 0) :
    ∀ q : K[X], q.Monic → q.natDegree = 1 → ¬ q ∣ f := by
  intro q hq hd hdvd
  rw [hq.eq_X_add_C hd] at hdvd
  refine h (-(q.coeff 0)) ?_
  rw [← IsRoot, ← dvd_iff_isRoot]
  rwa [map_neg, sub_neg_eq_add]

theorem no_monic_dvd_two {f : K[X]} (h : ∀ b c : K, ¬ (X ^ 2 + C b * X + C c ∣ f)) :
    ∀ q : K[X], q.Monic → q.natDegree = 2 → ¬ q ∣ f := by
  intro q hq hd hdvd
  rw [Rhone.Algebra.Galois.monic_natDegree_two_eq hq hd] at hdvd
  exact h _ _ hdvd

theorem no_monic_dvd_three {f : K[X]}
    (h : ∀ b c d : K, ¬ (X ^ 3 + C b * X ^ 2 + C c * X + C d ∣ f)) :
    ∀ q : K[X], q.Monic → q.natDegree = 3 → ¬ q ∣ f := by
  intro q hq hd hdvd
  rw [monic_natDegree_three_eq hq hd] at hdvd
  exact h _ _ _ hdvd

end Field

section Transfer

variable {R S K : Type*} [CommRing R] [IsDomain R]

theorem exists_monic_dvd_map [Field K] (φ : R →+* K) {f g : R[X]} (hg : g ∣ f)
    (hlc : φ f.leadingCoeff ≠ 0) :
    ∃ q : K[X], q.Monic ∧ q.natDegree = g.natDegree ∧ q ∣ f.map φ := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp at hlc
  have hlcmap : (f.map φ).leadingCoeff = φ f.leadingCoeff :=
    leadingCoeff_map_of_leadingCoeff_ne_zero φ hlc
  have hfm0 : f.map φ ≠ 0 := fun h => hlc (by rw [← hlcmap, h, leadingCoeff_zero])
  have hdeg : (f.map φ).natDegree = f.natDegree := natDegree_map_of_leadingCoeff_ne_zero φ hlc
  obtain ⟨h, rfl⟩ := hg
  have hg0 : g ≠ 0 := fun h0 => hf0 (by rw [h0, zero_mul])
  have hh0 : h ≠ 0 := fun h0 => hf0 (by rw [h0, mul_zero])
  rw [Polynomial.map_mul] at hfm0 hdeg
  have hgm0 : g.map φ ≠ 0 := left_ne_zero_of_mul hfm0
  have hhm0 : h.map φ ≠ 0 := right_ne_zero_of_mul hfm0
  have hsum : (g.map φ).natDegree + (h.map φ).natDegree = g.natDegree + h.natDegree := by
    rw [← natDegree_mul hgm0 hhm0, hdeg, natDegree_mul hg0 hh0]
  have hle1 : (g.map φ).natDegree ≤ g.natDegree := natDegree_map_le
  have hle2 : (h.map φ).natDegree ≤ h.natDegree := natDegree_map_le
  have hgd : (g.map φ).natDegree = g.natDegree := by omega
  refine ⟨(g.map φ) * C ((g.map φ).leadingCoeff)⁻¹, monic_mul_leadingCoeff_inv hgm0, ?_, ?_⟩
  · rw [natDegree_mul_leadingCoeff_inv _ hgm0, hgd]
  · refine ⟨C ((g.map φ).leadingCoeff) * h.map φ, ?_⟩
    rw [Polynomial.map_mul]
    have hlcg : ((g.map φ).leadingCoeff)⁻¹ * (g.map φ).leadingCoeff = 1 :=
      inv_mul_cancel₀ (leadingCoeff_ne_zero.mpr hgm0)
    calc g.map φ * h.map φ
        = g.map φ * C (((g.map φ).leadingCoeff)⁻¹ * (g.map φ).leadingCoeff) * h.map φ := by
          rw [hlcg, C_1, mul_one]
      _ = g.map φ * C ((g.map φ).leadingCoeff)⁻¹ * (C ((g.map φ).leadingCoeff) * h.map φ) := by
          rw [C_mul]; ring

theorem no_factor_of_map [Field K] (φ : R →+* K) {f : R[X]} (hlc : φ f.leadingCoeff ≠ 0)
    {d : ℕ} (hno : ∀ q : K[X], q.Monic → q.natDegree = d → ¬ q ∣ f.map φ)
    {g : R[X]} (hg : g ∣ f) : g.natDegree ≠ d := by
  intro hd
  obtain ⟨q, hq1, hq2, hq3⟩ := exists_monic_dvd_map φ hg hlc
  exact hno q hq1 (hq2.trans hd) hq3

theorem irreducible_of_isPrimitive_of_no_factor {f : R[X]} {n : ℕ} (hprim : f.IsPrimitive)
    (hdeg : f.natDegree = n) (hn : 0 < n)
    (hno : ∀ g : R[X], g ∣ f → 1 ≤ g.natDegree → 2 * g.natDegree ≤ n → False) :
    Irreducible f := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp at hdeg
    omega
  refine ⟨fun hu => ?_, fun a b hab => ?_⟩
  · rw [natDegree_eq_zero_of_isUnit hu] at hdeg
    omega
  have ha0 : a ≠ 0 := fun h => hf0 (by rw [hab, h, zero_mul])
  have hb0 : b ≠ 0 := fun h => hf0 (by rw [hab, h, mul_zero])
  have hsum : a.natDegree + b.natDegree = n := by rw [← natDegree_mul ha0 hb0, ← hab, hdeg]
  have hconst : ∀ c : R[X], c ∣ f → c.natDegree = 0 → IsUnit c := by
    intro c hcf hc0
    rw [eq_C_of_natDegree_eq_zero hc0] at hcf ⊢
    exact isUnit_C.mpr (hprim _ hcf)
  rcases Nat.eq_zero_or_pos a.natDegree with h | h
  · exact Or.inl (hconst a ⟨b, hab⟩ h)
  rcases Nat.eq_zero_or_pos b.natDegree with h' | h'
  · exact Or.inr (hconst b ⟨a, by rw [hab]; ring⟩ h')
  rcases le_or_gt a.natDegree b.natDegree with hle | hle
  · exact absurd (hno a ⟨b, hab⟩ h (by omega)) not_false
  · exact absurd (hno b ⟨a, by rw [hab]; ring⟩ h' (by omega)) not_false

end Transfer

section Specialization

variable {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]

theorem irreducible_of_specialization (φ : R →+* S) {f : R[X]} (hprim : f.IsPrimitive)
    (hlc : φ f.leadingCoeff ≠ 0) (h : Irreducible (f.map φ)) : Irreducible f :=
  Rhone.Algebra.Galois.irreducible_of_map_of_isPrimitive φ hprim
    (natDegree_map_of_leadingCoeff_ne_zero φ hlc) h

variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  [UniqueFactorizationMonoid R]

theorem irreducible_ratFunc_of_specialization (φ : R →+* S) {f : R[X]} (hprim : f.IsPrimitive)
    (hlc : φ f.leadingCoeff ≠ 0) (h : Irreducible (f.map φ)) :
    Irreducible (f.map (algebraMap R K)) :=
  (hprim.irreducible_iff_irreducible_map_fraction_map).mp
    (irreducible_of_specialization φ hprim hlc h)

end Specialization

end Rhone.Algebra.GaloisDegreeSeven
