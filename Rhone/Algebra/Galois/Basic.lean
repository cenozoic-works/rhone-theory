/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.Tactic.ComputeDegree

/-! # Elementary irreducibility tools for the Galois obstruction -/

@[expose] public section

namespace Rhone.Algebra.Galois

open Polynomial

section CommRing

variable {K : Type*} [CommRing K]

theorem monic_natDegree_two_eq {q : K[X]} (hq : q.Monic) (h : q.natDegree = 2) :
    q = X ^ 2 + C (q.coeff 1) * X + C (q.coeff 0) := by
  have hle : (q - X ^ 2).natDegree ≤ 1 := by
    refine natDegree_le_iff_coeff_eq_zero.mpr fun N hN => ?_
    rcases eq_or_lt_of_le (Nat.succ_le_of_lt hN) with h2 | h2
    · have hN2 : N = 2 := h2.symm
      subst hN2
      have hc : q.coeff 2 = 1 := by
        have := hq.coeff_natDegree
        rwa [h] at this
      simp [hc, coeff_X_pow]
    · have hq0 : q.coeff N = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
      have hx0 : (X ^ 2 : K[X]).coeff N = 0 := by
        rw [coeff_X_pow]; exact ite_eq_right (by omega)
      simp [hq0, hx0]
  have key := eq_X_add_C_of_natDegree_le_one hle
  have h1 : (q - X ^ 2).coeff 1 = q.coeff 1 := by simp [coeff_X_pow]
  have h0 : (q - X ^ 2).coeff 0 = q.coeff 0 := by simp [coeff_X_pow]
  rw [h1, h0] at key
  rw [add_assoc]
  exact sub_eq_iff_eq_add'.mp key

theorem isPrimitive_of_bezout {f : K[X]} {i j : ℕ} {u v : K}
    (h : f.coeff i * u + f.coeff j * v = 1) : f.IsPrimitive := by
  intro r hr
  rw [C_dvd_iff_dvd_coeff] at hr
  exact isUnit_of_dvd_one (h ▸ dvd_add ((hr i).mul_right u) ((hr j).mul_right v))

end CommRing

section Domain

variable {K : Type*} [CommRing K] [IsDomain K]

theorem not_dvd_of_remainder {f q s r : K[X]} (h : f = q * s + r) (hr : r ≠ 0)
    (hdeg : r.natDegree < q.natDegree) : ¬ q ∣ f := by
  rintro ⟨t, ht⟩
  refine hr (eq_zero_of_dvd_of_natDegree_lt ?_ hdeg)
  have hrr : r = f - q * s := by rw [h]; ring
  rw [hrr]
  exact dvd_sub ⟨t, ht⟩ (Dvd.intro s rfl)

theorem not_dvd_of_rem_pair {f q s : K[X]} {r1 r0 : K}
    (h : f = q * s + C r1 * X + C r0) (hq : q.natDegree = 2) (hne : r1 ≠ 0 ∨ r0 ≠ 0) :
    ¬ q ∣ f := by
  refine not_dvd_of_remainder (s := s) (r := C r1 * X + C r0) (by rw [h]; ring) ?_ ?_
  · intro h0
    have c1 : (C r1 * X + C r0 : K[X]).coeff 1 = r1 := by simp
    have c0 : (C r1 * X + C r0 : K[X]).coeff 0 = r0 := by simp
    rw [h0, coeff_zero] at c1 c0
    rcases hne with hh | hh
    · exact hh c1.symm
    · exact hh c0.symm
  · have h1 : (C r1 * X + C r0 : K[X]).natDegree ≤ 1 := by compute_degree
    omega

end Domain

section Field

variable {K : Type*} [Field K]

theorem irreducible_quintic {f : K[X]} (h5 : f.natDegree = 5) (hlin : ∀ x : K, f.eval x ≠ 0)
    (hquad : ∀ b c : K, ¬ (X ^ 2 + C b * X + C c ∣ f)) : Irreducible f := by
  have hf0 : f ≠ 0 := fun h => by simp [h] at h5
  have hfu : ¬ IsUnit f := by
    intro h
    rw [natDegree_eq_zero_of_isUnit h] at h5
    exact absurd h5 (by norm_num)
  rw [irreducible_iff_lt_natDegree_lt hf0 hfu]
  intro q hq hmem hdvd
  rw [h5] at hmem
  simp only [Finset.mem_Ioc] at hmem
  rcases (show q.natDegree = 1 ∨ q.natDegree = 2 by omega) with hd | hd
  · rw [hq.eq_X_add_C hd] at hdvd
    refine hlin (-(q.coeff 0)) ?_
    rw [← IsRoot, ← dvd_iff_isRoot]
    rwa [map_neg, sub_neg_eq_add]
  · rw [monic_natDegree_two_eq hq hd] at hdvd
    exact hquad _ _ hdvd

theorem irreducible_C_mul_iff {c : K} (hc : c ≠ 0) {p : K[X]} :
    Irreducible (C c * p) ↔ Irreducible p := by
  obtain ⟨u, hu⟩ : IsUnit (C c : K[X]) := isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc)
  have hass : Associated p (C c * p) := ⟨u, by rw [hu, mul_comm]⟩
  exact ⟨fun h => hass.symm.irreducible h, fun h => hass.irreducible h⟩

end Field

section RootCount

variable {F S : Type*} [Field F] [CommRing S] [IsDomain S] [Algebra F S]

theorem le_card_rootSet {p : F[X]} (hp : p ≠ 0) (T : Finset S)
    (hT : ∀ x ∈ T, aeval x p = 0) : T.card ≤ Fintype.card (p.rootSet S) := by
  have hsub : ↑T ⊆ p.rootSet S := by
    intro x hx
    exact (mem_rootSet_of_ne hp).mpr (hT x (by simpa using hx))
  have hcard := Fintype.card_le_of_embedding (Set.embeddingOfSubset _ _ hsub)
  simpa using hcard

end RootCount

section Transfer

variable {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]

theorem irreducible_of_map_of_isPrimitive (φ : R →+* S) {f : R[X]} (hprim : f.IsPrimitive)
    (hdeg : (f.map φ).natDegree = f.natDegree) (h : Irreducible (f.map φ)) : Irreducible f := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp at h
  refine ⟨fun hu => h.not_isUnit (hu.map (mapRingHom φ)), fun a b hab => ?_⟩
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hab
    exact hf0 hab
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hab
    exact hf0 hab
  have hmap : f.map φ = a.map φ * b.map φ := by rw [hab, Polynomial.map_mul]
  have hsum : f.natDegree = a.natDegree + b.natDegree := by
    rw [hab, natDegree_mul ha0 hb0]
  have hconst : ∀ c : R[X], c ∣ f → c.natDegree = 0 → IsUnit c := by
    intro c hcf hc0
    rw [eq_C_of_natDegree_eq_zero hc0] at hcf ⊢
    exact isUnit_C.mpr (hprim _ hcf)
  rcases h.isUnit_or_isUnit hmap with hu | hu
  · left
    refine hconst a ⟨b, hab⟩ ?_
    have h1 : (a.map φ).natDegree = 0 := natDegree_eq_zero_of_isUnit hu
    have h2 : (f.map φ).natDegree ≤ (b.map φ).natDegree := by
      rw [hmap]
      exact le_trans (natDegree_mul_le) (by omega)
    have h3 : (b.map φ).natDegree ≤ b.natDegree := natDegree_map_le
    omega
  · right
    refine hconst b ⟨a, by rw [hab]; ring⟩ ?_
    have h1 : (b.map φ).natDegree = 0 := natDegree_eq_zero_of_isUnit hu
    have h2 : (f.map φ).natDegree ≤ (a.map φ).natDegree := by
      rw [hmap]
      exact le_trans (natDegree_mul_le) (by omega)
    have h3 : (a.map φ).natDegree ≤ a.natDegree := natDegree_map_le
    omega

end Transfer

end Rhone.Algebra.Galois
