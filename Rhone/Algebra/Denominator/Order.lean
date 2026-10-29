/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.RingTheory.Valuation.PrimeMultiplicity

/-! # A pole survives a split `x = cΦ + Ψ`: the valuation argument -/

@[expose] public section

namespace Rhone.Algebra.Denominator

section Valuation

variable {R : Type*} [CommRing R] {Γ : Type*} [LinearOrderedAddCommMonoidWithTop Γ]

theorem pole_survives (v : AddValuation R Γ) {N c NΦ E NΨ : R}
    (hid : N = c * NΦ + E * NΨ) (hc : v c = 0) (hΦ : v NΦ = 0)
    (hΨ : 0 ≤ v NΨ) (hE : 0 < v E) : v N = 0 := by
  have h1 : v (c * NΦ) = 0 := by rw [AddValuation.map_mul, hc, hΦ, add_zero]
  have h2 : v E ≤ v (E * NΨ) := by
    rw [AddValuation.map_mul]
    exact le_add_of_nonneg_right hΨ
  have h3 : v (c * NΦ) < v (E * NΨ) := lt_of_lt_of_le (h1 ▸ hE) h2
  rw [hid, AddValuation.map_add_eq_of_lt_left v h3, h1]

theorem order_transfer (v : AddValuation R Γ) {D Nd d N : R}
    (hid : D * Nd = d * N) (hN : v N = 0) (hNd : 0 ≤ v Nd) : v D ≤ v d := by
  have h1 : v D + v Nd = v d := by
    have := congrArg v hid
    rwa [AddValuation.map_mul, AddValuation.map_mul, hN, add_zero] at this
  calc v D ≤ v D + v Nd := le_add_of_nonneg_right hNd
    _ = v d := h1

end Valuation

section Dvd

variable {R : Type*} [CommRing R]

theorem not_dvd_of_pole_survives {N c NΦ E NΨ e : R}
    (hid : N = c * NΦ + E * NΨ) (hc : IsUnit c) (hE : e ∣ E) (hΦ : ¬ e ∣ NΦ) : ¬ e ∣ N := by
  intro hN
  refine hΦ ?_
  obtain ⟨u, rfl⟩ := hc
  have h1 : e ∣ (u : R) * NΦ := by
    have : (u : R) * NΦ = N - E * NΨ := by rw [hid]; ring
    rw [this]
    exact dvd_sub hN (hE.mul_right NΨ)
  obtain ⟨k, hk⟩ := h1
  refine ⟨(↑u⁻¹ : R) * k, ?_⟩
  have hu : (↑u⁻¹ : R) * ((u : R) * NΦ) = NΦ := by
    rw [← mul_assoc, Units.inv_mul, one_mul]
  rw [← hu, hk]
  ring

end Dvd

section Multiplicity

variable {R : Type*} [CommRing R] [IsDomain R] {e : R}

omit [IsDomain R] in
theorem emultiplicity_eq_zero_of_isUnit (he : ¬ IsUnit e) {c : R} (hc : IsUnit c) :
    emultiplicity e c = 0 :=
  emultiplicity_of_isUnit_right he hc

theorem emultiplicity_num_eq_zero (hp : Prime e) {N c NΦ E NΨ : R}
    (hid : N = c * NΦ + E * NΨ) (hc : IsUnit c) (hΦ : emultiplicity e NΦ = 0)
    (hE : 0 < emultiplicity e E) : emultiplicity e N = 0 :=
  pole_survives (multiplicity_addValuation hp) hid
    (emultiplicity_eq_zero_of_isUnit hp.not_isUnit hc) hΦ zero_le hE

theorem emultiplicity_le_of_num_eq_zero (hp : Prime e) {D Nd d N : R}
    (hid : D * Nd = d * N) (hN : emultiplicity e N = 0) :
    emultiplicity e D ≤ emultiplicity e d :=
  order_transfer (multiplicity_addValuation hp) hid hN zero_le

end Multiplicity

end Rhone.Algebra.Denominator
