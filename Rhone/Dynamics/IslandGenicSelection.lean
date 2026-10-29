/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Dynamics.DiploidSelection
public import Mathlib.Basic.Real.Basic

/-!
# Genic selection followed by migration from a monomorphic pool

Source: burger2013_migration_selection, sec. 4. -/

@[expose] public section
namespace Rhone.Dynamics

/-- Source: burger2013_migration_selection, sec. 4. -/
noncomputable def islandGenicStep (s m p : ℝ) : ℝ := (1 - m) * p / (1 - s + s * p)

/-- Source: burger2013_migration_selection, sec. 4. -/
theorem island_genic_mem_Icc {s m p : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) (hm0 : 0 ≤ m) (hm1 : m < 1)
    (hp : p ∈ Set.Icc 0 1) : islandGenicStep s m p ∈ Set.Icc 0 1 := by
  have hD : 0 < 1 - s + s * p := by nlinarith [mul_nonneg hs0.le hp.1]
  constructor
  · exact div_nonneg (mul_nonneg (by linarith) hp.1) hD.le
  · apply (div_le_one hD).mpr
    nlinarith [mul_nonneg hm0 hp.1, mul_nonneg (sub_nonneg.mpr hs1.le) (sub_nonneg.mpr hp.2)]

/-- Source: burger2013_migration_selection, sec. 4. -/
theorem island_genic_fixed_iff {s m p : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) (_hm0 : 0 ≤ m) (_hm1 : m < 1)
    (hp : p ∈ Set.Icc 0 1) :
    islandGenicStep s m p = p ↔ p = 0 ∨ p = 1 - m / s := by
  have hD : 1 - s + s * p ≠ 0 := by
    have : 0 < 1 - s + s * p := by nlinarith [mul_nonneg hs0.le hp.1]
    exact ne_of_gt this
  have hs : s ≠ 0 := ne_of_gt hs0
  rw [islandGenicStep, div_eq_iff hD]
  constructor
  · intro h
    have hz : p * (s * p - s + m) = 0 := by nlinarith
    rcases mul_eq_zero.mp hz with h | h
    · exact Or.inl h
    · right
      apply (eq_sub_iff_add_eq).mpr
      field_simp
      nlinarith
  · intro h
    rcases h with h | h
    · simp [h]
    · rw [h]
      field_simp
      ring

/-- Source: burger2013_migration_selection, sec. 4. -/
theorem island_genic_positive_equilibrium_iff {s m : ℝ}
    (hs0 : 0 < s) (hs1 : s < 1) (hm0 : 0 ≤ m) (hm1 : m < 1) :
    (∃ p ∈ Set.Ioc 0 1, islandGenicStep s m p = p) ↔ m < s := by
  constructor
  · rintro ⟨p, hp, hfix⟩
    rcases (island_genic_fixed_iff hs0 hs1 hm0 hm1 ⟨hp.1.le, hp.2⟩).mp hfix with h | h
    · linarith [hp.1]
    · have : m / s < 1 := by linarith [hp.1]
      exact (div_lt_one hs0).mp this
  · intro hms
    have hpos : 0 < 1 - m / s := sub_pos.mpr ((div_lt_one hs0).mpr hms)
    have hle : 1 - m / s ≤ 1 := by have := div_nonneg hm0 hs0.le; linarith
    refine ⟨1 - m / s, ⟨hpos, hle⟩, ?_⟩
    exact (island_genic_fixed_iff hs0 hs1 hm0 hm1 ⟨hpos.le, hle⟩).mpr (Or.inr rfl)

end Rhone.Dynamics
