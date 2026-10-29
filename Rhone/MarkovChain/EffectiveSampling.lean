/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.EffectiveSize

/-! # Finite ancestral-copy sampling -/

@[expose] public section

namespace Rhone.MarkovChain.EffectiveSize

open Finset

noncomputable def uniformCopyPairMass (K : ℕ) (_ : Fin K × Fin K) : ℝ := 1 / (K : ℝ) ^ 2

noncomputable def uniformCopyCoincidence (K : ℕ) : ℝ :=
  ∑ ab : Fin K × Fin K, if ab.1 = ab.2 then uniformCopyPairMass K ab else 0

theorem uniform_copy_pair_mass_sum {K : ℕ} (hK : 0 < K) :
    ∑ ab : Fin K × Fin K, uniformCopyPairMass K ab = 1 := by
  have hK' : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hK.ne'
  simp only [uniformCopyPairMass, sum_const, card_univ, Fintype.card_prod, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_mul]
  field_simp

/-- Source: wright1931, pp. 109–110. -/
theorem uniform_copy_coincidence {K : ℕ} (hK : 0 < K) :
    uniformCopyCoincidence K = 1 / (K : ℝ) := by
  have hK' : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hK.ne'
  simp [uniformCopyCoincidence, uniformCopyPairMass, Fintype.sum_prod_type]
  field_simp

/-- Source: wright1931, pp. 109–110. -/
theorem diploid_uniform_coincidence {N : ℕ} (hN : 0 < N) :
    uniformCopyCoincidence (2 * N) = 1 / (2 * (N : ℝ)) := by
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using uniform_copy_coincidence (by omega : 0 < 2 * N)

noncomputable def sexCopyWeight (Nm Nf : ℕ) :
    (Fin Nm × Fin 2) ⊕ (Fin Nf × Fin 2) → ℝ
  | Sum.inl _ => 1 / (4 * (Nm : ℝ))
  | Sum.inr _ => 1 / (4 * (Nf : ℝ))

noncomputable def sexCopyPairMass (Nm Nf : ℕ)
    (cd : ((Fin Nm × Fin 2) ⊕ (Fin Nf × Fin 2)) ×
      ((Fin Nm × Fin 2) ⊕ (Fin Nf × Fin 2))) : ℝ :=
  sexCopyWeight Nm Nf cd.1 * sexCopyWeight Nm Nf cd.2

noncomputable def sexCopyCoincidence (Nm Nf : ℕ) : ℝ :=
  ∑ cd : ((Fin Nm × Fin 2) ⊕ (Fin Nf × Fin 2)) ×
    ((Fin Nm × Fin 2) ⊕ (Fin Nf × Fin 2)),
    if cd.1 = cd.2 then sexCopyPairMass Nm Nf cd else 0

theorem sex_copy_weight_nonneg (Nm Nf : ℕ)
    (c : (Fin Nm × Fin 2) ⊕ (Fin Nf × Fin 2)) : 0 ≤ sexCopyWeight Nm Nf c := by
  cases c <;> simp only [sexCopyWeight] <;> positivity

theorem sex_copy_weight_sum {Nm Nf : ℕ} (hm : 0 < Nm) (hf : 0 < Nf) :
    ∑ c, sexCopyWeight Nm Nf c = 1 := by
  have hm' : (Nm : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hf' : (Nf : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hf.ne'
  simp [Fintype.sum_sum_type, sexCopyWeight]
  field_simp
  ring

theorem sex_copy_pair_mass_sum {Nm Nf : ℕ} (hm : 0 < Nm) (hf : 0 < Nf) :
    ∑ cd, sexCopyPairMass Nm Nf cd = 1 := by
  simp only [sexCopyPairMass, Fintype.sum_prod_type, ← mul_sum, sex_copy_weight_sum hm hf,
    mul_one]

theorem sex_copy_coincidence {Nm Nf : ℕ} (hm : 0 < Nm) (hf : 0 < Nf) :
    sexCopyCoincidence Nm Nf = sexPairCoalescence Nm Nf := by
  have hm' : (Nm : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hf' : (Nf : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hf.ne'
  simp [sexCopyCoincidence, sexCopyPairMass, Fintype.sum_prod_type,
    Fintype.sum_sum_type, sexCopyWeight, sexPairCoalescence]
  field_simp
  ring

/-- Source: wright1931, pp. 108–109. -/
theorem sampled_unequal_sex_effective {Nm Nf : ℕ} (hm : 0 < Nm) (hf : 0 < Nf) :
    coalescenceEffective (sexCopyCoincidence Nm Nf) =
      4 * (Nm : ℝ) * (Nf : ℝ) / ((Nm : ℝ) + (Nf : ℝ)) := by
  rw [sex_copy_coincidence hm hf]
  exact unequal_sex_effective hm hf

end Rhone.MarkovChain.EffectiveSize
