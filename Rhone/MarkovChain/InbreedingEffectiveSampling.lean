/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.MarkovChain.EffectiveSampling
/-!
# Inbreeding effective size derived from a finite founder-copy sampler

Source: wright1931, pp. 109–110. -/
@[expose] public section
namespace Rhone.MarkovChain.EffectiveSize
open Finset
noncomputable def distinctCopyPairMass (K : ℕ) (ab : Fin K × Fin K) : ℝ :=
  if ab.1 ≠ ab.2 then 1 / ((K : ℝ) * (K - 1 : ℕ)) else 0
noncomputable def distinctCopyIbd {A : Type*} [DecidableEq A]
    (K : ℕ) (g : Fin K → A) : ℝ :=
  ∑ ab : Fin K × Fin K,
    if ab.1 ≠ ab.2 ∧ g ab.1 = g ab.2 then 1 / ((K : ℝ) * (K - 1 : ℕ)) else 0
noncomputable def offspringCopyIbd {A : Type*} [DecidableEq A]
    (K : ℕ) (g : Fin K → A) : ℝ :=
  ∑ ab : Fin K × Fin K,
    if g ab.1 = g ab.2 then uniformCopyPairMass K ab else 0
theorem distinct_copy_pair_mass_sum (K : ℕ) (hK : 2 ≤ K) :
    ∑ ab : Fin K × Fin K, distinctCopyPairMass K ab = 1 := by
  have hK0 : (K : ℝ) ≠ 0 := by positivity
  have hKm0 : ((K - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show K - 1 ≠ 0 by omega)
  unfold distinctCopyPairMass
  have he : ∀ ab : Fin K × Fin K,
      (if ab.1 ≠ ab.2 then 1 / ((K : ℝ) * (K - 1 : ℕ)) else 0) =
      1 / ((K : ℝ) * (K - 1 : ℕ)) -
        (if ab.1 = ab.2 then 1 / ((K : ℝ) * (K - 1 : ℕ)) else 0) := by
    intro ab
    by_cases ha : ab.1 = ab.2 <;> simp [ha]
  simp_rw [he]
  rw [sum_sub_distrib]
  have hd : (∑ ab : Fin K × Fin K,
      if ab.1 = ab.2 then 1 / ((K : ℝ) * (K - 1 : ℕ)) else 0) =
      (K : ℝ) * (1 / ((K : ℝ) * (K - 1 : ℕ))) := by
    simp [Fintype.sum_prod_type]
  rw [hd]
  simp only [one_div, mul_inv_rev, sum_const, card_univ, Fintype.card_prod,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul]
  rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hm : ((K - 1 : ℕ) : ℝ) = (K : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  rw [hm] at hKm0
  field_simp

theorem distinct_copy_ibd_pushforward {A : Type*} [DecidableEq A]
    (K : ℕ) (g : Fin K → A) :
    distinctCopyIbd K g = ∑ ab : Fin K × Fin K,
      if g ab.1 = g ab.2 then distinctCopyPairMass K ab else 0 := by
  unfold distinctCopyIbd distinctCopyPairMass
  apply sum_congr rfl
  intro ab hab
  by_cases ha : ab.1 = ab.2 <;> by_cases hg : g ab.1 = g ab.2 <;> simp [ha, hg]

theorem offspring_copy_ibd_recursion {A : Type*} [DecidableEq A]
    (K : ℕ) (hK : 2 ≤ K) (g : Fin K → A) :
    offspringCopyIbd K g = 1 / (K : ℝ) +
      (1 - 1 / (K : ℝ)) * distinctCopyIbd K g := by
  have hK0 : (K : ℝ) ≠ 0 := by positivity
  have hKm0 : ((K - 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show K - 1 ≠ 0 by omega)
  have hKm : ((K - 1 : ℕ) : ℝ) = (K : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  conv_rhs => lhs; rw [← uniform_copy_coincidence (by omega : 0 < K)]
  unfold offspringCopyIbd distinctCopyIbd uniformCopyCoincidence
  rw [mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro ab hab
  by_cases ha : ab.1 = ab.2
  · simp [ha]
  · by_cases hg : g ab.1 = g ab.2
    · simp only [ha, hg, ne_eq, not_false_eq_true, and_true, ite_false, ite_true, zero_add,
        uniformCopyPairMass]
      rw [hKm]
      have hKm1 : (K : ℝ) - 1 ≠ 0 := by rw [← hKm]; exact hKm0
      field_simp
    · simp [ha, hg]

/-- Source: wright1931, pp. 109–110. -/
theorem sampled_inbreeding_effective {A : Type*} [DecidableEq A]
    (N : ℕ) (hN : 0 < N) (g : Fin (2 * N) → A)
    (hF : distinctCopyIbd (2 * N) g ≠ 1) :
    inbreedingEffective (distinctCopyIbd (2 * N) g) (offspringCopyIbd (2 * N) g) = N := by
  have hr := offspring_copy_ibd_recursion (2 * N) (by omega) g
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hr
  rw [inbreeding_effective_recursion hF (by positivity) hr]
  exact coalescence_effective_diploid hN
end Rhone.MarkovChain.EffectiveSize
