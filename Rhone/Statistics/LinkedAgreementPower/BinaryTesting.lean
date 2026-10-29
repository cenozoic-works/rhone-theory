/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.DependentPairedTest.Coupling
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-! # Independent paired-binary test bridge using the fixed self-normalized rule -/

@[expose] public section

open scoped BigOperators
namespace Rhone.Statistics.LinkedAgreementPower
open DependenceBudget DependentPairedTest
variable {X : Type*} [Fintype X]

noncomputable def independentPair (P Q : Law X) : Law (X × X) where
  mass := fun x => P.mass x.1 * Q.mass x.2
  nonneg := fun x => mul_nonneg (P.nonneg _) (Q.nonneg _)
  total := by simp [Fintype.sum_prod_type, ← Finset.mul_sum, P.total, Q.total]

theorem independent_coupling (P Q : Law X) : IsCoupling (independentPair P Q) P Q := by
  constructor
  · intro x
    simp [independentPair, ← Finset.mul_sum, Q.total]
  · intro y
    simp [independentPair, ← Finset.sum_mul, P.total]

noncomputable def independentTest (P Q : Law X) (F : X → ℝ) (N : ℕ) : ℝ :=
  probability (iid (independentPair P Q) N)
    (fun x => Rejects (fun i => F (x i).1 - F (x i).2))

theorem binary_test_common_size (P : Law X) {F : X → ℝ} (hF : Binary F) (N : ℕ) :
    independentTest P P F N ≤ (1 : ℝ) / 20 :=
  coupling_null_size _ P P (independent_coupling P P) hF hF rfl N

theorem independent_discordance (P Q : Law X) {F : X → ℝ} (hF : Binary F) :
    discordance (independentPair P Q) (fun x => F x.1) (fun x => F x.2) =
      rejection P F + rejection Q F - 2 * rejection P F * rejection Q F := by
  rw [discordance_identity _ (fun x => hF x.1) (fun x => hF x.2),
    coupling_first_mean _ P Q (independent_coupling P Q),
    coupling_second_mean _ P Q (independent_coupling P Q)]
  have he : rejection (independentPair P Q) (fun x => F x.1 * F x.2) =
      rejection P F * rejection Q F := by
    simp only [rejection, independentPair, Fintype.sum_prod_type]
    simp_rw [show ∀ x y, P.mass x * Q.mass y * (F x * F y) =
      (P.mass x * F x) * (Q.mass y * F y) from fun _ _ => by ring1]
    simp only [← Finset.mul_sum, ← Finset.sum_mul]
  rw [he]
  ring1

theorem binary_signed_power (P Q : Law X) {F : X → ℝ} (hF : Binary F) (N : ℕ)
    (hgap : rejection P F ≠ rejection Q F)
    (hb : 160 * (rejection P F + rejection Q F - 2 * rejection P F * rejection Q F) ≤
      N * (rejection P F - rejection Q F) ^ 2) :
    (19 : ℝ) / 20 ≤ independentTest P Q F N := by
  apply iid_binary_power (independentPair P Q) N (fun x => hF x.1) (fun x => hF x.2)
  · rw [coupling_contrast_mean _ P Q (independent_coupling P Q)]
    exact sub_ne_zero.mpr hgap
  · rw [coupling_contrast_mean _ P Q (independent_coupling P Q), independent_discordance P Q hF]
    exact hb

theorem binary_test_exists (P Q : Law X) {F : X → ℝ} (hF : Binary F)
    (hgap : rejection P F ≠ rejection Q F) :
    ∃ N : ℕ, (19 : ℝ) / 20 ≤ independentTest P Q F N := by
  have hd : 0 < (rejection P F - rejection Q F) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hgap)
  obtain ⟨N, hN⟩ := exists_nat_ge (160 / (rejection P F - rejection Q F) ^ 2)
  refine ⟨N, ?_⟩
  exact coupling_worst_discordance_power _ P Q (independent_coupling P Q) hF hF N
    ((div_le_iff₀ hd).mp hN)

end Rhone.Statistics.LinkedAgreementPower
