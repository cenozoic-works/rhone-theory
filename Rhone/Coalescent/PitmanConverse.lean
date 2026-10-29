/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.LambdaRates
public import Rhone.Analysis.HausdorffMoment

/-!
# The converse of Pitman's consistency theorem for Λ-coalescent rates

Source: pitman1999, Section 3.1, Lemma 18, eq. (22). -/

@[expose] public section

namespace Rhone.Coalescent

open MeasureTheory Set
open scoped fwdDiff

theorem lambdaRate_diag_eq_moment {Λ : Measure ℝ} (hΛ : Λ (Icc (0 : ℝ) 1)ᶜ = 0) (n : ℕ) :
    lambdaRate Λ (n + 2) (n + 2) = ∫ x, x ^ n ∂Λ := by
  unfold lambdaRate
  have h : Λ.restrict (Icc (0 : ℝ) 1) = Λ :=
    Measure.restrict_eq_self_of_ae_mem (mem_ae_iff.2 hΛ)
  rw [h]
  simp

/-- Source: pitman1999, Section 3.1, Lemma 18, eq. (22). -/
theorem lambdaRate_existsUnique_of_consistent (lam : ℕ → ℕ → ℝ)
    (hnn : ∀ b k : ℕ, 2 ≤ k → k ≤ b → 0 ≤ lam b k)
    (hrec : ∀ b k : ℕ, 2 ≤ k → k ≤ b → lam b k = lam (b + 1) k + lam (b + 1) (k + 1)) :
    ∃! Λ : Measure ℝ, IsFiniteMeasure Λ ∧ Λ (Icc (0 : ℝ) 1)ᶜ = 0 ∧
      ∀ b k : ℕ, 2 ≤ k → k ≤ b → lam b k = lambdaRate Λ b k := by
  have hD : ∀ j n : ℕ, (-1 : ℝ) ^ j * (Δ_[1]^[j] fun n => lam (n + 2) (n + 2)) n =
      lam (n + j + 2) (n + 2) := by
    intro j
    induction j with
    | zero => intro n; simp
    | succ j ih =>
      intro n
      have h1 := ih n
      have h2 := ih (n + 1)
      have h3 := hrec (n + j + 2) (n + 2) (by omega) (by omega)
      rw [show n + 1 + j + 2 = n + j + 2 + 1 from by omega,
        show n + 1 + 2 = n + 2 + 1 from by omega] at h2
      rw [Function.iterate_succ_apply', fwdDiff, pow_succ,
        show n + (j + 1) + 2 = n + j + 2 + 1 from by omega]
      linear_combination h1 - h2 + h3
  obtain ⟨μ, ⟨hfin, hsupp, hmom⟩, huniq⟩ :=
    Rhone.Analysis.HausdorffMoment.hausdorff_moment_existsUnique
      (fun n => lam (n + 2) (n + 2)) fun j n => by
      rw [hD]
      exact hnn _ _ (by omega) (by omega)
  have hμ : μ (Icc (0 : ℝ) 1) ≠ ⊤ := measure_ne_top μ _
  have hall : ∀ d k : ℕ, 2 ≤ k → lam (k + d) k = lambdaRate μ (k + d) k := by
    intro d
    induction d with
    | zero =>
      intro k hk
      obtain ⟨n, rfl⟩ : ∃ n, k = n + 2 := ⟨k - 2, by omega⟩
      rw [Nat.add_zero, lambdaRate_diag_eq_moment hsupp]
      exact hmom n
    | succ d ih =>
      intro k hk
      have h1 := hrec (k + d) k hk (by omega)
      have h2 := lambdaRate_consistency hμ hk (show k ≤ k + d by omega)
      have h3 := ih k hk
      have h4 := ih (k + 1) (by omega)
      rw [show k + 1 + d = k + d + 1 from by omega] at h4
      rw [show k + (d + 1) = k + d + 1 from by omega]
      linarith
  refine ⟨μ, ⟨hfin, hsupp, fun b k hk hkb => ?_⟩, ?_⟩
  · obtain ⟨d, rfl⟩ : ∃ d, b = k + d := ⟨b - k, by omega⟩
    exact hall d k hk
  · rintro Λ ⟨hΛfin, hΛsupp, hΛ⟩
    refine huniq Λ ⟨hΛfin, hΛsupp, fun n => ?_⟩
    rw [← lambdaRate_diag_eq_moment hΛsupp]
    exact hΛ (n + 2) (n + 2) (by omega) le_rfl

end Rhone.Coalescent
