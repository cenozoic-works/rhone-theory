/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.Spectral.Upper

/-! # Slack-weighted refinement of the spectral floor, and optimality of the floor -/

@[expose] public section

namespace Rhone.LinearAlgebra.Spectral

open Matrix Finset

variable {i j : ℕ} {θA θB ρ lam : ℝ}

noncomputable def Wsum (i j : ℕ) (r : ℝ) : ℝ := ∑ t : Fin (min i j + 1), 1 / W i j r (t : ℕ)

noncomputable def slackWsum (i j : ℕ) (r : ℝ) : ℝ :=
  ∑ t : Fin (min i j + 1), slack (i : ℝ) (j : ℝ) ((t : ℕ) : ℝ) / W i j r (t : ℕ)

noncomputable def weightedSlack (i j : ℕ) (r : ℝ) : ℝ := slackWsum i j r / Wsum i j r

theorem Wsum_pos (hr : 0 < r) : 0 < Wsum i j r := by
  refine Finset.sum_pos (fun t _ => ?_) ⟨0, Finset.mem_univ 0⟩
  exact one_div_pos.2 (W_pos hr _)

theorem innerW_one_one (r : ℝ) :
    innerW i j r (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) = Wsum i j r := by
  unfold innerW Wsum
  exact Finset.sum_congr rfl fun t _ => by rw [one_mul]

theorem innerW_one_T_one_split :
    innerW i j ρ (T i j θA θB ρ *ᵥ fun _ => (1 : ℝ)) (fun _ => (1 : ℝ))
      = floorMu i j θA θB * Wsum i j ρ + slackWsum i j ρ := by
  rw [innerW_one_T_one_eq]
  unfold Wsum slackWsum
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun t _ => by ring

theorem weightedSlack_le_bigS (hr : 0 < r) :
    weightedSlack i j r ≤ bigS (i : ℝ) (j : ℝ) := by
  have hW : 0 < Wsum i j r := Wsum_pos hr
  rw [weightedSlack, div_le_iff₀ hW]
  unfold slackWsum Wsum
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun t _ => ?_
  have hWt : 0 < W i j r (t : ℕ) := W_pos hr _
  have hs := slack_row_le_bigS (i := i) (j := j) t
  rw [mul_one_div]
  gcongr

theorem weightedSlack_ge_min (hr : 0 < r) :
    bigS (i : ℝ) (j : ℝ) - ((min i j : ℕ) : ℝ) * (((min i j : ℕ) : ℝ) - 1)
      ≤ weightedSlack i j r := by
  have hW : 0 < Wsum i j r := Wsum_pos hr
  rw [weightedSlack, le_div_iff₀ hW]
  unfold slackWsum Wsum
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun t _ => ?_
  have hWt : 0 < W i j r (t : ℕ) := W_pos hr _
  have hs := slack_row_ge_min (i := i) (j := j) t
  rw [mul_one_div]
  gcongr

theorem Te_exists_eigenvalue_le_weightedSlack (hlam : 0 < lam) (hρ : 0 < ρ) :
    ∃ (μ : ℝ) (v : Fin (min i j + 1) → ℝ), v ≠ 0 ∧ Te i j lam θA θB ρ *ᵥ v = μ • v ∧
      μ ≤ floorMu i j θA θB + weightedSlack i j (lam * ρ) / lam := by
  have hlam' : lam ≠ 0 := ne_of_gt hlam
  have hr : 0 < lam * ρ := mul_pos hlam hρ
  have hW : 0 < Wsum i j (lam * ρ) := Wsum_pos hr
  obtain ⟨ν, v, hv, hveq, hray⟩ :=
    T_exists_eigenvalue_le_rayleighW (i := i) (j := j) (θA := lam * θA) (θB := lam * θB)
      (ρ := lam * ρ) hr (fun _ => (1 : ℝ))
  refine ⟨ν / lam, v, hv, ?_, ?_⟩
  · rw [Te_mulVec_iff hlam', mul_div_cancel₀ _ hlam']
    exact hveq
  · rw [innerW_one_one, innerW_one_T_one_split] at hray
    have hquot : ν - floorMu i j (lam * θA) (lam * θB)
        ≤ slackWsum i j (lam * ρ) / Wsum i j (lam * ρ) := by
      rw [le_div_iff₀ hW]
      nlinarith [hray]
    have hν : ν ≤ floorMu i j (lam * θA) (lam * θB) + weightedSlack i j (lam * ρ) := by
      unfold weightedSlack
      linarith [hquot]
    have hkey : floorMu i j (lam * θA) (lam * θB) = lam * floorMu i j θA θB := by
      unfold floorMu; ring
    rw [hkey] at hν
    rw [div_le_iff₀ hlam]
    have : (floorMu i j θA θB + weightedSlack i j (lam * ρ) / lam) * lam
        = lam * floorMu i j θA θB + weightedSlack i j (lam * ρ) := by
      field_simp
    rw [this]
    exact hν

theorem natCast_mul_pred_nonneg (n : ℕ) : 0 ≤ (n : ℝ) * ((n : ℝ) - 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · norm_num
  · have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
    nlinarith

theorem bigS_nonneg (i j : ℕ) : 0 ≤ bigS (i : ℝ) (j : ℝ) := by
  unfold bigS
  linarith [natCast_mul_pred_nonneg i, natCast_mul_pred_nonneg j]

theorem no_better_lam_uniform_floor (hρ : 0 < ρ) {c : ℝ}
    (h : ∀ l : ℝ, 0 < l → ∀ μ ∈ TeSpec i j l θA θB ρ, c ≤ μ) :
    c ≤ floorMu i j θA θB := by
  by_contra hcon'
  rw [not_le] at hcon'
  have hcon : floorMu i j θA θB < c := hcon'
  set d : ℝ := c - floorMu i j θA θB with hd
  have hdpos : 0 < d := by rw [hd]; linarith
  set l : ℝ := (bigS (i : ℝ) (j : ℝ) + 1) / d with hl
  have hlpos : 0 < l := by
    rw [hl]
    exact div_pos (by linarith [bigS_nonneg i j]) hdpos
  obtain ⟨μ, v, hv, hveq, hle⟩ :=
    Te_exists_eigenvalue_le_sharp (i := i) (j := j) (θA := θA) (θB := θB) hlpos hρ
  have hcμ : c ≤ μ := h l hlpos μ ⟨v, hv, hveq⟩
  have hSl : bigS (i : ℝ) (j : ℝ) / l < d := by
    rw [hl, div_div_eq_mul_div, div_lt_iff₀ (by linarith [bigS_nonneg i j])]
    nlinarith [bigS_nonneg i j, hdpos]
  linarith [hle, hcμ, hSl]

end Rhone.LinearAlgebra.Spectral
