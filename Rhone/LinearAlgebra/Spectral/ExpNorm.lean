/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.Spectral.Decay
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-! # Norm bounds for matrix exponentials, and the `∞`-norm decay bound -/

@[expose] public section

namespace Rhone.LinearAlgebra.Spectral

open Matrix Finset
open scoped Matrix.Norms.Operator Nat

section General

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

theorem linfty_opNorm_le_of_row_sum_le (A : Matrix n n ℝ) {c : ℝ}
    (h : ∀ t, ∑ s, |A t s| ≤ c) : ‖A‖ ≤ c := by
  have hc : 0 ≤ c :=
    le_trans (Finset.sum_nonneg fun _ _ => abs_nonneg _) (h (Classical.arbitrary n))
  rw [Matrix.linfty_opNorm_def, show c = ((⟨c, hc⟩ : NNReal) : ℝ) from rfl]
  refine NNReal.coe_le_coe.2 (Finset.sup_le fun t _ => ?_)
  have key : ((∑ s, ‖A t s‖₊ : NNReal) : ℝ) ≤ c := by
    rw [NNReal.coe_sum]
    simpa [Real.norm_eq_abs] using h t
  exact key

theorem norm_exp_le (X : Matrix n n ℝ) : ‖NormedSpace.exp X‖ ≤ Real.exp ‖X‖ := by
  have hsum : Summable fun k : ℕ => ‖((k ! : ℝ)⁻¹ : ℝ) • X ^ k‖ :=
    NormedSpace.norm_expSeries_summable' (𝕂 := ℝ) X
  have hsumR : Summable fun k : ℕ => ((k ! : ℝ)⁻¹ : ℝ) • ‖X‖ ^ k :=
    (NormedSpace.norm_expSeries_summable' (𝕂 := ℝ) ‖X‖).of_norm
  have hexp : NormedSpace.exp X = ∑' k : ℕ, ((k ! : ℝ)⁻¹ : ℝ) • X ^ k :=
    congrFun (NormedSpace.exp_eq_tsum ℝ) X
  have hR : Real.exp ‖X‖ = ∑' k : ℕ, ((k ! : ℝ)⁻¹ : ℝ) • ‖X‖ ^ k := by
    rw [Real.exp_eq_exp_ℝ]
    exact congrFun (NormedSpace.exp_eq_tsum ℝ) ‖X‖
  rw [hexp, hR]
  refine le_trans (norm_tsum_le_tsum_norm hsum) (hsum.tsum_le_tsum (fun k => ?_) hsumR)
  rw [norm_smul, smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hpow : ‖X ^ k‖ ≤ ‖X‖ ^ k := by
    rcases Nat.eq_zero_or_pos k with hk | hk
    · simp [hk]
    · exact norm_pow_le' X hk
  exact mul_le_mul_of_nonneg_left hpow (by positivity)

omit [Nonempty n] in
theorem exp_smul_one (r : ℝ) :
    NormedSpace.exp (r • (1 : Matrix n n ℝ)) = Real.exp r • (1 : Matrix n n ℝ) := by
  have h := NormedSpace.algebraMap_exp_comm (𝕂 := ℝ) (𝔸 := Matrix n n ℝ) r
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, ← Real.exp_eq_exp_ℝ] at h
  exact h.symm

theorem norm_exp_smul_le_of_row_measure_le (M : Matrix n n ℝ) {c s : ℝ} (hs : 0 ≤ s)
    (h : ∀ t, M t t + ∑ u ∈ Finset.univ.erase t, |M t u| ≤ c) :
    ‖NormedSpace.exp (s • M)‖ ≤ Real.exp (s * c) := by
  classical
  set B : Matrix n n ℝ := M - c • (1 : Matrix n n ℝ) with hBdef
  have hBd : ∀ t, B t t = M t t - c := by
    intro t
    simp [hBdef, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq]
  have hBo : ∀ t u, u ≠ t → B t u = M t u := by
    intro t u hu
    simp [hBdef, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_ne (Ne.symm hu)]
  have hrow : ∀ t, B t t + ∑ u ∈ Finset.univ.erase t, |B t u| ≤ 0 := by
    intro t
    have hcongr : ∑ u ∈ Finset.univ.erase t, |B t u| = ∑ u ∈ Finset.univ.erase t, |M t u| :=
      Finset.sum_congr rfl fun u hu => by rw [hBo t u (Finset.mem_erase.1 hu).1]
    rw [hBd t, hcongr]
    linarith [h t]
  set γ : ℝ := Finset.univ.sup' Finset.univ_nonempty (fun t => -B t t) with hγdef
  have hγge : ∀ t, -B t t ≤ γ := fun t =>
    Finset.le_sup' (f := fun t => -B t t) (Finset.mem_univ t)
  have hγnonneg : 0 ≤ γ := by
    have h0 := hγge (Classical.arbitrary n)
    have := Finset.sum_nonneg (fun u (_ : u ∈ Finset.univ.erase (Classical.arbitrary n)) =>
      abs_nonneg (B (Classical.arbitrary n) u))
    linarith [hrow (Classical.arbitrary n)]
  set N : Matrix n n ℝ := B + γ • (1 : Matrix n n ℝ) with hNdef
  have hNrow : ∀ t, ∑ u, |N t u| ≤ γ := by
    intro t
    have hNd : N t t = B t t + γ := by
      simp [hNdef, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq]
    have hNo : ∀ u ∈ Finset.univ.erase t, |N t u| = |B t u| := by
      intro u hu
      have : N t u = B t u := by
        simp [hNdef, Matrix.add_apply, Matrix.smul_apply,
          Matrix.one_apply_ne (Ne.symm (Finset.mem_erase.1 hu).1)]
      rw [this]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ t), Finset.sum_congr rfl hNo, hNd,
      abs_of_nonneg (by linarith [hγge t])]
    linarith [hrow t]
  have hNnorm : ‖N‖ ≤ γ := linfty_opNorm_le_of_row_sum_le N hNrow
  have hdecomp : s • M = (s * (c - γ)) • (1 : Matrix n n ℝ) + s • N := by
    rw [hNdef, hBdef]
    ext t u
    simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]
    ring
  have hcomm : Commute ((s * (c - γ)) • (1 : Matrix n n ℝ)) (s • N) :=
    ((Commute.one_left N).smul_left (s * (c - γ))).smul_right s
  rw [hdecomp, Matrix.exp_add_of_commute _ _ hcomm, exp_smul_one, Matrix.smul_mul, one_mul,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
  have hsN : ‖s • N‖ ≤ s * γ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs]
    exact mul_le_mul_of_nonneg_left hNnorm hs
  calc Real.exp (s * (c - γ)) * ‖NormedSpace.exp (s • N)‖
      ≤ Real.exp (s * (c - γ)) * Real.exp ‖s • N‖ := by
        exact mul_le_mul_of_nonneg_left (norm_exp_le _) (Real.exp_nonneg _)
    _ ≤ Real.exp (s * (c - γ)) * Real.exp (s * γ) := by
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hsN) (Real.exp_nonneg _)
    _ = Real.exp (s * c) := by
        rw [← Real.exp_add]
        ring_nf

end General

variable {i j : ℕ} {θA θB ρ lam : ℝ}

theorem bigS_sub_min_nonneg (i j : ℕ) :
    0 ≤ bigS (i : ℝ) (j : ℝ) - ((min i j : ℕ) : ℝ) * (((min i j : ℕ) : ℝ) - 1) := by
  have h := slack_row_nonneg (i := i) (j := j) (⟨min i j, Nat.lt_succ_self _⟩)
  have he : slack (i : ℝ) (j : ℝ) ((min i j : ℕ) : ℝ)
      = bigS (i : ℝ) (j : ℝ) - ((min i j : ℕ) : ℝ) * (((min i j : ℕ) : ℝ) - 1) :=
    slack_eq_closed _ _ _
  rw [he] at h
  exact h

theorem norm_exp_neg_smul_Te_le (hlam : 0 < lam) (hρ : 0 ≤ ρ) {s : ℝ} (hs : 0 ≤ s) :
    ‖NormedSpace.exp (s • (-Te i j lam θA θB ρ))‖
      ≤ Real.exp (-(s * (floorMu i j θA θB
          + (bigS (i : ℝ) (j : ℝ)
            - ((min i j : ℕ) : ℝ) * (((min i j : ℕ) : ℝ) - 1)) / lam))) := by
  have hmeas := norm_exp_smul_le_of_row_measure_le (-Te i j lam θA θB ρ) hs
    (neg_Te_row_measure_le (i := i) (j := j) (θA := θA) (θB := θB) hlam hρ)
  refine le_trans hmeas (le_of_eq ?_)
  congr 1
  ring

theorem norm_exp_neg_smul_Te_le_floor (hlam : 0 < lam) (hρ : 0 ≤ ρ) {s : ℝ} (hs : 0 ≤ s) :
    ‖NormedSpace.exp (s • (-Te i j lam θA θB ρ))‖ ≤ Real.exp (-(s * floorMu i j θA θB)) := by
  refine le_trans (norm_exp_neg_smul_Te_le hlam hρ hs) (Real.exp_le_exp.2 ?_)
  have h1 : 0 ≤ (bigS (i : ℝ) (j : ℝ)
      - ((min i j : ℕ) : ℝ) * (((min i j : ℕ) : ℝ) - 1)) / lam :=
    div_nonneg (bigS_sub_min_nonneg i j) hlam.le
  nlinarith [hs, h1]

theorem norm_prod_exp_neg_smul_Te_le {E : ℕ} (lamf θAf θBf ρf sf : Fin E → ℝ)
    (hlam : ∀ e, 0 < lamf e) (hρ : ∀ e, 0 ≤ ρf e) (hs : ∀ e, 0 ≤ sf e) :
    ‖(List.ofFn fun e =>
        NormedSpace.exp (sf e • (-Te i j (lamf e) (θAf e) (θBf e) (ρf e)))).prod‖
      ≤ ∏ e, Real.exp (-(sf e * floorMu i j (θAf e) (θBf e))) := by
  refine le_trans (List.norm_prod_le _) ?_
  rw [List.map_ofFn, List.prod_ofFn]
  refine Finset.prod_le_prod₀ (fun e _ => norm_nonneg _) fun e _ => ?_
  exact norm_exp_neg_smul_Te_le_floor (hlam e) (hρ e) (hs e)

end Rhone.LinearAlgebra.Spectral
