/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum

public import Rhone.Statistics.Breeder

/-!
# Finite multivariate selection regression

Source: lande_arnold1983, pp. 1212–1213, eq. (4), (6c), p. 1217, eq. (16)–(17); svensson2023, p.
1494; lande1979, p. 406, eq. (6)–(7b). -/

@[expose] public section

namespace Rhone.Statistics

/-- Source: lande_arnold1983, p. 1212; svensson2023, p. 1494. -/
noncomputable def phenotypeCovariance {ι κ : Type*} [Fintype ι]
    (z : ι → κ → ℝ) (j k : κ) : ℝ :=
  popCov (fun i => z i j) (fun i => z i k)

/-- Source: lande_arnold1983, p. 1217, eq. (16); svensson2023, p. 1494. -/
noncomputable def selectionResidual {ι κ : Type*} [Fintype ι] [Fintype κ]
    (w : ι → ℝ) (z : ι → κ → ℝ) (β : κ → ℝ) (i : ι) : ℝ :=
  w i / popMean w - 1 - ∑ k, β k * (z i k - popMean (fun i => z i k))

private theorem mean_mul {ι : Type*} [Fintype ι] (c : ℝ) (f : ι → ℝ) :
    popMean (fun i => c * f i) = c * popMean f := by
  simp only [popMean, ← Finset.mul_sum]
  ring

private theorem mean_sum {ι κ : Type*} [Fintype ι] [Fintype κ] (f : κ → ι → ℝ) :
    popMean (fun i => ∑ k, f k i) = ∑ k, popMean (f k) := by
  simp only [popMean, Finset.sum_div]
  rw [Finset.sum_comm]

private theorem cov_affine {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]
    (f : ι → ℝ) (g : κ → ι → ℝ) (c : ℝ) (b : κ → ℝ) :
    popCov f (fun i => c + ∑ k, b k * g k i) = ∑ k, b k * popCov f (g k) := by
  have hc : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hconst : popMean (fun _ : ι => c) = c := by simp [popMean, hc]
  simp only [popCov, mul_add, popMean_add, mean_sum]
  rw [hconst]
  have hprod : (fun i => f i * c) = (fun i => c * f i) := by funext i; ring
  rw [hprod, mean_mul]
  have hsum : (fun i => f i * ∑ k, b k * g k i) =
      (fun i => ∑ k, b k * (f i * g k i)) := by
    funext i
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hsum, mean_sum]
  simp only [mean_mul, Finset.mul_sum]
  ring_nf
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Source: lande_arnold1983, p. 1217, eq. (17); svensson2023, p. 1494. -/
theorem selection_gradient_normal_equation
    {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]
    (w : ι → ℝ) (z : ι → κ → ℝ) (β : κ → ℝ)
    (hw : popMean w ≠ 0)
    (horth : ∀ j, popCov (fun i => z i j) (selectionResidual w z β) = 0) :
    ∀ j, ∑ k, phenotypeCovariance z j k * β k =
      selectionDifferential w (fun i => z i j) := by
  intro j
  have h : (fun i => w i / popMean w) =
      (fun i => 1 - ∑ k, β k * popMean (fun i => z i k) +
        ∑ k, β k * z i k + selectionResidual w z β i) := by
    funext i
    simp only [selectionResidual, mul_sub, Finset.sum_sub_distrib]
    ring
  have hcov : popCov (fun i => z i j) (fun i => w i / popMean w) =
      ∑ k, β k * phenotypeCovariance z j k := by
    rw [h]
    have hadd : popCov (fun i => z i j)
        (fun i => (1 - ∑ k, β k * popMean (fun i => z i k) +
          ∑ k, β k * z i k) + selectionResidual w z β i) =
        popCov (fun i => z i j)
          (fun i => 1 - ∑ k, β k * popMean (fun i => z i k) + ∑ k, β k * z i k) +
        popCov (fun i => z i j) (selectionResidual w z β) := by
      simp only [popCov, mul_add, popMean_add]
      ring
    rw [hadd, horth j, add_zero, cov_affine]
    rfl
  have hscale : popCov (fun i => z i j) (fun i => w i / popMean w) =
      popCov w (fun i => z i j) / popMean w := by
    rw [popCov_comm]
    have hdiv (f : ι → ℝ) (c : ℝ) :
        popMean (fun i => f i / c) = popMean f / c := by
      simp only [popMean, ← Finset.sum_div]
      ring
    simp only [popCov, div_mul_eq_mul_div, hdiv]
    ring
  rw [hscale] at hcov
  rw [selectionDifferential, robertson_price w (fun i => z i j) hw, hcov]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Source: lande1979, p. 406, eq. (7a). -/
theorem multivariate_breeder_equation
    {ι κ η : Type*} [Fintype ι] [Fintype κ]
    (w : ι → ℝ) (m : ι → κ → ℝ) (o : ι → η → ℝ)
    (a : η → ℝ) (B : η → κ → ℝ)
    (hw : popMean w ≠ 0)
    (hlin : ∀ i j, o i j = a j + ∑ k, B j k * m i k) :
    ∀ j, selectionResponse w (fun i => o i j) =
      ∑ k, B j k * selectionDifferential w (fun i => m i k) := by
  intro j
  have hc : (Fintype.card ι : ℝ) ≠ 0 := by
    intro hc
    apply hw
    simp [popMean, hc]
  have hconst : popMean (fun _ : ι => a j) = a j := by simp [popMean, hc]
  have ho : (fun i => o i j) = (fun i => a j + ∑ k, B j k * m i k) :=
    funext (fun i => hlin i j)
  rw [selectionResponse, ho]
  simp only [nextMean, popMean_add, mean_sum, mean_mul]
  rw [hconst]
  have hprod : (fun i => w i * (a j + ∑ k, B j k * m i k)) =
      (fun i => a j * w i + ∑ k, B j k * (w i * m i k)) := by
    funext i
    simp only [mul_add, Finset.mul_sum]
    congr 1
    · ring
    · apply Finset.sum_congr rfl; intro k _; ring
  rw [hprod, popMean_add, mean_mul, mean_sum]
  simp only [mean_mul, selectionDifferential, nextMean]
  rw [add_div, mul_div_cancel_right₀ _ hw, Finset.sum_div]
  simp only [mul_sub, mul_div_assoc]
  ring_nf
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

end Rhone.Statistics
