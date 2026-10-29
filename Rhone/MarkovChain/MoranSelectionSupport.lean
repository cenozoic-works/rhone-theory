/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.FixationHarmonic
public import Mathlib.Tactic.LinearCombination

/-!
# Selected Moran finite Green summands

Source: ewens2004, sec. 3.4; altrock_traulsen2009, eq. (14). -/

@[expose] public section
namespace Rhone.MarkovChain

open Finset

/-- Source: ewens2004, sec. 3.4. -/
noncomputable def moranGeomSum (r : ℝ) (i : ℕ) : ℝ := ∑ k ∈ range i, (r⁻¹) ^ k

/-- Source: altrock_traulsen2009, eq. (14). -/
noncomputable def moranSelectionGreen (N : ℕ) (r : ℝ) (i j : ℕ) : ℝ :=
  moranFixProb N r (min i j) * (moranGeomSum r N - moranGeomSum r (max i j)) /
    (moranUp N r j * (r⁻¹) ^ j)

namespace MoranSelectionSupport

/-- Source: ewens2004, sec. 3.4. -/
theorem geom_pos {N : ℕ} (hN : 0 < N) {r : ℝ} (hr : 0 < r) :
    0 < moranGeomSum r N := by
  unfold moranGeomSum
  apply sum_pos (fun k _ => by positivity)
  exact ⟨0, mem_range.mpr hN⟩

/-- Source: ewens2004, sec. 3.4. -/
theorem geom_succ (r : ℝ) (i : ℕ) :
    moranGeomSum r (i + 1) = moranGeomSum r i + (r⁻¹) ^ i := by
  exact sum_range_succ _ _

/-- Source: ewens2004, sec. 3.4. -/
theorem geom_eq_fix {N : ℕ} (hN : 0 < N) {r : ℝ} (hr : 0 < r) (i : ℕ) :
    moranGeomSum r i = moranFixProb N r i * moranGeomSum r N := by
  have hs := (geom_pos hN hr).ne'
  change moranGeomSum r i = (moranGeomSum r i / moranGeomSum r N) * moranGeomSum r N
  rw [div_mul_cancel₀ _ hs]

/-- Source: ewens2004, sec. 3.4. -/
theorem power_balance {N i : ℕ} {r : ℝ} (hr : 0 < r) (hi : 0 < i) :
    moranUp N r i * (r⁻¹) ^ i = moranDown N r i * (r⁻¹) ^ (i - 1) := by
  have he : i = (i - 1) + 1 := by omega
  have hp : r * (r⁻¹) ^ i = (r⁻¹) ^ (i - 1) := by
    conv_lhs => rw [he, pow_succ]
    rw [mul_left_comm, mul_inv_cancel₀ hr.ne', mul_one]
  rw [moranUp_eq_mul_moranDown, mul_assoc, mul_comm (moranDown N r i), ← mul_assoc, hp]
  ring

/-- Source: ewens2004, sec. 3.4. -/
theorem fix_flux {N i : ℕ} {r : ℝ} (hr : 0 < r) (hi : i < N) :
    moranUp N r i * (moranFixProb N r (i + 1) - moranFixProb N r i) +
    moranDown N r i * (moranFixProb N r (i - 1) - moranFixProb N r i) = 0 := by
  have h := moranFixProb_isHarmonic (N := N) hr ⟨i, by omega⟩
  rw [moran_expect (moranFixProb N r)] at h
  linarith

/-- Source: ewens2004, sec. 3.4. -/
theorem green_lower (N : ℕ) (r : ℝ) {i j : ℕ} (hij : i ≤ j) :
    moranSelectionGreen N r i j = moranFixProb N r i *
      ((moranGeomSum r N - moranGeomSum r j) / (moranUp N r j * (r⁻¹) ^ j)) := by
  simp only [moranSelectionGreen, min_eq_left hij, max_eq_right hij]
  ring

/-- Source: ewens2004, sec. 3.4. -/
theorem green_upper {N : ℕ} (hN : 0 < N) {r : ℝ} (hr : 0 < r)
    {i j : ℕ} (hji : j ≤ i) :
    moranSelectionGreen N r i j = (1 - moranFixProb N r i) *
      (moranFixProb N r j * moranGeomSum r N / (moranUp N r j * (r⁻¹) ^ j)) := by
  simp only [moranSelectionGreen, min_eq_right hji, max_eq_left hji]
  rw [geom_eq_fix hN hr i]
  ring

/-- Source: ewens2004, sec. 3.4. -/
theorem green_poisson {N i j : ℕ} {r : ℝ} (hr : 0 < r)
    (hi0 : 0 < i) (hiN : i < N) (hj0 : 0 < j) (hjN : j < N) :
    moranUp N r i * (moranSelectionGreen N r (i + 1) j - moranSelectionGreen N r i j) +
    moranDown N r i * (moranSelectionGreen N r (i - 1) j - moranSelectionGreen N r i j) =
      if j = i then -1 else 0 := by
  have hN : 0 < N := lt_trans hi0 hiN
  have hf := fix_flux hr hiN
  rcases lt_trichotomy i j with hij | hij | hij
  · simp only [green_lower N r (by omega : i + 1 ≤ j),
      green_lower N r (by omega : i - 1 ≤ j), green_lower N r hij.le]
    have hji : j ≠ i := by omega
    rw [ite_eq_right hji]
    calc
      _ = ((moranGeomSum r N - moranGeomSum r j) / (moranUp N r j * (r⁻¹) ^ j)) *
          (moranUp N r i * (moranFixProb N r (i + 1) - moranFixProb N r i) +
          moranDown N r i * (moranFixProb N r (i - 1) - moranFixProb N r i)) := by ring
      _ = 0 := by rw [hf]; ring
  · subst j
    have hs := (geom_pos hN hr).ne'
    have hp : 0 < moranUp N r i := by
      have hi : (0 : ℝ) < i := by exact_mod_cast hi0
      have hd : (0 : ℝ) < (N : ℝ) - i := by
        have : (i : ℝ) < N := by exact_mod_cast hiN
        linarith
      unfold moranUp
      positivity
    have hd : moranUp N r i * (r⁻¹) ^ i ≠ 0 := by positivity
    have hpre : moranGeomSum r i = moranGeomSum r (i - 1) + (r⁻¹) ^ (i - 1) := by
      have he : i = (i - 1) + 1 := by omega
      conv_lhs => rw [he, geom_succ]
    have hbal := power_balance (N := N) hr hi0
    have h1 : i ≤ i + 1 := by omega
    have h2 : i - 1 ≤ i := by omega
    simp only [moranSelectionGreen, min_eq_right h1, max_eq_left h1,
      min_eq_left h2, max_eq_right h2, min_self, max_self, ite_true]
    change moranUp N r i *
      (moranFixProb N r i * (moranGeomSum r N - moranGeomSum r (i + 1)) /
       (moranUp N r i * (r⁻¹) ^ i) -
       moranFixProb N r i * (moranGeomSum r N - moranGeomSum r i) /
       (moranUp N r i * (r⁻¹) ^ i)) +
      moranDown N r i *
      (moranFixProb N r (i - 1) * (moranGeomSum r N - moranGeomSum r i) /
       (moranUp N r i * (r⁻¹) ^ i) -
       moranFixProb N r i * (moranGeomSum r N - moranGeomSum r i) /
       (moranUp N r i * (r⁻¹) ^ i)) = -1
    have hfix : ∀ k, moranFixProb N r k = moranGeomSum r k / moranGeomSum r N := fun _ => rfl
    simp only [hfix, geom_succ, hpre]
    field_simp [hs, hd]
    linear_combination (moranGeomSum r N -
      (moranGeomSum r (i - 1) + (r⁻¹) ^ (i - 1))) * hbal
  · simp only [green_upper hN hr (by omega : j ≤ i + 1),
      green_upper hN hr (by omega : j ≤ i - 1), green_upper hN hr hij.le]
    have hji : j ≠ i := by omega
    rw [ite_eq_right hji]
    calc
      _ = -(moranFixProb N r j * moranGeomSum r N / (moranUp N r j * (r⁻¹) ^ j)) *
          (moranUp N r i * (moranFixProb N r (i + 1) - moranFixProb N r i) +
          moranDown N r i * (moranFixProb N r (i - 1) - moranFixProb N r i)) := by ring
      _ = 0 := by rw [hf]; ring

end MoranSelectionSupport
end Rhone.MarkovChain
