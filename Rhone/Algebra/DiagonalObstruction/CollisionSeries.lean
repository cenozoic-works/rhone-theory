/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.RecombinationExpansion.Usmani
public import Rhone.Algebra.DiagonalObstruction.CollisionCoefficient
public import Rhone.Algebra.DiagonalObstruction.CollisionContinuant

/-! # Constant fibres and path products for the continuant collision argument -/

@[expose] public section

namespace Rhone.Algebra.DiagonalObstruction

open PowerSeries LinearAlgebra.Tridiag LinearAlgebra.RecombinationExpansion

variable {R : Type*} [CommRing R]

theorem constantCoeff_cont_of_lower_zero (d b c : ℕ → R⟦X⟧)
    (hc : ∀ t, constantCoeff (c t) = 0) (n : ℕ) :
    constantCoeff (cont d b c n) =
      ∏ t ∈ Finset.range n, constantCoeff (d t) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp [cont]
    | 1 => simp [cont]
    | k + 2 =>
      simp only [cont, map_sub, map_mul, hc, mul_zero, zero_mul, sub_zero]
      rw [ih (k + 1) (by omega)]
      conv_rhs => rw [Finset.prod_range_succ]
      ring

theorem constantCoeff_Qc_of_lower_zero (d b c : ℕ → R⟦X⟧)
    (hc : ∀ t, constantCoeff (c t) = 0) {n s : ℕ} (hs : s ≤ n) :
    constantCoeff (Qc d b c n s) =
      ∏ t ∈ Finset.range (n - s), constantCoeff (d (t + s)) := by
  rw [Qc_of_le d b c hs, tridFrom_eq_trid_shift, det_trid_eq_cont]
  exact constantCoeff_cont_of_lower_zero _ _ _ (fun t => hc (t + s)) _

theorem runProd_extract_X (b c : ℕ → R⟦X⟧) (i j : ℕ) :
    runProd (fun t => b t * (X * c t)) i j =
      X ^ (j - i) * runProd (fun t => b t * c t) i j := by
  simp only [runProd, mul_left_comm (b _) X, Finset.prod_mul_distrib,
    Finset.prod_const, Nat.card_Ico]

theorem isUnit_constantCoeff_runProd (b c : ℕ → R⟦X⟧) (i j : ℕ)
    (hb : ∀ t ∈ Finset.Ico i j, IsUnit (constantCoeff (b t)))
    (hc : ∀ t ∈ Finset.Ico i j, IsUnit (constantCoeff (c t))) :
    IsUnit (constantCoeff (runProd (fun t => b t * c t) i j)) := by
  simp only [runProd, map_prod, map_mul]
  exact IsUnit.prod_iff.mpr (fun t ht => (hb t ht).mul (hc t ht))

noncomputable def spectralSeriesDiagonal (a v : ℕ → R) (z : R⟦X⟧) (t : ℕ) : R⟦X⟧ :=
  z - C (a t) + X * C (v t)

@[simp]
theorem constantCoeff_spectralSeriesDiagonal (a v : ℕ → R) (z : R⟦X⟧) (t : ℕ) :
    constantCoeff (spectralSeriesDiagonal a v z t) = constantCoeff z - a t := by
  simp [spectralSeriesDiagonal]

theorem constantCoeff_spectral_cont (a v b c : ℕ → R) (z : R⟦X⟧) (n : ℕ) :
    constantCoeff (cont (spectralSeriesDiagonal a v z)
      (fun t => C (b t)) (fun t => X * C (c t)) n) =
      ∏ t ∈ Finset.range n, (constantCoeff z - a t) := by
  rw [constantCoeff_cont_of_lower_zero _ _ _ (by simp)]
  simp only [constantCoeff_spectralSeriesDiagonal]

theorem constantCoeff_spectral_Qc (a v b c : ℕ → R) (z : R⟦X⟧)
    {n s : ℕ} (hs : s ≤ n) :
    constantCoeff (Qc (spectralSeriesDiagonal a v z)
      (fun t => C (b t)) (fun t => X * C (c t)) n s) =
      ∏ t ∈ Finset.range (n - s), (constantCoeff z - a (t + s)) := by
  rw [constantCoeff_Qc_of_lower_zero _ _ _ (by simp) hs]
  simp only [constantCoeff_spectralSeriesDiagonal]

theorem isUnit_constantCoeff_spectral_cont (a v b c : ℕ → R) (z : R⟦X⟧) (n : ℕ)
    (hu : ∀ t < n, IsUnit (constantCoeff z - a t)) :
    IsUnit (constantCoeff (cont (spectralSeriesDiagonal a v z)
      (fun t => C (b t)) (fun t => X * C (c t)) n)) := by
  rw [constantCoeff_spectral_cont]
  exact IsUnit.prod_iff.mpr (fun t ht => hu t (Finset.mem_range.mp ht))

theorem isUnit_constantCoeff_spectral_Qc (a v b c : ℕ → R) (z : R⟦X⟧)
    {n s : ℕ} (hs : s ≤ n)
    (hu : ∀ t, s ≤ t → t < n → IsUnit (constantCoeff z - a t)) :
    IsUnit (constantCoeff (Qc (spectralSeriesDiagonal a v z)
      (fun t => C (b t)) (fun t => X * C (c t)) n s)) := by
  rw [constantCoeff_spectral_Qc a v b c z hs]
  apply IsUnit.prod_iff.mpr
  intro t ht
  have ht' : t < n - s := Finset.mem_range.mp ht
  exact hu (t + s) (by omega) (by omega)

theorem constantCoeff_spectral_Qc_ne_zero [IsDomain R]
    (a v b c : ℕ → R) (z : R⟦X⟧) {n s : ℕ} (hs : s ≤ n)
    (hu : ∀ t, s ≤ t → t < n → constantCoeff z - a t ≠ 0) :
    constantCoeff (Qc (spectralSeriesDiagonal a v z)
      (fun t => C (b t)) (fun t => X * C (c t)) n s) ≠ 0 := by
  rw [constantCoeff_spectral_Qc a v b c z hs]
  apply Finset.prod_ne_zero_iff.mpr
  intro t ht
  have ht' : t < n - s := Finset.mem_range.mp ht
  exact hu (t + s) (by omega) (by omega)

theorem not_isUnit_constantCoeff_spectral_Qc
    (a v b c : ℕ → R) (z : R⟦X⟧) {n s j : ℕ}
    (hsj : s ≤ j) (hjn : j < n)
    (hj : ¬ IsUnit (constantCoeff z - a j)) :
    ¬ IsUnit (constantCoeff (Qc (spectralSeriesDiagonal a v z)
      (fun t => C (b t)) (fun t => X * C (c t)) n s)) := by
  rw [constantCoeff_spectral_Qc a v b c z (by omega)]
  intro hu
  have hmem : j - s ∈ Finset.range (n - s) := Finset.mem_range.mpr (by omega)
  have ht := IsUnit.prod_iff.mp hu (j - s) hmem
  exact hj (by simpa only [Nat.sub_add_cancel hsj] using ht)

theorem isUnit_constantCoeff_spectral_path
    (a v b c : ℕ → R) (z : R⟦X⟧) {n i j : ℕ} (hjn : j < n)
    (hb : ∀ t ∈ Finset.Ico i j, IsUnit (b t))
    (hc : ∀ t ∈ Finset.Ico i j, IsUnit (c t))
    (hl : ∀ t < i, IsUnit (constantCoeff z - a t))
    (hr : ∀ t, j < t → t < n → IsUnit (constantCoeff z - a t)) :
    IsUnit (constantCoeff
      (runProd (fun t => C (b t) * C (c t)) i j *
        cont (spectralSeriesDiagonal a v z)
          (fun t => C (b t)) (fun t => X * C (c t)) i *
        Qc (spectralSeriesDiagonal a v z)
          (fun t => C (b t)) (fun t => X * C (c t)) n (j + 1))) := by
  simp only [map_mul]
  apply IsUnit.mul
  · apply IsUnit.mul
    · exact isUnit_constantCoeff_runProd _ _ i j
        (by simpa only [constantCoeff_C] using hb)
        (by simpa only [constantCoeff_C] using hc)
    · exact isUnit_constantCoeff_spectral_cont a v b c z i hl
  · exact isUnit_constantCoeff_spectral_Qc a v b c z (by omega)
      (fun t ht hn => hr t (by omega) hn)

theorem no_spectral_continuant_root_of_isolated_gap [IsDomain R]
    (a v b c : ℕ → R) (z : R⟦X⟧) {n i j : ℕ}
    (hij : i < j) (hjn : j < n) (hz : constantCoeff z = a i)
    (hne : ∀ t < n, t ≠ i → a i - a t ≠ 0)
    (hgap : ¬ IsUnit (a i - a j))
    (houtside : ∀ t < n, t ≠ i → t ≠ j → IsUnit (a i - a t))
    (hb : ∀ t ∈ Finset.Ico i j, IsUnit (b t))
    (hc : ∀ t ∈ Finset.Ico i j, IsUnit (c t)) :
    cont (spectralSeriesDiagonal a v z)
      (fun t => C (b t)) (fun t => X * C (c t)) n ≠ 0 := by
  intro hzero
  let d := spectralSeriesDiagonal a v z
  let B : ℕ → R⟦X⟧ := fun t => C (b t)
  let Cc : ℕ → R⟦X⟧ := fun t => X * C (c t)
  let P := runProd (fun t => C (b t) * C (c t)) i j
  have hid := cont_mul_interval_eq d B Cc hij hjn
  change cont d B Cc n = 0 at hzero
  rw [hzero, zero_mul] at hid
  have hpath : runProd (fun t => B t * Cc t) i j = X ^ (j - i) * P :=
    runProd_extract_X _ _ i j
  rw [hpath] at hid
  have he : cont d B Cc j * Qc d B Cc n (i + 1) =
      X ^ (j - i) * (P * cont d B Cc i * Qc d B Cc n (j + 1)) := by
    calc
      _ = (X ^ (j - i) * P) * cont d B Cc i * Qc d B Cc n (j + 1) :=
        sub_eq_zero.mp hid.symm
      _ = _ := by ring
  apply no_collision_product_over_domain
    (cont d B Cc j) (Qc d B Cc n (i + 1))
    (P * cont d B Cc i * Qc d B Cc n (j + 1)) (j - i) ?_ ?_ ?_ he
  · apply constantCoeff_spectral_Qc_ne_zero a v b c z (by omega)
    intro t hit htn
    rw [hz]
    exact hne t htn (by omega)
  · apply not_isUnit_constantCoeff_spectral_Qc a v b c z (by omega) hjn
    simpa only [hz] using hgap
  · apply isUnit_constantCoeff_spectral_path a v b c z hjn hb hc
    · intro t hti
      rw [hz]
      exact houtside t (by omega) (by omega) (by omega)
    · intro t hjt htn
      rw [hz]
      exact houtside t htn (by omega) (by omega)

theorem constantCoeff_spectral_cont_ne_zero [IsDomain R]
    (a v b c : ℕ → R) (z : R⟦X⟧) (n : ℕ)
    (hu : ∀ t < n, constantCoeff z - a t ≠ 0) :
    constantCoeff (cont (spectralSeriesDiagonal a v z)
      (fun t => C (b t)) (fun t => X * C (c t)) n) ≠ 0 := by
  rw [constantCoeff_spectral_cont]
  exact Finset.prod_ne_zero_iff.mpr (fun t ht => hu t (Finset.mem_range.mp ht))

theorem not_isUnit_constantCoeff_spectral_cont
    (a v b c : ℕ → R) (z : R⟦X⟧) {n i : ℕ} (hin : i < n)
    (hi : ¬ IsUnit (constantCoeff z - a i)) :
    ¬ IsUnit (constantCoeff (cont (spectralSeriesDiagonal a v z)
      (fun t => C (b t)) (fun t => X * C (c t)) n)) := by
  rw [constantCoeff_spectral_cont]
  intro hu
  exact hi (IsUnit.prod_iff.mp hu i (Finset.mem_range.mpr hin))

theorem no_spectral_continuant_root_of_isolated_gap_right [IsDomain R]
    (a v b c : ℕ → R) (z : R⟦X⟧) {n i j : ℕ}
    (hij : i < j) (hjn : j < n) (hz : constantCoeff z = a j)
    (hne : ∀ t < n, t ≠ j → a j - a t ≠ 0)
    (hgap : ¬ IsUnit (a j - a i))
    (houtside : ∀ t < n, t ≠ i → t ≠ j → IsUnit (a j - a t))
    (hb : ∀ t ∈ Finset.Ico i j, IsUnit (b t))
    (hc : ∀ t ∈ Finset.Ico i j, IsUnit (c t)) :
    cont (spectralSeriesDiagonal a v z)
      (fun t => C (b t)) (fun t => X * C (c t)) n ≠ 0 := by
  intro hzero
  let d := spectralSeriesDiagonal a v z
  let B : ℕ → R⟦X⟧ := fun t => C (b t)
  let Cc : ℕ → R⟦X⟧ := fun t => X * C (c t)
  let P := runProd (fun t => C (b t) * C (c t)) i j
  have hid := cont_mul_interval_eq d B Cc hij hjn
  change cont d B Cc n = 0 at hzero
  rw [hzero, zero_mul] at hid
  have hpath : runProd (fun t => B t * Cc t) i j = X ^ (j - i) * P :=
    runProd_extract_X _ _ i j
  rw [hpath] at hid
  have he : Qc d B Cc n (i + 1) * cont d B Cc j =
      X ^ (j - i) * (P * cont d B Cc i * Qc d B Cc n (j + 1)) := by
    calc
      _ = cont d B Cc j * Qc d B Cc n (i + 1) := mul_comm _ _
      _ = (X ^ (j - i) * P) * cont d B Cc i * Qc d B Cc n (j + 1) :=
        sub_eq_zero.mp hid.symm
      _ = _ := by ring
  apply no_collision_product_over_domain
    (Qc d B Cc n (i + 1)) (cont d B Cc j)
    (P * cont d B Cc i * Qc d B Cc n (j + 1)) (j - i) ?_ ?_ ?_ he
  · apply constantCoeff_spectral_cont_ne_zero a v b c z j
    intro t htj
    rw [hz]
    exact hne t (by omega) (by omega)
  · apply not_isUnit_constantCoeff_spectral_cont a v b c z hij
    simpa only [hz] using hgap
  · apply isUnit_constantCoeff_spectral_path a v b c z hjn hb hc
    · intro t hti
      rw [hz]
      exact houtside t (by omega) (by omega) (by omega)
    · intro t hjt htn
      rw [hz]
      exact houtside t htn (by omega) (by omega)

end Rhone.Algebra.DiagonalObstruction
