/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.EffectiveSize
public import Rhone.MarkovChain.CanningsFourthMoment
public import Rhone.MarkovChain.VaryingSizeVarianceEffective

/-!
# Variance effective size of a Cannings model

Source: ewens2004, sec. 3.3, sec. 3.7; cannings1974, sec. 3, p. 266. -/

@[expose] public section

namespace Rhone.MarkovChain.CanningsModel

variable {N : ℕ} {Ω : Type*} [Fintype Ω]

/-- Source: ewens2004, sec. 3.3; cannings1974, sec. 3, p. 266. -/
theorem countChain_frequency_variance (M : CanningsModel N Ω) (k : Fin N)
    (i : Fin (N + 1)) :
    M.countChain.expect (fun j => ((j : ℝ) / N - (i : ℝ) / N) ^ 2) i =
      M.offspringVariance k / ((N : ℝ) - 1) * ((i : ℝ) / N) * (1 - (i : ℝ) / N) := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Fin.pos k).ne'
  have hscale : (fun j : Fin (N + 1) => ((j : ℝ) / N - (i : ℝ) / N) ^ 2) =
      fun j : Fin (N + 1) => (1 / (N : ℝ) ^ 2) * (((j : ℝ) - i) ^ 2) := by
    funext j
    rw [div_sub_div_same, div_pow]
    ring
  rw [hscale]
  have h := M.countChain_expect_sq_increment k i
  change M.countKernel.expect (fun j => ((j : ℝ) - i) ^ 2) i = _ at h
  change M.countKernel.expect (fun j => (1 / (N : ℝ) ^ 2) * (((j : ℝ) - i) ^ 2)) i = _
  rw [CountKernel.expect_const_mul, h]
  have e : (1 : ℝ) - (i : ℝ) / N = ((N : ℝ) - i) / N := by
    rw [sub_div, div_self hN]
  rw [e]
  ring

end Rhone.MarkovChain.CanningsModel

namespace Rhone.MarkovChain.EffectiveSize

variable {N : ℕ} {Ω : Type*} [Fintype Ω]

private theorem mul_div_two_mul_div_mul_mul {p q s a : ℝ} (hpq : p * q ≠ 0) :
    p * q / (2 * (s / a * p * q)) = a / (2 * s) := by
  have h1 : 2 * (s / a * p * q) = p * q * (2 * s) / a := by ring
  rw [h1, div_div_eq_mul_div, mul_div_mul_left _ _ hpq]

private theorem mul_div_div_mul_mul {p q s a : ℝ} (hpq : p * q ≠ 0) :
    p * q / (s / a * p * q) = a / s := by
  have h1 : s / a * p * q = p * q * s / a := by ring
  rw [h1, div_div_eq_mul_div, mul_div_mul_left _ _ hpq]

private theorem interior_freq_mul_ne_zero {i N : ℕ} (hi0 : 0 < i) (hi1 : i < N) :
    ((i : ℝ) / N) * (1 - (i : ℝ) / N) ≠ 0 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hi0' : (0 : ℝ) < i := by exact_mod_cast hi0
  have hi1' : (i : ℝ) < N := by exact_mod_cast hi1
  have hp0 : (0 : ℝ) < (i : ℝ) / N := div_pos hi0' hN
  have hp1 : (i : ℝ) / N < 1 := (div_lt_one hN).mpr hi1'
  exact (mul_pos hp0 (by linarith)).ne'

/-- Source: ewens2004, secs. 3.3, 3.7. -/
theorem variance_effective_cannings (M : CanningsModel N Ω) (k : Fin N)
    (i : Fin (N + 1)) (hi0 : 0 < i.val) (hi1 : i.val < N) :
    varianceEffective ((i : ℝ) / N)
        (M.countChain.expect (fun j => ((j : ℝ) / N - (i : ℝ) / N) ^ 2) i) =
      ((N : ℝ) - 1) / (2 * M.offspringVariance k) := by
  rw [M.countChain_frequency_variance k i]
  unfold varianceEffective
  exact mul_div_two_mul_div_mul_mul (interior_freq_mul_ne_zero hi0 hi1)

/-- Source: ewens2004, secs. 3.3, 3.7. -/
theorem haploid_variance_effective_cannings (M : CanningsModel N Ω) (k : Fin N)
    (i : Fin (N + 1)) (hi0 : 0 < i.val) (hi1 : i.val < N) :
    Rhone.MarkovChain.haploidVarianceEffective ((i : ℝ) / N)
        (M.countChain.expect (fun j => ((j : ℝ) / N - (i : ℝ) / N) ^ 2) i) =
      ((N : ℝ) - 1) / M.offspringVariance k := by
  rw [M.countChain_frequency_variance k i]
  unfold Rhone.MarkovChain.haploidVarianceEffective
  exact mul_div_div_mul_mul (interior_freq_mul_ne_zero hi0 hi1)

/-- Source: ewens2004, sec. 3.7. -/
theorem variance_effective_cannings_eq_eigenvalue (M : CanningsModel N Ω) (k : Fin N)
    (i : Fin (N + 1)) (hi0 : 0 < i.val) (hi1 : i.val < N) :
    varianceEffective ((i : ℝ) / N)
        (M.countChain.expect (fun j => ((j : ℝ) / N - (i : ℝ) / N) ^ 2) i) =
      eigenvalueEffective (1 - M.offspringVariance k / ((N : ℝ) - 1)) := by
  rw [variance_effective_cannings M k i hi0 hi1]
  unfold eigenvalueEffective coalescenceEffective
  rw [sub_sub_cancel, mul_div_assoc', one_div_div]

/-- Source: ewens2004, secs. 3.3, 3.7. -/
theorem variance_effective_cannings_wf {N : ℕ} (hN : 0 < N)
    (i : Fin (2 * N + 1)) (hi0 : 0 < i.val) (hi1 : i.val < 2 * N) :
    varianceEffective ((i : ℝ) / ((2 * N : ℕ) : ℝ))
        ((wfModel (2 * N)).countChain.expect
          (fun j => ((j : ℝ) / ((2 * N : ℕ) : ℝ) - (i : ℝ) / ((2 * N : ℕ) : ℝ)) ^ 2) i) =
      (N : ℝ) := by
  have k : Fin (2 * N) := ⟨0, by omega⟩
  rw [variance_effective_cannings (wfModel (2 * N)) k i hi0 hi1,
    wfModel_offspringVariance (2 * N) k]
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (N : ℝ) ≠ 0 := by linarith
  push_cast
  have h1 : 2 * (1 - 1 / (2 * (N : ℝ))) = (2 * (N : ℝ) - 1) * 1 / N := by
    field_simp
  have h2 : 2 * (N : ℝ) - 1 ≠ 0 := by linarith
  rw [h1, div_div_eq_mul_div, mul_div_mul_left _ _ h2, div_one]

/-- Source: ewens2004, secs. 3.4, 3.7. -/
theorem variance_effective_cannings_moran {N : ℕ} (hN : 0 < N)
    (i : Fin (N + 1)) (hi0 : 0 < i.val) (hi1 : i.val < N) :
    varianceEffective ((i : ℝ) / N)
        ((moranModel N hN).countChain.expect
          (fun j => ((j : ℝ) / N - (i : ℝ) / N) ^ 2) i) =
      (N : ℝ) ^ 2 / 4 := by
  have k : Fin N := ⟨0, hN⟩
  rw [variance_effective_cannings (moranModel N hN) k i hi0 hi1,
    moranModel_offspringVariance N hN k]
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast (show 2 ≤ N by omega)
  have hN1 : (N : ℝ) - 1 ≠ 0 := by linarith
  have h1 : 2 * (2 * ((N : ℝ) - 1) / (N : ℝ) ^ 2) = ((N : ℝ) - 1) * 4 / (N : ℝ) ^ 2 := by
    ring
  rw [h1, div_div_eq_mul_div, mul_div_mul_left _ _ hN1]

end Rhone.MarkovChain.EffectiveSize
