/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.MarkovChain.FluctuatingSizeHeterozygosity
public import Rhone.MarkovChain.WrightFisherGeneratorLimitMoments

/-!
# Conditional variance effective size for changing haploid copy counts

Source: felsenstein1971, pp. 590–591, eq. (14); crow_kimura1970, sec. 7.6. -/

@[expose] public section
namespace Rhone.MarkovChain
open Finset

noncomputable def haploidVarianceEffective (p v : Real) : Real := p * (1 - p) / v

theorem wfResize_frequency_mean (M N : Nat) (hN : 0 < N) (i : Fin (M + 1)) :
    ∑ j, wfResize M N i j * ((j : Real) / N) = (i : Real) / M := by
  have hn : (N : Real) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  unfold wfResize
  calc
    _ = (∑ j : Fin (N + 1), binomRow N ((i : Real) / M) j * (j : Real)) / N := by
      rw [sum_div]
      apply sum_congr rfl
      intro j _
      exact (mul_div_assoc _ _ _).symm
    _ = _ := by
      rw [sum_fin_eq_range (fun j => binomRow N ((i : Real) / M) j * j),
        sum_binomRow_mul]
      field_simp

theorem wfResize_frequency_variance (M N : Nat) (hN : 0 < N) (i : Fin (M + 1)) :
    ∑ j, wfResize M N i j * ((j : Real) / N - (i : Real) / M) ^ 2 =
      ((i : Real) / M) * (1 - (i : Real) / M) / N := by
  have hn : (N : Real) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  unfold wfResize
  rw [sum_fin_eq_range (fun j =>
    binomRow N ((i : Real) / M) j * ((j : Real) / N - (i : Real) / M) ^ 2),
    sum_binomRow_freq_sub_pow (by omega : 1 ≤ N), sum_binomRow_central_sq]
  field_simp

theorem haploid_variance_effective_resize (M N : Nat) (hN : 0 < N)
    (i : Fin (M + 1)) (hi0 : 0 < i.val) (hiM : i.val < M) :
    haploidVarianceEffective ((i : Real) / M)
      (∑ j, wfResize M N i j * ((j : Real) / N - (i : Real) / M) ^ 2) = (N : Real) := by
  have hm : (0 : Real) < M := by exact_mod_cast (show 0 < M by omega)
  have hp : 0 < (i : Real) / M := div_pos (by exact_mod_cast hi0) hm
  have hp1 : (i : Real) / M < 1 := (div_lt_one hm).mpr (by exact_mod_cast hiM)
  rw [wfResize_frequency_variance M N hN, haploidVarianceEffective]
  have hz : ((i : Real) / M) * (1 - (i : Real) / M) ≠ 0 :=
    ne_of_gt (mul_pos hp (by linarith))
  exact div_div_cancel₀ hz

theorem wf_varying_variance_effective (n : Nat → Nat) (t : Nat) (hn : 0 < n (t + 1))
    (i : Fin (n t + 1)) (hi0 : 0 < i.val) (hiM : i.val < n t) :
    haploidVarianceEffective ((i : Real) / n t)
      (∑ j, wfResize (n t) (n (t + 1)) i j *
        ((j : Real) / n (t + 1) - (i : Real) / n t) ^ 2) = (n (t + 1) : Real) :=
  haploid_variance_effective_resize (n t) (n (t + 1)) hn i hi0 hiM

end Rhone.MarkovChain
