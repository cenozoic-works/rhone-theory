/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.DriftHeterozygosity
public import Mathlib.Tactic.FieldSimp

/-! # Distinct effective-size quantities -/

@[expose] public section

namespace Rhone.MarkovChain.EffectiveSize

open Finset

/-- Source: felsenstein1971, pp. 584–585. -/
noncomputable def coalescenceEffective (c : ℝ) : ℝ := 1 / (2 * c)

/-- Source: felsenstein1971, pp. 584–585. -/
noncomputable def inbreedingEffective (F0 F1 : ℝ) : ℝ :=
  coalescenceEffective ((F1 - F0) / (1 - F0))

/-- Source: felsenstein1971, p. 582. -/
noncomputable def varianceEffective (p v : ℝ) : ℝ := p * (1 - p) / (2 * v)

/-- Source: ewens1982, eq. (5). -/
noncomputable def eigenvalueEffective (lam : ℝ) : ℝ := coalescenceEffective (1 - lam)

/-- Source: felsenstein1971, pp. 584–585. -/
theorem inbreeding_effective_recursion {F0 F1 c : ℝ}
    (hF0 : F0 ≠ 1) (hc : c ≠ 0) (hrec : F1 = c + (1 - c) * F0) :
    inbreedingEffective F0 F1 = coalescenceEffective c := by
  have hD : 1 - F0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hF0)
  have hrate : (F1 - F0) / (1 - F0) = c := by
    rw [hrec]
    field_simp
    ring
  have hpositive_denominator : 2 * c ≠ 0 := mul_ne_zero (by norm_num) hc
  unfold inbreedingEffective coalescenceEffective
  apply (div_eq_div_iff (by simpa only [hrate] using hpositive_denominator)
    hpositive_denominator).mpr
  rw [hrate]

theorem variance_effective_binomial {N p : ℝ}
    (hN : N ≠ 0) (hp0 : p ≠ 0) (hp1 : p ≠ 1) :
    varianceEffective p (p * (1 - p) / (2 * N)) = N := by
  have hq : 1 - p ≠ 0 := sub_ne_zero.mpr (Ne.symm hp1)
  unfold varianceEffective
  field_simp

/-- Source: ewens1982, eq. (3)–(4). -/
theorem eigenvalue_effective_diploid {N : ℕ} (hN : 0 < N) :
    eigenvalueEffective (1 - 1 / (2 * (N : ℝ))) = N := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  unfold eigenvalueEffective coalescenceEffective
  field_simp
  ring

theorem coalescence_effective_diploid {N : ℕ} (hN : 0 < N) :
    coalescenceEffective (1 / (2 * (N : ℝ))) = N := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  unfold coalescenceEffective
  field_simp

/-- Source: wright1931, pp. 108–109. -/
noncomputable def sexPairCoalescence (Nm Nf : ℕ) : ℝ :=
  1 / (8 * (Nm : ℝ)) + 1 / (8 * (Nf : ℝ))

/-- Source: wright1931, pp. 108–109. -/
theorem unequal_sex_effective {Nm Nf : ℕ} (hm : 0 < Nm) (hf : 0 < Nf) :
    coalescenceEffective (sexPairCoalescence Nm Nf) =
      4 * (Nm : ℝ) * (Nf : ℝ) / ((Nm : ℝ) + (Nf : ℝ)) := by
  have hm' : (0 : ℝ) < Nm := by exact_mod_cast hm
  have hf' : (0 : ℝ) < Nf := by exact_mod_cast hf
  have hsum : (Nm : ℝ) + (Nf : ℝ) ≠ 0 := by positivity
  have hrate : 1 / (8 * (Nm : ℝ)) + 1 / (8 * (Nf : ℝ)) ≠ 0 := by positivity
  unfold coalescenceEffective sexPairCoalescence
  field_simp
  ring

noncomputable def harmonicSize {T : ℕ} (N : Fin T → ℝ) : ℝ :=
  (T : ℝ) / (∑ t, 1 / N t)

theorem harmonic_size_mean_rate {T : ℕ} (hT : 0 < T)
    (N : Fin T → ℝ) (hN : ∀ t, 0 < N t) :
    coalescenceEffective ((1 / (T : ℝ)) * ∑ t, 1 / (2 * N t)) = harmonicSize N := by
  have hT' : (T : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hT.ne'
  have hsum : 0 < ∑ t, 1 / N t := by
    apply sum_pos
    · intro t _
      exact one_div_pos.mpr (hN t)
    · exact ⟨⟨0, hT⟩, mem_univ _⟩
  have hs : ∑ t, 1 / (2 * N t) = (1 / 2 : ℝ) * ∑ t, 1 / N t := by
    rw [mul_sum]
    apply sum_congr rfl
    intro t _
    ring
  unfold coalescenceEffective harmonicSize
  rw [hs]
  field_simp

theorem varying_size_deficit (N F : ℕ → ℝ)
    (hrec : ∀ t, F (t + 1) = 1 / (2 * N t) + (1 - 1 / (2 * N t)) * F t)
    (T : ℕ) :
    1 - F T = (∏ t ∈ range T, (1 - 1 / (2 * N t))) * (1 - F 0) := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [prod_range_succ, hrec T]
    have hfactor : 1 - (1 / (2 * N T) + (1 - 1 / (2 * N T)) * F T) =
        (1 - 1 / (2 * N T)) * (1 - F T) := by ring
    rw [hfactor, ih]
    ring

theorem wf_frequency_variance (N : ℕ) (i : Fin (2 * N + 1)) :
    (wf (2 * N)).expect (fun j => ((j : ℝ) / (2 * N) - (i : ℝ) / (2 * N)) ^ 2) i =
      ((i : ℝ) / (2 * N)) * (1 - (i : ℝ) / (2 * N)) / (2 * N) := by
  rcases Nat.eq_zero_or_pos N with hzero | hN
  · subst N
    simp [CountKernel.expect]
  have hN' : (2 * (N : ℝ)) ≠ 0 := by positivity
  have hscale : (wf (2 * N)).expect
      (fun j => ((j : ℝ) / (2 * N) - (i : ℝ) / (2 * N)) ^ 2) i =
      (1 / (2 * (N : ℝ)) ^ 2) * (wf (2 * N)).expect (fun j => ((j : ℝ) - i) ^ 2) i := by
    unfold CountKernel.expect
    rw [mul_sum]
    apply sum_congr rfl
    intro j _
    field_simp
  rw [hscale, wf_variance]
  push_cast
  field_simp

/-- Source: ewens1982, eq. (2). -/
theorem wf_heterozygosity_eigen (N : ℕ) (i : Fin (2 * N + 1)) :
    (wf (2 * N)).expect (fun j => het (2 * N) j) i =
      (1 - 1 / (2 * (N : ℝ))) * het (2 * N) i := by
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using wf_expect_het (2 * N) i

theorem variance_effective_wf {N : ℕ} (hN : 0 < N)
    (i : Fin (2 * N + 1)) (hi0 : 0 < i.val) (hi1 : i.val < 2 * N) :
    varianceEffective ((i : ℝ) / (2 * N))
      ((wf (2 * N)).expect
        (fun j => ((j : ℝ) / (2 * N) - (i : ℝ) / (2 * N)) ^ 2) i) = (N : ℝ) := by
  rw [wf_frequency_variance]
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hi0' : (0 : ℝ) < i := by exact_mod_cast hi0
  have hi1' : (i : ℝ) < 2 * (N : ℝ) := by exact_mod_cast hi1
  have hp0 : (i : ℝ) / (2 * N) ≠ 0 := by positivity
  have hp1 : (i : ℝ) / (2 * N) ≠ 1 := by
    have : (i : ℝ) / (2 * N) < 1 := (div_lt_one (by positivity)).mpr hi1'
    linarith
  exact variance_effective_binomial (by positivity) hp0 hp1

end Rhone.MarkovChain.EffectiveSize
