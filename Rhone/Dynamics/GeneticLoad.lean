/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Dynamics.MutationSelection
public import Rhone.Dynamics.DiploidSelection
public import Mathlib.Basic.Real.Basic

/-!
# Exact mutation and segregation loads

Source: felsenstein_teg2019, sec. III.7, eq. (III-28)–(III-33), pp. 156–157; crow_kimura1970, sec.
6.5. -/

@[expose] public section

namespace Rhone.Dynamics

/--
Source: felsenstein_teg2019, sec. III.7, eq. (III-28)–(III-33), pp. 156–157; crow_kimura1970, sec.
6.5. -/
theorem haploid_balance_load {s μ q : ℝ} (hμ : 0 < μ) (hμs : μ < s) (hs : s < 1)
    (_hq0 : 0 ≤ q) (hq1 : q < 1) (hfix : hapMutSelStep s μ q = q) :
    1 - (1 - s * q) = μ := by
  have hs0 : 0 < s := hμ.trans hμs
  have hW : 1 - s * q ≠ 0 := by
    have hsq : s * q < 1 := by
      calc
        s * q < s * 1 := mul_lt_mul_of_pos_left hq1 hs0
        _ = s := mul_one s
        _ < 1 := hs
    exact (sub_pos.mpr hsq).ne'
  rcases (hapMutSelStep_eq_iff hs0.ne' hW).mp hfix with hq | hq
  · exact False.elim (hq1.ne hq)
  · rw [hq, mul_div_cancel₀ _ hs0.ne']
    ring

/--
Source: felsenstein_teg2019, sec. III.7, eq. (III-28)–(III-33), pp. 156–157; crow_kimura1970, sec.
6.5. -/
theorem recessive_balance_load {s μ q : ℝ} (hμ : 0 < μ) (hμs : μ < s) (hs : s < 1)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hfix : dipMutSelStep 0 s μ q = q) :
    1 - meanFit 1 1 (1 - s) (1 - q) = μ := by
  have hs0 : 0 < s := hμ.trans hμs
  have hW : 1 - s * q ^ 2 ≠ 0 := by
    have hq2 : q ^ 2 < 1 := by
      have hprod : 0 < (1 - q) * (1 + q) :=
        mul_pos (sub_pos.mpr hq1) (by linarith)
      nlinarith
    have hsq : s * q ^ 2 < 1 := by
      calc
        s * q ^ 2 < s * 1 := mul_lt_mul_of_pos_left hq2 hs0
        _ = s := mul_one s
        _ < 1 := hs
    exact (sub_pos.mpr hsq).ne'
  rcases (recessive_mutSel_fixed_iff hs0.ne' hW).mp hfix with hq | hq
  · exact False.elim (hq1.ne hq)
  · have hbal : s * q ^ 2 = μ := by rw [hq, mul_div_cancel₀ _ hs0.ne']
    simp only [meanFit]
    nlinarith

/-- Source: crow_kimura1970, sec. 6.2. -/
theorem overdominance_segregation_load {s t : ℝ}
    (hs0 : 0 < s) (_hs1 : s < 1) (ht0 : 0 < t) (_ht1 : t < 1) :
    1 - meanFit (1 - s) 1 (1 - t) (t / (s + t)) = s * t / (s + t) := by
  have hst : s + t ≠ 0 := (add_pos hs0 ht0).ne'
  simp only [meanFit]
  field_simp
  ring

end Rhone.Dynamics
