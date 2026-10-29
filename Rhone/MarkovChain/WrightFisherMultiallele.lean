/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.FinChain
public import Rhone.MarkovChain.WrightFisher
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Algebra.BigOperators.Field

/-!
# Multiallele Wright–Fisher finite chain

Source: ewens2004, sec. 3.5; cannings1974, sec. 3.1, pp. 268–269. -/

@[expose] public section
namespace Rhone.MarkovChain

open Finset

/-- Source: ewens2004, sec. 3.5. -/
abbrev AlleleCounts (N K : ℕ) :=
  ↥(Finset.piAntidiag (Finset.univ : Finset (Fin K)) N)

namespace AlleleCounts

/-- Source: ewens2004, sec. 3.5. -/
theorem sum {N K : ℕ} (a : AlleleCounts N K) : ∑ l : Fin K, a.val l = N :=
  (Finset.mem_piAntidiag.mp a.property).1

/-- Source: ewens2004, sec. 3.5. -/
theorem sum_real {N K : ℕ} (a : AlleleCounts N K) :
    ∑ l : Fin K, (a.val l : ℝ) = N := by
  exact_mod_cast a.sum

/-- Source: ewens2004, sec. 3.5. -/
theorem frequency_sum_pow {N K : ℕ} (a : AlleleCounts N K) :
    (∑ l : Fin K, (a.val l : ℝ) / N) ^ N = 1 := by
  by_cases hN : N = 0
  · simp [hN]
  · rw [← Finset.sum_div, a.sum_real, div_self (Nat.cast_ne_zero.mpr hN), one_pow]

end AlleleCounts

/-- Source: cannings1974, sec. 3.1, pp. 268–269. -/
noncomputable def wfMultiallele (N K : ℕ) (a b : AlleleCounts N K) : ℝ :=
  (Nat.multinomial (Finset.univ : Finset (Fin K)) b.val : ℝ) *
    ∏ l : Fin K, ((a.val l : ℝ) / N) ^ (b.val l)

/-- Source: cannings1974, sec. 3.1, pp. 268–269. -/
theorem wfMultiallele_nonneg (N K : ℕ) (a b : AlleleCounts N K) :
    0 ≤ wfMultiallele N K a b := by
  unfold wfMultiallele
  positivity

/-- Source: cannings1974, sec. 3.1, pp. 268–269. -/
theorem wfMultiallele_sum (N K : ℕ) (a : AlleleCounts N K) :
    ∑ b : AlleleCounts N K, wfMultiallele N K a b = 1 := by
  have h := Finset.sum_pow_eq_sum_piAntidiag (Finset.univ : Finset (Fin K))
    (fun l => (a.val l : ℝ) / N) N
  rw [← Finset.sum_coe_sort (Finset.piAntidiag (Finset.univ : Finset (Fin K)) N)] at h
  have h' : (∑ b : AlleleCounts N K, wfMultiallele N K a b) =
      (∑ l : Fin K, (a.val l : ℝ) / N) ^ N := by
    simpa [wfMultiallele] using h.symm
  exact h'.trans a.frequency_sum_pow

/-- Source: ewens2004, sec. 3.5. -/
noncomputable def wfMultialleleChain (N K : ℕ) :
    Rhone.MarkovChain.FinChain (AlleleCounts N K) where
  P := wfMultiallele N K
  nonneg := wfMultiallele_nonneg N K
  row_sum := wfMultiallele_sum N K

/-- Source: ewens2004, sec. 3.5. -/
theorem wfMultialleleChain_P (N K : ℕ) :
    (wfMultialleleChain N K).P = wfMultiallele N K := rfl

/-- Source: cannings1974, sec. 3.1, pp. 268–269. -/
noncomputable def wfAlleleAllocationCounts (N K : ℕ) (ω : Fin N → Fin K) :
    AlleleCounts N K := by
  refine ⟨(fun l => (Finset.univ.filter (fun t => ω t = l)).card),
    Finset.mem_piAntidiag.mpr ⟨?_, by simp⟩⟩
  simpa using Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset (Fin N)) (Finset.univ : Finset (Fin K)) ω

/-- Source: cannings1974, sec. 3.1, pp. 268–269. -/
theorem wfAlleleAllocationCounts_apply (N K : ℕ) (ω : Fin N → Fin K)
    (l : Fin K) :
    (wfAlleleAllocationCounts N K ω).val l =
      (Finset.univ.filter (fun t => ω t = l)).card := rfl

/-- Source: ewens2004, sec. 3.5. -/
noncomputable def wfMultialleleAllocationWeight (N K : ℕ)
    (a : AlleleCounts N K) (ω : Fin N → Fin K) : ℝ :=
  ∏ t : Fin N, ((a.val (ω t) : ℝ) / N)

end Rhone.MarkovChain
