module

public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

set_option maxSynthPendingDepth 3

@[expose] public section

namespace Rhone.MarkovChain

abbrev CountKernel (N : ℕ) : Type := Fin (N + 1) → Fin (N + 1) → ℝ

namespace CountKernel

variable {N : ℕ}

def expect (P : CountKernel N) (f : Fin (N + 1) → ℝ) (i : Fin (N + 1)) : ℝ :=
  ∑ j, P i j * f j

def expectIter (P : CountKernel N) : ℕ → (Fin (N + 1) → ℝ) → Fin (N + 1) → ℝ
  | 0, f => f
  | t + 1, f => P.expect (P.expectIter t f)

end CountKernel

end Rhone.MarkovChain

namespace Rhone.MarkovChain

open Finset

def binomRow (n : ℕ) (p : ℝ) (j : ℕ) : ℝ := (n.choose j : ℝ) * p ^ j * (1 - p) ^ (n - j)

noncomputable def wfRow (N i j : ℕ) : ℝ := binomRow N ((i : ℝ) / N) j

noncomputable def wf (N : ℕ) : CountKernel N := fun i j => wfRow N i j

end Rhone.MarkovChain

namespace Rhone.MarkovChain

open Finset

noncomputable def het (N i : ℕ) : ℝ := 2 * ((i : ℝ) / N) * (1 - (i : ℝ) / N)

end Rhone.MarkovChain

namespace Rhone.MarkovChain.EffectiveSize

open Finset

noncomputable def harmonicSize {T : ℕ} (N : Fin T → ℝ) : ℝ :=
  (T : ℝ) / (∑ t, 1 / N t)

end Rhone.MarkovChain.EffectiveSize

namespace Rhone.MarkovChain

open Finset EffectiveSize

noncomputable def wfResize (M N : ℕ) : Fin (M + 1) → Fin (N + 1) → ℝ :=
  fun i j => binomRow N ((i : ℝ) / M) j

noncomputable def wfVarExpect (n : ℕ → ℕ) :
    (t : ℕ) → (Fin (n t + 1) → ℝ) → Fin (n 0 + 1) → ℝ
  | 0, f => f
  | t + 1, f => wfVarExpect n t (fun i => ∑ j, wfResize (n t) (n (t + 1)) i j * f j)

end Rhone.MarkovChain

namespace Rhone.Palomar.FluctuatingSize

open Finset MarkovChain MarkovChain.EffectiveSize

theorem wfResize_nonneg (M N : ℕ) (i : Fin (M + 1)) (j : Fin (N + 1)) :
    0 ≤ wfResize M N i j := by
  sorry

theorem wfResize_row_sum (M N : ℕ) (i : Fin (M + 1)) : ∑ j, wfResize M N i j = 1 := by
  sorry

theorem wfResize_self (N : ℕ) : wfResize N N = wf N := by
  sorry

theorem wfVarExpect_const (N t : ℕ) (f : Fin (N + 1) → ℝ) :
    wfVarExpect (fun _ => N) t f = (wf N).expectIter t f := by
  sorry

theorem wfResize_expect_het (M : ℕ) {N : ℕ} (hN : 0 < N) (i : Fin (M + 1)) :
    ∑ j, wfResize M N i j * het N j = (1 - 1 / (N : ℝ)) * het M i := by
  sorry

theorem wfVarExpect_het (n : ℕ → ℕ) (t : ℕ) (hpos : ∀ s, s < t → 0 < n (s + 1))
    (i : Fin (n 0 + 1)) :
    wfVarExpect n t (fun j => het (n t) j) i =
      (∏ s ∈ range t, (1 - 1 / (n (s + 1) : ℝ))) * het (n 0) i := by
  sorry

theorem sum_inv_eq_div_harmonicSize {T : ℕ} (a : Fin T → ℝ) :
    ∑ t, 1 / a t = T / harmonicSize a := by
  sorry

theorem prod_deficit_le_harmonic {T : ℕ} (a : Fin T → ℝ) (ha : ∀ t, 1 ≤ a t) :
    ∏ t, (1 - 1 / a t) ≤ (1 - 1 / harmonicSize a) ^ T := by
  sorry

theorem prod_deficit_eq_harmonic_iff {T : ℕ} (a : Fin T → ℝ) (ha : ∀ t, 1 ≤ a t) :
    ∏ t, (1 - 1 / a t) = (1 - 1 / harmonicSize a) ^ T ↔ ∀ s t, a s = a t := by
  sorry

theorem harmonic_sub_prod_deficit_le {T : ℕ} (a : Fin T → ℝ) (ha : ∀ t, 1 ≤ a t) :
    (1 - 1 / harmonicSize a) ^ T - ∏ t, (1 - 1 / a t) ≤
      ((T : ℝ) - 1) / (2 * T) * (∑ t, 1 / a t) ^ 2 := by
  sorry

theorem abs_prod_deficit_sub_harmonic_le {T : ℕ} (a : Fin T → ℝ) (ha : ∀ t, 1 ≤ a t) :
    |∏ t, (1 - 1 / a t) - (1 - 1 / harmonicSize a) ^ T| ≤ (∑ t, 1 / a t) ^ 2 / 2 := by
  sorry

theorem wfVarExpect_het_le_harmonic (n : ℕ → ℕ) (t : ℕ) (hpos : ∀ s, s < t → 0 < n (s + 1))
    (i : Fin (n 0 + 1)) :
    wfVarExpect n t (fun j => het (n t) j) i ≤
      (1 - 1 / harmonicSize (fun s : Fin t => (n (s + 1) : ℝ))) ^ t * het (n 0) i := by
  sorry

theorem prod_deficit_two_four :
    ∏ t : Fin 2, (1 - 1 / ((![2, 4] : Fin 2 → ℝ) t)) = 3 / 8 := by
  sorry

theorem harmonicSize_two_four : harmonicSize (![2, 4] : Fin 2 → ℝ) = 8 / 3 := by
  sorry

theorem harmonic_power_two_four :
    (1 - 1 / harmonicSize (![2, 4] : Fin 2 → ℝ)) ^ 2 = 25 / 64 := by
  sorry

theorem prod_deficit_two_four_ne_harmonic :
    ∏ t : Fin 2, (1 - 1 / ((![2, 4] : Fin 2 → ℝ) t)) ≠
      (1 - 1 / harmonicSize (![2, 4] : Fin 2 → ℝ)) ^ 2 := by
  sorry

end Rhone.Palomar.FluctuatingSize
