/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcSupport.Rates
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Prod

/-! # Finite pre-split recursion driven by the concrete state's hull rates -/
@[expose] public section
namespace Rhone.Coalescent.SmcSupport
open IntervalProcess SmcBound

def CountState (n : ℕ) := {s : State // Valid s ∧ s.2.2.1 = n + 1}

abbrev CoalChoices (n : ℕ) :=
  {ij : Fin (n + 2) × Fin (n + 2) // ij.1 < ij.2}

noncomputable instance (n : ℕ) : Fintype (CoalChoices n) := by
  classical
  unfold CoalChoices
  infer_instance

instance (n : ℕ) : Nonempty (CoalChoices n) :=
  ⟨⟨(⟨0, by omega⟩, ⟨1, by omega⟩), by change (0 : ℕ) < 1; norm_num⟩⟩

noncomputable def recombinationRace (R : ℝ) (n : ℕ)
    (s : CountState (n + 1)) : ℝ :=
  recombinationRate R s.val /
    (((n : ℝ) + 2) * ((n : ℝ) + 1) / 2 + recombinationRate R s.val)

theorem recombinationRace_bounds (R : ℝ) (hR : 0 ≤ R) (n : ℕ)
    (s : CountState (n + 1)) :
    0 ≤ recombinationRace R n s ∧ recombinationRace R n s ≤ hazard R n := by
  obtain ⟨hb0, hb1⟩ := recombinationRate_bounds R hR s.val s.property.1
  have hc : (s.val.2.2.1 : ℝ) = (n : ℝ) + 2 := by
    rw [s.property.2]
    push_cast
    ring
  rw [hc] at hb1
  constructor
  · unfold recombinationRace
    positivity
  · exact normalized_rate_le_hazard R _ n hR hb0 hb1

noncomputable def prefixFailure (R : ℝ)
    (next : ∀ n, CountState (n + 1) → CoalChoices n → CountState n) :
    ∀ n, CountState n → ℝ
  | 0, _ => 0
  | n + 1, s => recombinationRace R n s + (1 - recombinationRace R n s) *
      ((∑ k, prefixFailure R next n (next n s k)) /
        (Fintype.card (CoalChoices n) : ℝ))

theorem prefixFailure_le (R : ℝ) (hR : 0 ≤ R)
    (next : ∀ n, CountState (n + 1) → CoalChoices n → CountState n)
    (n : ℕ) (s : CountState n) :
    prefixFailure R next n s ≤ raceBound (hazard R) n := by
  classical
  induction n with
  | zero => rfl
  | succ n ih =>
    have hq := recombinationRace_bounds R hR n s
    have hh := hazard_bounds R hR n
    have ht := raceBound_nonneg_le_one (hazard R) (fun j => hazard_bounds R hR j) n
    have hcard : 0 < (Fintype.card (CoalChoices n) : ℝ) := by
      exact_mod_cast Fintype.card_pos
    have havg :
        (∑ k, prefixFailure R next n (next n s k)) /
          (Fintype.card (CoalChoices n) : ℝ) ≤ raceBound (hazard R) n := by
      apply (div_le_iff₀ hcard).2
      calc
        _ ≤ ∑ _k : CoalChoices n, raceBound (hazard R) n :=
          Finset.sum_le_sum (fun k _ => ih (next n s k))
        _ = _ := by simp [mul_comm]
    have hmul := mul_le_mul_of_nonneg_left havg
      (show 0 ≤ 1 - recombinationRace R n s by linarith)
    have hmono := mul_le_mul_of_nonneg_right hq.2
      (show 0 ≤ 1 - raceBound (hazard R) n by linarith)
    simp only [prefixFailure, raceBound]
    nlinarith

end Rhone.Coalescent.SmcSupport
