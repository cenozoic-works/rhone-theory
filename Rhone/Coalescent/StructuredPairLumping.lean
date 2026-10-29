/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.StructuredPair
public import Rhone.MarkovChain.RateLumping

/-! # The pair chain is a lumping of the structured coalescent with two lineages -/

@[expose] public section

namespace Rhone.Coalescent.StructuredPair

open Finset
open IslandPair (State)

variable {d : ℕ}

def pairOf (x : Structured.State 2 d) : State d :=
  match x 0, x 1 with
  | Sum.inr a, Sum.inr b => some (a, b)
  | _, _ => none

theorem pairOf_of_inr {x : Structured.State 2 d} {a b : Fin d} (h0 : x 0 = Sum.inr a)
    (h1 : x 1 = Sum.inr b) : pairOf x = some (a, b) := by
  simp [pairOf, h0, h1]

theorem sum_generator_mul_pairOf (M : Fin d → Fin d → ℝ) (c : Fin d → ℝ)
    (x : Structured.State 2 d) (g : State d → ℝ) :
    ∑ y, Structured.generator M c x y * g (pairOf y) =
      ∑ t, generator M c (pairOf x) t * g t := by
  rw [Structured.sum_generator_mul M c x fun y => g (pairOf y)]
  rcases h0 : x 0 with i0 | a0 <;> rcases h1 : x 1 with i1 | b0
  case inr.inr =>
    rw [pairOf_of_inr h0 h1, sum_generator_mul]
    have hm0 : ∀ b, pairOf (Structured.migrate x 0 b) = some (b, b0) := fun b => by
      simp [pairOf, Structured.migrate, h1]
    have hm1 : ∀ b, pairOf (Structured.migrate x 1 b) = some (a0, b) := fun b => by
      simp [pairOf, Structured.migrate, h0]
    have hmg : pairOf (Structured.merge x 0 1) = none := by
      simp [pairOf, Structured.merge, h0]
    have hA : ∀ F : Fin d → Fin d → ℝ, (∑ a, ∑ b,
        if (Sum.inr a0 : Fin 2 ⊕ Fin d) = Sum.inr a ∧ a ≠ b then F a b else 0) =
        ∑ b, if a0 ≠ b then F a0 b else 0 := by
      intro F
      rw [Finset.sum_eq_single a0]
      · simp
      · intro a _ ha
        exact Finset.sum_eq_zero fun b _ =>
          ite_eq_right fun hh => ha (Sum.inr.inj hh.1).symm
      · exact fun h => absurd (mem_univ a0) h
    have hC : ∀ r : Fin d → ℝ, (∑ a,
        if (Sum.inr a0 : Fin 2 ⊕ Fin d) = Sum.inr a ∧
          (Sum.inr b0 : Fin 2 ⊕ Fin d) = Sum.inr a then r a else 0) =
        if a0 = b0 then r a0 else 0 := by
      intro r
      rw [Finset.sum_eq_single a0]
      · simp [eq_comm]
      · intro a _ ha
        exact ite_eq_right fun hh => ha (Sum.inr.inj hh.1).symm
      · exact fun h => absurd (mem_univ a0) h
    simp only [Fin.sum_univ_two, h0, h1, hm0, hm1, hmg, lt_irrefl,
      false_and, ↓reduceIte, Finset.sum_const_zero, add_zero, zero_add, Fin.zero_lt_one,
      true_and, not_lt_of_gt Fin.zero_lt_one]
    rw [hA fun a b => M a b * (g (some (b, b0)) - g (some (a0, b0))),
      show (∑ a, ∑ b, if (Sum.inr b0 : Fin 2 ⊕ Fin d) = Sum.inr a ∧ a ≠ b then
        M a b * (g (some (a0, b)) - g (some (a0, b0))) else 0) =
        ∑ b, if b0 ≠ b then M b0 b * (g (some (a0, b)) - g (some (a0, b0))) else 0 from by
        rw [Finset.sum_eq_single b0]
        · simp
        · intro a _ ha
          exact Finset.sum_eq_zero fun b _ =>
            ite_eq_right fun hh => ha (Sum.inr.inj hh.1).symm
        · exact fun h => absurd (mem_univ b0) h,
      hC fun a => c a * (g none - g (some (a0, b0)))]
    ring
  all_goals
    have hpx : pairOf x = none := by simp [pairOf, h0, h1]
    have hrhs : ∑ t, generator M c (pairOf x) t * g t = 0 := by
      rw [hpx]
      simp [generator, eventRate]
    rw [hrhs, Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero]
    · intro i _
      refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun a _ => ite_eq_right ?_
      rintro ⟨hij, hi, hj⟩
      fin_cases i <;> fin_cases j <;> simp_all
    · intro i _
      refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
      split_ifs with hh
      · have hmig : pairOf (Structured.migrate x i b) = none := by
          fin_cases i <;> simp_all [pairOf, Structured.migrate]
        rw [hmig, hpx, sub_self, mul_zero]
      · rfl

theorem lumps_pairOf (M : Fin d → Fin d → ℝ) (c : Fin d → ℝ)
    (hM : ∀ a b, a ≠ b → 0 ≤ M a b) (hc : ∀ a, 0 ≤ c a) :
    (Structured.chain 2 M c hM hc).Lumps pairOf (chain M c hM hc) := by
  intro x t
  have h := sum_generator_mul_pairOf M c x fun s => if s = t then 1 else 0
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', mem_univ, ↓reduceIte] at h
  rw [Finset.sum_filter]
  exact h

theorem sum_semigroup_pairOf (M : Fin d → Fin d → ℝ) (c : Fin d → ℝ)
    (hM : ∀ a b, a ≠ b → 0 ≤ M a b) (hc : ∀ a, 0 ≤ c a) (t : ℝ) (x : Structured.State 2 d)
    (s : State d) :
    ∑ y with pairOf y = s, (Structured.chain 2 M c hM hc).semigroup t x y =
      (chain M c hM hc).semigroup t (pairOf x) s :=
  (lumps_pairOf M c hM hc).sum_semigroup_fibre t x s

end Rhone.Coalescent.StructuredPair
