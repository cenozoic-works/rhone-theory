/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.EffectiveSize
public import Rhone.MarkovChain.EffectiveSize
public import Rhone.MarkovChain.CanningsHeterozygosity
public import Mathlib.Basic.Real.Basic

/-!
# Executable effective sizes equal the specification

Source: wright1931, pp. 108–109; felsenstein1971, pp. 582–585; cannings1974, sec. 3, p. 266. -/

@[expose] public section
namespace Rhone.Computation.EffectiveSize
open Finset

theorem cast_sumBy {α : Type} (f : α → Rat) (l : List α) :
    ((sumBy f l : Rat) : ℝ) = ∑ i : Fin l.length, ((f l[i.1] : Rat) : ℝ) := by
  induction l with
  | nil => simp [sumBy]
  | cons x xs ih =>
    rw [sumBy, Rat.cast_add, ih]
    exact (Fin.sum_univ_succ (n := xs.length) (fun i : Fin (xs.length + 1) =>
      ((f (x :: xs)[i.1] : Rat) : ℝ))).symm

def sizesReal (sizes : List Rat) : Fin sizes.length → ℝ := fun i => ((sizes[i.1] : Rat) : ℝ)

theorem harmonicMean_eq_none_iff (sizes : List Rat) :
    harmonicMean sizes = none ↔ sizes = [] ∨ ∃ x ∈ sizes, x ≤ 0 := by
  unfold harmonicMean
  by_cases h : sizes.isEmpty ∨ sizes.any (fun x => decide (x ≤ 0)) = true
  · simp only [h, ↓reduceIte, true_iff]
    rcases h with h | h
    · exact Or.inl (List.isEmpty_iff.1 h)
    · right
      obtain ⟨x, hx, hx0⟩ := List.any_eq_true.1 h
      exact ⟨x, hx, by simpa using hx0⟩
  · simp only [h, ↓reduceIte, reduceCtorEq, false_iff]
    intro h'
    apply h
    rcases h' with h' | ⟨x, hx, hx0⟩
    · exact Or.inl (by simp [h'])
    · exact Or.inr (List.any_eq_true.2 ⟨x, hx, by simpa using hx0⟩)

theorem harmonicMean_eq (sizes : List Rat) (hne : sizes ≠ []) (hpos : ∀ x ∈ sizes, 0 < x) :
    ∃ q : Rat, harmonicMean sizes = some q ∧
      (q : ℝ) = Rhone.MarkovChain.EffectiveSize.harmonicSize (sizesReal sizes) ∧
      (q : ℝ) = Rhone.MarkovChain.EffectiveSize.coalescenceEffective
        ((1 / (sizes.length : ℝ)) * ∑ t, 1 / (2 * sizesReal sizes t)) := by
  have hnone : ¬ (sizes.isEmpty ∨ sizes.any (fun x => decide (x ≤ 0)) = true) := by
    rintro (h | h)
    · exact hne (List.isEmpty_iff.1 h)
    · obtain ⟨x, hx, hx0⟩ := List.any_eq_true.1 h
      have := hpos x hx
      have hx1 : x ≤ 0 := by simpa using hx0
      exact absurd hx1 (not_le.2 this)
  have hdef : harmonicMean sizes =
      some ((sizes.length : Nat) / sumBy (fun x => 1 / x) sizes) := by
    unfold harmonicMean
    simp only [hnone, ↓reduceIte]
  have hT : 0 < sizes.length := List.length_pos_iff.2 hne
  have hposR : ∀ t, 0 < sizesReal sizes t := fun t => by
    unfold sizesReal
    exact_mod_cast hpos _ (List.getElem_mem t.2)
  have hcast : (((sizes.length : Nat) / sumBy (fun x => 1 / x) sizes : Rat) : ℝ) =
      Rhone.MarkovChain.EffectiveSize.harmonicSize (sizesReal sizes) := by
    unfold Rhone.MarkovChain.EffectiveSize.harmonicSize
    rw [Rat.cast_div, Rat.cast_natCast, cast_sumBy]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold sizesReal
    push_cast
    rfl
  refine ⟨_, hdef, hcast, ?_⟩
  rw [hcast]
  exact (Rhone.MarkovChain.EffectiveSize.harmonic_size_mean_rate hT (sizesReal sizes) hposR).symm

theorem unequalSexEffective_eq_none_iff (Nm Nf : Nat) :
    unequalSexEffective Nm Nf = none ↔ Nm = 0 ∨ Nf = 0 := by
  unfold unequalSexEffective
  by_cases h : Nm = 0 ∨ Nf = 0 <;> simp [h]

theorem unequalSexEffective_eq (Nm Nf : Nat) (hm : 0 < Nm) (hf : 0 < Nf) :
    ∃ q : Rat, unequalSexEffective Nm Nf = some q ∧
      (q : ℝ) = Rhone.MarkovChain.EffectiveSize.coalescenceEffective
        (Rhone.MarkovChain.EffectiveSize.sexPairCoalescence Nm Nf) ∧
      (q : ℝ) = 4 * (Nm : ℝ) * (Nf : ℝ) / ((Nm : ℝ) + (Nf : ℝ)) := by
  have hn : ¬ (Nm = 0 ∨ Nf = 0) := by omega
  have hq : (((4 * (Nm : Rat) * (Nf : Rat) / ((Nm : Rat) + (Nf : Rat)) : Rat)) : ℝ) =
      4 * (Nm : ℝ) * (Nf : ℝ) / ((Nm : ℝ) + (Nf : ℝ)) := by push_cast; rfl
  refine ⟨_, by simp [unequalSexEffective, hn], ?_, hq⟩
  rw [hq]
  exact (Rhone.MarkovChain.EffectiveSize.unequal_sex_effective hm hf).symm

theorem varianceEffective_eq_none_iff (p v : Rat) :
    varianceEffective p v = none ↔ ¬ (0 < p ∧ p < 1 ∧ 0 < v) := by
  unfold varianceEffective
  by_cases h : 0 < p ∧ p < 1 ∧ 0 < v <;> simp [h]

theorem varianceEffective_eq (p v : Rat) (hp0 : 0 < p) (hp1 : p < 1) (hv : 0 < v) :
    ∃ q : Rat, varianceEffective p v = some q ∧
      (q : ℝ) = Rhone.MarkovChain.EffectiveSize.varianceEffective (p : ℝ) (v : ℝ) := by
  refine ⟨p * (1 - p) / (2 * v), by simp [varianceEffective, hp0, hp1, hv], ?_⟩
  simp [Rhone.MarkovChain.EffectiveSize.varianceEffective]

theorem varianceEffective_binomial (N p : Rat) (hN : 0 < N) (hp0 : 0 < p) (hp1 : p < 1) :
    varianceEffective p (p * (1 - p) / (2 * N)) = some N := by
  have hq : 0 < 1 - p := sub_pos.2 hp1
  have hv : 0 < p * (1 - p) / (2 * N) := by positivity
  simp only [varianceEffective, hp0, hp1, hv, and_self, ↓reduceIte]
  congr 1
  field_simp

theorem offspringVarianceEffective_eq_none_iff (N : Nat) (sigma2 : Rat) :
    offspringVarianceEffective N sigma2 = none ↔ ¬ (2 ≤ N ∧ 0 < sigma2) := by
  unfold offspringVarianceEffective
  by_cases h : 2 ≤ N ∧ 0 < sigma2 <;> simp [h]

theorem offspringVarianceEffective_eq (N : Nat) (sigma2 : Rat) (hN : 2 ≤ N)
    (hs : 0 < sigma2) :
    ∃ q : Rat, offspringVarianceEffective N sigma2 = some q ∧
      (q : ℝ) = Rhone.MarkovChain.EffectiveSize.eigenvalueEffective
        (1 - (sigma2 : ℝ) / ((N : ℝ) - 1)) := by
  refine ⟨((N : Rat) - 1) / (2 * sigma2), by simp [offspringVarianceEffective, hN, hs], ?_⟩
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have h1 : (N : ℝ) - 1 ≠ 0 := by linarith
  have hs' : (sigma2 : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  unfold Rhone.MarkovChain.EffectiveSize.eigenvalueEffective
    Rhone.MarkovChain.EffectiveSize.coalescenceEffective
  rw [sub_sub_cancel]
  push_cast
  field_simp

theorem offspringVarianceEffective_decay {N : Nat} {Ω : Type*} [Fintype Ω]
    (M : Rhone.MarkovChain.CanningsModel N Ω) (k : Fin N) (sigma2 : Rat) (hN : 2 ≤ N)
    (hs : 0 < sigma2) (hv : M.offspringVariance k = (sigma2 : ℝ)) (i : Fin (N + 1)) :
    ∃ q : Rat, offspringVarianceEffective N sigma2 = some q ∧
      M.countChain.expect (fun j => Rhone.MarkovChain.het N j) i =
        (1 - 1 / (2 * (q : ℝ))) * Rhone.MarkovChain.het N i := by
  obtain ⟨q, hq, hqe⟩ := offspringVarianceEffective_eq N sigma2 hN hs
  refine ⟨q, hq, ?_⟩
  rw [Rhone.MarkovChain.CanningsModel.countChain_expect_het M k i, hv]
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have h1 : (N : ℝ) - 1 ≠ 0 := by linarith
  have hs' : (sigma2 : ℝ) ≠ 0 := by exact_mod_cast hs.ne'
  have hq' : (q : ℝ) = ((N : ℝ) - 1) / (2 * (sigma2 : ℝ)) := by
    rw [hqe]
    unfold Rhone.MarkovChain.EffectiveSize.eigenvalueEffective
      Rhone.MarkovChain.EffectiveSize.coalescenceEffective
    rw [sub_sub_cancel]
    field_simp
  rw [hq']
  congr 1
  field_simp

end Rhone.Computation.EffectiveSize
