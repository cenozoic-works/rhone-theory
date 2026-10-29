/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.AtomicRank.FiniteRank

/-! # Finite-atomic iid triple expectations and their weight derivatives -/

@[expose] public section

noncomputable section
open scoped BigOperators
namespace Rhone.Statistics.AtomicRank

variable {α : Type*} [Fintype α]

def weightedTriple (K : α × α × α → ℝ) (w : α → ℝ) : ℝ :=
  ∑ p : α × α × α, w p.1 * w p.2.1 * w p.2.2 * K p

def weightedConditional (K : α × α × α → ℝ) (w : α → ℝ) (a : α) : ℝ :=
  ∑ b : α, ∑ c : α, w b * w c * K (a, b, c)

def rawWeightDerivative (K : α × α × α → ℝ) (w v : α → ℝ) : ℝ :=
  ∑ p : α × α × α,
    (v p.1 * w p.2.1 * w p.2.2 + w p.1 * v p.2.1 * w p.2.2 +
      w p.1 * w p.2.1 * v p.2.2) * K p

def swapFirstTwo : (α × α × α) ≃ (α × α × α) :=
  Function.Involutive.toPerm (fun p => (p.2.1, p.1, p.2.2)) (by rintro ⟨a, b, c⟩; rfl)

def swapOuter : (α × α × α) ≃ (α × α × α) :=
  Function.Involutive.toPerm (fun p => (p.2.2, p.2.1, p.1)) (by rintro ⟨a, b, c⟩; rfl)

lemma weightedTriple_hasDerivAt (K : α × α × α → ℝ) {w : ℝ → α → ℝ}
    {v : α → ℝ} {x : ℝ} (hw : ∀ i, HasDerivAt (fun t => w t i) (v i) x) :
    HasDerivAt (fun t => weightedTriple K (w t)) (rawWeightDerivative K (w x) v) x := by
  apply HasDerivAt.fun_sum
  intro p _
  convert! (((hw p.1).mul (hw p.2.1)).mul (hw p.2.2)).mul_const (K p) using 1
  dsimp
  ring

lemma rawWeightDerivative_symmetric (K : α × α × α → ℝ) (w v : α → ℝ)
    (h12 : ∀ p, K (swapFirstTwo p) = K p) (h13 : ∀ p, K (swapOuter p) = K p) :
    rawWeightDerivative K w v = 3 * ∑ a : α, v a * weightedConditional K w a := by
  have h2 : (∑ p : α × α × α, w p.1 * v p.2.1 * w p.2.2 * K p) =
      ∑ p : α × α × α, v p.1 * w p.2.1 * w p.2.2 * K p := by
    apply Fintype.sum_equiv swapFirstTwo
    intro p
    simp only [h12]
    dsimp [swapFirstTwo, Function.Involutive.toPerm]
    ring
  have h3 : (∑ p : α × α × α, w p.1 * w p.2.1 * v p.2.2 * K p) =
      ∑ p : α × α × α, v p.1 * w p.2.1 * w p.2.2 * K p := by
    apply Fintype.sum_equiv swapOuter
    intro p
    simp only [h13]
    dsimp [swapOuter, Function.Involutive.toPerm]
    ring
  have hfirst : (∑ p : α × α × α, v p.1 * w p.2.1 * w p.2.2 * K p) =
      ∑ a : α, v a * weightedConditional K w a := by
    simp only [weightedConditional, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]
  simp only [rawWeightDerivative, add_mul, Finset.sum_add_distrib]
  rw [h2, h3, hfirst]
  ring

theorem weightedTriple_symmetric_hasDerivAt (K : α × α × α → ℝ) {w : ℝ → α → ℝ}
    {v : α → ℝ} {x : ℝ} (hw : ∀ i, HasDerivAt (fun t => w t i) (v i) x)
    (h12 : ∀ p, K (swapFirstTwo p) = K p) (h13 : ∀ p, K (swapOuter p) = K p) :
    HasDerivAt (fun t => weightedTriple K (w t))
      (3 * ∑ a : α, v a * weightedConditional K (w x) a) x := by
  rw [← rawWeightDerivative_symmetric K (w x) v h12 h13]
  exact weightedTriple_hasDerivAt K hw

lemma weightedTriple_eq_conditional (K : α × α × α → ℝ) (w : α → ℝ) :
    weightedTriple K w = ∑ a : α, w a * weightedConditional K w a := by
  simp only [weightedTriple, weightedConditional, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

end Rhone.Statistics.AtomicRank
