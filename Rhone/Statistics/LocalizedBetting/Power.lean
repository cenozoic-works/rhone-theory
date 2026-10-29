/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.LocalizedBetting.FiniteNull
public import Rhone.Statistics.LocalizedBetting.LogBounds

/-! # Fixed-sample power bound with separately explicit localization error -/

@[expose] public section

noncomputable section
open scoped BigOperators
namespace Rhone.Statistics.LocalizedBetting
open DependenceBudget DependentPairedTest VarianceAwarePairBetting
variable {X : Type*} [Fintype X]

theorem product_failure (P : Law X) (N : ℕ) (factor : X → ℝ)
    (hf : ∀ x, 0 < factor x) {m v : ℝ}
    (hm : m ≤ rejection P (fun x => Real.log (factor x)))
    (hv : rejection P (fun x => Real.log (factor x) ^ 2) ≤ v)
    (hbudget : 3 < N * m) :
    probability (iid P N) (fun z => productWealth factor z < 20) ≤
      N * v / (N * m - 3) ^ 2 := by
  let f : X → ℝ := fun x => Real.log (factor x)
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have ha : 0 < (N : ℝ) * m - 3 := by linarith
  have hsub : ∀ z : Fin N → X, productWealth factor z < 20 →
      N * m - 3 ≤ |(∑ i, f (z i)) - N * rejection P f| := by
    intro z hz
    have hp : 0 < productWealth factor z := Finset.prod_pos (fun i _ => hf (z i))
    have hl := (Real.log_lt_log hp hz).trans log_twenty_lt_three
    have he : Real.log (productWealth factor z) = ∑ i, f (z i) :=
      Real.log_prod (fun i _ => (hf (z i)).ne')
    rw [he] at hl
    have hmean := mul_le_mul_of_nonneg_left hm hN
    have hab := neg_le_abs ((∑ i, f (z i)) - N * rejection P f)
    dsimp [f] at *
    linarith
  have ht := (probability_mono _ hsub).trans
    (finite_chebyshev (iid P N) (fun z => ∑ i, f (z i)) (N * rejection P f) ha)
  rw [iid_centered_sq] at ht
  apply ht.trans
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  apply mul_le_mul_of_nonneg_left _ hN
  dsimp [f]
  linarith [sq_nonneg (rejection P (fun x => Real.log (factor x)))]

theorem localized_power (P : Law X) (N : ℕ) (factor : X → ℝ)
    (localizes : (Fin N → X) → Prop) (hf : ∀ x, 0 < factor x) {m v error : ℝ}
    (hm : m ≤ rejection P (fun x => Real.log (factor x)))
    (hv : rejection P (fun x => Real.log (factor x) ^ 2) ≤ v)
    (hbudget : 3 < N * m)
    (hloc : probability (iid P N) (fun z => ¬ localizes z) ≤ error) :
    1 - error - N * v / (N * m - 3) ^ 2 ≤
      probability (iid P N) (fun z => localizes z ∧ 20 ≤ productWealth factor z) := by
  have hsub : ∀ z : Fin N → X, ¬(localizes z ∧ 20 ≤ productWealth factor z) →
      ¬ localizes z ∨ productWealth factor z < 20 := by
    intro z hz
    by_cases h : localizes z
    · exact Or.inr (lt_of_not_ge (fun hw => hz ⟨h, hw⟩))
    · exact Or.inl h
  have h := (probability_mono _ hsub).trans
    (probability_union_le (iid P N) (fun z => ¬ localizes z)
      (fun z => productWealth factor z < 20))
  have hb := product_failure P N factor hf hm hv hbudget
  rw [probability_complement] at h
  linarith

end Rhone.Statistics.LocalizedBetting
