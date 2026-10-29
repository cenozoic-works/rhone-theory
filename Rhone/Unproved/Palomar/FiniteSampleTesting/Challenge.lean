module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

set_option maxSynthPendingDepth 3

@[expose] public section

open scoped BigOperators

namespace Rhone.Statistics.DependenceBudget

structure Law (X : Type*) [Fintype X] where
  mass : X → ℝ
  nonneg : ∀ x, 0 ≤ mass x
  total : ∑ x, mass x = 1

variable {X : Type*} [Fintype X]

noncomputable def rejection (P : Law X) (φ : X → ℝ) : ℝ :=
  ∑ x, P.mass x * φ x

noncomputable def totalVariation (P Q : Law X) : ℝ :=
  (∑ x, |P.mass x - Q.mass x|) / 2

end Rhone.Statistics.DependenceBudget

namespace Rhone.Statistics.DependentPairedTest
open DependenceBudget
variable {X : Type*} [Fintype X]

noncomputable def iid (P : Law X) (N : ℕ) : Law (Fin N → X) where
  mass := fun x => ∏ i, P.mass (x i)
  nonneg := fun x => Finset.prod_nonneg (fun i _ => P.nonneg (x i))
  total := by
    rw [← Fintype.prod_sum]
    simp [P.total]

end Rhone.Statistics.DependentPairedTest

namespace Rhone.Palomar.FiniteSampleTesting

open Statistics.DependenceBudget Statistics.DependentPairedTest

theorem size_transfer {X : Type*} [Fintype X] (P Q : Law X) (φ : X → ℝ)
    (hφ : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1) {α ε : ℝ}
    (hsize : rejection Q φ ≤ α) (hTV : totalVariation P Q ≤ ε) :
    rejection P φ ≤ α + ε := by
  sorry

theorem power_transfer {X : Type*} [Fintype X] (P Q : Law X) (φ : X → ℝ)
    (hφ : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1) {β ε : ℝ}
    (hpower : 1 - β ≤ rejection Q φ) (hTV : totalVariation P Q ≤ ε) :
    1 - β - ε ≤ rejection P φ := by
  sorry

theorem approximable_test_power_le_size {X : Type*} [Fintype X] (P : Law X)
    (null : Set (Law X)) (N : ℕ)
    (φ : (Fin N → X) → ℝ) (hφ : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1) {α : ℝ}
    (hsize : ∀ Q ∈ null, rejection (iid Q N) φ ≤ α)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ Q ∈ null, totalVariation P Q < ε) :
    rejection (iid P N) φ ≤ α := by
  sorry

theorem test_advantage_implies_gap {X : Type*} [Fintype X] (P : Law X)
    (null : Set (Law X)) (N : ℕ)
    (φ : (Fin N → X) → ℝ) (hφ : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1) {α : ℝ}
    (hsize : ∀ Q ∈ null, rejection (iid Q N) φ ≤ α)
    (hpower : α < rejection (iid P N) φ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ Q ∈ null, ε ≤ totalVariation P Q := by
  sorry

theorem iid_necessary_inverse_square {X : Type*} [Fintype X] [Nonempty X]
    (P Q : Law X) (N : ℕ)
    (φ : (Fin N → X) → ℝ) (hφ : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    {b C ε δ : ℝ} (hb : 0 < b) (hC : 0 < C) (hε : 0 < ε) (hδ : 0 ≤ δ)
    (hQ : ∀ x, b ≤ Q.mass x) (hclose : ∀ x, |P.mass x - Q.mass x| ≤ C * ε)
    (hadvantage : δ ≤ rejection (iid P N) φ - rejection (iid Q N) φ) :
    δ ^ 2 * b / (Fintype.card X * C ^ 2 * ε ^ 2) ≤ (N : ℝ) := by
  sorry

end Rhone.Palomar.FiniteSampleTesting
