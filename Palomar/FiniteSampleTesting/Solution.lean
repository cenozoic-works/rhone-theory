module

public import Rhone.Statistics.DependenceBudget.Transfer
public import Rhone.Statistics.NullClosureTesting.Testing
public import Rhone.Statistics.FiniteObservationRate.Testing

@[expose] public section

namespace Rhone.Palomar.FiniteSampleTesting

open Statistics.DependenceBudget Statistics.DependentPairedTest

theorem size_transfer {X : Type*} [Fintype X] (P Q : Law X) (φ : X → ℝ)
    (hφ : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1) {α ε : ℝ}
    (hsize : rejection Q φ ≤ α) (hTV : totalVariation P Q ≤ ε) :
    rejection P φ ≤ α + ε :=
  Rhone.Statistics.DependenceBudget.size_transfer P Q φ hφ hsize hTV

theorem power_transfer {X : Type*} [Fintype X] (P Q : Law X) (φ : X → ℝ)
    (hφ : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1) {β ε : ℝ}
    (hpower : 1 - β ≤ rejection Q φ) (hTV : totalVariation P Q ≤ ε) :
    1 - β - ε ≤ rejection P φ :=
  Rhone.Statistics.DependenceBudget.power_transfer P Q φ hφ hpower hTV

theorem approximable_test_power_le_size {X : Type*} [Fintype X] (P : Law X)
    (null : Set (Law X)) (N : ℕ)
    (φ : (Fin N → X) → ℝ) (hφ : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1) {α : ℝ}
    (hsize : ∀ Q ∈ null, rejection (iid Q N) φ ≤ α)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ Q ∈ null, totalVariation P Q < ε) :
    rejection (iid P N) φ ≤ α :=
  Rhone.Statistics.NullClosureTesting.approximable_test_power_le_size P null N φ hφ hsize
    happrox

theorem test_advantage_implies_gap {X : Type*} [Fintype X] (P : Law X)
    (null : Set (Law X)) (N : ℕ)
    (φ : (Fin N → X) → ℝ) (hφ : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1) {α : ℝ}
    (hsize : ∀ Q ∈ null, rejection (iid Q N) φ ≤ α)
    (hpower : α < rejection (iid P N) φ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ Q ∈ null, ε ≤ totalVariation P Q :=
  Rhone.Statistics.NullClosureTesting.test_advantage_implies_gap P null N φ hφ hsize hpower

theorem iid_necessary_inverse_square {X : Type*} [Fintype X] [Nonempty X]
    (P Q : Law X) (N : ℕ)
    (φ : (Fin N → X) → ℝ) (hφ : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    {b C ε δ : ℝ} (hb : 0 < b) (hC : 0 < C) (hε : 0 < ε) (hδ : 0 ≤ δ)
    (hQ : ∀ x, b ≤ Q.mass x) (hclose : ∀ x, |P.mass x - Q.mass x| ≤ C * ε)
    (hadvantage : δ ≤ rejection (iid P N) φ - rejection (iid Q N) φ) :
    δ ^ 2 * b / (Fintype.card X * C ^ 2 * ε ^ 2) ≤ (N : ℝ) :=
  Rhone.Statistics.FiniteObservationRate.iid_necessary_inverse_square P Q N φ hφ hb hC hε hδ
    hQ hclose hadvantage

end Rhone.Palomar.FiniteSampleTesting
