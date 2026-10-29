/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeIntegrableFlux

/-! # Locally-L1 pre-merger flow for an arbitrary initial occupancy distribution -/

@[expose] public section

noncomputable section
open Set Filter Matrix MeasureTheory
open scoped BigOperators Topology Matrix
namespace Rhone.Statistics.Identifiability.ThreeSampling

abbrev State := ThreeState

def preRow (ρ : State → ℝ) (k : ℕ) (c q : ℝ → ℝ) (t : ℝ) : State → ℝ :=
  ρ ᵥ* inhomogeneousTransition (fun u => threeGenerator k (c u) (q u)) 0 t

def survival (ρ : State → ℝ) (k : ℕ) (c q : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∑ i, preRow ρ k c q t i

lemma preRow_initial (ρ : State → ℝ) (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume) :
    preRow ρ k c q 0 = ρ := by
  unfold preRow
  rw [integrableTransition_self _ (ThreeIntegrable.preGenerator_locallyIntegrable k c q hc hq),
    Matrix.vecMul_one]

lemma preRow_nonnegative (ρ : State → ℝ) (k : ℕ) (c q : ℝ → ℝ)
    (hρ : ∀ i, 0 ≤ ρ i) (hc : LocallyIntegrable c volume)
    (hq : LocallyIntegrable q volume) (hqn : ∀ᵐ t, 0 ≤ t → 0 ≤ q t)
    {t : ℝ} (ht : 0 ≤ t) (i : State) : 0 ≤ preRow ρ k c q t i := by
  change 0 ≤ ∑ j : State, ρ j *
    inhomogeneousTransition (fun u => threeGenerator k (c u) (q u)) 0 t j i
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (hρ j)
    (integrableTransition_nonneg _ (ThreeIntegrable.preGenerator_locallyIntegrable k c q hc hq)
      (ThreeIntegrable.preGenerator_metzler_ae k c q hqn) le_rfl ht j i)

lemma survival_positive (ρ : State → ℝ) (k : ℕ) (c q : ℝ → ℝ)
    (hρ : ∀ i, 0 ≤ ρ i) (hρsum : ∑ i, ρ i = 1)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (hqn : ∀ᵐ t, 0 ≤ t → 0 ≤ q t) {t : ℝ} (ht : 0 ≤ t) :
    0 < survival ρ k c q t := by
  have hex : ∃ i, 0 < ρ i := by
    by_contra h
    push Not at h
    have hz : ∀ i, ρ i = 0 := fun i => le_antisymm (h i) (hρ i)
    simp [hz] at hρsum
  obtain ⟨i, hi⟩ := hex
  have hdiag := integrableTransition_diagonal_positive _
    (ThreeIntegrable.preGenerator_locallyIntegrable k c q hc hq)
    (ThreeIntegrable.preGenerator_metzler_ae k c q hqn) le_rfl ht i
  have hcoord : 0 < preRow ρ k c q t i := by
    apply (mul_pos hi hdiag).trans_le
    change ρ i * inhomogeneousTransition (fun u => threeGenerator k (c u) (q u)) 0 t i i ≤
      ∑ j : State, ρ j *
        inhomogeneousTransition (fun u => threeGenerator k (c u) (q u)) 0 t j i
    apply Finset.single_le_sum (f := fun j : State => ρ j *
      inhomogeneousTransition (fun u => threeGenerator k (c u) (q u)) 0 t j i)
      _ (Finset.mem_univ i)
    intro j _
    exact mul_nonneg (hρ j)
      (integrableTransition_nonneg _ (ThreeIntegrable.preGenerator_locallyIntegrable k c q hc hq)
        (ThreeIntegrable.preGenerator_metzler_ae k c q hqn) le_rfl ht j i)
  exact hcoord.trans_le (Finset.single_le_sum
    (fun j _ => preRow_nonnegative ρ k c q hρ hc hq hqn ht j) (Finset.mem_univ i))

lemma preRow_ac (ρ : State → ℝ) (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume)
    (a b : ℝ) (i : State) :
    AbsolutelyContinuousOnInterval (fun t => preRow ρ k c q t i) a b := by
  change AbsolutelyContinuousOnInterval
    (fun t => ∑ j : State, ρ j *
      inhomogeneousTransition (fun u => threeGenerator k (c u) (q u)) 0 t j i) a b
  apply ac_finset_sum Finset.univ
  intro j _
  exact (integrableTransition_entry_ac_right _
    (ThreeIntegrable.preGenerator_locallyIntegrable k c q hc hq) 0 a b j i).const_mul (ρ j)

lemma preRow_derivative_ae (ρ : State → ℝ) (k : ℕ) (c q : ℝ → ℝ)
    (hc : LocallyIntegrable c volume) (hq : LocallyIntegrable q volume) :
    ∀ᵐ t, ∀ i, HasDerivAt (fun u => preRow ρ k c q u i)
      ((preRow ρ k c q t ᵥ* threeGenerator k (c t) (q t)) i) t := by
  filter_upwards [integrableTransition_ae_hasDerivAt_right _
    (ThreeIntegrable.preGenerator_locallyIntegrable k c q hc hq)] with t ht i
  apply (HasDerivAt.fun_sum (u := Finset.univ)
    (fun j _ => (ht 0 j i).const_mul (ρ j))).congr_deriv
  simp only [preRow, Matrix.vecMul, Matrix.mul_apply, dotProduct, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  ring

end Rhone.Statistics.Identifiability.ThreeSampling
