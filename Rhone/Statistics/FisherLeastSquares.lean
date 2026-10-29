/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Dynamics.HaploidSelection
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Weighted least-squares average effects

Source: ewens_lessard2015, p. 61, eq. 11–13; ewens1989, p. 176, eq. (25)–(26). -/

@[expose] public section
namespace Rhone.Statistics
open Rhone.Dynamics
open scoped BigOperators
variable {G K : Type*} [Fintype G] [Fintype K]

/-- Source: ewens_lessard2015, p. 61, eq. 11. -/
noncomputable def fisherScore (X : G → K → ℝ) (β : K → ℝ) (g : G) : ℝ :=
  ∑ k, X g k * β k

/-- Source: ewens1989, p. 176, eq. (25). -/
noncomputable def fisherLoss (P W : G → ℝ) (X : G → K → ℝ) (β : K → ℝ) : ℝ :=
  wMean P (fun g => (W g - fisherScore X β g) ^ 2)

/-- Source: ewens1989, p. 176, eq. (25). -/
def IsFisherLeastSquares (P W : G → ℝ) (X : G → K → ℝ) (β : K → ℝ) : Prop :=
  ∀ γ, fisherLoss P W X β ≤ fisherLoss P W X γ

noncomputable def fisherWeightedDesign (P : G → ℝ) (X : G → K → ℝ) :
    (K → ℝ) →ₗ[ℝ] EuclideanSpace ℝ G where
  toFun β := WithLp.toLp 2 (fun g => Real.sqrt (P g) * fisherScore X β g)
  map_add' β γ := by
    ext g
    change Real.sqrt (P g) * (∑ k, X g k * (β k + γ k)) =
      Real.sqrt (P g) * (∑ k, X g k * β k) +
        Real.sqrt (P g) * (∑ k, X g k * γ k)
    simp only [mul_add, Finset.sum_add_distrib]
  map_smul' c β := by
    ext g
    change Real.sqrt (P g) * (∑ k, X g k * (c * β k)) =
      c * (Real.sqrt (P g) * (∑ k, X g k * β k))
    simp only [mul_left_comm (X g _) c, ← Finset.mul_sum]
    ring

noncomputable def fisherWeightedTarget (P W : G → ℝ) : EuclideanSpace ℝ G :=
  WithLp.toLp 2 (fun g => Real.sqrt (P g) * W g)

theorem fisher_loss_eq_norm_sq (P W : G → ℝ) (X : G → K → ℝ) (β : K → ℝ)
    (hp : ∀ g, 0 ≤ P g) :
    fisherLoss P W X β =
      ‖fisherWeightedTarget P W - fisherWeightedDesign P X β‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_congr rfl
  intro g _
  change P g * (W g - fisherScore X β g) ^ 2 =
    (Real.sqrt (P g) * W g - Real.sqrt (P g) * fisherScore X β g) ^ 2
  rw [← mul_sub, mul_pow, Real.sq_sqrt (hp g)]

theorem fisher_leastSquares_exists (P W : G → ℝ) (X : G → K → ℝ)
    (hp : ∀ g, 0 ≤ P g) : ∃ β, IsFisherLeastSquares P W X β := by
  let T : (K → ℝ) →ₗ[ℝ] EuclideanSpace ℝ G := fisherWeightedDesign P X
  let U : Submodule ℝ (EuclideanSpace ℝ G) := LinearMap.range T
  let y : EuclideanSpace ℝ G := fisherWeightedTarget P W
  have hb : BddBelow (Set.range (fun z : U => ‖y - (z : EuclideanSpace ℝ G)‖)) :=
    ⟨0, by rintro _ ⟨z, rfl⟩; exact norm_nonneg _⟩
  obtain ⟨β, hβ⟩ := U.starProjection_apply_mem y
  refine ⟨β, fun γ => ?_⟩
  rw [fisher_loss_eq_norm_sq P W X β hp, fisher_loss_eq_norm_sq P W X γ hp]
  change ‖y - T β‖ ^ 2 ≤ ‖y - T γ‖ ^ 2
  have hmin : ‖y - U.starProjection y‖ ≤ ‖y - T γ‖ := by
    rw [Submodule.starProjection_minimal]
    exact ciInf_le hb ⟨T γ, LinearMap.mem_range_self T γ⟩
  rw [← hβ] at hmin
  nlinarith [norm_nonneg (y - T β), norm_nonneg (y - T γ)]

/-- Source: ewens1989, p. 176, eq. (26); ewens_lessard2015, p. 61. -/
theorem fisher_leastSquares_normal (P W : G → ℝ) (X : G → K → ℝ) (β : K → ℝ)
    (hp : ∀ g, 0 ≤ P g) (hfit : IsFisherLeastSquares P W X β) (k : K) :
    wMean P (fun g => (W g - fisherScore X β g) * X g k) = 0 := by
  classical
  let T : (K → ℝ) →ₗ[ℝ] EuclideanSpace ℝ G := fisherWeightedDesign P X
  let U : Submodule ℝ (EuclideanSpace ℝ G) := LinearMap.range T
  let y : EuclideanSpace ℝ G := fisherWeightedTarget P W
  have hb : BddBelow (Set.range (fun z : U => ‖y - (z : EuclideanSpace ℝ G)‖)) :=
    ⟨0, by rintro _ ⟨z, rfl⟩; exact norm_nonneg _⟩
  obtain ⟨γ, hγ⟩ := U.starProjection_apply_mem y
  have hnorm : ‖y - T β‖ = ‖y - U.starProjection y‖ := by
    have hmin : ‖y - U.starProjection y‖ ≤ ‖y - T β‖ := by
      rw [Submodule.starProjection_minimal]
      exact ciInf_le hb ⟨T β, LinearMap.mem_range_self T β⟩
    have hfit' := hfit γ
    rw [fisher_loss_eq_norm_sq P W X β hp,
      fisher_loss_eq_norm_sq P W X γ hp] at hfit'
    change ‖y - T β‖ ^ 2 ≤ ‖y - T γ‖ ^ 2 at hfit'
    rw [hγ] at hfit'
    nlinarith [norm_nonneg (y - T β), norm_nonneg (y - U.starProjection y)]
  have heq : ‖y - T β‖ = ⨅ z : U, ‖y - z‖ :=
    hnorm.trans (Submodule.starProjection_minimal y)
  have ho := (U.norm_eq_iInf_iff_inner_eq_zero (LinearMap.mem_range_self T β)).mp heq
  have hk := ho (T (Pi.single k 1)) (LinearMap.mem_range_self T _)
  have he : inner ℝ (y - T β) (T (Pi.single k 1)) =
      wMean P (fun g => (W g - fisherScore X β g) * X g k) := by
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro g _
    rw [RCLike.inner_apply']
    change (Real.sqrt (P g) * W g - Real.sqrt (P g) * fisherScore X β g) *
      (Real.sqrt (P g) * fisherScore X (Pi.single k 1) g) =
        P g * ((W g - fisherScore X β g) * X g k)
    have hs : fisherScore X (Pi.single k 1) g = X g k := by
      unfold fisherScore
      rw [Finset.sum_eq_single k]
      · simp
      · intro j _ hj
        simp [hj]
      · simp
    rw [hs]
    calc
      _ = Real.sqrt (P g) ^ 2 * ((W g - fisherScore X β g) * X g k) := by ring
      _ = _ := by rw [Real.sq_sqrt (hp g)]
  rw [he] at hk
  exact hk

end Rhone.Statistics
