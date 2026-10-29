/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.IntegrableProjectionDuhamel
public import Rhone.Statistics.Identifiability.FiniteProductFlow

/-! # Product evolution for locally integrable finite generators -/

@[expose] public section

open Set Filter MeasureTheory
open scoped BigOperators Topology Matrix

namespace Rhone.Statistics.Identifiability

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [Fintype ι] [Fintype κ] in
theorem productRowGenerator_locallyIntegrable (A : ℝ → Matrix ι ι ℝ)
    (B : ℝ → Matrix κ κ ℝ)
    (hA : ∀ i j, LocallyIntegrable (fun t => A t i j) volume)
    (hB : ∀ i j, LocallyIntegrable (fun t => B t i j) volume) (i j : ι × κ) :
    LocallyIntegrable (fun t => productRowGenerator (A t) (B t) i j) volume := by
  exact ((hA i.1 j.1).mul_continuous continuous_const).add
    ((hB i.2 j.2).continuous_mul continuous_const)

theorem integrableTransition_product (A : ℝ → Matrix ι ι ℝ)
    (B : ℝ → Matrix κ κ ℝ)
    (hA : ∀ i j, LocallyIntegrable (fun t => A t i j) volume)
    (hB : ∀ i j, LocallyIntegrable (fun t => B t i j) volume)
    (s t : ℝ) (i j : ι × κ) :
    inhomogeneousTransition (fun u => productRowGenerator (A u) (B u)) s t i j =
      inhomogeneousTransition A s t i.1 j.1 * inhomogeneousTransition B s t i.2 j.2 := by
  let Q := fun u => productRowGenerator (A u) (B u)
  let z : ℝ → ι × κ → ℝ := fun u =>
    tensorRow (inhomogeneousTransition A s u i.1) (inhomogeneousTransition B s u i.2)
  have hQ : ∀ a b, LocallyIntegrable (fun u => Q u a b) volume :=
    productRowGenerator_locallyIntegrable A B hA hB
  have hzac : ∀ k, AbsolutelyContinuousOnInterval (fun u => z u k) s t := by
    intro k
    exact (integrableTransition_entry_ac_right A hA s s t i.1 k.1).fun_mul
      (integrableTransition_entry_ac_right B hB s s t i.2 k.2)
  have hz : ∀ᵐ u, u ∈ uIcc s t → ∀ k,
      HasDerivAt (fun v => z v k) ((z u ᵥ* Q u) k) u := by
    filter_upwards [integrableTransition_ae_hasDerivAt_right A hA,
      integrableTransition_ae_hasDerivAt_right B hB] with u hAu hBu _ k
    exact tensorRow_hasDerivAt A B (fun v => inhomogeneousTransition A s v i.1)
      (fun v => inhomogeneousTransition B s v i.2) u (hAu s i.1) (hBu s i.2) k
  have hzs : z s = (1 : Matrix (ι × κ) (ι × κ) ℝ) i := by
    funext k
    simp only [z, tensorRow, integrableTransition_self A hA, integrableTransition_self B hB,
      Matrix.one_apply]
    by_cases h₁ : i.1 = k.1 <;> by_cases h₂ : i.2 = k.2 <;>
      simp [h₁, h₂, Prod.ext_iff]
  have h := finiteRow_integrable_homogeneous_eq_transition Q hQ z s t hzac hz
  rw [hzs] at h
  change z t = ((1 : Matrix (ι × κ) (ι × κ) ℝ) * inhomogeneousTransition Q s t) i at h
  rw [Matrix.one_mul] at h
  exact (congrFun h j).symm

end Rhone.Statistics.Identifiability
