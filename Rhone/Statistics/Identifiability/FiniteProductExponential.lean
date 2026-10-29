/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.FiniteProductFlow
public import Rhone.Statistics.Identifiability.FiniteExponentialJetCriterion

/-! # Literal finite product generators realize products of matrix exponentials -/

@[expose] public section

noncomputable section
open Matrix
open scoped Matrix Matrix.Norms.Operator
namespace Rhone.Statistics.Identifiability.FiniteExponentialJets
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

lemma exp_entry_hasDerivAt (Q : Matrix ι ι ℝ) (i j : ι) (t : ℝ) :
    HasDerivAt (fun u => NormedSpace.exp (u • Q) i j)
      ((NormedSpace.exp (t • Q) * Q) i j) t := by
  let L : Matrix ι ι ℝ →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj j : (ι → ℝ) →L[ℝ] ℝ).comp
      (ContinuousLinearMap.proj i : Matrix ι ι ℝ →L[ℝ] (ι → ℝ))
  exact L.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_exp_smul_const Q t)

lemma transition_const_eq_exp (Q : Matrix ι ι ℝ) (s t : ℝ) :
    inhomogeneousTransition (fun _ => Q) s t = NormedSpace.exp ((t - s) • Q) := by
  have hd : ∀ u i j, HasDerivAt (fun v => NormedSpace.exp ((v - s) • Q) i j)
      ((NormedSpace.exp ((u - s) • Q) * Q) i j) u := by
    intro u i j
    convert! (exp_entry_hasDerivAt Q i j (u - s)).comp u
      ((hasDerivAt_id u).sub_const s) using 1
    simp
  have h := finiteMatrix_solution_eq_transition (fun _ => Q)
    (fun u => NormedSpace.exp ((u - s) • Q)) (fun _ _ => continuous_const) s hd t
  simpa using h.symm

lemma exp_productRowGenerator (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ)
    (t : ℝ) (i j : ι × κ) :
    NormedSpace.exp (t • productRowGenerator A B) i j =
      NormedSpace.exp (t • A) i.1 j.1 * NormedSpace.exp (t • B) i.2 j.2 := by
  have h := inhomogeneousTransition_product (fun _ => A) (fun _ => B)
    (fun _ _ => continuous_const) (fun _ _ => continuous_const) 0 t i j
  simpa only [transition_const_eq_exp, sub_zero] using h

lemma tensor_flow_output (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ)
    (α u : ι → ℝ) (β v : κ → ℝ) (t : ℝ) :
    dotProduct (tensorRow α β)
        (NormedSpace.exp (t • productRowGenerator A B) *ᵥ tensorRow u v) =
      dotProduct α (NormedSpace.exp (t • A) *ᵥ u) *
        dotProduct β (NormedSpace.exp (t • B) *ᵥ v) := by
  have hm : NormedSpace.exp (t • productRowGenerator A B) *ᵥ tensorRow u v =
      tensorRow (NormedSpace.exp (t • A) *ᵥ u) (NormedSpace.exp (t • B) *ᵥ v) := by
    funext i
    simp only [Matrix.mulVec, dotProduct, tensorRow, exp_productRowGenerator,
      Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [hm]
  simp only [dotProduct, tensorRow, Fintype.sum_prod_type,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

end Rhone.Statistics.Identifiability.FiniteExponentialJets
