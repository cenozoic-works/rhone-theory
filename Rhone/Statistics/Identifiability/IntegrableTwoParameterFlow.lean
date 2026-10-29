/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.TwoParameterMarkovFlow
public import Rhone.Statistics.Identifiability.IntegrableMarkovFlow

/-! # Two-parameter finite matrix evolution for locally integrable histories -/

@[expose] public section

open Set Filter MeasureTheory
open scoped BigOperators Topology Matrix Matrix.Norms.Elementwise

namespace Rhone.Statistics.Identifiability

theorem ac_finset_sum_normed {κ E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Finset κ) {f : κ → ℝ → E} {a b : ℝ}
    (hf : ∀ i ∈ s, AbsolutelyContinuousOnInterval (f i) a b) :
    AbsolutelyContinuousOnInterval (fun t => ∑ i ∈ s, f i t) a b := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using (LipschitzWith.const (0 : E)).lipschitzOnWith.absolutelyContinuousOnInterval
  | @insert i s hi ih =>
      simpa only [Finset.sum_insert hi] using
        (hf i (Finset.mem_insert_self i s)).fun_add
          (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem ac_finite_pi {κ E : Type*} [Fintype κ] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → κ → E} {a b : ℝ}
    (hf : ∀ i, AbsolutelyContinuousOnInterval (fun t => f t i) a b) :
    AbsolutelyContinuousOnInterval f a b := by
  classical
  have h : AbsolutelyContinuousOnInterval
      (fun t => ∑ i, (ContinuousLinearMap.single ℝ (fun _ : κ => E) i) (f t i)) a b := by
    apply ac_finset_sum_normed Finset.univ
    intro i _
    exact ac_comp_lipschitz (hf i) (ContinuousLinearMap.single ℝ (fun _ : κ => E) i).lipschitzWith
  simpa only [ContinuousLinearMap.single_apply, Finset.univ_sum_single] using h

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[simp] theorem integrableFundamental_zero (Q : ℝ → Matrix ι ι ℝ)
    (hQ : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume) :
    inhomogeneousFundamental Q 0 = 1 := by
  funext i
  exact LocallyIntegrableLinearODE.solution_zero
    (inhomogeneousRowOperator_locallyIntegrable Q hQ) _

theorem integrableFundamental_continuous (Q : ℝ → Matrix ι ι ℝ)
    (hQ : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume) :
    Continuous (inhomogeneousFundamental Q) := by
  apply continuous_pi
  intro i
  exact LocallyIntegrableLinearODE.solution_continuous
    (inhomogeneousRowOperator_locallyIntegrable Q hQ) _

theorem integrableFundamental_ac (Q : ℝ → Matrix ι ι ℝ)
    (hQ : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (inhomogeneousFundamental Q) a b := by
  apply ac_finite_pi
  intro i
  exact LocallyIntegrableLinearODE.solution_absolutelyContinuousOnInterval
    (inhomogeneousRowOperator_locallyIntegrable Q hQ) _ a b

theorem integrableFundamental_entry_ac (Q : ℝ → Matrix ι ι ℝ)
    (hQ : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume) (a b : ℝ) (i j : ι) :
    AbsolutelyContinuousOnInterval (fun t => inhomogeneousFundamental Q t i j) a b := by
  exact ac_coordinate
    (LocallyIntegrableLinearODE.solution_absolutelyContinuousOnInterval
      (inhomogeneousRowOperator_locallyIntegrable Q hQ) _ a b) j

theorem integrableFundamental_ae_hasDerivAt (Q : ℝ → Matrix ι ι ℝ)
    (hQ : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume) :
    ∀ᵐ t, ∀ i j, HasDerivAt (fun s => inhomogeneousFundamental Q s i j)
      ((inhomogeneousFundamental Q t * Q t) i j) t := by
  apply ae_all_iff.mpr
  intro i
  filter_upwards [LocallyIntegrableLinearODE.solution_ae_hasDerivAt
    (inhomogeneousRowOperator_locallyIntegrable Q hQ) ((1 : Matrix ι ι ℝ) i)] with t ht j
  exact (hasDerivAt_pi.mp ht) j

@[simp] theorem integrableFundamentalInverse_zero (Q : ℝ → Matrix ι ι ℝ)
    (hQ : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume) :
    inhomogeneousFundamentalInverse Q 0 = 1 := by
  rw [inhomogeneousFundamentalInverse, integrableFundamental_zero]
  · exact Matrix.transpose_one
  · exact fun i j => (hQ j i).neg

theorem integrableFundamentalInverse_continuous (Q : ℝ → Matrix ι ι ℝ)
    (hQ : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume) :
    Continuous (inhomogeneousFundamentalInverse Q) := by
  apply continuous_pi; intro i
  apply continuous_pi; intro j
  exact (continuous_apply i).comp ((continuous_apply j).comp
    (integrableFundamental_continuous (fun t => -(Q t).transpose)
      (fun i j => (hQ j i).neg)))

theorem integrableFundamentalInverse_entry_ac (Q : ℝ → Matrix ι ι ℝ)
    (hQ : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume) (a b : ℝ) (i j : ι) :
    AbsolutelyContinuousOnInterval (fun t => inhomogeneousFundamentalInverse Q t i j) a b :=
  integrableFundamental_entry_ac (fun t => -(Q t).transpose)
    (fun i j => (hQ j i).neg) a b j i

theorem integrableFundamentalInverse_ac (Q : ℝ → Matrix ι ι ℝ)
    (hQ : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (inhomogeneousFundamentalInverse Q) a b :=
  ac_finite_pi fun i => ac_finite_pi fun j => integrableFundamentalInverse_entry_ac Q hQ a b i j

theorem integrableFundamentalInverse_ae_hasDerivAt (Q : ℝ → Matrix ι ι ℝ)
    (hQ : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume) :
    ∀ᵐ t, ∀ i j, HasDerivAt (fun s => inhomogeneousFundamentalInverse Q s i j)
      (-(Q t * inhomogeneousFundamentalInverse Q t) i j) t := by
  filter_upwards [integrableFundamental_ae_hasDerivAt (fun t => -(Q t).transpose)
    (fun i j => (hQ j i).neg)] with t ht i j
  simpa only [inhomogeneousFundamentalInverse, Matrix.transpose_apply,
    Matrix.mul_apply, Matrix.neg_apply, mul_neg, ← Finset.sum_neg_distrib, mul_comm, neg_mul]
      using ht j i

omit [DecidableEq ι] in
theorem finiteMatrixProduct_entry_ac (A B : ℝ → Matrix ι ι ℝ) (a b : ℝ)
    (hA : ∀ i j, AbsolutelyContinuousOnInterval (fun t => A t i j) a b)
    (hB : ∀ i j, AbsolutelyContinuousOnInterval (fun t => B t i j) a b) (i j : ι) :
    AbsolutelyContinuousOnInterval (fun t => (A t * B t) i j) a b := by
  exact ac_finset_sum Finset.univ fun k _ => (hA i k).fun_mul (hB k j)

omit [DecidableEq ι] in
theorem finiteMatrixProduct_hasDerivAt_at (A B : ℝ → Matrix ι ι ℝ)
    (A' B' : Matrix ι ι ℝ) (t : ℝ)
    (hA : ∀ i j, HasDerivAt (fun s => A s i j) (A' i j) t)
    (hB : ∀ i j, HasDerivAt (fun s => B s i j) (B' i j) t) (i j : ι) :
    HasDerivAt (fun s => (A s * B s) i j) ((A' * B t + A t * B') i j) t := by
  simpa only [Matrix.mul_apply, Matrix.add_apply, Pi.mul_apply, Finset.sum_add_distrib] using
    HasDerivAt.fun_sum (u := Finset.univ) (fun k _ => (hA i k).mul (hB k j))

theorem integrableFundamental_mul_inverse (Q : ℝ → Matrix ι ι ℝ)
    (hQ : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume) (t : ℝ) :
    inhomogeneousFundamental Q t * inhomogeneousFundamentalInverse Q t = 1 := by
  have hd : ∀ᵐ t, ∀ i j, HasDerivAt
      (fun s => (inhomogeneousFundamental Q s * inhomogeneousFundamentalInverse Q s) i j)
      0 t := by
    filter_upwards [integrableFundamental_ae_hasDerivAt Q hQ,
      integrableFundamentalInverse_ae_hasDerivAt Q hQ] with s hs hi i j
    have h := finiteMatrixProduct_hasDerivAt_at
      (inhomogeneousFundamental Q) (inhomogeneousFundamentalInverse Q)
      (inhomogeneousFundamental Q s * Q s)
      (-(Q s * inhomogeneousFundamentalInverse Q s)) s hs hi i j
    simpa only [Matrix.mul_neg, ← Matrix.mul_assoc, add_neg_cancel, Matrix.zero_apply] using h
  ext i j
  have hac := finiteMatrixProduct_entry_ac
    (inhomogeneousFundamental Q) (inhomogeneousFundamentalInverse Q) 0 t
    (integrableFundamental_entry_ac Q hQ 0 t)
    (integrableFundamentalInverse_entry_ac Q hQ 0 t) i j
  obtain ⟨C, hC⟩ := hac.const_of_ae_hasDerivAt_zero (by
    filter_upwards [hd] with s hs _
    exact hs i j)
  have h := (hC t (by simp)).trans (hC 0 (by simp)).symm
  simpa only [integrableFundamental_zero Q hQ,
    integrableFundamentalInverse_zero Q hQ, Matrix.one_mul] using h

theorem integrableFundamentalInverse_mul (Q : ℝ → Matrix ι ι ℝ)
    (hQ : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume) (t : ℝ) :
    inhomogeneousFundamentalInverse Q t * inhomogeneousFundamental Q t = 1 :=
  mul_eq_one_comm.mp (integrableFundamental_mul_inverse Q hQ t)

@[simp] theorem integrableTransition_self (Q : ℝ → Matrix ι ι ℝ)
    (hQ : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume) (s : ℝ) :
    inhomogeneousTransition Q s s = 1 :=
  integrableFundamentalInverse_mul Q hQ s

theorem integrableTransition_cocycle (Q : ℝ → Matrix ι ι ℝ)
    (hQ : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume) (s u t : ℝ) :
    inhomogeneousTransition Q s t =
      inhomogeneousTransition Q s u * inhomogeneousTransition Q u t := by
  unfold inhomogeneousTransition
  symm
  calc
    _ = inhomogeneousFundamentalInverse Q s *
        ((inhomogeneousFundamental Q u * inhomogeneousFundamentalInverse Q u) *
          inhomogeneousFundamental Q t) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [integrableFundamental_mul_inverse Q hQ, Matrix.one_mul]

theorem integrableTransition_continuous (Q : ℝ → Matrix ι ι ℝ)
    (hQ : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume) :
    Continuous (fun p : ℝ × ℝ => inhomogeneousTransition Q p.1 p.2) := by
  apply continuous_pi; intro i
  apply continuous_pi; intro j
  unfold inhomogeneousTransition
  simp only [Matrix.mul_apply]
  apply continuous_finsetSum; intro k _
  exact (((continuous_apply k).comp ((continuous_apply i).comp
    (integrableFundamentalInverse_continuous Q hQ))).comp continuous_fst).mul
    (((continuous_apply j).comp ((continuous_apply k).comp
      (integrableFundamental_continuous Q hQ))).comp continuous_snd)

theorem integrableTransition_entry_ac_right (Q : ℝ → Matrix ι ι ℝ)
    (hQ : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume) (s a b : ℝ) (i j : ι) :
    AbsolutelyContinuousOnInterval (fun t => inhomogeneousTransition Q s t i j) a b := by
  apply finiteMatrixProduct_entry_ac
  · intro k l
    exact (LipschitzWith.const _).lipschitzOnWith.absolutelyContinuousOnInterval
  · exact integrableFundamental_entry_ac Q hQ a b

theorem integrableTransition_entry_ac_left (Q : ℝ → Matrix ι ι ℝ)
    (hQ : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume) (t a b : ℝ) (i j : ι) :
    AbsolutelyContinuousOnInterval (fun s => inhomogeneousTransition Q s t i j) a b := by
  apply finiteMatrixProduct_entry_ac
  · exact integrableFundamentalInverse_entry_ac Q hQ a b
  · intro k l
    exact (LipschitzWith.const _).lipschitzOnWith.absolutelyContinuousOnInterval

theorem integrableTransition_ac_right (Q : ℝ → Matrix ι ι ℝ)
    (hQ : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume) (s a b : ℝ) :
    AbsolutelyContinuousOnInterval (inhomogeneousTransition Q s) a b :=
  ac_finite_pi fun i => ac_finite_pi fun j => integrableTransition_entry_ac_right Q hQ s a b i j

theorem integrableTransition_ac_left (Q : ℝ → Matrix ι ι ℝ)
    (hQ : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume) (t a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun s => inhomogeneousTransition Q s t) a b :=
  ac_finite_pi fun i => ac_finite_pi fun j => integrableTransition_entry_ac_left Q hQ t a b i j

theorem integrableTransition_ae_hasDerivAt_right (Q : ℝ → Matrix ι ι ℝ)
    (hQ : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume) :
    ∀ᵐ t, ∀ s i j, HasDerivAt (fun u => inhomogeneousTransition Q s u i j)
      ((inhomogeneousTransition Q s t * Q t) i j) t := by
  filter_upwards [integrableFundamental_ae_hasDerivAt Q hQ] with t ht s i j
  have h := finiteMatrixProduct_hasDerivAt_at
    (fun _ => inhomogeneousFundamentalInverse Q s) (inhomogeneousFundamental Q)
    0 (inhomogeneousFundamental Q t * Q t) t
    (fun i j => hasDerivAt_const t (inhomogeneousFundamentalInverse Q s i j)) ht i j
  simpa only [inhomogeneousTransition, Matrix.zero_mul, zero_add, Matrix.mul_assoc] using h

theorem integrableTransition_ae_hasDerivAt_left (Q : ℝ → Matrix ι ι ℝ)
    (hQ : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume) :
    ∀ᵐ s, ∀ t i j, HasDerivAt (fun u => inhomogeneousTransition Q u t i j)
      (-(Q s * inhomogeneousTransition Q s t) i j) s := by
  filter_upwards [integrableFundamentalInverse_ae_hasDerivAt Q hQ] with s hs t i j
  have h := finiteMatrixProduct_hasDerivAt_at
    (inhomogeneousFundamentalInverse Q) (fun _ => inhomogeneousFundamental Q t)
    (-(Q s * inhomogeneousFundamentalInverse Q s)) 0 s hs
    (fun i j => hasDerivAt_const s (inhomogeneousFundamental Q t i j)) i j
  simpa only [inhomogeneousTransition, Matrix.mul_zero, add_zero,
    Matrix.neg_mul, Matrix.mul_assoc, Matrix.neg_apply] using h

theorem integrableTransition_matrix_ae_hasDerivAt_right (Q : ℝ → Matrix ι ι ℝ)
    (hQ : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume) :
    ∀ᵐ t, ∀ s, HasDerivAt (inhomogeneousTransition Q s)
      (inhomogeneousTransition Q s t * Q t) t := by
  filter_upwards [integrableTransition_ae_hasDerivAt_right Q hQ] with t ht s
  exact hasDerivAt_pi.mpr fun i => hasDerivAt_pi.mpr fun j => ht s i j

theorem integrableTransition_matrix_ae_hasDerivAt_left (Q : ℝ → Matrix ι ι ℝ)
    (hQ : ∀ i j, LocallyIntegrable (fun t => Q t i j) volume) :
    ∀ᵐ s, ∀ t, HasDerivAt (fun u => inhomogeneousTransition Q u t)
      (-(Q s * inhomogeneousTransition Q s t)) s := by
  filter_upwards [integrableTransition_ae_hasDerivAt_left Q hQ] with s hs t
  exact hasDerivAt_pi.mpr fun i => hasDerivAt_pi.mpr fun j => hs t i j

end Rhone.Statistics.Identifiability
