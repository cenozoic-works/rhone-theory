/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.MatrixFlow
public import Rhone.Statistics.Identifiability.HalfLineIdentification
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Tactic

/-! # Finite Cayley-Hamilton certificates for scalar matrix-exponential identities -/

@[expose] public section

noncomputable section
open Set Filter Matrix Polynomial
open scoped Topology Matrix Matrix.Norms.Operator
namespace Rhone.Statistics.Identifiability.FiniteExponentialJets
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

lemma all_powers_of_finite (M : Matrix ι ι ℝ) (L : Matrix ι ι ℝ →L[ℝ] ℝ)
    (hzero : ∀ k : ℕ, k < Fintype.card ι → L (M ^ k) = 0) :
    ∀ k : ℕ, L (M ^ k) = 0 := by
  have hne : M.charpoly ≠ 1 := by
    intro he
    have hh := congrArg Polynomial.natDegree he
    simp only [Matrix.charpoly_natDegree_eq_dim, Polynomial.natDegree_one] at hh
    have hp := Fintype.card_pos (α := ι)
    omega
  intro k
  have hdeg : (Polynomial.X ^ k %ₘ M.charpoly).natDegree < Fintype.card ι := by
    simpa only [Matrix.charpoly_natDegree_eq_dim] using
      Polynomial.natDegree_modByMonic_lt (Polynomial.X ^ k) M.charpoly_monic hne
  rw [M.pow_eq_aeval_mod_charpoly k, Polynomial.aeval_eq_sum_range' hdeg, map_sum]
  apply Finset.sum_eq_zero
  intro i hi
  rw [map_smul, hzero i (Finset.mem_range.mp hi), smul_zero]

lemma exp_zero_of_finite (M : Matrix ι ι ℝ) (L : Matrix ι ι ℝ →L[ℝ] ℝ)
    (hzero : ∀ k : ℕ, k < Fintype.card ι → L (M ^ k) = 0) (t : ℝ) :
    L (NormedSpace.exp (t • M)) = 0 := by
  have hp := all_powers_of_finite M L hzero
  have hs := L.hasSum (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (t • M))
  have hz : HasSum (fun _ : ℕ => (0 : ℝ)) (L (NormedSpace.exp (t • M))) := by
    convert! hs using 1
    simp only [smul_pow, map_smul, hp, smul_zero]
  exact hz.unique hasSum_zero

def jet (M : Matrix ι ι ℝ) (L : Matrix ι ι ℝ →L[ℝ] ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  L (M ^ k * NormedSpace.exp (t • M))

omit [Nonempty ι] in
lemma jet_hasDerivAt (M : Matrix ι ι ℝ) (L : Matrix ι ι ℝ →L[ℝ] ℝ) (k : ℕ) (t : ℝ) :
    HasDerivAt (jet M L k) (jet M L (k + 1) t) t := by
  have h := (hasDerivAt_exp_smul_const' M t).const_mul (M ^ k)
  have hh := L.hasFDerivAt.comp_hasDerivAt t h
  convert! hh using 1
  simp only [jet, pow_succ, mul_assoc]
  rfl

omit [Nonempty ι] in
lemma jet_continuous (M : Matrix ι ι ℝ) (L : Matrix ι ι ℝ →L[ℝ] ℝ) (k : ℕ) :
    Continuous (jet M L k) :=
  continuous_iff_continuousAt.mpr fun t => (jet_hasDerivAt M L k t).continuousAt

omit [Nonempty ι] in
lemma powers_zero_of_positive_exp_zero (M : Matrix ι ι ℝ) (L : Matrix ι ι ℝ →L[ℝ] ℝ)
    (hzero : ∀ t : ℝ, 0 < t → L (NormedSpace.exp (t • M)) = 0) :
    ∀ k : ℕ, L (M ^ k) = 0 := by
  have hall : ∀ k : ℕ, ∀ t : ℝ, 0 < t → jet M L k t = 0 := by
    intro k
    induction k with
    | zero =>
      intro t ht
      simpa only [jet, pow_zero, Matrix.one_mul] using hzero t ht
    | succ k ih =>
      intro t ht
      have he : jet M L k =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
        filter_upwards [Ioi_mem_nhds ht] with u hu
        exact ih u hu
      exact (jet_hasDerivAt M L k t).unique
        ((hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq he)
  intro k
  have h := (eqOn_closed_halfline (jet_continuous M L k) continuous_const
    (fun t ht => hall k t ht)) (show (0 : ℝ) ∈ Ici 0 by simp)
  simpa only [jet, zero_smul, NormedSpace.exp_zero, Matrix.mul_one] using h

theorem positive_exp_zero_iff_finite (M : Matrix ι ι ℝ) (L : Matrix ι ι ℝ →L[ℝ] ℝ) :
    (∀ t : ℝ, 0 < t → L (NormedSpace.exp (t • M)) = 0) ↔
      (∀ k : ℕ, k < Fintype.card ι → L (M ^ k) = 0) := by
  constructor
  · intro h k _
    exact powers_zero_of_positive_exp_zero M L h k
  · intro h t _
    exact exp_zero_of_finite M L h t

end Rhone.Statistics.Identifiability.FiniteExponentialJets
