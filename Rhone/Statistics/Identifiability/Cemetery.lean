/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.GeneratorValid

/-! # A conservative cemetery extension of a finite killed generator -/

@[expose] public section

open scoped Matrix Matrix.Norms.Operator
open Finset
namespace Rhone.Statistics.Identifiability

noncomputable def cemetery {d : Nat} (Q : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  Fin.lastCases (fun _ => 0) (fun i =>
    Fin.lastCases (-(∑ j, Q i j)) (fun j => Q i j))

@[simp] theorem cemetery_alive {d : Nat} (Q : Matrix (Fin d) (Fin d) ℝ)
    (i j : Fin d) : cemetery Q i.castSucc j.castSucc = Q i j := by
  simp [cemetery]

@[simp] theorem cemetery_kill {d : Nat} (Q : Matrix (Fin d) (Fin d) ℝ)
    (i : Fin d) : cemetery Q i.castSucc (Fin.last d) = -(∑ j, Q i j) := by
  simp [cemetery]

@[simp] theorem cemetery_absorbed {d : Nat} (Q : Matrix (Fin d) (Fin d) ℝ)
    (j : Fin (d + 1)) : cemetery Q (Fin.last d) j = 0 := by
  simp [cemetery]

theorem cemetery_conservative {d : Nat} (Q : Matrix (Fin d) (Fin d) ℝ) :
    IsConservative (cemetery Q) := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [Matrix.mulVec, dotProduct]
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc]

theorem cemetery_metzler {d : Nat} (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : IsMetzler Q) (hrow : ∀ i, (∑ j, Q i j) ≤ 0) :
    IsMetzler (cemetery Q) := by
  intro i j hij
  revert hij
  refine Fin.lastCases ?_ (fun a => ?_) i
  · simp
  · refine Fin.lastCases ?_ (fun b => ?_) j
    · intro _
      simpa using neg_nonneg.mpr (hrow a)
    · intro hab
      simpa using hQ a b (fun heq => hab (congrArg Fin.castSucc heq))

theorem cemetery_power_alive {d : Nat} (Q : Matrix (Fin d) (Fin d) ℝ) (n : Nat) :
    (∀ i j : Fin d, (cemetery Q ^ n) i.castSucc j.castSucc = (Q ^ n) i j) ∧
    (∀ j : Fin d, (cemetery Q ^ n) (Fin.last d) j.castSucc = 0) := by
  induction n with
  | zero =>
    constructor
    · intro i j
      simp [Matrix.one_apply]
    · intro j
      have h : Fin.last d ≠ j.castSucc := by
        intro heq
        have hv := congrArg Fin.val heq
        simp only [Fin.val_last, Fin.val_castSucc] at hv
        exact (Nat.ne_of_lt j.isLt) hv.symm
      simp [h]
  | succ n ih =>
    constructor
    · intro i j
      simp only [pow_succ', Matrix.mul_apply, Fin.sum_univ_castSucc,
        cemetery_alive, ih.1, ih.2, mul_zero, add_zero]
    · intro j
      simp [pow_succ', Matrix.mul_apply]

theorem cemetery_smul {d : Nat} (Q : Matrix (Fin d) (Fin d) ℝ) (t : ℝ) :
    cemetery (t • Q) = t • cemetery Q := by
  ext i j
  refine Fin.lastCases ?_ (fun a => ?_) i
  · simp
  · refine Fin.lastCases ?_ (fun b => ?_) j
    · simp [← Finset.mul_sum]
    · simp

set_option backward.isDefEq.respectTransparency false in
theorem cemetery_exp_alive {d : Nat} (Q : Matrix (Fin d) (Fin d) ℝ)
    (t : ℝ) (i j : Fin d) :
    NormedSpace.exp (t • cemetery Q) i.castSucc j.castSucc =
      NormedSpace.exp (t • Q) i j := by
  rw [← cemetery_smul]
  have h := exp_entry_hasSum (cemetery (t • Q)) i.castSucc j.castSucc
  simp only [(cemetery_power_alive (t • Q) _).1] at h
  exact h.unique (exp_entry_hasSum (t • Q) i j)

theorem subgenerator_rows_le_one {d : Nat} (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : IsMetzler Q) (hrow : ∀ i, (∑ j, Q i j) ≤ 0) {t : ℝ} (ht : 0 ≤ t)
    (i : Fin d) : (∑ j, NormedSpace.exp (t • Q) i j) ≤ 1 := by
  have hM := cemetery_metzler Q hQ hrow
  have hn := exp_generator_nonneg (cemetery Q) hM ht i.castSucc (Fin.last d)
  have hs := congrFun (exp_generator_rows (cemetery Q) (cemetery_conservative Q) t)
    i.castSucc
  simp only [Matrix.mulVec, dotProduct, mul_one, Fin.sum_univ_castSucc,
    cemetery_exp_alive] at hs
  linarith

theorem island_cemetery_stochastic (k : Nat) {c q r t : ℝ}
    (hc : 0 ≤ c) (hq : 0 ≤ q) (hr : 0 ≤ r) (ht : 0 ≤ t) :
    NormedSpace.exp (t • cemetery (MarkovChain.Identifiability.generator k c q r)) ∈
      Matrix.rowStochastic ℝ (Fin 17) := by
  apply exp_generator_stochastic _
    (cemetery_metzler _ (generator_metzler k hc hq hr) ?_)
    (cemetery_conservative _) ht
  intro i
  rw [generator_row_sum]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc) (Nat.cast_nonneg _)

end Rhone.Statistics.Identifiability
