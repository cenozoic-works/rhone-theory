/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.CommonClockIslandPhaseIntegral

/-! # The finite post-event variation-of-constants identity in arbitrary dimensions -/

@[expose] public section

open Set MeasureTheory
open scoped Matrix Matrix.Norms.Operator
namespace Rhone.Statistics.Identifiability

theorem phase_block_post_integral_general {n m : ℕ}
    (N : Matrix (Fin (n + m)) (Fin (n + m)) ℝ) (Q : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) (D : Matrix (Fin m) (Fin m) ℝ)
    (hpp : ∀ i j, N (Fin.castAdd m i) (Fin.castAdd m j) = Q i j)
    (hlp : ∀ i j, N (Fin.natAdd n i) (Fin.castAdd m j) = 0)
    (hpl : ∀ i j, N (Fin.castAdd m i) (Fin.natAdd n j) = B i j)
    (hll : ∀ i j, N (Fin.natAdd n i) (Fin.natAdd n j) = D i j)
    (i : Fin n) (w : Fin m → ℝ) (t : ℝ) :
    (∑ j : Fin m, NormedSpace.exp (t • N) (Fin.castAdd m i) (Fin.natAdd n j) * w j) =
      ∫ s in 0..t, ((NormedSpace.exp (s • Q) * B *
        NormedSpace.exp ((t - s) • D)) *ᵥ w) i := by
  let a (j : Fin m) (s : ℝ) :=
    NormedSpace.exp (s • N) (Fin.castAdd m i) (Fin.natAdd n j)
  let b (j : Fin m) (s : ℝ) := (NormedSpace.exp ((t - s) • D) *ᵥ w) j
  let v (j : Fin m) (s : ℝ) := ∑ l, NormedSpace.exp (s • Q) i l * B l j
  have ha (j : Fin m) (s : ℝ) : HasDerivAt (a j)
      (v j s + ∑ l : Fin m, a l s * D l j) s := by
    have h := phase_exp_entry_hasDerivAt N (Fin.castAdd m i) (Fin.natAdd n j) s
    simpa only [Fin.sum_univ_add, hpl, hll, phase_pre_exp N Q hpp hlp, a, v] using h
  have hb (j : Fin m) (s : ℝ) : HasDerivAt (b j)
      (-(∑ l : Fin m, D j l * b l s)) s := by
    have h := (phase_flow_hasDerivAt_left D j w (t - s)).scomp s
      ((hasDerivAt_id s).const_sub t)
    simpa only [neg_smul, one_smul, Function.comp_def, b] using h
  have heq (s : ℝ) :
      ((NormedSpace.exp (s • Q) * B * NormedSpace.exp ((t - s) • D)) *ᵥ w) i =
        ∑ j, v j s * b j s := by
    rw [← Matrix.mulVec_mulVec]
    rfl
  have hderiv (s : ℝ) : HasDerivAt
      (fun s => ∑ j, a j s * b j s)
      (((NormedSpace.exp (s • Q) * B * NormedSpace.exp ((t - s) • D)) *ᵥ w) i) s := by
    rw [heq]
    have h := HasDerivAt.sum fun j (_ : j ∈ Finset.univ) => (ha j s).mul (hb j s)
    convert! h using 1
    · ext u; simp
    · have hc : (∑ j, (∑ l, a l s * D l j) * b j s) =
          ∑ j, a j s * (∑ l, D j l * b l s) := by
        simp only [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro l _
        ring
      simp only [add_mul, Finset.sum_add_distrib, mul_neg, Finset.sum_neg_distrib]
      rw [hc]
      ring
  have hv (j : Fin m) : Continuous (v j) := by
    apply continuous_finsetSum
    intro l _
    exact (phase_exp_entry_continuous Q i l).mul_const _
  have hbc (j : Fin m) : Continuous (b j) :=
    continuous_iff_continuousAt.mpr fun s => (hb j s).continuousAt
  have hint : Continuous (fun s : ℝ =>
      ((NormedSpace.exp (s • Q) * B * NormedSpace.exp ((t - s) • D)) *ᵥ w) i) := by
    simp_rw [heq]
    exact continuous_finsetSum _ (fun j _ => (hv j).mul (hbc j))
  have hne (j : Fin m) : Fin.castAdd m i ≠ Fin.natAdd n j := by
    intro h
    have hh := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hh
    omega
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hderiv s) (hint.intervalIntegrable 0 t)
  simpa [a, b, Matrix.one_apply, hne] using h.symm

end Rhone.Statistics.Identifiability
