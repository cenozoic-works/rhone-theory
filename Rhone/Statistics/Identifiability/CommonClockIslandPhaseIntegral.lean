/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.CommonClockIslandBlocks
public import Rhone.Statistics.Identifiability.CommonClockIslandJetDerivatives
public import Rhone.Statistics.Identifiability.FirstExit
public import Rhone.Statistics.Identifiability.MarkedLaw

/-! # Phase-block integral of the common-clock island phase density -/

@[expose] public section

open Set MeasureTheory
open scoped Matrix Matrix.Norms.Operator
namespace Rhone.Statistics.Identifiability

set_option backward.isDefEq.respectTransparency false

theorem phase_pre_power {n m : ℕ}
    (N : Matrix (Fin (n + m)) (Fin (n + m)) ℝ) (Q : Matrix (Fin n) (Fin n) ℝ)
    (hpp : ∀ i j, N (Fin.castAdd m i) (Fin.castAdd m j) = Q i j)
    (hlp : ∀ i j, N (Fin.natAdd n i) (Fin.castAdd m j) = 0)
    (a : ℕ) (i j : Fin n) :
    (N^a) (Fin.castAdd m i) (Fin.castAdd m j) = (Q^a) i j := by
  induction a generalizing j with
  | zero => simp [Matrix.one_apply]
  | succ a ih =>
    simp only [pow_succ, Matrix.mul_apply, Fin.sum_univ_add, hpp, hlp, mul_zero,
      Finset.sum_const_zero, add_zero]
    exact Finset.sum_congr rfl (fun l _ => by rw [ih])

theorem phase_exp_entry_hasSum {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) (t : ℝ) :
    HasSum (fun a : ℕ => (a.factorial : ℝ)⁻¹ * t^a * (Q^a) i j)
      (NormedSpace.exp (t • Q) i j) := by
  have h := flowOutput_series Q i (Pi.single j 1) t
  simpa only [Matrix.mulVec_single_one, Matrix.col_apply, flowOutput, pow_zero,
    Matrix.one_mul] using h

theorem phase_pre_exp {n m : ℕ}
    (N : Matrix (Fin (n + m)) (Fin (n + m)) ℝ) (Q : Matrix (Fin n) (Fin n) ℝ)
    (hpp : ∀ i j, N (Fin.castAdd m i) (Fin.castAdd m j) = Q i j)
    (hlp : ∀ i j, N (Fin.natAdd n i) (Fin.castAdd m j) = 0)
    (t : ℝ) (i j : Fin n) :
    NormedSpace.exp (t • N) (Fin.castAdd m i) (Fin.castAdd m j) =
      NormedSpace.exp (t • Q) i j := by
  apply HasSum.unique (phase_exp_entry_hasSum N (Fin.castAdd m i) (Fin.castAdd m j) t)
  simpa only [phase_pre_power N Q hpp hlp] using phase_exp_entry_hasSum Q i j t

theorem phase_exp_entry_hasDerivAt {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) (t : ℝ) :
    HasDerivAt (fun u => NormedSpace.exp (u • Q) i j)
      (∑ l, NormedSpace.exp (t • Q) i l * Q l j) t := by
  have h := flowOutput_hasDerivAt_right Q i (Pi.single j 1) t
  rw [Matrix.mulVec_single_one] at h
  convert! h using 1
  · funext u
    simp [flowOutput, Matrix.col]
  · simp [flowOutput, Matrix.mulVec, dotProduct, Matrix.col]

theorem phase_exp_entry_continuous {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    Continuous (fun t : ℝ => NormedSpace.exp (t • Q) i j) :=
  continuous_iff_continuousAt.mpr fun t => (phase_exp_entry_hasDerivAt Q i j t).continuousAt

theorem phase_flow_hasDerivAt_left {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) (v : Fin n → ℝ) (t : ℝ) :
    HasDerivAt (fun u => (NormedSpace.exp (u • Q) *ᵥ v) i)
      (∑ l, Q i l * (NormedSpace.exp (t • Q) *ᵥ v) l) t := by
  have h := flowOutput_hasDerivAt Q i v 0 t
  convert! h using 1
  · funext u
    simp [flowOutput]
  · simp only [flowOutput, zero_add, pow_one]
    rw [← Matrix.mulVec_mulVec]
    rfl

theorem phase_block_post_integral {n : ℕ}
    (N : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ) (Q : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin 2) ℝ) (D : Matrix (Fin 2) (Fin 2) ℝ)
    (hpp : ∀ i j, N (Fin.castAdd 2 i) (Fin.castAdd 2 j) = Q i j)
    (hlp : ∀ i j, N (Fin.natAdd n i) (Fin.castAdd 2 j) = 0)
    (hpl : ∀ i j, N (Fin.castAdd 2 i) (Fin.natAdd n j) = B i j)
    (hll : ∀ i j, N (Fin.natAdd n i) (Fin.natAdd n j) = D i j)
    (i : Fin n) (w : Fin 2 → ℝ) (t : ℝ) :
    (∑ j : Fin 2, NormedSpace.exp (t • N) (Fin.castAdd 2 i) (Fin.natAdd n j) * w j) =
      ∫ s in 0..t, ((NormedSpace.exp (s • Q) * B *
        NormedSpace.exp ((t-s) • D)) *ᵥ w) i := by
  let a (j : Fin 2) (s : ℝ) :=
    NormedSpace.exp (s • N) (Fin.castAdd 2 i) (Fin.natAdd n j)
  let b (j : Fin 2) (s : ℝ) := (NormedSpace.exp ((t-s) • D) *ᵥ w) j
  let v (j : Fin 2) (s : ℝ) := ∑ l, NormedSpace.exp (s • Q) i l * B l j
  have ha (j : Fin 2) (s : ℝ) : HasDerivAt (a j)
      (v j s + ∑ l : Fin 2, a l s * D l j) s := by
    have h := phase_exp_entry_hasDerivAt N (Fin.castAdd 2 i) (Fin.natAdd n j) s
    simpa only [Fin.sum_univ_add, hpl, hll, phase_pre_exp N Q hpp hlp, a, v] using h
  have hb (j : Fin 2) (s : ℝ) : HasDerivAt (b j)
      (-(∑ l : Fin 2, D j l * b l s)) s := by
    have h := (phase_flow_hasDerivAt_left D j w (t-s)).scomp s
      ((hasDerivAt_id s).const_sub t)
    simpa only [neg_smul, one_smul, Function.comp_def, b] using h
  have heq (s : ℝ) :
      ((NormedSpace.exp (s • Q) * B * NormedSpace.exp ((t-s) • D)) *ᵥ w) i =
        v 0 s * b 0 s + v 1 s * b 1 s := by
    rw [← Matrix.mulVec_mulVec]
    change (∑ j : Fin 2, v j s * b j s) = _
    exact Fin.sum_univ_two _
  have hderiv (s : ℝ) : HasDerivAt
      (fun s => a 0 s * b 0 s + a 1 s * b 1 s)
      (((NormedSpace.exp (s • Q) * B * NormedSpace.exp ((t-s) • D)) *ᵥ w) i) s := by
    rw [heq]
    convert! ((ha 0 s).mul (hb 0 s)).add ((ha 1 s).mul (hb 1 s)) using 1
    simp only [Fin.sum_univ_two]
    ring
  have hv (j : Fin 2) : Continuous (v j) := by
    apply continuous_finsetSum
    intro l _
    exact (phase_exp_entry_continuous Q i l).mul_const _
  have hbc (j : Fin 2) : Continuous (b j) :=
    continuous_iff_continuousAt.mpr fun s => (hb j s).continuousAt
  have hint : Continuous (fun s : ℝ =>
      ((NormedSpace.exp (s • Q) * B * NormedSpace.exp ((t-s) • D)) *ᵥ w) i) := by
    simp_rw [heq]
    exact ((hv 0).mul (hbc 0)).add ((hv 1).mul (hbc 1))
  have hne (j : Fin 2) : Fin.castAdd 2 i ≠ Fin.natAdd n j := by
    intro h
    have hh := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hh
    omega
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hderiv s) (hint.intervalIntegrable 0 t)
  simpa [a, b, Fin.sum_univ_two, Matrix.one_apply, hne] using h.symm

theorem commonClockIslandPhaseDensity_integral (k : ℕ) (c q r t : ℝ) :
    commonClockIslandPhaseDensity k c q r t =
      markFlux k c q r 0 t / 2 +
        ∫ s in 0..t, ((NormedSpace.exp (s • MarkovChain.Identifiability.generator k c q r) *
          commonClockFirstRate c *
          NormedSpace.exp ((2*(t-s)) • MarkovChain.Identifiability.pairGenerator k c q)) *ᵥ
              MarkovChain.Identifiability.pairDensity c) 0 := by
  have hpre := phase_pre_exp (n := 16) (m := 2) (commonClockIslandPhase k c q r)
      (MarkovChain.Identifiability.generator k c q r)
    (commonClockIslandPhase_pre_pre k c q r) (commonClockIslandPhase_post_pre k c q r)
  have hpost := phase_block_post_integral (commonClockIslandPhase k c q r)
    (MarkovChain.Identifiability.generator k c q r) (commonClockFirstRate c)
        ((2 : ℝ) • MarkovChain.Identifiability.pairGenerator k c q)
    (commonClockIslandPhase_pre_pre k c q r) (commonClockIslandPhase_post_pre k c q r)
    (commonClockIslandPhase_pre_post k c q r)
    (by intro i j; simp) (0 : Fin 16) (MarkovChain.Identifiability.pairDensity c) t
  rw [commonClockIslandPhaseDensity_exp]
  change (∑ j : Fin (16+2), NormedSpace.exp (t • commonClockIslandPhase k c q r)
    (Fin.castAdd 2 (0 : Fin 16)) j * commonClockIslandReward c j) = _
  rw [Fin.sum_univ_add]
  simp only [commonClockIslandReward_pre, commonClockIslandReward_post, hpre]
  rw [hpost]
  congr 1
  · simp only [markFlux, flowOutput, pow_zero, Matrix.one_mul, Matrix.mulVec,
      dotProduct, mul_div_assoc, Finset.sum_div]
  · apply intervalIntegral.integral_congr
    intro s _
    simp only [smul_smul, mul_comm]

end Rhone.Statistics.Identifiability
