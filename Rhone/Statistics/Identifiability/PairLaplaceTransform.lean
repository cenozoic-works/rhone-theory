/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.RewardIntegral
public import Rhone.Statistics.Identifiability.PairNonidentifiability

/-! # Exact Laplace transform and mean of the same-deme pair coalescence time -/

@[expose] public section

open scoped Matrix Matrix.Norms.Operator Topology
open Set Filter MeasureTheory

namespace Rhone.Statistics.Identifiability

set_option backward.isDefEq.respectTransparency false

theorem flowOutput_sub_scalar_identity {d : Nat}
    (Q : Matrix (Fin d) (Fin d) ℝ) (s : ℝ) (i : Fin d) (v : Fin d → ℝ) (t : ℝ) :
    flowOutput (Q - s • 1) i v 0 t = Real.exp (-s * t) * flowOutput Q i v 0 t := by
  have hsplit : t • (Q - s • 1) = (-s * t) • 1 + t • Q := by
    ext a b
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have hcomm : Commute ((-s * t) • (1 : Matrix (Fin d) (Fin d) ℝ)) (t • Q) :=
    (Commute.one_left _).smul_left _
  simp only [flowOutput, pow_zero, Matrix.one_mul]
  rw [hsplit, Matrix.exp_add_of_commute _ _ hcomm, exp_smul_identity,
    Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mulVec]
  rfl

theorem isMetzler_sub_scalar_identity {d : Nat}
    {Q : Matrix (Fin d) (Fin d) ℝ} (hQ : IsMetzler Q) (s : ℝ) :
    IsMetzler (Q - s • 1) := by
  intro i j hij
  simpa [Matrix.one_apply, hij] using hQ i j hij

theorem survival_sub_scalar_identity_tendsto_zero {d : Nat}
    (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : IsMetzler Q)
    {s : ℝ} (hs : 0 ≤ s) (i : Fin d)
    (htail : Tendsto (flowOutput Q i (fun _ => 1) 0) atTop (𝓝 0)) :
    Tendsto (flowOutput (Q - s • 1) i (fun _ => 1) 0) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htail
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact survival_nonneg _ (isMetzler_sub_scalar_identity hQ s) i ht
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    rw [flowOutput_sub_scalar_identity]
    exact mul_le_of_le_one_left (survival_nonneg Q hQ i ht)
      (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs) ht))

noncomputable def pairLaplaceDenominator (k : Nat) (c q s : ℝ) : ℝ :=
  s ^ 2 + s * (c + 2 * ((k : ℝ) + 2) * q) + 2 * c * q

noncomputable def pairLaplacePotential (k : Nat) (c q s : ℝ) : Fin 2 → ℝ :=
  ![c * (s + 2*q) / pairLaplaceDenominator k c q s,
    2*c*q / pairLaplaceDenominator k c q s]

theorem pairLaplaceDenominator_pos (k : Nat) {c q s : ℝ}
    (hc : 0 < c) (hq : 0 < q) (hs : 0 ≤ s) :
    0 < pairLaplaceDenominator k c q s := by
  unfold pairLaplaceDenominator
  positivity

theorem pairLaplacePotential_equation (k : Nat) {c q s : ℝ}
    (hD : pairLaplaceDenominator k c q s ≠ 0) :
    (MarkovChain.Identifiability.pairGenerator k c q - s • 1) *ᵥ pairLaplacePotential k c q s =
        -MarkovChain.Identifiability.pairDensity c := by
  ext i
  fin_cases i <;>
    simp [MarkovChain.Identifiability.pairGenerator, pairLaplacePotential,
        MarkovChain.Identifiability.totalMigration, MarkovChain.Identifiability.pairDensity,
      Matrix.mulVec, Matrix.one_apply, dotProduct, Fin.sum_univ_succ] <;>
    field_simp [hD] <;> simp only [pairLaplaceDenominator] <;> ring_nf

theorem pair_density_laplace_integrable (k : Nat) {c q s : ℝ}
    (hc : 0 < c) (hq : 0 < q) (hs : 0 ≤ s) :
    IntegrableOn (fun t => Real.exp (-s*t) * densityJet k c q 0 t) (Ioi 0) := by
  have h := reward_integrable (MarkovChain.Identifiability.pairGenerator k c q - s • 1)
    (isMetzler_sub_scalar_identity (pairGenerator_metzler k hq.le) s) 0
    (pairLaplacePotential k c q s) (MarkovChain.Identifiability.pairDensity c)
    (pairLaplacePotential_equation k (pairLaplaceDenominator_pos k hc hq hs).ne')
    (by intro j; fin_cases j <;> simp [MarkovChain.Identifiability.pairDensity, hc.le])
    (survival_sub_scalar_identity_tendsto_zero _ (pairGenerator_metzler k hq.le) hs 0
      (pair_survival_tendsto_zero k hc hq 0))
  convert h using 1
  ext t
  exact (flowOutput_sub_scalar_identity _ s 0 (MarkovChain.Identifiability.pairDensity c) t).symm

theorem pair_density_laplace_transform (k : Nat) {c q s : ℝ}
    (hc : 0 < c) (hq : 0 < q) (hs : 0 ≤ s) :
    (∫ t in Ioi 0, Real.exp (-s*t) * densityJet k c q 0 t) =
      c * (s + 2*q) / (s^2 + s*(c + 2*((k : ℝ)+2)*q) + 2*c*q) := by
  have h := reward_integral_eq_potential (MarkovChain.Identifiability.pairGenerator k c q - s • 1)
    (isMetzler_sub_scalar_identity (pairGenerator_metzler k hq.le) s) 0
    (pairLaplacePotential k c q s) (MarkovChain.Identifiability.pairDensity c)
    (pairLaplacePotential_equation k (pairLaplaceDenominator_pos k hc hq hs).ne')
    (by intro j; fin_cases j <;> simp [MarkovChain.Identifiability.pairDensity, hc.le])
    (survival_sub_scalar_identity_tendsto_zero _ (pairGenerator_metzler k hq.le) hs 0
      (pair_survival_tendsto_zero k hc hq 0))
  simpa only [flowOutput_sub_scalar_identity, densityJet, pairLaplacePotential,
    Matrix.cons_val_zero, pairLaplaceDenominator] using h

noncomputable def pairMeanPotential (k : Nat) (c q : ℝ) : Fin 2 → ℝ :=
  ![((k : ℝ) + 2) / c, ((k : ℝ) + 2) / c + 1 / (2*q)]

theorem pairMeanPotential_equation (k : Nat) {c q : ℝ} (hc : c ≠ 0) (hq : q ≠ 0) :
    MarkovChain.Identifiability.pairGenerator k c q *ᵥ pairMeanPotential k c q =
        -MarkovChain.Identifiability.pairSurvival := by
  ext i
  fin_cases i <;>
    simp [MarkovChain.Identifiability.pairGenerator, pairMeanPotential,
        MarkovChain.Identifiability.totalMigration, MarkovChain.Identifiability.pairSurvival,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> field_simp [hc, hq] <;> ring

theorem pair_survival_integrable (k : Nat) {c q : ℝ} (hc : 0 < c) (hq : 0 < q) :
    IntegrableOn (survivalJet k c q 0) (Ioi 0) := by
  exact reward_integrable _ (pairGenerator_metzler k hq.le) 0
    (pairMeanPotential k c q) MarkovChain.Identifiability.pairSurvival
        (pairMeanPotential_equation k hc.ne' hq.ne')
    (fun _ => zero_le_one) (pair_survival_tendsto_zero k hc hq 0)

theorem pair_survival_integral_mean (k : Nat) {c q : ℝ} (hc : 0 < c) (hq : 0 < q) :
    (∫ t in Ioi 0, survivalJet k c q 0 t) = ((k : ℝ) + 2) / c := by
  exact reward_integral_eq_potential _ (pairGenerator_metzler k hq.le) 0
    (pairMeanPotential k c q) MarkovChain.Identifiability.pairSurvival
        (pairMeanPotential_equation k hc.ne' hq.ne')
    (fun _ => zero_le_one) (pair_survival_tendsto_zero k hc hq 0)

end Rhone.Statistics.Identifiability
