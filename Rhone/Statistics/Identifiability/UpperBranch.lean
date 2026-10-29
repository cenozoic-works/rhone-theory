/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ShearDensity
public import Rhone.Statistics.Identifiability.RankFactorization

/-! # Mark fluxes and the upper-branch density of the ordered event law -/

@[expose] public section

open scoped Matrix Matrix.Norms.Operator ENNReal
open Set MeasureTheory
namespace Rhone.Statistics.Identifiability

theorem markFlux_one (k : Nat) (c q r s : ℝ) :
    markFlux k c q r 1 s = transferJet k c q r 0 0 s := by
  unfold markFlux transferJet
  congr 1
  funext i
  exact markRates_A_same c i

theorem markFlux_two (k : Nat) (c q r s : ℝ) :
    markFlux k c q r 2 s = transferJet k c q r 0 1 s := by
  unfold markFlux transferJet
  congr 1
  funext i
  exact markRates_A_apart c i

theorem upperDensity_markFlux (k : Nat) (c q r s t : ℝ) :
    upperDensity k c q r s t =
      markFlux k c q r 1 s * forwardDensity k c q 0 (t-s) +
      markFlux k c q r 2 s * forwardDensity k c q 1 (t-s) := by
  rw [markFlux_one, markFlux_two, upperDensity, ← Matrix.mulVec_mulVec]
  simp only [transferJet_zero_order, forwardDensity, flowOutput, pow_zero, Matrix.one_mul]
  conv_lhs => rw [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem forwardDensity_nonneg (k : Nat) {c q t : ℝ}
    (hc : 0 ≤ c) (hq : 0 ≤ q) (ht : 0 ≤ t) (i : Fin 2) :
    0 ≤ forwardDensity k c q i t := by
  simp only [forwardDensity, flowOutput, pow_zero, Matrix.one_mul]
  exact matrix_mulVec_nonneg _ _ (exp_generator_nonneg _ (pairGenerator_metzler k hq) ht)
    (pairDensity_nonneg hc) i

noncomputable def upperEventLaw (k : Nat) (c q r : ℝ) : Measure (ℝ × ℝ) :=
  ((markLaw k c q r 1).prod (firstExitLaw (MarkovChain.Identifiability.pairGenerator k c q) 0)).map
      upperShear +
  ((markLaw k c q r 2).prod (firstExitLaw (MarkovChain.Identifiability.pairGenerator k c q) 1)).map
      upperShear

theorem upperEventLaw_density (k : Nat) {c q r : ℝ}
    (hc : 0 ≤ c) (hq : 0 ≤ q) (hr : 0 ≤ r) :
    upperEventLaw k c q r = (planeVolume.restrict upperWedge).withDensity
      (fun p => ENNReal.ofReal (upperDensity k c q r p.1 p.2)) := by
  have hmark (m : Fin 5) : Measurable (fun s => ENNReal.ofReal (markFlux k c q r m s)) :=
    (markFlux_continuous k c q r m).measurable.ennreal_ofReal
  have hpair (i : Fin 2) : Measurable (fun t => ENNReal.ofReal (forwardDensity k c q i t)) :=
    (flowOutput_continuous _ _ _ _).measurable.ennreal_ofReal
  unfold upperEventLaw markLaw firstExitLaw
  simp only [pair_exitRate]
  change (((volume.restrict (Ioi 0)).withDensity _).prod
    ((volume.restrict (Ioi 0)).withDensity
      (fun t => ENNReal.ofReal (forwardDensity k c q 0 t)))).map
    upperShear + (((volume.restrict (Ioi 0)).withDensity _).prod
    ((volume.restrict (Ioi 0)).withDensity
      (fun t => ENNReal.ofReal (forwardDensity k c q 1 t)))).map
    upperShear = _
  rw [shear_product_density _ _ (hmark 1) (hpair 0),
    shear_product_density _ _ (hmark 2) (hpair 1)]
  have hm1 : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (markFlux k c q r 1 p.1) *
      ENNReal.ofReal (forwardDensity k c q 0 (p.2-p.1))) :=
    ((hmark 1).comp measurable_fst).mul ((hpair 0).comp (measurable_snd.sub measurable_fst))
  rw [← withDensity_add_left hm1]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem upperWedge_open.measurableSet] with p hp
  have hs : 0 ≤ p.1 := hp.1.le
  have hd : 0 ≤ p.2-p.1 := sub_nonneg.mpr hp.2.le
  change ENNReal.ofReal (markFlux k c q r 1 p.1) * ENNReal.ofReal
    (forwardDensity k c q 0 (p.2-p.1)) + ENNReal.ofReal (markFlux k c q r 2 p.1) *
    ENNReal.ofReal (forwardDensity k c q 1 (p.2-p.1)) = _
  rw [← ENNReal.ofReal_mul (markFlux_nonneg k hc hq hr hs 1),
    ← ENNReal.ofReal_mul (markFlux_nonneg k hc hq hr hs 2),
    ← ENNReal.ofReal_add
      (mul_nonneg (markFlux_nonneg k hc hq hr hs 1) (forwardDensity_nonneg k hc hq hd 0))
      (mul_nonneg (markFlux_nonneg k hc hq hr hs 2) (forwardDensity_nonneg k hc hq hd 1)),
    ← upperDensity_markFlux]

end Rhone.Statistics.Identifiability
