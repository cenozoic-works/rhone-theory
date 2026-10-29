/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.WFLDStationaryRatio

/-! # Positivity of the denominator of the finite-chain stationary LD ratio -/

@[expose] public section
noncomputable section
namespace Rhone.MarkovChain.WFAllocationLD

theorem ld_sigma_denominator_pos (m c u : ℝ) (hm : 3 ≤ m)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2) :
    0 < ldSigmaDenominator m c u := by
  let k := (1-c)*(1-2*u)^4
  let l := (1-c)^2*(1-2*u)^4
  let a := (m-2)^2*(m-1)
  let b := m^3-3*m^2+4*m-4
  let d := 4*(m-1)^2*(m-2)^2
  have hc : 0 ≤ 1-c := by linarith
  have hcone : 1-c ≤ 1 := by linarith
  have hu : 0 ≤ 1-2*u := by linarith
  have huone : 1-2*u ≤ 1 := by linarith
  have hk0 : 0 ≤ k := mul_nonneg hc (pow_nonneg hu 4)
  have hl0 : 0 ≤ l := mul_nonneg (sq_nonneg _) (pow_nonneg hu 4)
  have hk1 : k ≤ 1 := by
    calc
      k ≤ 1*(1-2*u)^4 := mul_le_mul_of_nonneg_right hcone (pow_nonneg hu 4)
      _ ≤ 1 := by simpa only [one_mul] using (pow_le_one₀ hu huone (n := 4))
  have hl1 : l ≤ 1 := by
    calc
      l ≤ 1*(1-2*u)^4 := mul_le_mul_of_nonneg_right (pow_le_one₀ hc hcone) (pow_nonneg hu 4)
      _ ≤ 1 := by simpa only [one_mul] using (pow_le_one₀ hu huone (n := 4))
  have ha : 0 ≤ a := mul_nonneg (sq_nonneg _) (by linarith)
  have hb : 0 ≤ b := by
    have hh : b = m^2*(m-3)+4*(m-1) := by dsimp [b]; ring
    rw [hh]
    exact add_nonneg (mul_nonneg (sq_nonneg _) (by linarith))
      (mul_nonneg (by norm_num) (by linarith))
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hma : 0 < m^3-a := by
    have hh : m^3-a = 5*(m-1)^2+2*m-1 := by dsimp [a]; ring
    rw [hh]
    nlinarith [sq_nonneg (m-1)]
  have hmb : 0 < m^3-b := by
    have hh : m^3-b = 3*(m-1)^2+2*m+1 := by dsimp [b]; ring
    rw [hh]
    positivity
  have hmb' : 0 ≤ m^3-b*l := by
    have hh := mul_nonneg hb (sub_nonneg.mpr hl1)
    linarith
  have hbase : 0 < m^2*(11*(m-1)^2+2*m+1) := by positivity
  have hterm1 : 0 ≤ (1-k)*(a*(m^3-b*l)+d*l) :=
    mul_nonneg (sub_nonneg.mpr hk1) (add_nonneg (mul_nonneg ha hmb') (mul_nonneg hd hl0))
  have hterm2 : 0 ≤ (1-l)*(b*(m^3-a)+d) :=
    mul_nonneg (sub_nonneg.mpr hl1) (add_nonneg (mul_nonneg hb hma.le) hd)
  have he : ldSigmaDenominator m c u = (m-1)*
      (m^2*(11*(m-1)^2+2*m+1)+(1-k)*(a*(m^3-b*l)+d*l)+(1-l)*(b*(m^3-a)+d)) := by
    unfold ldSigmaDenominator
    dsimp [a,b,d,k,l]
    ring
  rw [he]
  exact mul_pos (by linarith) (by linarith)

end Rhone.MarkovChain.WFAllocationLD
