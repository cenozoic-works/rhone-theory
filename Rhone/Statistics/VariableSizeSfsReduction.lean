/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Statistics.VariableSizeSfs

/-!
# Reduction of variable-size SFS means to clock Laplace transforms

Source: myers_fefferman_patterson2008, secs. 3–5. -/

@[expose] public section

namespace Rhone.Statistics

open MeasureTheory ProbabilityTheory Finset MarkovChain Coalescent Rhone.Combinatorics Probability
open Filter
open scoped ENNReal NNReal Topology

noncomputable def clockLaplace (ν : ℝ → ℝ) (r : ℝ) : ℝ :=
  ∫ t in Set.Ioi 0, Real.exp (-(r * cumIntensity ν t))

variable {ν : ℝ → ℝ}

theorem integrableOn_exp_neg_mul_cumIntensity (hν : IsSizeFunction ν)
    (hint : IntegrableOn (fun t => Real.exp (-cumIntensity ν t)) (Set.Ioi 0)) {r : ℝ}
    (hr : 1 ≤ r) :
    IntegrableOn (fun t => Real.exp (-(r * cumIntensity ν t))) (Set.Ioi 0) := by
  have hcont : ContinuousOn (fun u => Real.exp (-(r * cumIntensity ν u))) (Set.Ioi 0) :=
    (Real.continuous_exp.comp_continuousOn ((continuousOn_const.mul hν.continuousOn).neg)).mono
      Set.Ioi_subset_Ici_self
  refine Integrable.mono' hint (hcont.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hΛ := hν.cumIntensity_nonneg (le_of_lt ht)
  exact Real.exp_le_exp.2 (by nlinarith)

theorem integral_lineageLaw_cumIntensity (hν : IsSizeFunction ν)
    (hint : IntegrableOn (fun t => Real.exp (-cumIntensity ν t)) (Set.Ioi 0)) (n : ℕ) {k : ℕ}
    (hk : 2 ≤ k) :
    IntegrableOn (fun t => lineageLaw n (cumIntensity ν t) k) (Set.Ioi 0) ∧
      ∫ t in Set.Ioi 0, lineageLaw n (cumIntensity ν t) k =
        ∑ j ∈ Icc k n, lineageCoeff n k j * clockLaplace ν (coalRate j) := by
  have hrate : ∀ j ∈ Icc k n, (1 : ℝ) ≤ (coalRate j : ℝ) := by
    intro j hj
    have hj2 : 2 ≤ j := hk.trans (mem_Icc.1 hj).1
    rw [coalRate_cast_eq_choose]
    have h1 : 1 ≤ j.choose 2 := Nat.choose_pos hj2
    exact_mod_cast h1
  have hL : (fun t => lineageLaw n (cumIntensity ν t) k) =
      fun t => ∑ j ∈ Icc k n,
        Real.exp (-((coalRate j : ℝ) * cumIntensity ν t)) * lineageCoeff n k j := by
    funext t
    simp only [lineageLaw, show 1 ≤ k from by omega, ↓reduceIte]
  have hi : ∀ j ∈ Icc k n, Integrable (fun t =>
      Real.exp (-((coalRate j : ℝ) * cumIntensity ν t)) * lineageCoeff n k j)
        (volume.restrict (Set.Ioi 0)) := fun j hj =>
    (integrableOn_exp_neg_mul_cumIntensity hν hint (hrate j hj)).mul_const _
  rw [hL]
  refine ⟨integrable_finsetSum _ hi, ?_⟩
  rw [integral_finsetSum _ hi]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_mul_const, clockLaplace, mul_comm]

theorem sum_lineageCoeff_mul_clockLaplace_nonneg (hν : IsSizeFunction ν)
    (hint : IntegrableOn (fun t => Real.exp (-cumIntensity ν t)) (Set.Ioi 0)) {n k : ℕ}
    (hk : 2 ≤ k) (hkn : k ≤ n) :
    0 ≤ ∑ j ∈ Icc k n, lineageCoeff n k j * clockLaplace ν (coalRate j) := by
  rw [← (integral_lineageLaw_cumIntensity hν hint n hk).2]
  exact setIntegral_nonneg measurableSet_Ioi fun t ht =>
    lineageLaw_cumIntensity_nonneg hν hk hkn (le_of_lt ht)

theorem lintegral_lineageLaw_cumIntensity (hν : IsSizeFunction ν)
    (hint : IntegrableOn (fun t => Real.exp (-cumIntensity ν t)) (Set.Ioi 0)) {n k : ℕ}
    (hk : 2 ≤ k) (hkn : k ≤ n) :
    ∫⁻ t in Set.Ioi 0, ENNReal.ofReal (lineageLaw n (cumIntensity ν t) k) =
      ENNReal.ofReal (∑ j ∈ Icc k n, lineageCoeff n k j * clockLaplace ν (coalRate j)) := by
  obtain ⟨hI, hval⟩ := integral_lineageLaw_cumIntensity hν hint n hk
  rw [← hval, ofReal_integral_eq_lintegral_ofReal hI]
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact lineageLaw_cumIntensity_nonneg hν hk hkn (le_of_lt ht)

theorem variableSizeMarkedLaw_sfs_mean_clockLaplace (hν : IsSizeFunction ν)
    (hint : IntegrableOn (fun t => Real.exp (-cumIntensity ν t)) (Set.Ioi 0)) {n i : ℕ}
    (hi : 1 ≤ i) (hin : i < n) (θ : ℝ≥0) :
    ∫ x, markedKingmanSfs n i x ∂variableSizeMarkedLaw n ν θ =
      (θ : ℝ) / 2 * ∑ k ∈ Icc 2 n, (k : ℝ) * ((subtendProb n k i : ℚ) : ℝ) *
        ∑ j ∈ Icc k n, lineageCoeff n k j * clockLaplace ν (coalRate j) :=
  variableSizeMarkedLaw_sfs_mean_of_levelTime hν hi hin θ
    (fun k => ∑ j ∈ Icc k n, lineageCoeff n k j * clockLaplace ν (coalRate j))
    (fun _ hk => sum_lineageCoeff_mul_clockLaplace_nonneg hν hint (mem_Icc.1 hk).1
      (mem_Icc.1 hk).2)
    (fun _ hk => lintegral_lineageLaw_cumIntensity hν hint (mem_Icc.1 hk).1 (mem_Icc.1 hk).2)

theorem lintegral_variableSizeMarkedLaw_sfs_clockLaplace (hν : IsSizeFunction ν)
    (hint : IntegrableOn (fun t => Real.exp (-cumIntensity ν t)) (Set.Ioi 0)) {n i : ℕ}
    (hi : 1 ≤ i) (hin : i < n) (θ : ℝ≥0) :
    ∫⁻ x, ENNReal.ofReal (markedKingmanSfs n i x) ∂variableSizeMarkedLaw n ν θ =
      ENNReal.ofReal ((θ : ℝ) / 2 * ∑ k ∈ Icc 2 n, (k : ℝ) * ((subtendProb n k i : ℚ) : ℝ) *
        ∑ j ∈ Icc k n, lineageCoeff n k j * clockLaplace ν (coalRate j)) := by
  have hsp : ∀ k : ℕ, (0 : ℝ) ≤ (k : ℝ) * ((subtendProb n k i : ℚ) : ℝ) := fun k =>
    mul_nonneg (Nat.cast_nonneg _) (by exact_mod_cast subtendProb_nonneg n k i)
  have hτ : ∀ k ∈ Icc 2 n,
      0 ≤ ∑ j ∈ Icc k n, lineageCoeff n k j * clockLaplace ν (coalRate j) := fun k hk =>
    sum_lineageCoeff_mul_clockLaplace_nonneg hν hint (mem_Icc.1 hk).1 (mem_Icc.1 hk).2
  rw [lintegral_variableSizeMarkedLaw_sfs hν hi hin θ, ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_sum_of_nonneg fun k hk => mul_nonneg (hsp k) (hτ k hk)]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [lintegral_lineageLaw_cumIntensity hν hint (mem_Icc.1 hk).1 (mem_Icc.1 hk).2,
    ENNReal.ofReal_mul (hsp k)]

theorem lintegral_variableSizeMarkedLaw_sfs_congr_clockLaplace {ν₁ ν₂ : ℝ → ℝ}
    (h₁ : IsSizeFunction ν₁) (h₂ : IsSizeFunction ν₂)
    (hint₁ : IntegrableOn (fun t => Real.exp (-cumIntensity ν₁ t)) (Set.Ioi 0))
    (hint₂ : IntegrableOn (fun t => Real.exp (-cumIntensity ν₂ t)) (Set.Ioi 0)) {n : ℕ}
    (hL : ∀ j ∈ Icc 2 n, clockLaplace ν₁ (coalRate j) = clockLaplace ν₂ (coalRate j))
    {i : ℕ} (hi : 1 ≤ i) (hin : i < n) (θ : ℝ≥0) :
    ∫⁻ x, ENNReal.ofReal (markedKingmanSfs n i x) ∂variableSizeMarkedLaw n ν₁ θ =
      ∫⁻ x, ENNReal.ofReal (markedKingmanSfs n i x) ∂variableSizeMarkedLaw n ν₂ θ := by
  rw [lintegral_variableSizeMarkedLaw_sfs_clockLaplace h₁ hint₁ hi hin θ,
    lintegral_variableSizeMarkedLaw_sfs_clockLaplace h₂ hint₂ hi hin θ]
  congr 2
  refine Finset.sum_congr rfl fun k hk => ?_
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [hL j (mem_Icc.2 ⟨(mem_Icc.1 hk).1.trans (mem_Icc.1 hj).1, (mem_Icc.1 hj).2⟩)]

end Rhone.Statistics
