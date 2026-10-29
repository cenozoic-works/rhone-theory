/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ThreeSiteSeparator.BlockStatistics
public import Rhone.Statistics.ThreeSiteSeparator.ObservableBounds

/-! # Bounds for the five three-site pattern features -/

@[expose] public section

namespace Rhone.Statistics.ThreeSiteRobustness
open ThreeSiteSeparator ThreeTipSites SingleSiteChannel

theorem uScore_bound {K : ℕ} (hK : 2 ≤ K) (e : Fin 3) (x : Triple K) :
    |uScore e x| ≤ 1 := by
  fin_cases e <;> exact pairScore_abs_le_one hK _ _

theorem vScore_bound {K : ℕ} (hK : 3 ≤ K) (x : Triple K) : |vScore x| ≤ 1 :=
  tripleScore_abs_le_one hK _ _ _

theorem threeProduct_bound {K : ℕ} (f g h : Triple K → ℝ)
    (hf : ∀ x, |f x| ≤ 1) (hg : ∀ x, |g x| ≤ 1) (hh : ∀ x, |h x| ≤ 1)
    (x : Panel K 3) : |threeProduct f g h x| ≤ 1 := by
  unfold threeProduct
  rw [abs_mul, abs_mul]
  have hab := mul_le_mul (hf (x 0)) (hg (x 1)) (abs_nonneg (g (x 1))) zero_le_one
  norm_num only [one_mul] at hab
  simpa only [one_mul] using mul_le_mul hab (hh (x 2)) (abs_nonneg (h (x 2))) zero_le_one

theorem average_three_bound {a b c : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (hc : |c| ≤ 1) : |(a + b + c) / 3| ≤ 1 := by
  have h1 := abs_le.mp ha
  have h2 := abs_le.mp hb
  have h3 := abs_le.mp hc
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem average_six_bound {a b c d e f : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (hc : |c| ≤ 1) (hd : |d| ≤ 1) (he : |e| ≤ 1) (hf : |f| ≤ 1) :
    |(a + b + c + d + e + f) / 6| ≤ 1 := by
  have h1 := abs_le.mp ha
  have h2 := abs_le.mp hb
  have h3 := abs_le.mp hc
  have h4 := abs_le.mp hd
  have h5 := abs_le.mp he
  have h6 := abs_le.mp hf
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem feature_bounds {K : ℕ} (hK : 3 ≤ K) (x : Panel K 3) :
    |aStat x| ≤ 1 ∧ |p2Stat x| ≤ 1 ∧ |p3Stat x| ≤ 1 ∧
      |hStat x| ≤ 1 ∧ |jStat x| ≤ 1 := by
  have hu := uScore_bound (by omega : 2 ≤ K)
  have hv := vScore_bound hK
  have hone : ∀ _ : Triple K, |(1 : ℝ)| ≤ 1 := by intro; norm_num
  constructor
  · exact average_three_bound
      (threeProduct_bound _ _ _ (hu 0) hone hone x)
      (threeProduct_bound _ _ _ (hu 1) hone hone x)
      (threeProduct_bound _ _ _ (hu 2) hone hone x)
  constructor
  · exact average_three_bound
      (threeProduct_bound _ _ _ (hu 0) (hu 0) hone x)
      (threeProduct_bound _ _ _ (hu 1) (hu 1) hone x)
      (threeProduct_bound _ _ _ (hu 2) (hu 2) hone x)
  constructor
  · exact average_three_bound
      (threeProduct_bound _ _ _ (hu 0) (hu 0) (hu 0) x)
      (threeProduct_bound _ _ _ (hu 1) (hu 1) (hu 1) x)
      (threeProduct_bound _ _ _ (hu 2) (hu 2) (hu 2) x)
  constructor
  · exact average_three_bound
      (threeProduct_bound _ _ _ hv (hu 0) (hu 0) x)
      (threeProduct_bound _ _ _ hv (hu 1) (hu 1) x)
      (threeProduct_bound _ _ _ hv (hu 2) (hu 2) x)
  · exact average_six_bound
      (threeProduct_bound _ _ _ hv (hu 0) (hu 1) x)
      (threeProduct_bound _ _ _ hv (hu 0) (hu 2) x)
      (threeProduct_bound _ _ _ hv (hu 1) (hu 0) x)
      (threeProduct_bound _ _ _ hv (hu 1) (hu 2) x)
      (threeProduct_bound _ _ _ hv (hu 2) (hu 0) x)
      (threeProduct_bound _ _ _ hv (hu 2) (hu 1) x)

end Rhone.Statistics.ThreeSiteRobustness
