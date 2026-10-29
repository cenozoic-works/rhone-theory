/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ThreeSiteSeparator.BlockExpectations

/-! # The five explicit three-site pattern statistics and fixed-cherry means -/

@[expose] public section

noncomputable section
open scoped BigOperators
namespace Rhone.Statistics.ThreeSiteSeparator
open ThreeTipSites SingleSiteChannel

def aStat {K : ℕ} (x : Panel K 3) : ℝ :=
  (threeProduct (uScore 0) (fun _ => 1) (fun _ => 1) x +
    threeProduct (uScore 1) (fun _ => 1) (fun _ => 1) x +
    threeProduct (uScore 2) (fun _ => 1) (fun _ => 1) x)/3

def p2Stat {K : ℕ} (x : Panel K 3) : ℝ :=
  (threeProduct (uScore 0) (uScore 0) (fun _ => 1) x +
    threeProduct (uScore 1) (uScore 1) (fun _ => 1) x +
    threeProduct (uScore 2) (uScore 2) (fun _ => 1) x)/3

def p3Stat {K : ℕ} (x : Panel K 3) : ℝ :=
  (threeProduct (uScore 0) (uScore 0) (uScore 0) x +
    threeProduct (uScore 1) (uScore 1) (uScore 1) x +
    threeProduct (uScore 2) (uScore 2) (uScore 2) x)/3

def hStat {K : ℕ} (x : Panel K 3) : ℝ :=
  (threeProduct vScore (uScore 0) (uScore 0) x +
    threeProduct vScore (uScore 1) (uScore 1) x +
    threeProduct vScore (uScore 2) (uScore 2) x)/3

def jStat {K : ℕ} (x : Panel K 3) : ℝ :=
  (threeProduct vScore (uScore 0) (uScore 1) x +
    threeProduct vScore (uScore 0) (uScore 2) x +
    threeProduct vScore (uScore 1) (uScore 0) x +
    threeProduct vScore (uScore 1) (uScore 2) x +
    threeProduct vScore (uScore 2) (uScore 0) x +
    threeProduct vScore (uScore 2) (uScore 1) x)/6

lemma aStat_mean {K : ℕ} (hK : 3 ≤ K) (k : ℝ) (t : ℝ × ℝ) (q : Fin 3) :
    fixedMean (uniformBlockRoots K 3 (by omega)) k t q aStat =
      (Real.exp (-k*t.1) + 2*Real.exp (-k*(t.1+t.2)))/3 := by
  have h2 : 2 ≤ K := by omega
  unfold aStat
  simp only [fixedMean_div, fixedMean_add, threeProduct_mean,
    oriented_pair_mean h2, oriented_one_mean (by omega : 0 < K), mul_one]
  fin_cases q <;> norm_num [pairMeans, Fin.ext_iff] <;> ring

lemma p2Stat_mean {K : ℕ} (hK : 3 ≤ K) (k : ℝ) (t : ℝ × ℝ) (q : Fin 3) :
    fixedMean (uniformBlockRoots K 3 (by omega)) k t q p2Stat =
      (Real.exp (-k*t.1)^2 + 2*Real.exp (-k*(t.1+t.2))^2)/3 := by
  have h2 : 2 ≤ K := by omega
  unfold p2Stat
  simp only [fixedMean_div, fixedMean_add, threeProduct_mean,
    oriented_pair_mean h2, oriented_one_mean (by omega : 0 < K), mul_one]
  fin_cases q <;> norm_num [pairMeans, Fin.ext_iff] <;> ring

lemma p3Stat_mean {K : ℕ} (hK : 3 ≤ K) (k : ℝ) (t : ℝ × ℝ) (q : Fin 3) :
    fixedMean (uniformBlockRoots K 3 (by omega)) k t q p3Stat =
      (Real.exp (-k*t.1)^3 + 2*Real.exp (-k*(t.1+t.2))^3)/3 := by
  have h2 : 2 ≤ K := by omega
  unfold p3Stat
  simp only [fixedMean_div, fixedMean_add, threeProduct_mean, oriented_pair_mean h2]
  fin_cases q <;> norm_num [pairMeans, Fin.ext_iff] <;> ring

lemma hStat_mean {K : ℕ} (hK : 3 ≤ K) (k : ℝ) (t : ℝ × ℝ) (q : Fin 3) :
    fixedMean (uniformBlockRoots K 3 (by omega)) k t q hStat =
      secondMomentKernel k t*(Real.exp (-k*t.1)^2 + 2*Real.exp (-k*(t.1+t.2))^2)/3 := by
  have h2 : 2 ≤ K := by omega
  unfold hStat
  simp only [fixedMean_div, fixedMean_add, threeProduct_mean,
    oriented_pair_mean h2, oriented_triple_mean hK]
  fin_cases q <;> norm_num [pairMeans, Fin.ext_iff] <;> ring

lemma jStat_mean {K : ℕ} (hK : 3 ≤ K) (k : ℝ) (t : ℝ × ℝ) (q : Fin 3) :
    fixedMean (uniformBlockRoots K 3 (by omega)) k t q jStat =
      secondMomentKernel k t*(2*Real.exp (-k*t.1)*Real.exp (-k*(t.1+t.2)) +
        Real.exp (-k*(t.1+t.2))^2)/3 := by
  have h2 : 2 ≤ K := by omega
  unfold jStat
  simp only [fixedMean_div, fixedMean_add, threeProduct_mean,
    oriented_pair_mean h2, oriented_triple_mean hK]
  fin_cases q <;> norm_num [pairMeans, Fin.ext_iff] <;> ring

end Rhone.Statistics.ThreeSiteSeparator
