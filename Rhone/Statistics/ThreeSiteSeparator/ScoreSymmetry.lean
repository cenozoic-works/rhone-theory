/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.ThreeSiteSeparator.SiteScores

/-! # Score means for every shared cherry, using explicit finite relabelling -/

@[expose] public section

noncomputable section
open scoped BigOperators
namespace Rhone.Statistics.ThreeSiteSeparator
open ThreeTipSites SingleSiteChannel

lemma pairScore_symm (K : ℕ) (a b : Fin K) : pairScore K a b = pairScore K b a := by
  simp only [pairScore, eq_comm]

lemma tripleScore_cycle (K : ℕ) (a b c : Fin K) :
    tripleScore K a b c = tripleScore K b c a := by
  have he : (a = b ∧ a = c) ↔ (b = c ∧ b = a) := by
    constructor
    · rintro ⟨h, h'⟩
      exact ⟨h.symm.trans h', h.symm⟩
    · rintro ⟨h, h'⟩
      exact ⟨h'.symm, h'.symm.trans h⟩
  simp only [tripleScore, he, eq_comm]
  ring

def uScore {K : ℕ} (e : Fin 3) (x : Triple K) : ℝ :=
  ![pairScore K x.1 x.2.1, pairScore K x.1 x.2.2, pairScore K x.2.1 x.2.2] e

def vScore {K : ℕ} (x : Triple K) : ℝ := tripleScore K x.1 x.2.1 x.2.2

def pairMeans (a b : ℝ) (q e : Fin 3) : ℝ :=
  if (q = 0 ∧ e = 0) ∨ (q = 1 ∧ e = 2) ∨ (q = 2 ∧ e = 1) then a else b

lemma oriented_score_sum {K : ℕ} (f : Triple K → ℝ) (k : ℝ) (t : ℝ × ℝ) (q : Fin 3) :
    (∑ x : Triple K, f x*site K (fun _ => 1/(K : ℝ)) k t (orientation K q x)) =
      ∑ y : Triple K, f ((orientation K q).symm y)*site K (fun _ => 1/(K : ℝ)) k t y := by
  simpa only [Equiv.symm_apply_apply] using
    (Equiv.sum_comp (orientation K q) (fun y =>
      f ((orientation K q).symm y)*site K (fun _ => 1/(K : ℝ)) k t y))

lemma oriented_pair_mean {K : ℕ} (hK : 2 ≤ K) (k : ℝ) (t : ℝ × ℝ)
    (q e : Fin 3) :
    (∑ x : Triple K, uScore e x*site K (fun _ => 1/(K : ℝ)) k t (orientation K q x)) =
      pairMeans (Real.exp (-k*t.1)) (Real.exp (-k*(t.1+t.2))) q e := by
  rw [oriented_score_sum]
  obtain ⟨ha, hb, hc⟩ := pair_score_means hK k t
  fin_cases q <;> fin_cases e <;>
    norm_num [uScore, pairMeans, orientation, cycle, pairScore_symm] at *
  all_goals first | exact ha | exact hb | exact hc

lemma oriented_triple_mean {K : ℕ} (hK : 3 ≤ K) (k : ℝ) (t : ℝ × ℝ)
    (q : Fin 3) :
    (∑ x : Triple K, vScore x*site K (fun _ => 1/(K : ℝ)) k t (orientation K q x)) =
      secondMomentKernel k t := by
  rw [oriented_score_sum]
  have hv (y : Triple K) : vScore ((orientation K q).symm y) = vScore y := by
    fin_cases q
    · rfl
    · change tripleScore K y.2.2 y.1 y.2.1 = tripleScore K y.1 y.2.1 y.2.2
      exact tripleScore_cycle K _ _ _
    · change tripleScore K y.2.1 y.2.2 y.1 = tripleScore K y.1 y.2.1 y.2.2
      exact (tripleScore_cycle K _ _ _).symm
  simp_rw [hv]
  exact triple_score_mean hK k t

end Rhone.Statistics.ThreeSiteSeparator
