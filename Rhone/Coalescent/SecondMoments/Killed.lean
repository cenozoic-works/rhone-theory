/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SecondMoments.Weights

/-! # Second-moment system for branch lengths of the mutation-killed genealogy -/

@[expose] public section

namespace Rhone.Coalescent.SecondMoments

open Finset TwoLocusGenealogy TypedAncestralChain BranchLengthMoments
open MeasureTheory
open ProbabilityTheory
open scoped ENNReal

variable {n KA KB : ℕ} {θA θB ρ : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ}

theorem isGenSol_fixed (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    {r u : TS n KA KB → ℝ} (hu : IsGenSol θA θB ρ πA πB r u) {t : TS n KA KB}
    (hwt : WF t.st.1) :
    u t = r t / rateTotS θA θB ρ t + ∑ t', transS θA θB ρ πA πB t t' * u t' := by
  by_cases htr : Transient t
  · have hst := isGenSol_step hθA hθB hρ hu htr
    linarith
  · have hab : t.st.1 = ∅ := by
      by_contra hc
      exact htr ⟨hwt, hc⟩
    rw [sum_transS_of_not_transient hwt htr u, hu.1 t htr, rateTotS_of_absorbed hab,
      div_zero]
    ring

theorem isGenSol_nonneg (h : Adm θA θB ρ πA πB) (hθA : 0 < θA) (hθB : 0 < θB)
    {r u : TS n KA KB → ℝ} (hr : ∀ t, 0 ≤ r t) (hu : IsGenSol θA θB ρ πA πB r u)
    (t : TS n KA KB) : 0 ≤ u t := by
  by_cases hwt : WF t.st.1
  · set g : TS n KA KB → ℝ := fun x => r x / rateTotS θA θB ρ x with hgdef
    have hgnn : ∀ x, 0 ≤ g x :=
      fun x => div_nonneg (hr x) (rateTotS_nonneg h.thA h.thB h.rho x)
    have hfix : ∀ x : TS n KA KB, WF x.st.1 →
        u x = g x + ∑ t', transS θA θB ρ πA πB x t' * u t' :=
      fun x hx => isGenSol_fixed hθA hθB h.rho hu hx
    have hu0 : ∀ x : TS n KA KB, WF x.st.1 → x.st.1 = ∅ → u x = 0 :=
      fun x _ hab => hu.1 x fun hc => hc.2 hab
    have hlim : Filter.Tendsto (fun N => mstep θA θB ρ πA πB N u t) Filter.atTop (nhds 0) :=
      tendsto_mstep_zero h hθA hθB hu0 hwt
    have hpart : ∀ N : ℕ, 0 ≤ u t - mstep θA θB ρ πA πB N u t := by
      intro N
      rw [← sum_mstep_eq closed_wf hfix N hwt]
      exact Finset.sum_nonneg fun k _ => mstep_nonneg h k hgnn t
    have hconv : Filter.Tendsto (fun N => u t - mstep θA θB ρ πA πB N u t) Filter.atTop
        (nhds (u t)) := by
      simpa using (tendsto_const_nhds (x := u t) (f := Filter.atTop (α := ℕ))).sub hlim
    exact ge_of_tendsto' hconv hpart
  · rw [hu.1 t fun hc => hwt hc.1]

theorem expected_branchLen_mul_eq (h : Adm θA θB ρ πA πB) (hθA : 0 < θA) (hθB : 0 < θB)
    (F G : Finset (Finset (Fin n))) {uA uB w : TS n KA KB → ℝ}
    (hA : IsGenSol θA θB ρ πA πB (rA F) uA) (hB : IsGenSol θA θB ρ πA πB (rB G) uB)
    (hw : IsGenSol θA θB ρ πA πB (fun t => rA F t * uB t + rB G t * uA t) w)
    {s : TS n KA KB} (hws : WF s.st.1) :
    (∫⁻ ω, branchLen θA θB ρ F ω * branchLenB θA θB ρ G ω
          ∂(argTrajT θA θB ρ πA πB h s))
        + (∫⁻ ω, occAll (fun t => holdA θA θB ρ F t * holdB θA θB ρ G t) ω
          ∂(argTrajT θA θB ρ πA πB h s))
      = ENNReal.ofReal (w s) := by
  have hgnn : ∀ t : TS n KA KB, 0 ≤ holdA θA θB ρ F t := holdA_nonneg h.thA h.thB h.rho F
  have hunn : ∀ t : TS n KA KB, 0 ≤ holdB θA θB ρ G t := holdB_nonneg h.thA h.thB h.rho G
  have hAnn : ∀ t : TS n KA KB, 0 ≤ uA t :=
    isGenSol_nonneg h hθA hθB (rA_nonneg F) hA
  have hBnn : ∀ t : TS n KA KB, 0 ≤ uB t :=
    isGenSol_nonneg h hθA hθB (rB_nonneg G) hB
  have hfA : ∀ t : TS n KA KB, WF t.st.1 →
      uA t = holdA θA θB ρ F t + ∑ t', transS θA θB ρ πA πB t t' * uA t' :=
    fun t ht => isGenSol_fixed hθA hθB h.rho hA ht
  have hfB : ∀ t : TS n KA KB, WF t.st.1 →
      uB t = holdB θA θB ρ G t + ∑ t', transS θA θB ρ πA πB t t' * uB t' :=
    fun t ht => isGenSol_fixed hθA hθB h.rho hB ht
  have hfw : ∀ t : TS n KA KB, WF t.st.1 →
      w t = (holdA θA θB ρ F t * uB t + holdB θA θB ρ G t * uA t)
        + ∑ t', transS θA θB ρ πA πB t t' * w t' := by
    intro t ht
    have hstep := isGenSol_fixed hθA hθB h.rho hw ht
    have harith : (rA F t * uB t + rB G t * uA t) / rateTotS θA θB ρ t
        = holdA θA θB ρ F t * uB t + holdB θA θB ρ G t * uA t := by
      rw [holdA, holdB]
      ring
    rw [hstep, harith]
  have hlA : ∀ t : TS n KA KB, WF t.st.1 →
      Filter.Tendsto (fun N => mstep θA θB ρ πA πB N uA t) Filter.atTop (nhds 0) :=
    fun t ht => tendsto_mstep_zero h hθA hθB (fun x _ hab => hA.1 x fun hc => hc.2 hab) ht
  have hlB : ∀ t : TS n KA KB, WF t.st.1 →
      Filter.Tendsto (fun N => mstep θA θB ρ πA πB N uB t) Filter.atTop (nhds 0) :=
    fun t ht => tendsto_mstep_zero h hθA hθB (fun x _ hab => hB.1 x fun hc => hc.2 hab) ht
  have hlw : Filter.Tendsto (fun N => mstep θA θB ρ πA πB N w s) Filter.atTop (nhds 0) :=
    tendsto_mstep_zero h hθA hθB (fun x _ hab => hw.1 x fun hc => hc.2 hab) hws
  exact lintegral_occAll_mul_eq h closed_wf hgnn hunn hAnn hBnn hfA hfB hlA hlB hfw hlw hws

theorem lintegral_branchLen_mul_eq_of_genSol (h : Adm θA θB ρ πA πB) (hθA : 0 < θA)
    (hθB : 0 < θB) (F G : Finset (Finset (Fin n))) {uA uB w w' : TS n KA KB → ℝ}
    (hA : IsGenSol θA θB ρ πA πB (rA F) uA) (hB : IsGenSol θA θB ρ πA πB (rB G) uB)
    (hw : IsGenSol θA θB ρ πA πB (fun t => rA F t * uB t + rB G t * uA t) w)
    (hw' : IsGenSol θA θB ρ πA πB
      (fun t => rA F t * rB G t / rateTotS θA θB ρ t) w')
    {s : TS n KA KB} (hws : WF s.st.1) :
    (∫⁻ ω, branchLen θA θB ρ F ω * branchLenB θA θB ρ G ω
        ∂(argTrajT θA θB ρ πA πB h s)) + ENNReal.ofReal (w' s) = ENNReal.ofReal (w s) := by
  have hdiag : (∫⁻ ω, occAll (fun t => holdA θA θB ρ F t * holdB θA θB ρ G t) ω
      ∂(argTrajT θA θB ρ πA πB h s)) = ENNReal.ofReal (w' s) := by
    have hprod : ∀ t : TS n KA KB, holdA θA θB ρ F t * holdB θA θB ρ G t
        = (fun x => rA F x * rB G x / rateTotS θA θB ρ x) t / rateTotS θA θB ρ t := by
      intro t
      rw [holdA, holdB]
      ring
    have hfix : ∀ t : TS n KA KB, WF t.st.1 →
        w' t = (fun x => holdA θA θB ρ F x * holdB θA θB ρ G x) t
          + ∑ t', transS θA θB ρ πA πB t t' * w' t' := by
      intro t ht
      change w' t = holdA θA θB ρ F t * holdB θA θB ρ G t
        + ∑ t', transS θA θB ρ πA πB t t' * w' t'
      rw [hprod t]
      exact isGenSol_fixed hθA hθB h.rho hw' ht
    exact lintegral_occAll_eq h closed_wf
      (fun t => mul_nonneg (holdA_nonneg h.thA h.thB h.rho F t)
        (holdB_nonneg h.thA h.thB h.rho G t)) hfix
      (tendsto_mstep_zero h hθA hθB (fun x _ hab => hw'.1 x fun hc => hc.2 hab) hws) hws
  rw [← hdiag]
  exact expected_branchLen_mul_eq h hθA hθB F G hA hB hw hws

theorem exists_secondMoment_genSol (h : Adm θA θB ρ πA πB) (hθA : 0 < θA) (hθB : 0 < θB)
    (F G : Finset (Finset (Fin n))) {s : TS n KA KB} (hws : WF s.st.1) :
    ∃ uA uB w : TS n KA KB → ℝ,
      IsGenSol θA θB ρ πA πB (rA F) uA ∧ IsGenSol θA θB ρ πA πB (rB G) uB
        ∧ IsGenSol θA θB ρ πA πB (fun t => rA F t * uB t + rB G t * uA t) w
        ∧ (∫⁻ ω, branchLen θA θB ρ F ω * branchLenB θA θB ρ G ω
              ∂(argTrajT θA θB ρ πA πB h s))
            + (∫⁻ ω, occAll (fun t => holdA θA θB ρ F t * holdB θA θB ρ G t) ω
              ∂(argTrajT θA θB ρ πA πB h s))
          = ENNReal.ofReal (w s) := by
  obtain ⟨uA, hA, -⟩ := existsUnique_genSol h hθA hθB (rA F)
  obtain ⟨uB, hB, -⟩ := existsUnique_genSol h hθA hθB (rB G)
  obtain ⟨w, hw, -⟩ := existsUnique_genSol h hθA hθB
    (fun t => rA F t * uB t + rB G t * uA t)
  exact ⟨uA, uB, w, hA, hB, hw, expected_branchLen_mul_eq h hθA hθB F G hA hB hw hws⟩

theorem expected_branchLen_sq_eq (h : Adm θA θB ρ πA πB) (hθA : 0 < θA) (hθB : 0 < θB)
    (F : Finset (Finset (Fin n))) {uA w : TS n KA KB → ℝ}
    (hA : IsGenSol θA θB ρ πA πB (rA F) uA)
    (hw : IsGenSol θA θB ρ πA πB (fun t => rA F t * uA t + rA F t * uA t) w)
    {s : TS n KA KB} (hws : WF s.st.1) :
    (∫⁻ ω, branchLen θA θB ρ F ω * branchLen θA θB ρ F ω
          ∂(argTrajT θA θB ρ πA πB h s))
        + (∫⁻ ω, occAll (fun t => holdA θA θB ρ F t * holdA θA θB ρ F t) ω
          ∂(argTrajT θA θB ρ πA πB h s))
      = ENNReal.ofReal (w s) := by
  have hgnn : ∀ t : TS n KA KB, 0 ≤ holdA θA θB ρ F t := holdA_nonneg h.thA h.thB h.rho F
  have hAnn : ∀ t : TS n KA KB, 0 ≤ uA t := isGenSol_nonneg h hθA hθB (rA_nonneg F) hA
  have hfA : ∀ t : TS n KA KB, WF t.st.1 →
      uA t = holdA θA θB ρ F t + ∑ t', transS θA θB ρ πA πB t t' * uA t' :=
    fun t ht => isGenSol_fixed hθA hθB h.rho hA ht
  have hfw : ∀ t : TS n KA KB, WF t.st.1 →
      w t = (holdA θA θB ρ F t * uA t + holdA θA θB ρ F t * uA t)
        + ∑ t', transS θA θB ρ πA πB t t' * w t' := by
    intro t ht
    have hstep := isGenSol_fixed hθA hθB h.rho hw ht
    have harith : (rA F t * uA t + rA F t * uA t) / rateTotS θA θB ρ t
        = holdA θA θB ρ F t * uA t + holdA θA θB ρ F t * uA t := by
      rw [holdA]
      ring
    rw [hstep, harith]
  have hlA : ∀ t : TS n KA KB, WF t.st.1 →
      Filter.Tendsto (fun N => mstep θA θB ρ πA πB N uA t) Filter.atTop (nhds 0) :=
    fun t ht => tendsto_mstep_zero h hθA hθB (fun x _ hab => hA.1 x fun hc => hc.2 hab) ht
  have hlw : Filter.Tendsto (fun N => mstep θA θB ρ πA πB N w s) Filter.atTop (nhds 0) :=
    tendsto_mstep_zero h hθA hθB (fun x _ hab => hw.1 x fun hc => hc.2 hab) hws
  exact lintegral_occAll_mul_eq h closed_wf hgnn hgnn hAnn hAnn hfA hfA hlA hlA hfw hlw hws

end Rhone.Coalescent.SecondMoments
