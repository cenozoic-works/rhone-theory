/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.ContinuousTimeGenealogy.Holding

/-! # The continuous-time second moment is the jump-chain second moment plus the diagonal -/

@[expose] public section

namespace Rhone.Coalescent.ContinuousTimeGenealogy

open Finset TwoLocusGenealogy TypedAncestralChain BranchLengthMoments
open SecondMoments
open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {n KA KB : ℕ} {θA θB ρ : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ}

theorem measurable_clock_pair (j k : ℕ) :
    Measurable fun e : (_ : ℕ) → ℝ => ENNReal.ofReal (e j) * ENNReal.ofReal (e k) := by
  fun_prop

theorem measurable_clock_pair_const (c : ℝ≥0∞) (j k : ℕ) :
    Measurable fun e : (_ : ℕ) → ℝ => c * (ENNReal.ofReal (e j) * ENNReal.ofReal (e k)) := by
  fun_prop

theorem measurable_clock_const (c : ℝ≥0∞) (k : ℕ) :
    Measurable fun e : (_ : ℕ) → ℝ => c * ENNReal.ofReal (e k) := by
  fun_prop

theorem lintegral_clocks_linear (a : ℕ → ℝ≥0∞) :
    (∫⁻ e, ∑' k : ℕ, a k * ENNReal.ofReal (e k) ∂clocks) = ∑' k : ℕ, a k := by
  rw [lintegral_tsum fun k => (measurable_clock_const (a k) k).aemeasurable]
  refine tsum_congr fun k => ?_
  rw [lintegral_const_mul _ (by fun_prop : Measurable fun e : (_ : ℕ) → ℝ => ENNReal.ofReal (e k)),
    lintegral_clocks_single, mul_one]

theorem lintegral_clocks_double (a b : ℕ → ℝ≥0∞) :
    (∫⁻ e, (∑' j : ℕ, a j * ENNReal.ofReal (e j)) * (∑' k : ℕ, b k * ENNReal.ofReal (e k))
        ∂clocks)
      = (∑' j : ℕ, a j) * (∑' k : ℕ, b k) + ∑' j : ℕ, a j * b j := by
  classical
  have hexp : ∀ e : (_ : ℕ) → ℝ,
      (∑' j : ℕ, a j * ENNReal.ofReal (e j)) * (∑' k : ℕ, b k * ENNReal.ofReal (e k))
        = ∑' j : ℕ, ∑' k : ℕ, (a j * b k) * (ENNReal.ofReal (e j) * ENNReal.ofReal (e k)) := by
    intro e
    rw [← ENNReal.tsum_mul_right]
    refine tsum_congr fun j => ?_
    rw [← ENNReal.tsum_mul_left]
    exact tsum_congr fun k => mul_mul_mul_comm _ _ _ _
  rw [lintegral_congr hexp, lintegral_tsum fun j =>
    (Measurable.tsum fun k => measurable_clock_pair_const (a j * b k) j k).aemeasurable]
  have hinner : ∀ j : ℕ,
      (∫⁻ e, ∑' k : ℕ, (a j * b k) * (ENNReal.ofReal (e j) * ENNReal.ofReal (e k)) ∂clocks)
        = (∑' k : ℕ, a j * b k) + a j * b j := by
    intro j
    rw [lintegral_tsum fun k => (measurable_clock_pair_const (a j * b k) j k).aemeasurable]
    have hpt : ∀ k : ℕ,
        (∫⁻ e, (a j * b k) * (ENNReal.ofReal (e j) * ENNReal.ofReal (e k)) ∂clocks)
          = a j * b k + (if j = k then a j * b k else 0) := by
      intro k
      rw [lintegral_const_mul _ (measurable_clock_pair j k), lintegral_clocks_pair]
      by_cases hk : j = k
      · rw [ite_eq_left hk, ite_eq_left hk]
        ring
      · rw [ite_eq_right hk, ite_eq_right hk]
        ring
    rw [tsum_congr hpt, ENNReal.tsum_add]
    congr 1
    rw [tsum_eq_single j fun k hk => ite_eq_right (Ne.symm hk), ite_eq_left rfl]
  rw [tsum_congr hinner, ENNReal.tsum_add]
  congr 1
  rw [← ENNReal.tsum_mul_right]
  exact tsum_congr fun j => ENNReal.tsum_mul_left

theorem lintegral_ctOcc (h : Adm θA θB ρ πA πB) (g : TS n KA KB → ℝ) (s : TS n KA KB) :
    (∫⁻ z, ctOcc g z ∂(ctLaw θA θB ρ πA πB h s))
      = ∫⁻ ω, occAll g ω ∂(argTrajT θA θB ρ πA πB h s) := by
  have hm : Measurable fun z : CtPath n KA KB => ctOcc g z := measurable_ctOcc g
  rw [ctLaw, lintegral_prod _ hm.aemeasurable]
  refine lintegral_congr fun ω => ?_
  exact lintegral_clocks_linear fun k => ENNReal.ofReal (g (ω k))

theorem lintegral_ctOcc_mul (h : Adm θA θB ρ πA πB) {g u : TS n KA KB → ℝ}
    (hg : ∀ t, 0 ≤ g t) (s : TS n KA KB) :
    (∫⁻ z, ctOcc g z * ctOcc u z ∂(ctLaw θA θB ρ πA πB h s))
      = (∫⁻ ω, occAll g ω * occAll u ω ∂(argTrajT θA θB ρ πA πB h s))
        + ∫⁻ ω, occAll (fun t => g t * u t) ω ∂(argTrajT θA θB ρ πA πB h s) := by
  have hm : Measurable fun z : CtPath n KA KB => ctOcc g z * ctOcc u z :=
    (measurable_ctOcc g).mul (measurable_ctOcc u)
  rw [ctLaw, lintegral_prod _ hm.aemeasurable]
  have hinner : ∀ ω : (_ : ℕ) → TS n KA KB,
      (∫⁻ e, ctOcc g (ω, e) * ctOcc u (ω, e) ∂clocks)
        = occAll g ω * occAll u ω + occAll (fun t => g t * u t) ω := by
    intro ω
    have hd := lintegral_clocks_double (fun j => ENNReal.ofReal (g (ω j)))
      (fun k => ENNReal.ofReal (u (ω k)))
    have hdiag : (∑' j : ℕ, ENNReal.ofReal (g (ω j)) * ENNReal.ofReal (u (ω j)))
        = occAll (fun t => g t * u t) ω :=
      tsum_congr fun j => (ENNReal.ofReal_mul (hg _)).symm
    rw [← hdiag]
    exact hd
  have hmo : Measurable fun ω : (_ : ℕ) → TS n KA KB => occAll g ω * occAll u ω :=
    (measurable_occAll g).mul (measurable_occAll u)
  rw [lintegral_congr hinner, lintegral_add_left hmo]

theorem lintegral_ctBranch_mul (h : Adm θA θB ρ πA πB) (F G : Finset (Finset (Fin n)))
    (s : TS n KA KB) :
    (∫⁻ z, ctBranch θA θB ρ (rA F) z * ctBranch θA θB ρ (rB G) z
        ∂(ctLaw θA θB ρ πA πB h s))
      = (∫⁻ ω, branchLen θA θB ρ F ω * branchLenB θA θB ρ G ω
          ∂(argTrajT θA θB ρ πA πB h s))
        + ∫⁻ ω, occAll (fun t => holdA θA θB ρ F t * holdB θA θB ρ G t) ω
            ∂(argTrajT θA θB ρ πA πB h s) := by
  have hcongr : ∀ z : CtPath n KA KB,
      ctBranch θA θB ρ (rA F) z * ctBranch θA θB ρ (rB G) z
        = ctOcc (holdA θA θB ρ F) z * ctOcc (holdB θA θB ρ G) z := by
    intro z
    rw [ctBranch_rA_eq h F z, ctBranch_rB_eq h G z]
  rw [lintegral_congr hcongr,
    lintegral_ctOcc_mul h (holdA_nonneg h.thA h.thB h.rho F) s]
  rfl

theorem lintegral_ctBranch (h : Adm θA θB ρ πA πB) (F : Finset (Finset (Fin n)))
    (s : TS n KA KB) :
    (∫⁻ z, ctBranch θA θB ρ (rA F) z ∂(ctLaw θA θB ρ πA πB h s))
      = ∫⁻ ω, branchLen θA θB ρ F ω ∂(argTrajT θA θB ρ πA πB h s) := by
  rw [lintegral_congr (ctBranch_rA_eq h F), lintegral_ctOcc h (holdA θA θB ρ F) s]
  rfl

theorem expected_ctBranch_mul_eq (h : Adm θA θB ρ πA πB) (hθA : 0 < θA) (hθB : 0 < θB)
    (F G : Finset (Finset (Fin n))) {uA uB w : TS n KA KB → ℝ}
    (hA : IsGenSol θA θB ρ πA πB (rA F) uA) (hB : IsGenSol θA θB ρ πA πB (rB G) uB)
    (hw : IsGenSol θA θB ρ πA πB (fun t => rA F t * uB t + rB G t * uA t) w)
    {s : TS n KA KB} (hws : WF s.st.1) :
    (∫⁻ z, ctBranch θA θB ρ (rA F) z * ctBranch θA θB ρ (rB G) z
        ∂(ctLaw θA θB ρ πA πB h s))
      = ENNReal.ofReal (w s) := by
  rw [lintegral_ctBranch_mul h F G s]
  exact expected_branchLen_mul_eq h hθA hθB F G hA hB hw hws

theorem exists_ctSecondMoment_genSol (h : Adm θA θB ρ πA πB) (hθA : 0 < θA) (hθB : 0 < θB)
    (F G : Finset (Finset (Fin n))) {s : TS n KA KB} (hws : WF s.st.1) :
    ∃ uA uB w : TS n KA KB → ℝ,
      IsGenSol θA θB ρ πA πB (rA F) uA ∧ IsGenSol θA θB ρ πA πB (rB G) uB
        ∧ IsGenSol θA θB ρ πA πB (fun t => rA F t * uB t + rB G t * uA t) w
        ∧ (∫⁻ z, ctBranch θA θB ρ (rA F) z * ctBranch θA θB ρ (rB G) z
            ∂(ctLaw θA θB ρ πA πB h s)) = ENNReal.ofReal (w s) := by
  obtain ⟨uA, hA, -⟩ := existsUnique_genSol h hθA hθB (rA F)
  obtain ⟨uB, hB, -⟩ := existsUnique_genSol h hθA hθB (rB G)
  obtain ⟨w, hw, -⟩ := existsUnique_genSol h hθA hθB
    (fun t => rA F t * uB t + rB G t * uA t)
  exact ⟨uA, uB, w, hA, hB, hw, expected_ctBranch_mul_eq h hθA hθB F G hA hB hw hws⟩

theorem expected_ct_total_length_sq (h : Adm (0 : ℝ) 0 ρ πA πB) :
    (∫⁻ z, ctBranch (0 : ℝ) 0 ρ (rA (cladeFam n)) z * ctBranch (0 : ℝ) 0 ρ (rA (cladeFam n)) z
        ∂(ctLaw (0 : ℝ) 0 ρ πA πB h (⟨initT n KA KB⟩ : TS n KA KB)))
      = ENNReal.ofReal ((2 * ∑ i ∈ Finset.range (n - 1), (1 : ℝ) / (i + 1)) ^ 2
          + 4 * ∑ i ∈ Finset.range (n - 1), (1 : ℝ) / (i + 1) ^ 2) := by
  have hcongr : ∀ z : CtPath n KA KB,
      ctBranch (0 : ℝ) 0 ρ (rA (cladeFam n)) z * ctBranch (0 : ℝ) 0 ρ (rA (cladeFam n)) z
        = ctOcc (holdA (0 : ℝ) 0 ρ (cladeFam n)) z
          * ctOcc (holdA (0 : ℝ) 0 ρ (cladeFam n)) z := by
    intro z
    rw [ctBranch_rA_eq h (cladeFam n) z]
  rw [lintegral_congr hcongr,
    lintegral_ctOcc_mul h (holdA_nonneg h.thA h.thB h.rho (cladeFam n))
      (⟨initT n KA KB⟩ : TS n KA KB)]
  exact expected_total_length_sq h

theorem expected_ct_total_length (h : Adm (0 : ℝ) 0 ρ πA πB) :
    (∫⁻ z, ctBranch (0 : ℝ) 0 ρ (rA (cladeFam n)) z
        ∂(ctLaw (0 : ℝ) 0 ρ πA πB h (⟨initT n KA KB⟩ : TS n KA KB)))
      = ENNReal.ofReal (2 * ∑ i ∈ Finset.range (n - 1), (1 : ℝ) / (i + 1)) := by
  rw [lintegral_ctBranch h (cladeFam n) (⟨initT n KA KB⟩ : TS n KA KB)]
  exact expected_total_length h

end Rhone.Coalescent.ContinuousTimeGenealogy
