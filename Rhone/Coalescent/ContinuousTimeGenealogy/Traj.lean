/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SecondMoments
public import Rhone.Coalescent.ContinuousTimeGenealogy.Exp
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Independence.Integration

/-! # The continuous-time ancestral recombination graph: jump chain plus holding times -/

@[expose] public section

namespace Rhone.Coalescent.ContinuousTimeGenealogy

open Finset TwoLocusGenealogy TypedAncestralChain BranchLengthMoments
open SecondMoments
open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {n KA KB : ℕ} {θA θB ρ : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ}

noncomputable def clocks : Measure ((_ : ℕ) → ℝ) := Measure.infinitePi fun _ : ℕ => expOne

instance isProbabilityMeasure_clocks : IsProbabilityMeasure clocks := by
  rw [clocks]
  infer_instance

theorem lintegral_clocks_eval {g : ℝ → ℝ≥0∞} (hg : Measurable g) (k : ℕ) :
    ∫⁻ e, g (e k) ∂clocks = ∫⁻ x, g x ∂expOne := by
  rw [clocks, ← lintegral_map hg (measurable_pi_apply k),
    Measure.infinitePi_map_eval (fun _ : ℕ => expOne) k]

theorem lintegral_clocks_single (k : ℕ) :
    ∫⁻ e, ENNReal.ofReal (e k) ∂clocks = 1 := by
  rw [lintegral_clocks_eval (g := fun x : ℝ => ENNReal.ofReal x) (by fun_prop) k,
    lintegral_id_expOne]

theorem lintegral_clocks_pair (j k : ℕ) :
    ∫⁻ e, ENNReal.ofReal (e j) * ENNReal.ofReal (e k) ∂clocks
      = 1 + (if j = k then 1 else 0) := by
  by_cases hjk : j = k
  · subst hjk
    rw [ite_eq_left rfl, lintegral_clocks_eval
      (g := fun x : ℝ => ENNReal.ofReal x * ENNReal.ofReal x) (by fun_prop) j,
      lintegral_sq_expOne]
    norm_num
  · have hind : iIndepFun (fun (i : ℕ) (e : (_ : ℕ) → ℝ) => e i) clocks := by
      rw [clocks]
      exact iIndepFun_infinitePi (X := fun (_ : ℕ) (x : ℝ) => x) fun _ => measurable_id
    have hpair : (fun e : (_ : ℕ) → ℝ => ENNReal.ofReal (e j))
        ⟂ᵢ[clocks] fun e : (_ : ℕ) → ℝ => ENNReal.ofReal (e k) :=
      (hind.indepFun hjk).comp ENNReal.measurable_ofReal ENNReal.measurable_ofReal
    have hmul := lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun
      (f := fun e : (_ : ℕ) → ℝ => ENNReal.ofReal (e j))
      (g := fun e : (_ : ℕ) → ℝ => ENNReal.ofReal (e k)) (by fun_prop) (by fun_prop) hpair
    rw [ite_eq_right hjk, add_zero]
    calc ∫⁻ e, ENNReal.ofReal (e j) * ENNReal.ofReal (e k) ∂clocks
        = (∫⁻ e, ENNReal.ofReal (e j) ∂clocks) * ∫⁻ e, ENNReal.ofReal (e k) ∂clocks := hmul
      _ = 1 := by rw [lintegral_clocks_single, lintegral_clocks_single, one_mul]

abbrev CtPath (n KA KB : ℕ) : Type :=
  ((_ : ℕ) → TS n KA KB) × ((_ : ℕ) → ℝ)

noncomputable def ctLaw (θA θB ρ : ℝ) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ)
    (h : Adm θA θB ρ πA πB) (s : TS n KA KB) : Measure (CtPath n KA KB) :=
  (argTrajT θA θB ρ πA πB h s).prod clocks

instance isProbabilityMeasure_ctLaw (h : Adm θA θB ρ πA πB) (s : TS n KA KB) :
    IsProbabilityMeasure (ctLaw θA θB ρ πA πB h s) := by
  rw [ctLaw]
  infer_instance

noncomputable def holdTime (θA θB ρ : ℝ) (z : CtPath n KA KB) (k : ℕ) : ℝ :=
  z.2 k / rateTotS θA θB ρ (z.1 k)

noncomputable def ctOcc (g : TS n KA KB → ℝ) (z : CtPath n KA KB) : ℝ≥0∞ :=
  ∑' k : ℕ, ENNReal.ofReal (g (z.1 k)) * ENNReal.ofReal (z.2 k)

noncomputable def ctBranch (θA θB ρ : ℝ) (r : TS n KA KB → ℝ) (z : CtPath n KA KB) : ℝ≥0∞ :=
  ∑' k : ℕ, ENNReal.ofReal (r (z.1 k)) * ENNReal.ofReal (holdTime θA θB ρ z k)

theorem ctBranch_eq_ctOcc (r : TS n KA KB → ℝ) (hr : ∀ t, 0 ≤ r t)
    (hrate : ∀ t : TS n KA KB, 0 ≤ rateTotS θA θB ρ t) (z : CtPath n KA KB) :
    ctBranch θA θB ρ r z = ctOcc (fun t => r t / rateTotS θA θB ρ t) z := by
  refine tsum_congr fun k => ?_
  rw [holdTime, ← ENNReal.ofReal_mul (hr _), ← ENNReal.ofReal_mul
    (div_nonneg (hr _) (hrate _))]
  congr 1
  field_simp

theorem ctBranch_rA_eq (h : Adm θA θB ρ πA πB) (F : Finset (Finset (Fin n)))
    (z : CtPath n KA KB) :
    ctBranch θA θB ρ (rA F) z = ctOcc (holdA θA θB ρ F) z :=
  ctBranch_eq_ctOcc (rA F) (rA_nonneg F) (rateTotS_nonneg h.thA h.thB h.rho) z

theorem ctBranch_rB_eq (h : Adm θA θB ρ πA πB) (F : Finset (Finset (Fin n)))
    (z : CtPath n KA KB) :
    ctBranch θA θB ρ (rB F) z = ctOcc (holdB θA θB ρ F) z :=
  ctBranch_eq_ctOcc (rB F) (rB_nonneg F) (rateTotS_nonneg h.thA h.thB h.rho) z

theorem measurable_coord (g : TS n KA KB → ℝ) (k : ℕ) :
    Measurable fun z : CtPath n KA KB => ENNReal.ofReal (g (z.1 k)) :=
  (Measurable.of_discrete (f := fun t : TS n KA KB => ENNReal.ofReal (g t))).comp
    ((measurable_pi_apply k).comp measurable_fst)

theorem measurable_ctOcc (g : TS n KA KB → ℝ) :
    Measurable (ctOcc (n := n) (KA := KA) (KB := KB) g) :=
  Measurable.tsum fun k => (measurable_coord g k).mul
    (ENNReal.measurable_ofReal.comp ((measurable_pi_apply k).comp measurable_snd))

end Rhone.Coalescent.ContinuousTimeGenealogy
