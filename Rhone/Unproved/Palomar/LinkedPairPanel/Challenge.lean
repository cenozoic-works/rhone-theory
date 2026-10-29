module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp

set_option maxSynthPendingDepth 3

@[expose] public section

elab "clear_aux_proof_cache" : command => do
  Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
  let ext ← unsafe Lean.Elab.Command.liftCoreM
    (Lean.evalConst (Lean.EnvExtension (Lean.PersistentHashMap Nat Nat))
      (Lean.Name.mkNum `_private.Lean.Meta.Match.Match 0 ++ `Lean.Meta.Match.matcherExt))
  Lean.modifyEnv fun env => ext.setState env {}

elab "set_main_module " m:ident : command =>
  Lean.modifyEnv fun env => env.setMainModule m.getId

open scoped BigOperators

set_main_module Rhone.Statistics.PairObservationChannel.Channel
clear_aux_proof_cache

namespace Rhone.Statistics.PairObservationChannel

structure Channel (K : ℕ) (H : Type*) [Fintype H] where
  positive : 0 < K
  row : Fin K → H → ℝ
  nonneg : ∀ i y, 0 ≤ row i y
  normalized : ∀ i, ∑ y, row i y = 1

variable {K : ℕ} {H : Type*} [Fintype H]

noncomputable def columnMean (E : Channel K H) (y : H) : ℝ :=
  (∑ i, E.row i y) / K

noncomputable def retainedVariance (E : Channel K H) : ℝ :=
  (∑ i, ∑ y, (E.row i y - columnMean E y)^2) / K

def Informative (E : Channel K H) : Prop := ∃ i j y, E.row i y ≠ E.row j y

end Rhone.Statistics.PairObservationChannel

set_main_module Rhone.Statistics.PairObservationChannel.Agreement
clear_aux_proof_cache

namespace Rhone.Statistics.PairObservationChannel
variable {K : ℕ} {H : Type*} [Fintype H]

noncomputable def sharedMass (E : Channel K H) (x y : H) : ℝ :=
  (∑ i, E.row i x * E.row i y) / K

noncomputable def reportedMass (E : Channel K H) (ℓ : ℝ) (x y : H) : ℝ :=
  (1-ℓ)*columnMean E x*columnMean E y + ℓ*sharedMass E x y

end Rhone.Statistics.PairObservationChannel

set_main_module Rhone.Statistics.PairObservationChannel.LaplaceKernel
clear_aux_proof_cache

namespace Rhone.Statistics.PairObservationChannel
open MeasureTheory

noncomputable def pairLaplace (μ : Measure ℝ) (k : ℝ) : ℝ :=
  ∫ t, Real.exp (-k*t) ∂μ

end Rhone.Statistics.PairObservationChannel

set_main_module Rhone.Statistics.LinkedPairMoments.Kernel
clear_aux_proof_cache

namespace Rhone.Statistics.LinkedPairMoments
open PairObservationChannel
variable {K : ℕ} {H : Type*} [Fintype H]

noncomputable def panelWeight (E : Channel K H) (k t : ℝ) (L : ℕ)
    (x : Fin L → H × H) : ℝ :=
  ∏ i, reportedMass E (Real.exp (-k * t)) (x i).1 (x i).2

end Rhone.Statistics.LinkedPairMoments

set_main_module Rhone.Unproved.Palomar.LinkedPairPanel.Challenge
clear_aux_proof_cache

namespace Rhone.Palomar.LinkedPairPanel

open MeasureTheory
open Statistics.PairObservationChannel Statistics.LinkedPairMoments

theorem panel_eq_iff {K : ℕ} {H : Type*} [Fintype H] (E : Channel K H) (hE : Informative E)
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {k : ℝ} (hk : 0 ≤ k)
    (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (hν : ∀ᵐ t ∂ν, 0 ≤ t) (L : ℕ) :
    (∀ x : Fin L → H × H, ∫ t, panelWeight E k t L x ∂μ = ∫ t, panelWeight E k t L x ∂ν) ↔
      ∀ r : ℕ, r ≤ L → pairLaplace μ ((r : ℝ) * k) = pairLaplace ν ((r : ℝ) * k) := by
  sorry

theorem panel_erased {K : ℕ} {H : Type*} [Fintype H] (E : Channel K H)
    (hE : retainedVariance E = 0) (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {k : ℝ} (hk : 0 ≤ k)
    (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (hν : ∀ᵐ t ∂ν, 0 ≤ t) (L : ℕ) (x : Fin L → H × H) :
    ∫ t, panelWeight E k t L x ∂μ = ∫ t, panelWeight E k t L x ∂ν := by
  sorry

theorem next_moment_upgrade {K : ℕ} {H : Type*} [Fintype H] (E : Channel K H)
    (hE : Informative E) (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {k : ℝ} (hk : 0 ≤ k)
    (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (hν : ∀ᵐ t ∂ν, 0 ≤ t) (L : ℕ)
    (hm : ∀ r : ℕ, r ≤ L → pairLaplace μ ((r : ℝ) * k) = pairLaplace ν ((r : ℝ) * k))
    (hnext : pairLaplace μ (((L + 1 : ℕ) : ℝ) * k) ≠
      pairLaplace ν (((L + 1 : ℕ) : ℝ) * k)) :
    (∀ x : Fin L → H × H, ∫ t, panelWeight E k t L x ∂μ = ∫ t, panelWeight E k t L x ∂ν) ∧
      ∃ x : Fin (L + 1) → H × H,
        ∫ t, panelWeight E k t (L + 1) x ∂μ ≠ ∫ t, panelWeight E k t (L + 1) x ∂ν := by
  sorry

theorem all_panels_eq_iff {K : ℕ} {H : Type*} [Fintype H] (E : Channel K H)
    (hE : Informative E) (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {k : ℝ} (hk : 0 < k)
    (hμ : ∀ᵐ t ∂μ, 0 ≤ t) (hν : ∀ᵐ t ∂ν, 0 ≤ t) :
    (∀ (L : ℕ) (x : Fin L → H × H),
      ∫ t, panelWeight E k t L x ∂μ = ∫ t, panelWeight E k t L x ∂ν) ↔ μ = ν := by
  sorry

end Rhone.Palomar.LinkedPairPanel
