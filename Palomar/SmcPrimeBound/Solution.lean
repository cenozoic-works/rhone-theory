module

public import Rhone.Coalescent.SmcPrimeTVBound
public import Rhone.Coalescent.FullARGTermination

@[expose] public section

namespace Rhone.Palomar.SmcPrimeBound

open MeasureTheory ProbabilityTheory MarkovChain Coalescent.IntervalProcess
    MarkovChain.IntervalProcess
open Coalescent.SmcPrime

noncomputable def processOfKernel {S : Type*} [MeasurableSpace S] (κ : Kernel S S) :
    DiscreteProcess S := by
  classical
  exact if h : IsMarkovKernel κ then { step := κ, isMarkov := h } else { step := Kernel.id }

noncomputable def fullARGLaw (N : ℕ) (R : ℝ) : Measure (Genealogy N) :=
  ((processOfKernel (eventKernel false R)).pathLaw (initialState N, (0, .inl ()))).map
    (genealogyObservation N)

noncomputable def initialTreeLaw (N : ℕ) : Measure (Tree N) :=
  (((processOfKernel (eventKernel false 0)).pathLaw (initialState N, (0, .inl ()))).map
    (fun ω => fun k : Fin N => ω k.val) : Measure (KingmanHistory N)).map
      (metricTreeFromHistory N)

noncomputable def smcPrimeLaw (N : ℕ) (R : ℝ) : Measure (Genealogy N) :=
  ((processOfKernel (spatialKernel N R)).law ((initialTreeLaw N).map (fun T => (0, T)))).map
    (spatialGenealogyObservation N)

theorem processOfKernel_of_isMarkovKernel {S : Type*} [MeasurableSpace S] (κ : Kernel S S)
    [h : IsMarkovKernel κ] : processOfKernel κ = { step := κ, isMarkov := h } := by
  unfold processOfKernel
  exact dite_eq_left h

theorem processOfKernel_eventKernel (mode : Mode) (R : ℝ) :
    processOfKernel (eventKernel mode R) = eventProcess mode R :=
  processOfKernel_of_isMarkovKernel _

theorem processOfKernel_spatialKernel (N : ℕ) (R : ℝ) :
    processOfKernel (spatialKernel N R) = spatialProcess N R :=
  processOfKernel_of_isMarkovKernel _

theorem fullARGLaw_eq (N : ℕ) (R : ℝ) : fullARGLaw N R = fullARGGenealogyLaw N R := by
  rw [fullARGLaw, processOfKernel_eventKernel]
  rfl

theorem initialTreeLaw_eq (N : ℕ) : initialTreeLaw N = kingmanTreeLaw N := by
  rw [initialTreeLaw, processOfKernel_eventKernel]
  rfl

theorem smcPrimeLaw_eq (N : ℕ) (R : ℝ) :
    smcPrimeLaw N R = smcPrimeGenealogyLaw N R := by
  rw [smcPrimeLaw, initialTreeLaw_eq, processOfKernel_spatialKernel]
  rfl

open Coalescent.SmcBound MarkovChain Probability

theorem eventKernel_isMarkovKernel (mode : Mode) (R : ℝ) :
    IsMarkovKernel (eventKernel mode R) :=
  Rhone.Coalescent.IntervalProcess.eventKernel_markov mode R

theorem spatialKernel_isMarkovKernel (N : ℕ) (R : ℝ) :
    IsMarkovKernel (spatialKernel N R) :=
  spatialKernel_markov N R

theorem fullARG_smcPrime_tv_bound (N : ℕ) (hN : 1 ≤ N)
    (R : ℝ) (hR : 0 ≤ R) :
    eventTV (fullARGLaw N R) (smcPrimeLaw N R) ≤
      ENNReal.ofReal (doubleBound R (N - 1)) ∧
    doubleBound R (N - 1) ≤ min 1 (R ^ 2 * quadraticCoefficient (N - 1)) := by
  rw [fullARGLaw_eq, smcPrimeLaw_eq]
  exact Coalescent.SmcPrime.fullARG_smcPrime_tv_bound N hN R hR

theorem fullARG_smcPrime_tv_quadratic (N : ℕ) (hN : 1 ≤ N)
    (R : ℝ) (hR : 0 ≤ R) :
    eventTV (fullARGLaw N R) (smcPrimeLaw N R) ≤
      ENNReal.ofReal (min 1 (R ^ 2 * quadraticCoefficient (N - 1))) := by
  rw [fullARGLaw_eq, smcPrimeLaw_eq]
  exact Coalescent.SmcPrime.fullARG_smcPrime_tv_quadratic N hN R hR

theorem fullARG_smcPrime_tv_one_sample (R : ℝ) (hR : 0 ≤ R) :
    eventTV (fullARGLaw 1 R) (smcPrimeLaw 1 R) = 0 := by
  rw [fullARGLaw_eq, smcPrimeLaw_eq]
  exact Coalescent.SmcPrime.fullARG_smcPrime_tv_one_sample R hR

theorem fullARG_smcPrime_tv_zero_recombination (N : ℕ) (hN : 1 ≤ N) :
    eventTV (fullARGLaw N 0) (smcPrimeLaw N 0) = 0 := by
  rw [fullARGLaw_eq, smcPrimeLaw_eq]
  exact Coalescent.SmcPrime.fullARG_smcPrime_tv_zero_recombination N hN

theorem fullARGGenealogyLaw_probability (N : ℕ) (R : ℝ) :
    IsProbabilityMeasure (fullARGLaw N R) := by
  rw [fullARGLaw_eq]
  exact Rhone.Coalescent.IntervalProcess.fullARGGenealogyLaw_probability N R

theorem smcPrimeGenealogyLaw_probability (N : ℕ) (R : ℝ) :
    IsProbabilityMeasure (smcPrimeLaw N R) := by
  rw [smcPrimeLaw_eq]
  exact Coalescent.IntervalProcess.smcPrimeGenealogyLaw_probability N R

theorem eventProcess_liveCount_reaches_one (N : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∀ᵐ ω ∂(processOfKernel (eventKernel false R)).pathLaw (initialState N, (0, .inl ())),
      ∃ K, ∀ k, K ≤ k → (ω k).1.2.2.1 ≤ 1 := by
  rw [processOfKernel_eventKernel]
  exact Rhone.Coalescent.IntervalProcess.eventProcess_liveCount_reaches_one N R hR

theorem eventProcess_active_events_le (N : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∑' k, (processOfKernel (eventKernel false R)).pathLaw (initialState N, (0, .inl ()))
      {ω | 2 ≤ (ω k).1.2.2.1} ≤ ENNReal.ofReal (absorptionBudget R N) := by
  rw [processOfKernel_eventKernel]
  exact Rhone.Coalescent.IntervalProcess.eventProcess_active_events_le N R hR

theorem eventProcess_total_time_le (N : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∫⁻ ω, ⨆ k, ENNReal.ofReal (ω k).1.1
      ∂(processOfKernel (eventKernel false R)).pathLaw (initialState N, (0, .inl ())) ≤
      ENNReal.ofReal (absorptionBudget R N) := by
  rw [processOfKernel_eventKernel]
  exact Rhone.Coalescent.IntervalProcess.eventProcess_total_time_le N R hR

theorem fullARGGenealogyLaw_ae_finite (N : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∀ᵐ G ∂fullARGLaw N R, ∀ q i j, G q i j < ⊤ := by
  rw [fullARGLaw_eq]
  exact Rhone.Coalescent.IntervalProcess.fullARGGenealogyLaw_ae_finite N R hR

theorem fullARGGenealogyLaw_lintegral_iSup_le (N : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∫⁻ G, ⨆ q, ⨆ i, ⨆ j, G q i j ∂fullARGLaw N R ≤
      ENNReal.ofReal (absorptionBudget R N) := by
  rw [fullARGLaw_eq]
  exact Rhone.Coalescent.IntervalProcess.fullARGGenealogyLaw_lintegral_iSup_le N R hR

end Rhone.Palomar.SmcPrimeBound
