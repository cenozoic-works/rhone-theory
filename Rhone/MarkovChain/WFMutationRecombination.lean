/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.WFSamplingLDMoments
public import Rhone.Dynamics.MutationModels
public import Rhone.MarkovChain.FinChain

/-!
# Independent mutation and recombination before finite haplotype sampling

Source: ewens2004, sec. 3.1. -/

@[expose] public section
noncomputable section
namespace Rhone.MarkovChain.WFAllocationLD
open Finset
open scoped Matrix

/-- Source: ewens2004, sec. 3.1. -/
def firstIndex : Fin 4 → Fin 2 := ![0,0,1,1]

/-- Source: ewens2004, sec. 3.1. -/
def secondIndex : Fin 4 → Fin 2 := ![0,1,0,1]

/-- Source: ewens2004, sec. 3.9, p. 135. -/
def independentMutation (u : ℝ) (g : Dynamics.Gametes ℝ) : Dynamics.Gametes ℝ :=
  Dynamics.TwoLocusSelection.fromVector (fun j => ∑ i : Fin 4,
    Dynamics.TwoLocusSelection.vector g i*
      Rhone.Dynamics.MutationModels.pimTransition (2*u) (fun _ : Fin 2 => 1/2)
        (firstIndex i) (firstIndex j)*
      Rhone.Dynamics.MutationModels.pimTransition (2*u) (fun _ : Fin 2 => 1/2)
        (secondIndex i) (secondIndex j))

def forcedGametes (c u : ℝ) (g : Dynamics.Gametes ℝ) : Dynamics.Gametes ℝ :=
  independentMutation u (g.recombine c)

/-- Source: ewens2004, sec. 3.1. -/
def forcedCountKernel (M : ℕ) (c u : ℝ) (a b : Rhone.MarkovChain.AlleleCounts M 4) : ℝ :=
  samplingKernel M (forcedGametes c u (countGametes M a)) b

/-- Source: ewens2004, sec. 3.9, p. 135. -/
theorem independent_mutation_distribution (u : ℝ) (g : Dynamics.Gametes ℝ)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2)
    (hg : ∀ i, 0 ≤ Dynamics.TwoLocusSelection.vector g i) (ht : g.total = 1) :
    (∀ i, 0 ≤ Dynamics.TwoLocusSelection.vector (independentMutation u g) i) ∧
      (independentMutation u g).total = 1 := by
  have hm := Rhone.Dynamics.MutationModels.pim_markov (2*u)
    (fun _ : Fin 2 => (1:ℝ)/2) (by intro i; norm_num)
    (by norm_num [Fin.sum_univ_succ]) (by linarith) (by linarith)
  constructor
  · intro j
    have hv : Dynamics.TwoLocusSelection.vector (independentMutation u g) j =
        ∑ i : Fin 4, Dynamics.TwoLocusSelection.vector g i *
          Rhone.Dynamics.MutationModels.pimTransition (2*u) (fun _ : Fin 2 => 1/2)
            (firstIndex i) (firstIndex j) *
          Rhone.Dynamics.MutationModels.pimTransition (2*u) (fun _ : Fin 2 => 1/2)
            (secondIndex i) (secondIndex j) := by
      fin_cases j <;> rfl
    rw [hv]
    exact sum_nonneg fun i _ => mul_nonneg (mul_nonneg (hg i) (hm.1 _ _)) (hm.1 _ _)
  · have hh : g.x22 = 1-g.x11-g.x12-g.x21 := by
      unfold Dynamics.Gametes.total at ht
      linarith
    norm_num [independentMutation, Dynamics.TwoLocusSelection.fromVector,
        Dynamics.TwoLocusSelection.vector,
      Dynamics.Gametes.total, Fin.sum_univ_four, firstIndex, secondIndex,
      Rhone.Dynamics.MutationModels.pimTransition]
    rw [hh]
    ring

theorem forced_gametes_distribution (c u : ℝ) (g : Dynamics.Gametes ℝ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2)
    (hg : ∀ i, 0 ≤ Dynamics.TwoLocusSelection.vector g i) (ht : g.total = 1) :
    (∀ i, 0 ≤ Dynamics.TwoLocusSelection.vector (forcedGametes c u g) i) ∧
      (forcedGametes c u g).total = 1 := by
  have hn := Dynamics.Gametes.recombine_nonneg hc0 hc1
    (hg 0) (hg 1) (hg 2) (hg 3)
  apply independent_mutation_distribution u (g.recombine c) hu0 hu1
  · intro i
    fin_cases i
    · exact hn.1
    · exact hn.2.1
    · exact hn.2.2.1
    · exact hn.2.2.2
  · exact Dynamics.Gametes.total_recombine c ht

theorem forced_moment_statistics (c u : ℝ) (g : Dynamics.Gametes ℝ) (ht : g.total = 1) :
    momentStatistics (forcedGametes c u g) =
      let a := u*(1-u)
      let b := (1-2*u)^2
      ![a^2+a*b*(g.pA*(1-g.pA)+g.pB*(1-g.pB))+b^2*momentStatistics g 0,
        (1-c)*b^2*momentStatistics g 1, (1-c)^2*b^2*momentStatistics g 2] := by
  have hh : g.x22 = 1-g.x11-g.x12-g.x21 := by
    unfold Dynamics.Gametes.total at ht
    linarith
  funext i
  fin_cases i <;>
    norm_num [momentStatistics, forcedGametes, independentMutation,
      Dynamics.TwoLocusSelection.fromVector, Dynamics.TwoLocusSelection.vector, Fin.sum_univ_four,
      firstIndex, secondIndex, Rhone.Dynamics.MutationModels.pimTransition,
      Dynamics.Gametes.recombine, Dynamics.Gametes.pA, Dynamics.Gametes.pB, Dynamics.Gametes.pA',
          Dynamics.Gametes.pB', Dynamics.Gametes.D]
  all_goals rw [hh]; ring

/-- Source: ewens2004, sec. 3.1. -/
theorem forced_count_kernel_distribution (M : ℕ) (hM : 0 < M) (c u : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2)
    (a : Rhone.MarkovChain.AlleleCounts M 4) :
    (∀ b, 0 ≤ forcedCountKernel M c u a b) ∧ ∑ b, forcedCountKernel M c u a b = 1 := by
  have hg : ∀ i, 0 ≤ Dynamics.TwoLocusSelection.vector (countGametes M a) i := by
    intro i
    fin_cases i <;>
      change 0 ≤ (_ : ℝ) / M <;> positivity
  have hf := forced_gametes_distribution c u (countGametes M a)
    hc0 hc1 hu0 hu1 hg (count_gametes_total M hM a)
  exact sampling_kernel_distribution M _ hf.1 hf.2

/-- Source: ewens2004, sec. 3.1. -/
def ldWFChain (M : ℕ) (hM : 0 < M) (c u : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2) :
    Rhone.MarkovChain.FinChain (Rhone.MarkovChain.AlleleCounts M 4) where
  P := forcedCountKernel M c u
  nonneg := fun a b => (forced_count_kernel_distribution M hM c u hc0 hc1 hu0 hu1 a).1 b
  row_sum := fun a => (forced_count_kernel_distribution M hM c u hc0 hc1 hu0 hu1 a).2

/-- Source: ewens2004, sec. 3.1. -/
theorem forced_sampling_moment_recursion (M : ℕ) (hM : 0 < M) (c u : ℝ)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2)
    (a : Rhone.MarkovChain.AlleleCounts M 4) :
    (fun i => ∑ b, forcedCountKernel M c u a b *
      momentStatistics (countGametes M b) i) =
      samplingMomentMatrix M *ᵥ momentStatistics (forcedGametes c u (countGametes M a)) := by
  have hg : ∀ i, 0 ≤ Dynamics.TwoLocusSelection.vector (countGametes M a) i := by
    intro i
    fin_cases i <;> change 0 ≤ (_ : ℝ) / M <;> positivity
  have hf := forced_gametes_distribution c u (countGametes M a)
    hc0 hc1 hu0 hu1 hg (count_gametes_total M hM a)
  exact sampling_moment_recursion M hM _ hf.1 hf.2

end Rhone.MarkovChain.WFAllocationLD
