/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.WrightFisherAllocation
public import Rhone.Dynamics.TwoLocusSelection

/-!
# Finite multinomial offspring sampling at two biallelic loci

Source: ewens2004, sec. 3.1. -/

@[expose] public section
noncomputable section
namespace Rhone.MarkovChain.WFAllocationLD
open Finset

/-- Source: ewens2004, sec. 3.1. -/
def countGametes (M : ℕ) (a : AlleleCounts M 4) : Dynamics.Gametes ℝ :=
  Dynamics.TwoLocusSelection.fromVector (fun i => (a.val i : ℝ)/M)

/-- Source: ewens2004, sec. 3.1. -/
def allocationWeight (M : ℕ) (g : Dynamics.Gametes ℝ) (ω : Fin M → Fin 4) : ℝ :=
  ∏ t : Fin M, Dynamics.TwoLocusSelection.vector g (ω t)

/-- Source: ewens2004, sec. 3.1. -/
def samplingKernel (M : ℕ) (g : Dynamics.Gametes ℝ) (b : AlleleCounts M 4) : ℝ :=
  ∑ ω : Fin M → Fin 4,
    if wfAlleleAllocationCounts M 4 ω = b then allocationWeight M g ω else 0

/-- Source: ewens2004, sec. 3.1. -/
def samplingExpectation (M : ℕ) (g : Dynamics.Gametes ℝ) (f : AlleleCounts M 4 → ℝ) : ℝ :=
  ∑ b, samplingKernel M g b*f b

/-- Source: ohta_kimura1969_ld, eq. (3)–(5), p. 49. -/
def momentStatistics (g : Dynamics.Gametes ℝ) : Fin 3 → ℝ :=
  ![g.pA*(1-g.pA)*g.pB*(1-g.pB), g.D*(1-2*g.pA)*(1-2*g.pB), g.D^2]

def samplingMomentMatrix (M : ℕ) : Matrix (Fin 3) (Fin 3) ℝ :=
  let m := (M : ℝ)
  !![(m-1)^2/m^2, (m-1)^2/m^3, 2*(m-1)/m^3;
      0, (m-2)^2*(m-1)/m^3, 4*(m-2)*(m-1)/m^3;
      (m-1)/m^2, (m-1)^2/m^3, (m-1)*(m^2-2*m+2)/m^3]

/-- Source: ewens2004, sec. 3.1. -/
theorem sampling_kernel_distribution (M : ℕ) (g : Dynamics.Gametes ℝ)
    (hg : ∀ i, 0 ≤ Dynamics.TwoLocusSelection.vector g i) (ht : g.total = 1) :
    (∀ b, 0 ≤ samplingKernel M g b) ∧ ∑ b, samplingKernel M g b = 1 := by
  classical
  have hv : ∑ i, Dynamics.TwoLocusSelection.vector g i = 1 := by
    simpa [Dynamics.TwoLocusSelection.vector, Fin.sum_univ_succ, Dynamics.Gametes.total, add_assoc]
        using ht
  constructor
  · intro b
    apply sum_nonneg
    intro ω _
    split_ifs
    · exact prod_nonneg fun t _ => hg (ω t)
    · exact le_refl 0
  · unfold samplingKernel allocationWeight
    rw [sum_comm]
    simp only [sum_ite_eq, mem_univ, ite_eq_left]
    rw [← Fintype.prod_sum]
    simp [hv]

/-- Source: ewens2004, sec. 3.1. -/
theorem sampling_expectation_allocation (M : ℕ) (g : Dynamics.Gametes ℝ)
    (f : AlleleCounts M 4 → ℝ) :
    samplingExpectation M g f = ∑ ω : Fin M → Fin 4,
      allocationWeight M g ω*f (wfAlleleAllocationCounts M 4 ω) := by
  classical
  unfold samplingExpectation samplingKernel
  simp_rw [sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro ω _
  simp [ite_mul]

end Rhone.MarkovChain.WFAllocationLD
