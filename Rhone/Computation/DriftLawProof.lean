/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.DriftLaw
public import Rhone.Computation.AbsorptionKernelProof
public import Rhone.Computation.DriftTrajectoryProof

/-! # The executable law of the count equals the law of the Core chains -/

@[expose] public section
namespace Rhone.Computation.Drift
open Finset MarkovChain MeasureTheory

theorem lawAfter_size (n : Nat) (row : Nat → Nat → Rat) (i t : Nat) :
    (lawAfter n row i t).size = n + 1 := by
  cases t <;> simp [lawAfter, pointLaw, stepLaw]

private theorem lawAfter_zero_getD (n : Nat) (row : Nat → Nat → Rat) (i : Nat)
    (j : Fin (n + 1)) :
    (lawAfter n row i 0).getD j 0 = if (j : Nat) = i then 1 else 0 := by
  simp [lawAfter, pointLaw, Array.getD, j.isLt, List.getElem_toArray, List.getElem_map,
    List.getElem_range]

private theorem lawAfter_succ_getD (n : Nat) (row : Nat → Nat → Rat) (i t : Nat)
    (j : Fin (n + 1)) :
    (lawAfter n row i (t + 1)).getD j 0 =
      Absorption.sum (fun k => (lawAfter n row i t).getD k 0 * row k j) (n + 1) := by
  simp [lawAfter, stepLaw, Array.getD, j.isLt, List.getElem_toArray, List.getElem_map,
    List.getElem_range]

theorem lawAfter_cast (n : Nat) (row : Nat → Nat → Rat) (C : FinChain (Fin (n + 1)))
    (hP : ∀ i j : Fin (n + 1), (row i j : Real) = C.P i j) (t : Nat) (i j : Fin (n + 1)) :
    ((lawAfter n row i t).getD j 0 : Real) = C.stepN t i j := by
  induction t generalizing j with
  | zero =>
    rw [lawAfter_zero_getD, FinChain.stepN_zero, Matrix.one_apply]
    by_cases h : i = j
    · subst h
      simp
    · have h' : (j : Nat) ≠ i := fun e => h (Fin.ext e.symm)
      simp [h, h']
  | succ t ih =>
    rw [lawAfter_succ_getD, FinChain.stepN_succ', Matrix.mul_apply, Absorption.sum_cast,
      ← Fin.sum_univ_eq_sum_range
        (fun k : Nat => (((lawAfter n row i t).getD k 0 * row k j : Rat) : Real)) (n + 1)]
    apply sum_congr rfl
    intro k _
    rw [Rat.cast_mul, ih k, hP k j]

theorem lawHeterozygosity_cast (n : Nat) (row : Nat → Nat → Rat)
    (C : FinChain (Fin (n + 1))) (hP : ∀ i j : Fin (n + 1), (row i j : Real) = C.P i j)
    (t : Nat) (i : Fin (n + 1)) :
    (lawHeterozygosity n (lawAfter n row i t) : Real) =
      C.expectN t (fun j => Rhone.MarkovChain.het n j) i := by
  rw [FinChain.expectN_apply, lawHeterozygosity, Absorption.sum_cast,
    ← Fin.sum_univ_eq_sum_range
      (fun j : Nat => (((lawAfter n row i t).getD j 0 * heterozygosity n j : Rat) : Real))
      (n + 1)]
  apply sum_congr rfl
  intro j _
  rw [Rat.cast_mul, lawAfter_cast n row C hP t i j, heterozygosity_cast]

theorem wfDistribution_size (n i t : Nat) : (wfDistribution n i t).size = n + 1 :=
  lawAfter_size _ _ _ _

theorem moranDistribution_size (n : Nat) (r : Rat) (i t : Nat) :
    (moranDistribution n r i t).size = n + 1 :=
  lawAfter_size _ _ _ _

theorem wfDistribution_real (n t : Nat) (i j : Fin (n + 1)) :
    ((wfDistribution n i t).getD j 0 : Real) =
      ((wfChain n).pathLaw i).real {ω | ω t = j} := by
  rw [FinChain.pathLaw_real_eval]
  exact lawAfter_cast n _ (wfChain n) (Absorption.wfKernel_getD_eq n) t i j

theorem moranDistribution_real (n : Nat) (r : Rat) (hr : 0 < (r : Real)) (t : Nat)
    (i j : Fin (n + 1)) :
    ((moranDistribution n r i t).getD j 0 : Real) =
      ((moranChain n (r : Real) hr).pathLaw i).real {ω | ω t = j} := by
  rw [FinChain.pathLaw_real_eval]
  exact lawAfter_cast n _ (moranChain n (r : Real) hr) (Absorption.moranKernel_getD_eq n r hr)
    t i j

theorem wfLawHeterozygosity_integral (n t : Nat) (i : Fin (n + 1)) :
    (lawHeterozygosity n (wfDistribution n i t) : Real) =
      ∫ ω, Rhone.MarkovChain.het n (ω t) ∂(wfChain n).pathLaw i := by
  rw [FinChain.integral_eval (wfChain n) t (fun j : Fin (n + 1) => Rhone.MarkovChain.het n j) i]
  exact lawHeterozygosity_cast n _ (wfChain n) (Absorption.wfKernel_getD_eq n) t i

theorem moranLawHeterozygosity_integral (n : Nat) (r : Rat) (hr : 0 < (r : Real)) (t : Nat)
    (i : Fin (n + 1)) :
    (lawHeterozygosity n (moranDistribution n r i t) : Real) =
      ∫ ω, Rhone.MarkovChain.het n (ω t) ∂(moranChain n (r : Real) hr).pathLaw i := by
  rw [FinChain.integral_eval (moranChain n (r : Real) hr) t
    (fun j : Fin (n + 1) => Rhone.MarkovChain.het n j) i]
  exact lawHeterozygosity_cast n _ (moranChain n (r : Real) hr)
    (Absorption.moranKernel_getD_eq n r hr) t i

theorem wfLawHeterozygosity_eq (n t : Nat) (i : Fin (n + 1)) :
    lawHeterozygosity n (wfDistribution n i t) = wfHeterozygosity n i t := by
  have h := (wfLawHeterozygosity_integral n t i).trans (wf_heterozygosity_integral n t i).symm
  exact_mod_cast h

private theorem moran_integral_one (n t : Nat) (i : Fin (n + 1)) (s : Real) (hs : 0 < s)
    (h1 : s = 1) :
    ∫ ω, Rhone.MarkovChain.het n (ω t) ∂(moranChain n s hs).pathLaw i =
      (moranHeterozygosity n i t : Real) := by
  subst h1
  exact (moran_heterozygosity_integral n t i).symm

theorem moranLawHeterozygosity_neutral (n t : Nat) (i : Fin (n + 1)) :
    lawHeterozygosity n (moranDistribution n 1 i t) = moranHeterozygosity n i t := by
  have hr : 0 < ((1 : Rat) : Real) := by norm_num
  have h := (moranLawHeterozygosity_integral n 1 hr t i).trans
    (moran_integral_one n t i _ hr (by norm_num))
  exact_mod_cast h

end Rhone.Computation.Drift
