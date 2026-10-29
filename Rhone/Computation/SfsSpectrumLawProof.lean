/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.SfsProof
public import Rhone.Computation.SfsNullProof
public import Rhone.Statistics.SfsMarkedSpectrum

/-!
# Executable expected spectrum under the marked Kingman law

Source: fu1995, eq. 22; watterson1975, p. 258, eq. (1.4a); durrett2008, Thm 1.20. -/

@[expose] public section
namespace Rhone.Computation.Sfs
open MeasureTheory

/-- Source: fu1995, eq. 22. -/
theorem spectrum_getD_eq_integral (theta : Rat) (htheta : 0 ≤ theta) {n i : Nat}
    (hi : 1 ≤ i) (hin : i < n) :
    (((spectrum n theta).getD (i - 1) 0 : Rat) : Real) =
      ∫ x, Rhone.Statistics.markedKingmanSfs n i x
        ∂Rhone.Coalescent.markedKingmanLaw n
            (NNReal.mk (theta : Real) (by exact_mod_cast htheta)) := by
  rw [spectrum_getD_eq theta hi hin]
  exact Rhone.Statistics.expSfs_eq_integral_markedKingmanSfs theta htheta hi hin

/-- Source: fu1995, eq. 22. -/
theorem spectrum_getElem_eq_integral (theta : Rat) (htheta : 0 ≤ theta) {n j : Nat}
    (hj : j < (spectrum n theta).size) :
    (((spectrum n theta)[j] : Rat) : Real) =
      ∫ x, Rhone.Statistics.markedKingmanSfs n (j + 1) x
        ∂Rhone.Coalescent.markedKingmanLaw n
            (NNReal.mk (theta : Real) (by exact_mod_cast htheta)) := by
  have hjn : j < n - 1 := by rwa [spectrum_size] at hj
  have h := spectrum_getD_eq_integral theta htheta (n := n) (i := j + 1) (by omega) (by omega)
  rw [← h, Nat.add_sub_cancel]
  simp [Array.getD, hj]

/-- Source: fu1995, eq. 22. -/
theorem spectrum_toList_sum (n : Nat) (theta : Rat) :
    (spectrum n theta).toList.sum =
      ∑ offset ∈ Finset.range (n - 1), meanBin theta (offset + 1) := by
  have h : ∀ m : Nat, ((List.range m).map (fun offset => meanBin theta (offset + 1))).sum =
      ∑ offset ∈ Finset.range m, meanBin theta (offset + 1) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
      simp
  simpa [spectrum] using h (n - 1)

/-- Source: fu1995, eq. 22; watterson1975, p. 258, eq. (1.4a); durrett2008, Thm 1.20. -/
theorem spectrum_toList_sum_eq_meanSegregating (n : Nat) (theta : Rat) :
    (spectrum n theta).toList.sum = (moments n theta).meanSegregating := by
  rw [spectrum_toList_sum, meanSegregating_eq, ← Rhone.Statistics.sum_expSfs,
    Finset.range_eq_Ico, Finset.sum_Ico_add' (fun i => meanBin theta i) 0 (n - 1) 1]
  apply Finset.sum_congr
  · ext i
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  · intro i hi
    rw [Finset.mem_Icc] at hi
    exact meanBin_eq theta hi.1 (by omega)

/-- Source: fu1995, eq. 22; watterson1975, p. 258, eq. (1.4a); durrett2008, Thm 1.20. -/
theorem spectrum_toList_sum_eq_integral (theta : Rat) (htheta : 0 ≤ theta)
    {n : Nat} (hn : 2 ≤ n) :
    (((spectrum n theta).toList.sum : Rat) : Real) =
      ∫ x, Rhone.Statistics.markedKingmanSegregating n x
        ∂Rhone.Coalescent.markedKingmanLaw n
            (NNReal.mk (theta : Real) (by exact_mod_cast htheta)) := by
  rw [spectrum_toList_sum_eq_meanSegregating]
  exact Rhone.Computation.SfsNull.meanSegregating_eq_integral theta htheta hn

/-- Source: fu1995, eq. 22. -/
theorem spectrum_toList_sum_eq_sum_integral (theta : Rat) (htheta : 0 ≤ theta)
    {n : Nat} (hn : 2 ≤ n) :
    (((spectrum n theta).toList.sum : Rat) : Real) =
      ∑ i ∈ Finset.Icc 1 (n - 1), ∫ x, Rhone.Statistics.markedKingmanSfs n i x
        ∂Rhone.Coalescent.markedKingmanLaw n
            (NNReal.mk (theta : Real) (by exact_mod_cast htheta)) := by
  rw [spectrum_toList_sum_eq_integral theta htheta hn]
  exact (Rhone.Statistics.sum_markedKingmanSfs_mean hn _).symm

end Rhone.Computation.Sfs
