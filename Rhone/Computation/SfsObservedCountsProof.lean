/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.SfsObserved
public import Rhone.Computation.SfsProof
public import Rhone.Statistics.SfsLinearStatistics
public import Rhone.Statistics.SfsSegregatingIdentification

/-!
# Exact observed-count summaries

Source: watterson1975, sec. 1.2, p. 257; durrett2008, Thm 1.22; tajima1989, p. 586, eq. (10)–(12);
fu1995, eq. 22. -/

@[expose] public section
namespace Rhone.Computation.SfsObserved
open scoped BigOperators

theorem total_eq_sum (counts : Array Nat) :
    total counts = ∑ k : Fin counts.size, counts[k.val] := by
  simp [total, List.sum_ofFn]

theorem pairwise_eq_sum (n : Nat) (counts : Array Nat) :
    pairwise n counts =
      ∑ k : Fin counts.size, pairWeight n (k.val + 1) * (counts[k.val] : Rat) := by
  simp [pairwise, List.sum_ofFn]

theorem pairWeight_cast (n i : Nat) (hn : 2 ≤ n) (hi : i ≤ n) :
    (pairWeight n i : Real) =
      2 * (i : Real) * ((n : Real) - i) / ((n : Real) * ((n : Real) - 1)) := by
  unfold pairWeight
  push_cast
  rw [Nat.cast_sub hi, Nat.cast_sub (by omega : 1 ≤ n)]
  simp only [Nat.cast_one]
  have hn0 : (n : Real) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hn1 : (n : Real) - 1 ≠ 0 := by
    have h : (2 : Real) ≤ n := by exact_mod_cast hn
    linarith
  field_simp [hn0, hn1]

theorem watterson_eq_estimator (n : Nat) (counts : Array Nat) :
    Sfs.watterson n (total counts) = Rhone.Statistics.wattersonEstimator n (total counts) :=
  Sfs.watterson_eq n _

def classCounts (n : Nat)
    (x : Rhone.Coalescent.KingmanMutationHistory n ×
        (Rhone.Coalescent.KingmanMutationBranch n → Nat)) :
    Array Nat :=
  Array.ofFn (fun k : Fin (n - 1) =>
    ∑ b, if b.2.card = k.val + 1 then x.2 b else 0)

private theorem sum_classes (n : Nat) (hn : 2 ≤ n) (f : Nat → Real) :
    (∑ k : Fin (n - 1), f (k.val + 1)) = ∑ i ∈ Finset.Icc 1 (n - 1), f i := by
  have hi : Finset.Icc 1 (n - 1) = Finset.Ico 1 n := by
    ext i
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hi, Finset.sum_Ico_eq_sum_range]
  rw [Fin.sum_univ_eq_sum_range (fun k => f (k + 1)) (n - 1)]
  simp only [Nat.add_comm]

theorem pairwise_classCounts (n : Nat) (hn : 2 ≤ n)
    (x : Rhone.Coalescent.KingmanMutationHistory n ×
        (Rhone.Coalescent.KingmanMutationBranch n → Nat)) :
    (pairwise n (classCounts n x) : Real) = Rhone.Coalescent.markedKingmanPi n x := by
  have hsum :
      (∑ k : Fin (n - 1), (pairWeight n (k.val + 1) : Real) *
        ∑ b, if b.2.card = k.val + 1 then (x.2 b : Real) else 0) =
      Rhone.Coalescent.markedKingmanPi n x := by
    rw [Rhone.Statistics.markedKingmanPi_eq_sum_sfs]
    unfold Rhone.Statistics.markedKingmanSfs
    calc
      _ = ∑ k : Fin (n - 1),
          (2 * ((k.val + 1 : Nat) : Real) * ((n : Real) - ((k.val + 1 : Nat) : Real)) /
            ((n : Real) * ((n : Real) - 1))) *
              ∑ b, if b.2.card = k.val + 1 then (x.2 b : Real) else 0 := by
        apply Finset.sum_congr rfl
        intro k _
        rw [pairWeight_cast n (k.val + 1) hn (by omega)]
      _ = _ := sum_classes n hn (fun i =>
        (2 * (i : Real) * ((n : Real) - i) / ((n : Real) * ((n : Real) - 1))) *
          ∑ b, if b.2.card = i then (x.2 b : Real) else 0)
  simpa [pairwise, classCounts, List.sum_ofFn, apply_ite] using hsum

theorem total_classCounts_ae (n : Nat) (hn : 2 ≤ n) (theta : NNReal) :
    (fun x => (total (classCounts n x) : Real)) =ᵐ[Rhone.Coalescent.markedKingmanLaw n theta]
      Rhone.Statistics.markedKingmanSegregating n := by
  have hsum : ∀ x, (total (classCounts n x) : Real) =
      ∑ i ∈ Finset.Icc 1 (n - 1), Rhone.Statistics.markedKingmanSfs n i x := by
    intro x
    simpa [total, classCounts, List.sum_ofFn, Rhone.Statistics.markedKingmanSfs] using
      sum_classes n hn (fun i => Rhone.Statistics.markedKingmanSfs n i x)
  filter_upwards [Rhone.Statistics.markedKingmanSegregating_ae_eq_sum_sfs n theta] with x hx
  exact (hsum x).trans hx.symm

theorem watterson_classCounts_ae (n : Nat) (hn : 2 ≤ n) (theta : NNReal) :
    (fun x => (Sfs.watterson n (total (classCounts n x)) : Real))
      =ᵐ[Rhone.Coalescent.markedKingmanLaw n theta] Rhone.Statistics.markedKingmanWatterson n := by
  filter_upwards [total_classCounts_ae n hn theta] with x hx
  simp only [Sfs.watterson, Rat.cast_div, Rat.cast_natCast, Sfs.a1_eq,
    Rhone.Statistics.markedKingmanWatterson]
  rw [hx]

end Rhone.Computation.SfsObserved
