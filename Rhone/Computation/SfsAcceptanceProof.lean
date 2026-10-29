/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.SfsMarkedProof
public import Rhone.Computation.SfsCheckProof
public import Rhone.Computation.SfsNullProof
public import Rhone.Computation.SfsNullCheckProof

/-! # Acceptance by the SFS and Watterson checkers against the marked Kingman law -/

@[expose] public section
namespace Rhone.Computation.Sfs
open MeasureTheory

structure Request where
  geneCopies : Nat
  theta : Rat

def Request.valid (q : Request) : Bool :=
  decide (2 ≤ q.geneCopies ∧ q.geneCopies ≤ 4096 ∧ 0 ≤ q.theta)

def Request.check (q : Request) (claim : Array Rat) : Bool :=
  checkReport q.geneCopies q.theta claim

theorem Request.valid_iff (q : Request) :
    q.valid = true ↔ 2 ≤ q.geneCopies ∧ q.geneCopies ≤ 4096 ∧ 0 ≤ q.theta := by
  simp [Request.valid]

private theorem array_eq_of_getD {a b : Array Rat} (hs : a.size = b.size)
    (h : ∀ i, i < a.size → a.getD i 0 = b.getD i 0) : a = b := by
  apply Array.ext hs
  intro i h1 h2
  have := h i h1
  simpa [Array.getD, h1, h2] using this

private theorem getD_append_left (xs ys : Array Rat) (k : Nat) (hk : k < xs.size) :
    (xs ++ ys).getD k 0 = xs.getD k 0 := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_append_left hk]

private theorem getD_append_right (xs ys : Array Rat) (k : Nat) :
    (xs ++ ys).getD (xs.size + k) 0 = ys.getD k 0 := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_append_right]

private theorem report_size (n : Nat) (theta : Rat) :
    (reportValues n theta).size = 9 + (n - 1) := by
  simp [reportValues, spectrum]
  omega

private theorem report_getD_bin (n : Nat) (theta : Rat) (k : Nat) (hk : k < n - 1) :
    (reportValues n theta).getD (9 + k) 0 = theta / ((k + 1 : Nat) : Rat) := by
  refine (getD_append_right _ (spectrum n theta) k).trans ?_
  simp [spectrum, Array.getD, hk, meanBin]

theorem Request.check_sound (q : Request) (claim : Array Rat)
    (hvalid : q.valid = true) (accepted : q.check claim = true)
    (htheta : 0 ≤ q.theta) :
    claim.size = q.geneCopies + 8 ∧
    claim.getD 0 0 = Rhone.Statistics.tajimaA1 q.geneCopies ∧
    claim.getD 1 0 = Rhone.Statistics.tajimaA2 q.geneCopies ∧
    claim.getD 2 0 = Rhone.Statistics.tajimaB1 q.geneCopies ∧
    claim.getD 3 0 = Rhone.Statistics.tajimaB2 q.geneCopies ∧
    (claim.getD 4 0 : Real) =
      ∫ x, Rhone.Statistics.markedKingmanSegregating q.geneCopies x
        ∂Rhone.Coalescent.markedKingmanLaw q.geneCopies
          (NNReal.mk (q.theta : Real) (by exact_mod_cast htheta)) ∧
    (claim.getD 5 0 : Real) =
      ProbabilityTheory.variance (Rhone.Statistics.markedKingmanSegregating q.geneCopies)
        (Rhone.Coalescent.markedKingmanLaw q.geneCopies
          (NNReal.mk (q.theta : Real) (by exact_mod_cast htheta))) ∧
    (claim.getD 6 0 : Real) =
      ∫ x, Rhone.Coalescent.markedKingmanPi q.geneCopies x
        ∂Rhone.Coalescent.markedKingmanLaw q.geneCopies
          (NNReal.mk (q.theta : Real) (by exact_mod_cast htheta)) ∧
    (claim.getD 7 0 : Real) =
      ∫ x, Rhone.Coalescent.markedKingmanPi q.geneCopies x ^ 2
        ∂Rhone.Coalescent.markedKingmanLaw q.geneCopies
          (NNReal.mk (q.theta : Real) (by exact_mod_cast htheta)) ∧
    (claim.getD 8 0 : Real) =
      ∫ x, (Rhone.Coalescent.markedKingmanPi q.geneCopies x - (q.theta : Real)) ^ 2
        ∂Rhone.Coalescent.markedKingmanLaw q.geneCopies
          (NNReal.mk (q.theta : Real) (by exact_mod_cast htheta)) ∧
    (∀ k, k < q.geneCopies - 1 →
      claim.getD (9 + k) 0 = q.theta / ((k + 1 : Nat) : Rat)) := by
  obtain ⟨n, theta⟩ := q
  obtain ⟨hn, -, -⟩ := (Request.valid_iff _).mp hvalid
  dsimp only at hn htheta ⊢
  have h : claim = reportValues n theta := (checkReport_iff _ _ _).mp accepted
  subst h
  have e0 : (reportValues n theta).getD 0 0 = (coefficients n).a1 :=
    getD_append_left _ _ 0 (by simp)
  have e1 : (reportValues n theta).getD 1 0 = (coefficients n).a2 :=
    getD_append_left _ _ 1 (by simp)
  have e2 : (reportValues n theta).getD 2 0 = (coefficients n).b1 :=
    getD_append_left _ _ 2 (by simp)
  have e3 : (reportValues n theta).getD 3 0 = (coefficients n).b2 :=
    getD_append_left _ _ 3 (by simp)
  have e4 : (reportValues n theta).getD 4 0 = (moments n theta).meanSegregating :=
    getD_append_left _ _ 4 (by simp)
  have e5 : (reportValues n theta).getD 5 0 = (moments n theta).varianceSegregating :=
    getD_append_left _ _ 5 (by simp)
  have e6 : (reportValues n theta).getD 6 0 = (moments n theta).meanPairwise :=
    getD_append_left _ _ 6 (by simp)
  have e7 : (reportValues n theta).getD 7 0 = (moments n theta).secondMomentPairwise :=
    getD_append_left _ _ 7 (by simp)
  have e8 : (reportValues n theta).getD 8 0 = (moments n theta).variancePairwise :=
    getD_append_left _ _ 8 (by simp)
  rw [e0, e1, e2, e3, e4, e5, e6, e7, e8]
  refine ⟨?_, a1_eq n, a2_eq n, b1_eq n, b2_eq n,
    SfsNull.meanSegregating_eq_integral theta htheta hn,
    SfsNull.varianceSegregating_eq_variance theta htheta hn,
    meanPairwise_eq_integral theta htheta hn,
    secondMomentPairwise_eq_integral theta htheta hn,
    variancePairwise_eq_integral theta htheta hn,
    fun k hk => report_getD_bin n theta k hk⟩
  rw [report_size]
  omega

theorem Request.check_complete (q : Request) (claim : Array Rat)
    (hvalid : q.valid = true) (htheta : 0 ≤ q.theta)
    (hsize : claim.size = q.geneCopies + 8)
    (ha1 : claim.getD 0 0 = Rhone.Statistics.tajimaA1 q.geneCopies)
    (ha2 : claim.getD 1 0 = Rhone.Statistics.tajimaA2 q.geneCopies)
    (hb1 : claim.getD 2 0 = Rhone.Statistics.tajimaB1 q.geneCopies)
    (hb2 : claim.getD 3 0 = Rhone.Statistics.tajimaB2 q.geneCopies)
    (hmeanS : (claim.getD 4 0 : Real) =
      ∫ x, Rhone.Statistics.markedKingmanSegregating q.geneCopies x
        ∂Rhone.Coalescent.markedKingmanLaw q.geneCopies
          (NNReal.mk (q.theta : Real) (by exact_mod_cast htheta)))
    (hvarS : (claim.getD 5 0 : Real) =
      ProbabilityTheory.variance (Rhone.Statistics.markedKingmanSegregating q.geneCopies)
        (Rhone.Coalescent.markedKingmanLaw q.geneCopies
          (NNReal.mk (q.theta : Real) (by exact_mod_cast htheta))))
    (hmeanPi : (claim.getD 6 0 : Real) =
      ∫ x, Rhone.Coalescent.markedKingmanPi q.geneCopies x
        ∂Rhone.Coalescent.markedKingmanLaw q.geneCopies
          (NNReal.mk (q.theta : Real) (by exact_mod_cast htheta)))
    (hsecondPi : (claim.getD 7 0 : Real) =
      ∫ x, Rhone.Coalescent.markedKingmanPi q.geneCopies x ^ 2
        ∂Rhone.Coalescent.markedKingmanLaw q.geneCopies
          (NNReal.mk (q.theta : Real) (by exact_mod_cast htheta)))
    (hvarPi : (claim.getD 8 0 : Real) =
      ∫ x, (Rhone.Coalescent.markedKingmanPi q.geneCopies x - (q.theta : Real)) ^ 2
        ∂Rhone.Coalescent.markedKingmanLaw q.geneCopies
          (NNReal.mk (q.theta : Real) (by exact_mod_cast htheta)))
    (hbins : ∀ k, k < q.geneCopies - 1 →
      claim.getD (9 + k) 0 = q.theta / ((k + 1 : Nat) : Rat)) :
    q.check claim = true := by
  obtain ⟨vsize, va1, va2, vb1, vb2, vmeanS, vvarS, vmeanPi, vsecondPi, vvarPi, vbins⟩ :=
    Request.check_sound q (reportValues q.geneCopies q.theta) hvalid
      (checkReport_complete _ _) htheta
  obtain ⟨hn, -, -⟩ := (Request.valid_iff _).mp hvalid
  refine (checkReport_iff _ _ _).mpr (array_eq_of_getD (hsize.trans vsize.symm) ?_)
  intro i hi
  rw [hsize] at hi
  rcases Nat.lt_or_ge i 9 with h9 | h9
  · interval_cases i
    · exact ha1.trans va1.symm
    · exact ha2.trans va2.symm
    · exact hb1.trans vb1.symm
    · exact hb2.trans vb2.symm
    · exact_mod_cast hmeanS.trans vmeanS.symm
    · exact_mod_cast hvarS.trans vvarS.symm
    · exact_mod_cast hmeanPi.trans vmeanPi.symm
    · exact_mod_cast hsecondPi.trans vsecondPi.symm
    · exact_mod_cast hvarPi.trans vvarPi.symm
  · obtain ⟨k, rfl⟩ : ∃ k, i = 9 + k := ⟨i - 9, by omega⟩
    have hk : k < q.geneCopies - 1 := by omega
    exact (hbins k hk).trans (vbins k hk).symm

theorem Request.zero_copies (theta : Rat) :
    (⟨0, theta⟩ : Request).valid = false ∧ (reportValues 0 theta).getD 2 0 = -1 / 3 := by
  refine ⟨by simp [Request.valid], ?_⟩
  have e2 : (reportValues 0 theta).getD 2 0 = (coefficients 0).b1 :=
    getD_append_left _ _ 2 (by simp)
  rw [e2]
  simp only [coefficients]
  norm_num

theorem Request.negative_theta (n : Nat) (theta : Rat) (htheta : theta < 0) :
    (⟨n, theta⟩ : Request).valid = false ∧ (reportValues n theta).getD 6 0 = theta := by
  refine ⟨?_, ?_⟩
  · simp [Request.valid, not_le.mpr htheta]
  · exact getD_append_left _ _ 6 (by simp)

end Rhone.Computation.Sfs

namespace Rhone.Computation.SfsNull
open MeasureTheory

structure Request where
  geneCopies : Nat
  theta : Rat
  observed : Option Nat

def Request.valid (q : Request) : Bool :=
  decide (2 ≤ q.geneCopies ∧ q.geneCopies ≤ 4096 ∧ 0 ≤ q.theta) &&
    (match q.observed with
      | none => true
      | some count => decide (count ≤ 18446744073709551615))

def Request.check (q : Request) (claim : Array Rat) : Bool :=
  checkReport q.geneCopies q.theta q.observed claim

theorem Request.valid_iff (q : Request) :
    q.valid = true ↔ 2 ≤ q.geneCopies ∧ q.geneCopies ≤ 4096 ∧ 0 ≤ q.theta ∧
      ∀ count, q.observed = some count → count ≤ 18446744073709551615 := by
  obtain ⟨n, theta, observed⟩ := q
  cases observed <;> simp [Request.valid, and_assoc]

private theorem report_some (n : Nat) (theta : Rat) (count : Nat) :
    reportValues n theta (some count) =
      #[(Sfs.coefficients n).a1, (Sfs.coefficients n).a2, (moments n theta).meanSegregating,
        (moments n theta).varianceSegregating, (moments n theta).meanWatterson,
        (moments n theta).varianceWatterson, Sfs.watterson n (count : Rat),
        observedWattersonVariance n (count : Rat)] := by
  simp [reportValues]

theorem Request.check_sound (q : Request) (claim : Array Rat)
    (accepted : q.check claim = true) (htheta : 0 ≤ q.theta) :
    claim.size = 6 + (if q.observed.isSome then 2 else 0) ∧
    claim.getD 0 0 = Rhone.Statistics.tajimaA1 q.geneCopies ∧
    claim.getD 1 0 = Rhone.Statistics.tajimaA2 q.geneCopies ∧
    (claim.getD 2 0 : Real) =
      ∫ x, Rhone.Statistics.markedKingmanSegregating q.geneCopies x
        ∂Rhone.Coalescent.markedKingmanLaw q.geneCopies
          (NNReal.mk (q.theta : Real) (by exact_mod_cast htheta)) ∧
    (claim.getD 3 0 : Real) =
      ProbabilityTheory.variance (Rhone.Statistics.markedKingmanSegregating q.geneCopies)
        (Rhone.Coalescent.markedKingmanLaw q.geneCopies
          (NNReal.mk (q.theta : Real) (by exact_mod_cast htheta))) ∧
    (claim.getD 4 0 : Real) =
      ∫ x, Rhone.Statistics.markedKingmanWatterson q.geneCopies x
        ∂Rhone.Coalescent.markedKingmanLaw q.geneCopies
          (NNReal.mk (q.theta : Real) (by exact_mod_cast htheta)) ∧
    (claim.getD 5 0 : Real) =
      ProbabilityTheory.variance (Rhone.Statistics.markedKingmanWatterson q.geneCopies)
        (Rhone.Coalescent.markedKingmanLaw q.geneCopies
          (NNReal.mk (q.theta : Real) (by exact_mod_cast htheta))) ∧
    (∀ count, q.observed = some count →
      claim.getD 6 0 = Rhone.Statistics.wattersonEstimator q.geneCopies (count : Rat)) := by
  obtain ⟨n, theta, observed⟩ := q
  obtain ⟨hn, -, h⟩ := (checkReport_iff _ _ _ _).mp accepted
  dsimp only at hn htheta h ⊢
  subst h
  cases observed with
  | none =>
    refine ⟨rfl, Sfs.a1_eq n, Sfs.a2_eq n, meanSegregating_eq_integral theta htheta hn,
      varianceSegregating_eq_variance theta htheta hn,
      meanWatterson_eq_integral theta htheta hn,
      varianceWatterson_eq_variance theta htheta hn, ?_⟩
    intro count hcount
    cases hcount
  | some observedCount =>
    rw [report_some]
    refine ⟨rfl, Sfs.a1_eq n, Sfs.a2_eq n, meanSegregating_eq_integral theta htheta hn,
      varianceSegregating_eq_variance theta htheta hn,
      meanWatterson_eq_integral theta htheta hn,
      varianceWatterson_eq_variance theta htheta hn, ?_⟩
    intro count hcount
    cases hcount
    exact Sfs.watterson_eq n _

theorem Request.check_complete (q : Request) (claim : Array Rat)
    (hvalid : q.valid = true) (htheta : 0 ≤ q.theta) (hnone : q.observed = none)
    (hsize : claim.size = 6)
    (ha1 : claim.getD 0 0 = Rhone.Statistics.tajimaA1 q.geneCopies)
    (ha2 : claim.getD 1 0 = Rhone.Statistics.tajimaA2 q.geneCopies)
    (hmeanS : (claim.getD 2 0 : Real) =
      ∫ x, Rhone.Statistics.markedKingmanSegregating q.geneCopies x
        ∂Rhone.Coalescent.markedKingmanLaw q.geneCopies
          (NNReal.mk (q.theta : Real) (by exact_mod_cast htheta)))
    (hvarS : (claim.getD 3 0 : Real) =
      ProbabilityTheory.variance (Rhone.Statistics.markedKingmanSegregating q.geneCopies)
        (Rhone.Coalescent.markedKingmanLaw q.geneCopies
          (NNReal.mk (q.theta : Real) (by exact_mod_cast htheta))))
    (hmeanW : (claim.getD 4 0 : Real) =
      ∫ x, Rhone.Statistics.markedKingmanWatterson q.geneCopies x
        ∂Rhone.Coalescent.markedKingmanLaw q.geneCopies
          (NNReal.mk (q.theta : Real) (by exact_mod_cast htheta)))
    (hvarW : (claim.getD 5 0 : Real) =
      ProbabilityTheory.variance (Rhone.Statistics.markedKingmanWatterson q.geneCopies)
        (Rhone.Coalescent.markedKingmanLaw q.geneCopies
          (NNReal.mk (q.theta : Real) (by exact_mod_cast htheta)))) :
    q.check claim = true := by
  obtain ⟨n, theta, observed⟩ := q
  dsimp only at hnone
  subst hnone
  obtain ⟨hn, -, -, -⟩ := (Request.valid_iff _).mp hvalid
  obtain ⟨vsize, va1, va2, vmeanS, vvarS, vmeanW, vvarW, -⟩ :=
    Request.check_sound ⟨n, theta, none⟩ (reportValues n theta none)
      (checkReport_complete hn _ htheta _) htheta
  replace vsize : (reportValues n theta none).size = 6 := by simpa using vsize
  refine (checkReport_iff _ _ _ _).mpr
    ⟨hn, htheta, Sfs.array_eq_of_getD (hsize.trans vsize.symm) ?_⟩
  intro i hi
  rw [hsize] at hi
  interval_cases i
  · exact ha1.trans va1.symm
  · exact ha2.trans va2.symm
  · exact_mod_cast hmeanS.trans vmeanS.symm
  · exact_mod_cast hvarS.trans vvarS.symm
  · exact_mod_cast hmeanW.trans vmeanW.symm
  · exact_mod_cast hvarW.trans vvarW.symm

theorem Request.check_eq_false (q : Request) (claim : Array Rat)
    (h : q.geneCopies < 2 ∨ q.theta < 0) : q.check claim = false := by
  rw [Bool.eq_false_iff]
  intro accepted
  obtain ⟨hn, htheta, -⟩ := (checkReport_iff _ _ _ _).mp accepted
  rcases h with h | h
  · omega
  · exact absurd htheta (not_le.mpr h)

end Rhone.Computation.SfsNull
