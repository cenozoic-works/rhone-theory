/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.TypedAncestralChain.OneStepLaw

/-! # The type-carrying chain computes the σ-weighted chain -/

@[expose] public section

namespace Rhone.Coalescent.TypedAncestralChain

open Finset TwoLocusGenealogy LinearAlgebra.Recursion

variable {n KA KB : ℕ} {θA θB ρ : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ}
variable {σA : Fin n → Fin KA} {σB : Fin n → Fin KB}

noncomputable def hitNT (σA : Fin n → Fin KA) (σB : Fin n → Fin KB) (θA θB ρ : ℝ)
    (πA : Fin KA → ℝ)
    (πB : Fin KB → ℝ) : ℕ → TSt n KA KB → ℝ
  | 0, s => if s.1 = ∅ ∧ Fits σA σB s then 1 else 0
  | N + 1, s =>
      if 0 < dtot θA θB ρ s.1 then
        stepT θA θB ρ πA πB (hitNT σA σB θA θB ρ πA πB N) s / dtot θA θB ρ s.1
      else if s.1 = ∅ ∧ Fits σA σB s then 1 else 0

theorem hitNT_zero (s : TSt n KA KB) :
    hitNT σA σB θA θB ρ πA πB 0 s = if s.1 = ∅ ∧ Fits σA σB s then 1 else 0 := rfl

theorem hitNT_succ_of_pos {s : TSt n KA KB} (N : ℕ) (h : 0 < dtot θA θB ρ s.1) :
    hitNT σA σB θA θB ρ πA πB (N + 1) s
      = stepT θA θB ρ πA πB (hitNT σA σB θA θB ρ πA πB N) s / dtot θA θB ρ s.1 := by
  rw [hitNT, ite_eq_left h]

theorem hitNT_succ_of_nonpos {s : TSt n KA KB} (N : ℕ) (h : ¬ 0 < dtot θA θB ρ s.1) :
    hitNT σA σB θA θB ρ πA πB (N + 1) s = if s.1 = ∅ ∧ Fits σA σB s then 1 else 0 := by
  rw [hitNT, ite_eq_right h]

theorem fits_mk {X : Finset (Lin n)} {τA : Fin n → Option (Fin KA)}
    {τB : Fin n → Option (Fin KB)} :
    Fits σA σB ((X, τA, τB) : TSt n KA KB) ↔ FitsT σA τA ∧ FitsT σB τB := Iff.rfl

theorem sum_pi_ite_A (πA : Fin KA → ℝ) (S : Finset (Fin n)) (v : ℝ) :
    (∑ i, πA i * (if ∀ k ∈ S, σA k = i then v else 0)) = matchA σA πA S * v := by
  rw [matchA, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by split_ifs <;> ring

theorem sum_pi_ite_B (πB : Fin KB → ℝ) (T : Finset (Fin n)) (v : ℝ) :
    (∑ j, πB j * (if ∀ k ∈ T, σB k = j then v else 0)) = matchB σB πB T * v := by
  rw [matchB, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by split_ifs <;> ring

theorem resA_of_mem {s : TSt n KA KB} (hs : WFT s) {p : Lin n} (hp : p ∈ s.1) :
    ∀ k ∈ p.1, s.2.1 k = none := fun k hk => (hs.resA k).2 (mem_coverA.2 ⟨p, hp, hk⟩)

theorem resB_of_mem {s : TSt n KA KB} (hs : WFT s) {p : Lin n} (hp : p ∈ s.1) :
    ∀ k ∈ p.2, s.2.2 k = none := fun k hk => (hs.resB k).2 (mem_coverB.2 ⟨p, hp, hk⟩)

theorem hitNT_of_nonpos {s : TSt n KA KB} (h : ¬ 0 < dtot θA θB ρ s.1) (N : ℕ) :
    hitNT σA σB θA θB ρ πA πB N s = if s.1 = ∅ ∧ Fits σA σB s then 1 else 0 := by
  cases N with
  | zero => exact hitNT_zero s
  | succ N => exact hitNT_succ_of_nonpos N h

theorem hitNT_succ_eq_sum (N : ℕ) (s : TSt n KA KB) :
    hitNT σA σB θA θB ρ πA πB (N + 1) s
      = ∑ t : TSt n KA KB, transT θA θB ρ πA πB s t * hitNT σA σB θA θB ρ πA πB N t := by
  by_cases hd : 0 < dtot θA θB ρ s.1
  · have key : (∑ t : TSt n KA KB, hitNT σA σB θA θB ρ πA πB N t
        * stepT θA θB ρ πA πB (fun t' => if t' = t then 1 else 0) s)
        = stepT θA θB ρ πA πB (hitNT σA σB θA θB ρ πA πB N) s := by
      rw [stepT_sum]
      congr 1
      funext t'
      simp
    rw [hitNT_succ_of_pos N hd, ← key, Finset.sum_div]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [transT_of_dtot_pos hd]
    ring
  · have hval : ∀ t : TSt n KA KB,
        transT θA θB ρ πA πB s t * hitNT σA σB θA θB ρ πA πB N t
          = if t = s then hitNT σA σB θA θB ρ πA πB N t else 0 := by
      intro t
      rw [transT_of_dtot_nonpos hd]
      split_ifs <;> ring
    rw [hitNT_succ_of_nonpos N hd, ← hitNT_of_nonpos hd N,
      Finset.sum_congr rfl fun t _ => hval t,
      Finset.sum_ite_eq' Finset.univ s (fun t => hitNT σA σB θA θB ρ πA πB N t),
      ite_eq_left (Finset.mem_univ s)]

theorem hitNT_eq (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (N : ℕ) {s : TSt n KA KB}
    (hs : WFT s) :
    hitNT σA σB θA θB ρ πA πB N s
      = if Fits σA σB s then hitN σA σB θA θB ρ πA πB N s.1 else 0 := by
  induction N generalizing s with
  | zero =>
    by_cases hf : Fits σA σB s
    · by_cases he : s.1 = ∅
      · rw [hitNT_zero, ite_eq_left ⟨he, hf⟩, ite_eq_left hf, he, hitN_empty]
      · rw [hitNT_zero, ite_eq_right (fun hc => he hc.1), ite_eq_left hf, hitN, ite_eq_right he]
    · rw [hitNT_zero, ite_eq_right (fun hc => hf hc.2), ite_eq_right hf]
  | succ N ih =>
    by_cases hd : 0 < dtot θA θB ρ s.1
    · have hne : s.1 ≠ ∅ := by
        intro hc
        rw [hc, dtot_empty] at hd
        exact absurd hd (lt_irrefl 0)
      have hstep : stepT θA θB ρ πA πB (hitNT σA σB θA θB ρ πA πB N) s
          = if Fits σA σB s then
              step σA σB θA θB ρ πA πB (hitN σA σB θA θB ρ πA πB N) s.1 else 0 := by
        by_cases hf : Fits σA σB s
        · rw [ite_eq_left hf, stepT, step]
          have hcoal : ∀ p ∈ s.1, ∀ q ∈ s.1.erase p,
              hitNT σA σB θA θB ρ πA πB N (coalL s.1 p q, s.2.1, s.2.2)
                = hitN σA σB θA θB ρ πA πB N (coalL s.1 p q) := by
            intro p hp q hq
            rw [ih (hs.coal hp hq), ite_eq_left (fits_mk.2 hf)]
          have hmutA : ∀ p ∈ carA s.1,
              (∑ i, πA i * hitNT σA σB θA θB ρ πA πB N
                  (mutAL s.1 p, setT s.2.1 p.1 i, s.2.2))
                = matchA σA πA p.1 * hitN σA σB θA θB ρ πA πB N (mutAL s.1 p) := by
            intro p hp
            have hpL : p ∈ s.1 := carA_subset _ hp
            rw [← sum_pi_ite_A πA p.1 (hitN σA σB θA θB ρ πA πB N (mutAL s.1 p))]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [ih (hs.mutA hpL i)]
            by_cases hc : ∀ k ∈ p.1, σA k = i
            · rw [ite_eq_left hc, ite_eq_left (fits_mk.2 ⟨(fitsT_setT hf.1).2 hc, hf.2⟩)]
            · rw [ite_eq_right hc,
                ite_eq_right (fun hcc => hc ((fitsT_setT hf.1).1 (fits_mk.1 hcc).1))]
          have hmutB : ∀ p ∈ carB s.1,
              (∑ j, πB j * hitNT σA σB θA θB ρ πA πB N
                  (mutBL s.1 p, s.2.1, setT s.2.2 p.2 j))
                = matchB σB πB p.2 * hitN σA σB θA θB ρ πA πB N (mutBL s.1 p) := by
            intro p hp
            have hpL : p ∈ s.1 := carB_subset _ hp
            rw [← sum_pi_ite_B πB p.2 (hitN σA σB θA θB ρ πA πB N (mutBL s.1 p))]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [ih (hs.mutB hpL j)]
            by_cases hc : ∀ k ∈ p.2, σB k = j
            · rw [ite_eq_left hc, ite_eq_left (fits_mk.2 ⟨hf.1, (fitsT_setT hf.2).2 hc⟩)]
            · rw [ite_eq_right hc,
                ite_eq_right (fun hcc => hc ((fitsT_setT hf.2).1 (fits_mk.1 hcc).2))]
          have hrec : ∀ p ∈ carC s.1,
              hitNT σA σB θA θB ρ πA πB N (recL s.1 p, s.2.1, s.2.2)
                = hitN σA σB θA θB ρ πA πB N (recL s.1 p) := by
            intro p hp
            obtain ⟨hpL, h1, h2⟩ := mem_carC.1 hp
            rw [ih (hs.recomb hpL h1 h2), ite_eq_left (fits_mk.2 hf)]
          rw [Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl (hcoal p hp),
            Finset.sum_congr rfl hmutA, Finset.sum_congr rfl hmutB,
            Finset.sum_congr rfl hrec]
        · have hf' : ¬ (FitsT σA s.2.1 ∧ FitsT σB s.2.2) := hf
          rw [ite_eq_right hf, stepT]
          have e1 : (∑ p ∈ s.1, ∑ q ∈ s.1.erase p,
              hitNT σA σB θA θB ρ πA πB N (coalL s.1 p q, s.2.1, s.2.2)) = 0 := by
            refine Finset.sum_eq_zero fun p hp => Finset.sum_eq_zero fun q hq => ?_
            rw [ih (hs.coal hp hq)]
            exact ite_eq_right fun hc => hf (fits_mk.1 hc)
          have e2 : (∑ p ∈ carA s.1, ∑ i, πA i * hitNT σA σB θA θB ρ πA πB N
              (mutAL s.1 p, setT s.2.1 p.1 i, s.2.2)) = 0 := by
            refine Finset.sum_eq_zero fun p hp => Finset.sum_eq_zero fun i _ => ?_
            have hpL : p ∈ s.1 := carA_subset _ hp
            rw [ih (hs.mutA hpL i)]
            refine mul_eq_zero_of_right _ (ite_eq_right fun hc => ?_)
            obtain ⟨hc1, hc2⟩ := fits_mk.1 hc
            rcases not_and_or.1 hf' with h | h
            · exact (not_fitsT_setT (resA_of_mem hs hpL) h) hc1
            · exact h hc2
          have e3 : (∑ p ∈ carB s.1, ∑ j, πB j * hitNT σA σB θA θB ρ πA πB N
              (mutBL s.1 p, s.2.1, setT s.2.2 p.2 j)) = 0 := by
            refine Finset.sum_eq_zero fun p hp => Finset.sum_eq_zero fun j _ => ?_
            have hpL : p ∈ s.1 := carB_subset _ hp
            rw [ih (hs.mutB hpL j)]
            refine mul_eq_zero_of_right _ (ite_eq_right fun hc => ?_)
            obtain ⟨hc1, hc2⟩ := fits_mk.1 hc
            rcases not_and_or.1 hf' with h | h
            · exact h hc1
            · exact (not_fitsT_setT (resB_of_mem hs hpL) h) hc2
          have e4 : (∑ p ∈ carC s.1,
              hitNT σA σB θA θB ρ πA πB N (recL s.1 p, s.2.1, s.2.2)) = 0 := by
            refine Finset.sum_eq_zero fun p hp => ?_
            obtain ⟨hpL, h1, h2⟩ := mem_carC.1 hp
            rw [ih (hs.recomb hpL h1 h2)]
            exact ite_eq_right fun hc => hf (fits_mk.1 hc)
          rw [e1, e2, e3, e4]
          ring
      rw [hitNT_succ_of_pos N hd, hstep]
      by_cases hf : Fits σA σB s
      · rw [ite_eq_left hf, ite_eq_left hf, hitN_succ_of_ne N hne]
      · rw [ite_eq_right hf, ite_eq_right hf, zero_div]
    · have he : s.1 = ∅ := by
        by_contra hc
        exact hd (dtot_pos hθA hθB hρ hs.wf (Finset.nonempty_iff_ne_empty.2 hc))
      rw [hitNT_succ_of_nonpos N hd, he]
      by_cases hf : Fits σA σB s
      · rw [ite_eq_left ⟨rfl, hf⟩, ite_eq_left hf, hitN_empty]
      · rw [ite_eq_right (fun hc => hf hc.2), ite_eq_right hf]

def noneT (n K : ℕ) : Fin n → Option (Fin K) := fun _ => none

def initT (n KA KB : ℕ) : TSt n KA KB := (fullState n, noneT n KA, noneT n KB)

theorem initT_wft : WFT (initT n KA KB) := by
  refine ⟨fullState_wf, fun k => ?_, fun k => ?_⟩
  · refine ⟨fun _ => mem_coverA.2 ⟨({k}, {k}), mem_fullState.2 ⟨k, rfl⟩, ?_⟩, fun _ => rfl⟩
    exact Finset.mem_singleton_self k
  · refine ⟨fun _ => mem_coverB.2 ⟨({k}, {k}), mem_fullState.2 ⟨k, rfl⟩, ?_⟩, fun _ => rfl⟩
    exact Finset.mem_singleton_self k

theorem initT_fits : Fits σA σB (initT n KA KB) :=
  ⟨fitsT_none σA, fitsT_none σB⟩

theorem fits_iff_eq {s : TSt n KA KB} (hs : WFT s) (he : s.1 = ∅) :
    Fits σA σB s ↔ (∀ k, s.2.1 k = some (σA k)) ∧ (∀ k, s.2.2 k = some (σB k)) := by
  have hA : ∀ k, ∃ i, s.2.1 k = some i := by
    intro k
    cases hh : s.2.1 k with
    | none =>
      have hc := (hs.resA k).1 hh
      rw [he] at hc
      simp only [coverA_empty] at hc
      exact absurd hc (by simp)
    | some i => exact ⟨i, rfl⟩
  have hB : ∀ k, ∃ j, s.2.2 k = some j := by
    intro k
    cases hh : s.2.2 k with
    | none =>
      have hc := (hs.resB k).1 hh
      rw [he] at hc
      simp only [coverB_empty] at hc
      exact absurd hc (by simp)
    | some j => exact ⟨j, rfl⟩
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun k => ?_, fun k => ?_⟩
    · obtain ⟨i, hi⟩ := hA k
      rw [hi, h1 k i hi]
    · obtain ⟨j, hj⟩ := hB k
      rw [hj, h2 k j hj]
  · rintro ⟨h1, h2⟩
    refine ⟨fun k i hki => ?_, fun k j hkj => ?_⟩
    · rw [h1 k] at hki
      exact Option.some.inj hki
    · rw [h2 k] at hkj
      exact Option.some.inj hkj

end Rhone.Coalescent.TypedAncestralChain
