/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.DriftFast

/-! # The fraction-free drift comparison equals the rational one -/

@[expose] public section
namespace Rhone.Computation.DriftFast
open Lean

theorem isum_cast (f : Nat → Int) (k : Nat) :
    ((isum f k : Int) : Rat) = Absorption.sum (fun x => (f x : Rat)) k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [isum, Absorption.sum, Rat.intCast_add, ih]

theorem sum_congr {f g : Nat → Rat} {k : Nat} (h : ∀ x, x < k → f x = g x) :
    Absorption.sum f k = Absorption.sum g k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [Absorption.sum]
    rw [ih (fun x hx => h x (Nat.lt_succ_of_lt hx)), h k (Nat.lt_succ_self k)]

theorem sum_div (f : Nat → Rat) (c : Rat) (k : Nat) :
    Absorption.sum (fun x => f x / c) k = Absorption.sum f k / c := by
  induction k with
  | zero => simp only [Absorption.sum]; grind
  | succ k ih =>
    simp only [Absorption.sum, ih]
    grind

theorem size_range {α : Type} (m : Nat) (f : Nat → α) :
    ((List.range m).map f).toArray.size = m := by
  simp

theorem getD_range {α : Type} {m j : Nat} (f : Nat → α) (d : α) (hj : j < m) :
    ((List.range m).map f).toArray.getD j d = f j := by
  simp [hj]

theorem array_eq_iff (a b : Array Rat) :
    a = b ↔ a.size = b.size ∧ ∀ j, j < a.size → a.getD j 0 = b.getD j 0 := by
  constructor
  · rintro rfl
    exact ⟨rfl, fun _ _ => rfl⟩
  · rintro ⟨hs, he⟩
    apply Array.ext hs
    intro j h1 h2
    have := he j h1
    simpa [h1, h2] using this

theorem num_cast_of_den {q : Rat} (h : q.den = 1) : ((q.num : Int) : Rat) = q :=
  Rat.ext (by simp) (by simp [h])

theorem scaleOk_spec {n : Nat} {row : Nat → Nat → Rat} {D : Nat} (h : scaleOk n row D = true) :
    D ≠ 0 ∧ ∀ k j, k < n + 1 → j < n + 1 → (((row k j * D).num : Int) : Rat) = row k j * D := by
  simp only [scaleOk, Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true, List.mem_range,
    beq_iff_eq] at h
  exact ⟨h.1, fun k j hk hj => num_cast_of_den (h.2 k hk j hj)⟩

theorem scaleVecOk_spec {n : Nat} {g : Nat → Rat} {G : Nat} (h : scaleVecOk n g G = true) :
    G ≠ 0 ∧ ∀ j, j < n + 1 → (((g j * G).num : Int) : Rat) = g j * G := by
  simp only [scaleVecOk, Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true, List.mem_range,
    beq_iff_eq] at h
  exact ⟨h.1, fun j hj => num_cast_of_den (h.2 j hj)⟩

theorem entry_scaledMatrix {n : Nat} {row : Nat → Nat → Rat} {D k j : Nat} (hk : k < n + 1)
    (hj : j < n + 1) : entry (scaledMatrix n row D) k j = (row k j * D).num := by
  simp [entry, scaledMatrix, hk, hj]

theorem lawAfter_vecAfter {n : Nat} {row : Nat → Nat → Rat} {D : Nat} (i : Nat)
    (h : scaleOk n row D = true) (t : Nat) :
    (Drift.lawAfter n row i t).size = n + 1 ∧
      (vecAfter n (scaledMatrix n row D) i t).size = n + 1 ∧
      ∀ j, j < n + 1 → (Drift.lawAfter n row i t).getD j 0 =
        (((vecAfter n (scaledMatrix n row D) i t).getD j 0 : Int) : Rat) / ((D : Rat) ^ t) := by
  obtain ⟨hD, hM⟩ := scaleOk_spec h
  have hDq : (D : Rat) ≠ 0 := by simpa using hD
  induction t with
  | zero =>
    refine ⟨size_range _ _, size_range _ _, fun j hj => ?_⟩
    simp only [Drift.lawAfter, vecAfter, Drift.pointLaw, pointVec, getD_range _ _ hj]
    split <;> grind
  | succ t ih =>
    obtain ⟨_, _, hlaw⟩ := ih
    refine ⟨size_range _ _, size_range _ _, fun j hj => ?_⟩
    simp only [Drift.lawAfter, vecAfter, Drift.stepLaw, stepVec, getD_range _ _ hj, isum_cast]
    rw [← sum_div]
    apply sum_congr
    intro k hk
    rw [hlaw k hk, entry_scaledMatrix hk hj, Rat.intCast_mul, hM k j hk hj]
    have hp : (D : Rat) ^ t ≠ 0 := by
      have : D ^ t ≠ 0 := by simp [hD]
      exact_mod_cast this
    grind

theorem eq_div_iff_cross (q : Rat) (a : Int) {E : Nat} (hE : E ≠ 0) :
    q = (a : Rat) / (E : Rat) ↔ q.num * E = a * q.den := by
  have hEq : (E : Rat) ≠ 0 := by simpa using hE
  have hd : (q.den : Rat) ≠ 0 := by simpa using q.den_nz
  have hq : q = (q.num : Rat) / (q.den : Rat) := by
    rw [← Rat.mkRat_eq_div, Rat.mkRat_self]
  constructor
  · intro h
    rw [← Rat.intCast_inj]
    push_cast
    rw [hq] at h
    grind
  · intro h
    have h' := congrArg (fun z : Int => (z : Rat)) h
    simp only [Rat.intCast_mul, Rat.intCast_natCast] at h'
    rw [hq]
    grind

theorem lawCheck_eq (n : Nat) (row : Nat → Nat → Rat) (i t : Nat) (distribution : Array Rat)
    (heterozygosity : Rat) :
    lawCheck n row i t distribution heterozygosity =
      (decide (distribution = Drift.lawAfter n row i t) &&
        decide (heterozygosity = Drift.lawHeterozygosity n (Drift.lawAfter n row i t))) := by
  unfold lawCheck
  simp only
  split
  · rename_i hguard
    simp only [Bool.and_eq_true] at hguard
    obtain ⟨hs, hv⟩ := hguard
    obtain ⟨hlawSize, _, hlaw⟩ := lawAfter_vecAfter i hs t
    obtain ⟨hG, hK⟩ := scaleVecOk_spec hv
    have hD := (scaleOk_spec hs).1
    have hE : denLcm n row ^ t ≠ 0 := by simp [hD]
    have hEG : denLcm n row ^ t * denLcmVec n (Drift.heterozygosity n) ≠ 0 :=
      Nat.mul_ne_zero hE hG
    have hDq : (denLcm n row : Rat) ^ t ≠ 0 := by
      exact_mod_cast hE
    have hGq : (denLcmVec n (Drift.heterozygosity n) : Rat) ≠ 0 := by simpa using hG
    congr 1
    · rw [Bool.eq_iff_iff, decide_eq_true_eq, array_eq_iff, hlawSize]
      simp only [lawMatches, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range]
      constructor
      · rintro ⟨hsize, hall⟩
        refine ⟨hsize, fun j hj => ?_⟩
        rw [hsize] at hj
        rw [hlaw j hj, ← Rat.natCast_pow, eq_div_iff_cross _ _ hE]
        exact hall j hj
      · rintro ⟨hsize, hall⟩
        refine ⟨hsize, fun j hj => ?_⟩
        have := hall j (hsize ▸ hj)
        rw [hlaw j hj, ← Rat.natCast_pow, eq_div_iff_cross _ _ hE] at this
        exact this
    · rw [Bool.eq_iff_iff, decide_eq_true_eq, scalarMatches, beq_iff_eq, ← eq_div_iff_cross _ _ hEG]
      have hsum : Drift.lawHeterozygosity n (Drift.lawAfter n row i t) =
          ((isum (fun j => (vecAfter n (scaledMatrix n row (denLcm n row)) i t).getD j 0 *
            (Drift.heterozygosity n j * denLcmVec n (Drift.heterozygosity n)).num) (n + 1) :
              Int) : Rat) /
            ((denLcm n row ^ t * denLcmVec n (Drift.heterozygosity n) : Nat) : Rat) := by
        unfold Drift.lawHeterozygosity
        rw [isum_cast, ← sum_div]
        apply sum_congr
        intro j hj
        rw [hlaw j hj, Rat.intCast_mul, hK j hj, Rat.natCast_mul, Rat.natCast_pow]
        grind
      rw [hsum]
  · rfl

theorem Request.law_eq (r : DriftFull.Request) :
    r.law = Drift.lawAfter r.base.geneCopies (Request.row r) r.base.initialCount r.base.steps := by
  unfold DriftFull.Request.law Request.row Request.kernel Drift.wfDistribution
    Drift.moranDistribution
  split <;> rfl

theorem Request.checkFast_eq (r : DriftFull.Request) : Request.checkFast r = r.check := by
  have hl := Request.law_eq r
  unfold Request.row at hl
  unfold Request.checkFast DriftFull.Request.check
  simp only [lawCheck_eq, ← hl, Bool.and_assoc]

theorem decision_eq (doc : Json) : decision doc = DriftFull.decision doc := by
  unfold decision DriftFull.decision
  cases DriftFull.decode doc with
  | error message => rfl
  | ok r => simp only [Request.checkFast_eq]

theorem requestAst_eq : requestAst = DriftFull.requestAst := by
  funext doc
  unfold requestAst DriftFull.requestAst
  rw [decision_eq]

theorem request_eq : request = DriftFull.request := by
  funext line
  unfold request DriftFull.request
  rw [requestAst_eq]

end Rhone.Computation.DriftFast
