/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.ClosedSet

/-! # Lumping a finite chain along a function of the state -/

@[expose] public section

namespace Rhone.MarkovChain

open Finset

def preimageFinset {S T : Type*} [Fintype S] [DecidableEq T] (f : S → T) (B : Finset T) :
    Finset S := univ.filter fun x => f x ∈ B

@[simp] theorem mem_preimageFinset {S T : Type*} [Fintype S] [DecidableEq T] {f : S → T}
    {B : Finset T} {x : S} : x ∈ preimageFinset f B ↔ f x ∈ B := by
  simp [preimageFinset]

namespace FinChain

variable {S T : Type*} [Fintype S] [Fintype T] [DecidableEq T]

def Lumps (C : FinChain S) (f : S → T) (D : FinChain T) : Prop :=
  ∀ x t, ∑ y with f y = t, C.P x y = D.P (f x) t

def IsLumpable (C : FinChain S) (f : S → T) : Prop :=
  ∀ x x', f x = f x' → ∀ t, ∑ y with f y = t, C.P x y = ∑ y with f y = t, C.P x' y

open Classical in
noncomputable def lump (C : FinChain S) (f : S → T) : FinChain T where
  P t t' := if h : ∃ x, f x = t then ∑ y with f y = t', C.P h.choose y
    else if t = t' then 1 else 0
  nonneg t t' := by
    split_ifs
    · exact Finset.sum_nonneg fun y _ => C.nonneg _ y
    · exact zero_le_one
    · exact le_rfl
  row_sum t := by
    by_cases h : ∃ x, f x = t
    · simp only [h, ↓reduceDIte]
      rw [Finset.sum_fiberwise univ f fun y => C.P h.choose y, C.row_sum]
    · simp [h]

variable {C : FinChain S} {f : S → T} {D : FinChain T}

theorem IsLumpable.lumps_lump (h : C.IsLumpable f) : C.Lumps f (C.lump f) := by
  intro x t
  have hex : ∃ x', f x' = f x := ⟨x, rfl⟩
  simp only [lump, hex, ↓reduceDIte]
  exact h x _ hex.choose_spec.symm t

theorem Lumps.isLumpable (hL : C.Lumps f D) : C.IsLumpable f := by
  intro x x' hxx' t
  rw [hL x t, hL x' t, hxx']

theorem lumps_id (D : FinChain T) : D.Lumps id D := by
  intro x t
  simp [Finset.filter_eq']

theorem Lumps.expect_comp (hL : C.Lumps f D) (g : T → ℝ) :
    C.expect (g ∘ f) = D.expect g ∘ f := by
  funext x
  rw [expect_apply, Function.comp_apply, expect_apply]
  refine (Finset.sum_fiberwise univ f fun y => C.P x y * (g ∘ f) y).symm.trans ?_
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← hL x t, Finset.sum_mul]
  exact Finset.sum_congr rfl fun y hy => by
    rw [Function.comp_apply, (Finset.mem_filter.1 hy).2]

theorem Lumps.isHarmonic_comp (hL : C.Lumps f D) {h : T → ℝ} (hh : D.IsHarmonic h) :
    C.IsHarmonic (h ∘ f) := by
  unfold IsHarmonic at *
  rw [hL.expect_comp, hh]

variable [DecidableEq S]

theorem Lumps.expectN_comp (hL : C.Lumps f D) (n : ℕ) (g : T → ℝ) :
    C.expectN n (g ∘ f) = D.expectN n g ∘ f := by
  induction n generalizing g with
  | zero => simp
  | succ n ih => rw [expectN_succ', hL.expect_comp, ih, expectN_succ']

theorem Lumps.sum_stepN_filter (hL : C.Lumps f D) (n : ℕ) (p : T → Prop) [DecidablePred p]
    (c : T → ℝ) (x : S) :
    ∑ y with p (f y), C.stepN n x y * c (f y) = ∑ t with p t, D.stepN n (f x) t * c t := by
  have h := congrFun (hL.expectN_comp n fun t => if p t then c t else 0) x
  simp only [expectN_apply, Function.comp_apply, mul_ite, mul_zero] at h
  rw [Finset.sum_filter, Finset.sum_filter]
  exact h

theorem Lumps.sum_stepN_fibre (hL : C.Lumps f D) (n : ℕ) (x : S) (t : T) :
    ∑ y with f y = t, C.stepN n x y = D.stepN n (f x) t := by
  have h := hL.sum_stepN_filter n (fun s => s = t) (fun _ => 1) x
  simpa [Finset.filter_eq'] using h

theorem Lumps.sum_stepN_preimage (hL : C.Lumps f D) (n : ℕ) (B : Finset T) (c : T → ℝ)
    (x : S) :
    ∑ y ∈ preimageFinset f B, C.stepN n x y * c (f y) = ∑ t ∈ B, D.stepN n (f x) t * c t := by
  have h := hL.sum_stepN_filter n (fun t => t ∈ B) c x
  have e : (univ.filter fun t => t ∈ B) = B := by
    ext t
    simp
  rw [e] at h
  exact h

theorem Lumps.sum_stepN_preimage_compl (hL : C.Lumps f D) (n : ℕ) (B : Finset T) (c : T → ℝ)
    (x : S) :
    ∑ y ∈ (preimageFinset f B)ᶜ, C.stepN n x y * c (f y) =
      ∑ t ∈ Bᶜ, D.stepN n (f x) t * c t := by
  have h := hL.sum_stepN_filter n (fun t => t ∉ B) c x
  have e1 : (univ.filter fun t => t ∉ B) = Bᶜ := by
    ext t
    simp
  have e2 : (univ.filter fun y => f y ∉ B) = (preimageFinset f B)ᶜ := by
    ext y
    simp
  rw [e1, e2] at h
  exact h

omit [DecidableEq S] in
theorem Lumps.isClosedSet_preimage (hL : C.Lumps f D) {B : Finset T} (hB : D.IsClosedSet B) :
    C.IsClosedSet (preimageFinset f B) := by
  intro x hx y hy
  rw [mem_preimageFinset] at hx hy
  have h0 := hB (f x) hx (f y) hy
  rw [← hL x (f y)] at h0
  exact (Finset.sum_eq_zero_iff_of_nonneg fun z _ => C.nonneg x z).1 h0 y
    (Finset.mem_filter.2 ⟨mem_univ y, rfl⟩)

theorem Lumps.reaches_preimage (hL : C.Lumps f D) {B : Finset T} (hR : D.Reaches B) :
    C.Reaches (preimageFinset f B) := by
  intro x
  obtain ⟨n, b, hb, hpos⟩ := hR (f x)
  rw [← hL.sum_stepN_fibre n x b] at hpos
  obtain ⟨y, hy, hypos⟩ := Finset.exists_lt_of_sum_lt (f := fun _ => (0 : ℝ))
    (g := fun y => C.stepN n x y) (s := univ.filter fun y => f y = b) (by simpa using hpos)
  refine ⟨n, y, ?_, hypos⟩
  rw [mem_preimageFinset, (Finset.mem_filter.1 hy).2]
  exact hb

theorem Lumps.survival_preimage (hL : C.Lumps f D) (B : Finset T) (n : ℕ) (x : S) :
    C.survival (preimageFinset f B) n x = D.survival B n (f x) := by
  have h := hL.sum_stepN_preimage_compl n B (fun _ => 1) x
  simpa [survival] using h

theorem Lumps.enterProb_preimage (hL : C.Lumps f D) (B : Finset T) (x : S) :
    C.enterProb (preimageFinset f B) x = D.enterProb B (f x) := by
  have h : ∀ n, ∑ a ∈ preimageFinset f B, C.stepN n x a = ∑ t ∈ B, D.stepN n (f x) t := fun n => by
    simpa using hL.sum_stepN_preimage n B (fun _ => 1) x
  simp only [enterProb, h]

theorem Lumps.absorbProb_preimage (hL : C.Lumps f D) (b : T) (x : S) :
    C.enterProb (preimageFinset f {b}) x = D.absorbProb b (f x) := by
  rw [hL.enterProb_preimage, enterProb_singleton]

theorem Lumps.potential_preimage (hL : C.Lumps f D) (B : Finset T) (c : T → ℝ) (x : S) :
    C.potential (preimageFinset f B) (c ∘ f) x = D.potential B c (f x) := by
  simp only [potential, Function.comp_apply, hL.sum_stepN_preimage_compl _ B c x]

theorem Lumps.absorbTime_preimage (hL : C.Lumps f D) (B : Finset T) (x : S) :
    C.absorbTime (preimageFinset f B) x = D.absorbTime B (f x) := by
  simp only [absorbTime, hL.survival_preimage]

end FinChain

end Rhone.MarkovChain
