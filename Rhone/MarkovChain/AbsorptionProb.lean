/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.Absorption

/-! # Absorption probabilities and expected costs before absorption -/

@[expose] public section

namespace Rhone.MarkovChain.FinChain

open Finset Filter Topology

variable {S : Type*} [Fintype S] [DecidableEq S] (C : FinChain S)

noncomputable def absorbProb (a x : S) : ℝ := ⨆ n, C.stepN n x a

noncomputable def potential (A : Finset S) (c : S → ℝ) (x : S) : ℝ :=
  ∑' n, ∑ y ∈ Aᶜ, C.stepN n x y * c y

noncomputable def absorbTime (A : Finset S) (x : S) : ℝ := ∑' n, C.survival A n x

variable {C} {A : Finset S}

theorem IsAbsorbing.stepN_mono {a : S} (ha : C.IsAbsorbing a) (x : S) :
    Monotone fun n => C.stepN n x a := by
  refine monotone_nat_of_le_succ fun n => ?_
  rw [stepN_succ', Matrix.mul_apply]
  have h := Finset.single_le_sum (f := fun z => C.stepN n x z * C.P z a)
    (fun z _ => mul_nonneg (C.stepN_nonneg n x z) (C.nonneg z a)) (mem_univ a)
  simpa [show C.P a a = 1 from ha] using h

theorem bddAbove_stepN (C : FinChain S) (x a : S) :
    BddAbove (Set.range fun n => C.stepN n x a) :=
  ⟨1, by rintro _ ⟨n, rfl⟩; exact C.stepN_le_one n x a⟩

theorem tendsto_stepN_absorbProb {a : S} (ha : C.IsAbsorbing a) (x : S) :
    Tendsto (fun n => C.stepN n x a) atTop (𝓝 (C.absorbProb a x)) :=
  tendsto_atTop_ciSup (ha.stepN_mono x) (C.bddAbove_stepN x a)

theorem absorbProb_nonneg (C : FinChain S) (a x : S) : 0 ≤ C.absorbProb a x :=
  le_ciSup_of_le (C.bddAbove_stepN x a) 0 (C.stepN_nonneg 0 x a)

theorem absorbProb_le_one (C : FinChain S) (a x : S) : C.absorbProb a x ≤ 1 :=
  ciSup_le fun n => C.stepN_le_one n x a

theorem absorbProb_isHarmonic {a : S} (ha : C.IsAbsorbing a) :
    C.IsHarmonic (C.absorbProb a) := by
  funext x
  have h1 : Tendsto (fun n => ∑ y, C.P x y * C.stepN n y a) atTop
      (𝓝 (∑ y, C.P x y * C.absorbProb a y)) :=
    tendsto_finsetSum _ fun y _ => (tendsto_stepN_absorbProb ha y).const_mul _
  have h2 : Tendsto (fun n => ∑ y, C.P x y * C.stepN n y a) atTop (𝓝 (C.absorbProb a x)) := by
    have := (tendsto_add_atTop_iff_nat 1).2 (tendsto_stepN_absorbProb ha x)
    refine this.congr fun n => ?_
    rw [stepN_succ, Matrix.mul_apply]
  exact tendsto_nhds_unique h1 h2

theorem absorbProb_of_isAbsorbing {b : S} (hb : C.IsAbsorbing b) (a : S) :
    C.absorbProb a b = if b = a then 1 else 0 := by
  simp [absorbProb, hb.stepN_apply]

theorem absorbProb_eq_of_isHarmonic (hA : C.IsAbsorbingSet A) (hR : C.Reaches A) {a : S}
    (ha : a ∈ A) {h : S → ℝ} (hh : C.IsHarmonic h) (h1 : h a = 1)
    (h0 : ∀ b ∈ A, b ≠ a → h b = 0) : C.absorbProb a = h := by
  refine (absorbProb_isHarmonic (hA a ha)).eq_of_eqOn hA hR hh fun b hb => ?_
  rw [absorbProb_of_isAbsorbing (hA b hb)]
  by_cases hba : b = a
  · simp [hba, h1]
  · simp [hba, h0 b hb hba]

theorem sum_absorbProb (hA : C.IsAbsorbingSet A) (hR : C.Reaches A) (x : S) :
    ∑ a ∈ A, C.absorbProb a x = 1 := by
  have h1 : Tendsto (fun n => ∑ a ∈ A, C.stepN n x a) atTop (𝓝 (∑ a ∈ A, C.absorbProb a x)) :=
    tendsto_finsetSum _ fun a ha => tendsto_stepN_absorbProb (hA a ha) x
  have h2 : Tendsto (fun n => ∑ a ∈ A, C.stepN n x a) atTop (𝓝 1) := by
    have := (tendsto_survival hA hR x).const_sub 1
    rw [sub_zero] at this
    refine this.congr fun n => ?_
    have := C.survival_add_sum A n x
    linarith
  exact tendsto_nhds_unique h1 h2

theorem summable_potential (hA : C.IsAbsorbingSet A) (hR : C.Reaches A) (c : S → ℝ) (x : S) :
    Summable fun n => ∑ y ∈ Aᶜ, C.stepN n x y * c y := by
  refine Summable.of_norm_bounded ((summable_survival hA hR x).mul_left (∑ z, |c z|)) fun n => ?_
  rw [Real.norm_eq_abs, survival, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun y _ => ?_)
  rw [abs_mul, abs_of_nonneg (C.stepN_nonneg n x y), mul_comm]
  exact mul_le_mul_of_nonneg_right
    (Finset.single_le_sum (f := fun z => |c z|) (fun z _ => abs_nonneg _) (mem_univ y))
    (C.stepN_nonneg n x y)

theorem potential_of_mem (hA : C.IsAbsorbingSet A) {a : S} (ha : a ∈ A) (c : S → ℝ) :
    C.potential A c a = 0 := by
  have : ∀ n, ∑ y ∈ Aᶜ, C.stepN n a y * c y = 0 := fun n =>
    Finset.sum_eq_zero fun y hy => by
      have hne : a ≠ y := fun h => (mem_compl.1 hy) (h ▸ ha)
      simp [(hA a ha).stepN_apply, hne]
  simp [potential, this]

theorem potential_nonneg (C : FinChain S) (A : Finset S) {c : S → ℝ} (hc : ∀ y, 0 ≤ c y)
    (x : S) : 0 ≤ C.potential A c x :=
  tsum_nonneg fun n => Finset.sum_nonneg fun y _ => mul_nonneg (C.stepN_nonneg n x y) (hc y)

theorem potential_step (hA : C.IsAbsorbingSet A) (hR : C.Reaches A) (c : S → ℝ) (x : S) :
    C.potential A c x = (if x ∈ A then 0 else c x) + ∑ y, C.P x y * C.potential A c y := by
  have hs := summable_potential hA hR c
  have h0 : ∑ y ∈ Aᶜ, C.stepN 0 x y * c y = if x ∈ A then 0 else c x := by
    simp [stepN_zero, Matrix.one_apply]
  have hsucc : ∀ n, ∑ y ∈ Aᶜ, C.stepN (n + 1) x y * c y =
      ∑ z, C.P x z * ∑ y ∈ Aᶜ, C.stepN n z y * c y := by
    intro n
    simp only [stepN_succ, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    exact Finset.sum_comm
  rw [potential, (hs x).tsum_eq_zero_add, h0]
  congr 1
  simp only [hsucc]
  rw [Summable.tsum_finsetSum fun z _ => (hs z).mul_left _]
  exact Finset.sum_congr rfl fun z _ => tsum_mul_left

theorem eq_potential_of_step (hA : C.IsAbsorbingSet A) (hR : C.Reaches A) {c u : S → ℝ}
    (h0 : ∀ a ∈ A, u a = 0) (hstep : ∀ x, x ∉ A → u x = c x + ∑ y, C.P x y * u y) :
    u = C.potential A c := by
  have hd : C.IsHarmonic (u - C.potential A c) := by
    funext x
    rw [expect_apply]
    simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    by_cases hx : x ∈ A
    · simp [(hA x hx).P_apply]
    · have h1 := hstep x hx
      have h2 := potential_step hA hR c x
      simp only [hx, ↓reduceIte] at h2
      linarith
  have := hd.eq_zero_of_eqOn hA hR fun a ha => by simp [h0 a ha, potential_of_mem hA ha]
  exact sub_eq_zero.1 this

theorem absorbTime_eq_potential (C : FinChain S) (A : Finset S) :
    C.absorbTime A = C.potential A fun _ => 1 := by
  funext x
  simp [absorbTime, potential, survival]

theorem absorbTime_of_mem (hA : C.IsAbsorbingSet A) {a : S} (ha : a ∈ A) :
    C.absorbTime A a = 0 := by
  rw [absorbTime_eq_potential, potential_of_mem hA ha]

theorem absorbTime_step (hA : C.IsAbsorbingSet A) (hR : C.Reaches A) {x : S} (hx : x ∉ A) :
    C.absorbTime A x = 1 + ∑ y, C.P x y * C.absorbTime A y := by
  rw [absorbTime_eq_potential, potential_step hA hR]
  simp only [hx, ↓reduceIte]

theorem eq_absorbTime_of_step (hA : C.IsAbsorbingSet A) (hR : C.Reaches A) {t : S → ℝ}
    (h0 : ∀ a ∈ A, t a = 0) (hstep : ∀ x, x ∉ A → t x = 1 + ∑ y, C.P x y * t y) :
    t = C.absorbTime A := by
  rw [absorbTime_eq_potential]
  exact eq_potential_of_step hA hR h0 hstep

end Rhone.MarkovChain.FinChain
