/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.Martingale

/-! # Increments of a harmonic function along a finite chain -/

@[expose] public section

namespace Rhone.MarkovChain.FinChain

open MeasureTheory ProbabilityTheory Finset Filter
open scoped NNReal

variable {S : Type*} [Fintype S] [MeasurableSpace S] [DiscreteMeasurableSpace S] (C : FinChain S)

omit [MeasurableSpace S] [DiscreteMeasurableSpace S] in
theorem abs_le_sum_abs (g : S → ℝ) (y : S) : |g y| ≤ ∑ z, |g z| :=
  Finset.single_le_sum (f := fun z => |g z|) (fun _ _ => abs_nonneg _) (Finset.mem_univ y)

theorem integral_mul_eval_succ (x : S) (n : ℕ) (g : S → ℝ) {h : (ℕ → S) → ℝ}
    (hh : StronglyMeasurable[Filtration.piLE (X := fun _ : ℕ => S) n] h) {B : ℝ}
    (hB : ∀ ω, |h ω| ≤ B) :
    ∫ ω, h ω * g (ω (n + 1)) ∂C.pathLaw x = ∫ ω, h ω * C.expect g (ω n) ∂C.pathLaw x := by
  have hle : Filtration.piLE (X := fun _ : ℕ => S) n ≤
      (inferInstance : MeasurableSpace (ℕ → S)) := Filtration.piLE.le n
  have hgm : Measurable fun ω : ℕ → S => g (ω (n + 1)) :=
    (Measurable.of_discrete (f := g)).comp (measurable_pi_apply _)
  have hint_g : Integrable (fun ω : ℕ → S => g (ω (n + 1))) (C.pathLaw x) :=
    C.integrable_eval g (n + 1) x
  have hint_hg : Integrable (h * fun ω : ℕ → S => g (ω (n + 1))) (C.pathLaw x) := by
    refine Integrable.of_bound ((hh.mono hle).mul hgm.stronglyMeasurable).aestronglyMeasurable
      (B * ∑ z, |g z|) (Eventually.of_forall fun ω => ?_)
    rw [Pi.mul_apply, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hB ω) (abs_le_sum_abs g _) (abs_nonneg _) ((abs_nonneg _).trans (hB ω))
  have h1 := integral_condExp (μ := C.pathLaw x)
    (f := h * fun ω : ℕ → S => g (ω (n + 1))) hle
  have h2 := condExp_mul_of_stronglyMeasurable_left (μ := C.pathLaw x) hh hint_hg hint_g
  have h3 : (C.pathLaw x)[fun ω : ℕ → S => g (ω (n + 1)) | Filtration.piLE n] =ᵐ[C.pathLaw x]
      fun ω => ∫ y, g y ∂C.kernel (ω n) :=
    C.toProcess.condExp_eval_succ x n (Measurable.of_discrete (f := g)) (abs_le_sum_abs g)
  calc ∫ ω, h ω * g (ω (n + 1)) ∂C.pathLaw x
      = ∫ ω, (C.pathLaw x)[h * fun ω : ℕ → S => g (ω (n + 1)) | Filtration.piLE n] ω
          ∂C.pathLaw x := h1.symm
    _ = ∫ ω, h ω * C.expect g (ω n) ∂C.pathLaw x := by
        refine integral_congr_ae ?_
        filter_upwards [h2, h3] with ω hω2 hω3
        rw [hω2, Pi.mul_apply, hω3, C.integral_kernel]

omit [Fintype S] [DiscreteMeasurableSpace S] in
theorem measurable_three [Finite S] [MeasurableSingletonClass S] (F : S → S → S → ℝ)
    (a n m : ℕ) : Measurable fun ω : ℕ → S => F (ω a) (ω n) (ω m) := by
  have hF : Measurable fun t : S × S × S => F t.1 t.2.1 t.2.2 := measurable_of_countable _
  have h3 : Measurable fun ω : ℕ → S => (ω a, ω n, ω m) :=
    (measurable_pi_apply a).prodMk ((measurable_pi_apply n).prodMk (measurable_pi_apply m))
  exact Measurable.comp (g := fun t : S × S × S => F t.1 t.2.1 t.2.2)
    (f := fun ω : ℕ → S => (ω a, ω n, ω m)) hF h3

theorem integrable_three (x : S) (F : S → S → S → ℝ) (a n m : ℕ) :
    Integrable (fun ω : ℕ → S => F (ω a) (ω n) (ω m)) (C.pathLaw x) := by
  obtain ⟨B, hB⟩ : ∃ B, ∀ t : S × S × S, |F t.1 t.2.1 t.2.2| ≤ B :=
    ⟨∑ t : S × S × S, |F t.1 t.2.1 t.2.2|, fun t =>
      Finset.single_le_sum (f := fun t : S × S × S => |F t.1 t.2.1 t.2.2|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ t)⟩
  exact Integrable.of_bound (measurable_three F a n m).aestronglyMeasurable B
    (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hB (ω a, ω n, ω m))

omit [Fintype S] in
theorem stronglyMeasurable_two [Finite S] (F : S → S → ℝ) {a n : ℕ} (han : a ≤ n) :
    StronglyMeasurable[Filtration.piLE (X := fun _ : ℕ => S) n]
      fun ω : ℕ → S => F (ω a) (ω n) := by
  have hF : Measurable fun t : S × S => F t.1 t.2 := measurable_of_countable _
  have ha : Measurable[Filtration.piLE (X := fun _ : ℕ => S) n] fun ω : ℕ → S => ω a :=
    (DiscreteProcess.measurable_eval_piLE (S := S) a).mono
      ((Filtration.piLE (X := fun _ : ℕ => S)).mono han) le_rfl
  have h2 : Measurable[Filtration.piLE (X := fun _ : ℕ => S) n]
      fun ω : ℕ → S => (ω a, ω n) := ha.prodMk (DiscreteProcess.measurable_eval_piLE (S := S) n)
  exact (Measurable.comp (g := fun t : S × S => F t.1 t.2)
    (f := fun ω : ℕ → S => (ω a, ω n)) hF h2).stronglyMeasurable

theorem integral_mul_eval_succ_two (x : S) (n : ℕ) (G : S → S → ℝ) {h : (ℕ → S) → ℝ}
    (hh : StronglyMeasurable[Filtration.piLE (X := fun _ : ℕ => S) n] h) {B : ℝ}
    (hB : ∀ ω, |h ω| ≤ B) :
    ∫ ω, h ω * G (ω n) (ω (n + 1)) ∂C.pathLaw x =
      ∫ ω, h ω * C.expect (G (ω n)) (ω n) ∂C.pathLaw x := by
  classical
  have hle : Filtration.piLE (X := fun _ : ℕ => S) n ≤
      (inferInstance : MeasurableSpace (ℕ → S)) := Filtration.piLE.le n
  have hB0 : 0 ≤ B := by
    obtain ⟨ω⟩ : Nonempty (ℕ → S) := ⟨fun _ => x⟩
    exact (abs_nonneg _).trans (hB ω)
  have hind : ∀ z : S, StronglyMeasurable[Filtration.piLE (X := fun _ : ℕ => S) n]
      (fun ω : ℕ → S => h ω * (if ω n = z then 1 else 0)) := fun z =>
    hh.mul ((Measurable.of_discrete (f := fun y : S => if y = z then (1 : ℝ) else 0)).comp
      (DiscreteProcess.measurable_eval_piLE (S := S) n)).stronglyMeasurable
  have hindB : ∀ z ω, |h ω * (if ω n = z then (1 : ℝ) else 0)| ≤ B := by
    intro z ω
    split_ifs
    · simpa using hB ω
    · simpa using hB0
  have hsplit : ∀ (F : S → ℝ) (ω : ℕ → S), (∑ z, (h ω * (if ω n = z then 1 else 0)) * F z) =
      h ω * F (ω n) := by
    intro F ω
    rw [Finset.sum_eq_single (ω n)]
    · simp
    · intro z _ hz
      simp [Ne.symm hz]
    · simp
  have hint : ∀ (z : S) (F : (ℕ → S) → ℝ), Measurable F → (∀ ω, |F ω| ≤ ∑ y, |G z y|) →
      Integrable (fun ω => (h ω * (if ω n = z then 1 else 0)) * F ω) (C.pathLaw x) := by
    intro z F hFm hFb
    refine Integrable.of_bound (((hind z).mono hle).mul hFm.stronglyMeasurable).aestronglyMeasurable
      (B * ∑ y, |G z y|) (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hindB z ω) (hFb ω) (abs_nonneg _) hB0
  have hexp : ∀ (z y : S), |C.expect (G z) y| ≤ ∑ y, |G z y| := by
    intro z y
    rw [expect_apply]
    calc |∑ w, C.P y w * G z w| ≤ ∑ w, |C.P y w * G z w| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ w, |G z w| := by
          refine Finset.sum_le_sum fun w _ => ?_
          rw [abs_mul, abs_of_nonneg (C.nonneg y w)]
          have hP1 : C.P y w ≤ 1 := by
            rw [← C.row_sum y]
            exact Finset.single_le_sum (f := fun w => C.P y w) (fun w _ => C.nonneg y w)
              (Finset.mem_univ w)
          exact mul_le_of_le_one_left (abs_nonneg _) hP1
  have eL : (fun ω : ℕ → S => h ω * G (ω n) (ω (n + 1))) =
      fun ω => ∑ z, (h ω * (if ω n = z then 1 else 0)) * G z (ω (n + 1)) := by
    funext ω
    exact (hsplit (fun z => G z (ω (n + 1))) ω).symm
  have eR : (fun ω : ℕ → S => h ω * C.expect (G (ω n)) (ω n)) =
      fun ω => ∑ z, (h ω * (if ω n = z then 1 else 0)) * C.expect (G z) (ω n) := by
    funext ω
    exact (hsplit (fun z => C.expect (G z) (ω n)) ω).symm
  rw [eL, eR, integral_finsetSum _ fun z _ => hint z (fun ω => G z (ω (n + 1)))
      ((Measurable.of_discrete (f := G z)).comp (measurable_pi_apply _))
      (fun ω => abs_le_sum_abs (G z) _),
    integral_finsetSum _ fun z _ => hint z (fun ω => C.expect (G z) (ω n))
      ((Measurable.of_discrete (f := C.expect (G z))).comp (measurable_pi_apply _))
      (fun ω => hexp z _)]
  exact Finset.sum_congr rfl fun z _ => C.integral_mul_eval_succ x n (G z) (hind z) (hindB z)

omit [MeasurableSpace S] [DiscreteMeasurableSpace S] in
theorem expect_sub_const (g : S → ℝ) (c : ℝ) (y : S) :
    C.expect (fun z => g z - c) y = C.expect g y - c := by
  simp only [expect_apply, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, C.row_sum, one_mul]

def incr (g : S → ℝ) (a k : ℕ) (ω : ℕ → S) : ℝ := g (ω (a + k)) - g (ω a)

omit [Fintype S] [MeasurableSpace S] [DiscreteMeasurableSpace S] in
theorem incr_succ (g : S → ℝ) (a k : ℕ) (ω : ℕ → S) :
    incr g a (k + 1) ω = incr g a k ω + (g (ω (a + k + 1)) - g (ω (a + k))) := by
  simp only [incr, ← add_assoc]
  ring

omit [Fintype S] [MeasurableSpace S] [DiscreteMeasurableSpace S] in
theorem abs_incr_le_one {g : S → ℝ} (hg : ∀ y, g y ∈ Set.Icc (0 : ℝ) 1) (a k : ℕ)
    (ω : ℕ → S) : |incr g a k ω| ≤ 1 := by
  have h1 := hg (ω (a + k))
  have h2 := hg (ω a)
  rw [incr, abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem integral_incr_sq_le {g : S → ℝ} (hg : C.IsHarmonic g)
    (hg01 : ∀ y, g y ∈ Set.Icc (0 : ℝ) 1) {v : ℝ}
    (hv : ∀ y, C.expect (fun z => (g z - g y) ^ 2) y ≤ v) (x : S) (a k : ℕ) :
    ∫ ω, incr g a k ω ^ 2 ∂C.pathLaw x ≤ k * v := by
  induction k with
  | zero => simp [incr]
  | succ k ih =>
    set n := a + k
    have hS := stronglyMeasurable_two (S := S) (fun ya yn => g yn - g ya) (Nat.le_add_right a k)
    have e : ∀ ω : ℕ → S, incr g a (k + 1) ω ^ 2 = incr g a k ω ^ 2 +
        (2 * incr g a k ω) * (g (ω (n + 1)) - g (ω n)) +
        1 * (g (ω (n + 1)) - g (ω n)) ^ 2 := by
      intro ω
      rw [incr_succ]
      ring
    simp_rw [e]
    rw [integral_add, integral_add]
    · have h1 := C.integral_mul_eval_succ_two x n (fun y z => g z - g y)
        (h := fun ω => 2 * incr g a k ω) (hS.const_mul 2) (B := 2)
        (fun ω => by rw [abs_mul, abs_two]; linarith [abs_incr_le_one hg01 a k ω])
      have h2 := C.integral_mul_eval_succ_two x n (fun y z => (g z - g y) ^ 2) (h := fun _ => 1)
        stronglyMeasurable_const (B := 1) (fun ω => by simp)
      rw [h1, h2]
      have hz : ∀ ω : ℕ → S, 2 * incr g a k ω * C.expect (fun z => g z - g (ω n)) (ω n) = 0 := by
        intro ω
        rw [C.expect_sub_const, hg]
        ring
      simp only [hz, integral_zero, add_zero, one_mul]
      have hle : ∫ ω, C.expect (fun z => (g z - g (ω n)) ^ 2) (ω n) ∂C.pathLaw x ≤ v := by
        calc ∫ ω, C.expect (fun z => (g z - g (ω n)) ^ 2) (ω n) ∂C.pathLaw x
            ≤ ∫ _ω, v ∂C.pathLaw x := integral_mono
                (C.integrable_three x (fun _ yn _ => C.expect (fun z => (g z - g yn) ^ 2) yn) 0 n 0)
                (integrable_const v) fun ω => hv (ω n)
          _ = v := by simp
      push_cast
      linarith
    · exact C.integrable_three x (fun ya yn _ => (g yn - g ya) ^ 2) a n 0
    · exact C.integrable_three x (fun ya yn ym => 2 * (g yn - g ya) * (g ym - g yn)) a n (n + 1)
    · exact (C.integrable_three x (fun ya yn _ => (g yn - g ya) ^ 2) a n 0).add
        (C.integrable_three x (fun ya yn ym => 2 * (g yn - g ya) * (g ym - g yn)) a n (n + 1))
    · exact C.integrable_three x (fun _ yn ym => 1 * (g ym - g yn) ^ 2) 0 n (n + 1)

theorem integral_incr_pow_four_le {g : S → ℝ} (hg : C.IsHarmonic g)
    (hg01 : ∀ y, g y ∈ Set.Icc (0 : ℝ) 1) {v q : ℝ}
    (hv : ∀ y, C.expect (fun z => (g z - g y) ^ 2) y ≤ v)
    (hq : ∀ y, C.expect (fun z => (g z - g y) ^ 4) y ≤ q) (x : S) (a k : ℕ) :
    ∫ ω, incr g a k ω ^ 4 ∂C.pathLaw x ≤ 4 * (k : ℝ) ^ 2 * v ^ 2 + 3 * k * q := by
  have hv0 : 0 ≤ v := by
    refine le_trans ?_ (hv x)
    rw [expect_apply]
    exact Finset.sum_nonneg fun z _ => mul_nonneg (C.nonneg x z) (sq_nonneg _)
  induction k with
  | zero => simp [incr]
  | succ k ih =>
    set n := a + k
    have hS := stronglyMeasurable_two (S := S) (fun ya yn => g yn - g ya) (Nat.le_add_right a k)
    have hsq := C.integral_incr_sq_le hg hg01 hv x a k
    have hpt : ∀ ω : ℕ → S, incr g a (k + 1) ω ^ 4 ≤ incr g a k ω ^ 4 +
        (4 * incr g a k ω ^ 3) * (g (ω (n + 1)) - g (ω n)) +
        (8 * incr g a k ω ^ 2) * (g (ω (n + 1)) - g (ω n)) ^ 2 +
        3 * (g (ω (n + 1)) - g (ω n)) ^ 4 := by
      intro ω
      rw [incr_succ]
      set s := incr g a k ω
      set d := g (ω (a + k + 1)) - g (ω (a + k))
      nlinarith [mul_nonneg (sq_nonneg d) (sq_nonneg (s - d))]
    have i1 : Integrable (fun ω => incr g a k ω ^ 4) (C.pathLaw x) :=
      C.integrable_three x (fun ya yn _ => (g yn - g ya) ^ 4) a n 0
    have i2 : Integrable (fun ω => 4 * incr g a k ω ^ 3 * (g (ω (n + 1)) - g (ω n)))
        (C.pathLaw x) :=
      C.integrable_three x (fun ya yn ym => 4 * (g yn - g ya) ^ 3 * (g ym - g yn)) a n (n + 1)
    have i3 : Integrable (fun ω => 8 * incr g a k ω ^ 2 * (g (ω (n + 1)) - g (ω n)) ^ 2)
        (C.pathLaw x) :=
      C.integrable_three x (fun ya yn ym => 8 * (g yn - g ya) ^ 2 * (g ym - g yn) ^ 2) a n
        (n + 1)
    have i4 : Integrable (fun ω => 3 * (g (ω (n + 1)) - g (ω n)) ^ 4) (C.pathLaw x) :=
      C.integrable_three x (fun _ yn ym => 3 * (g ym - g yn) ^ 4) 0 n (n + 1)
    have i12 : Integrable (fun ω => incr g a k ω ^ 4 +
        4 * incr g a k ω ^ 3 * (g (ω (n + 1)) - g (ω n))) (C.pathLaw x) := i1.add i2
    have i123 : Integrable (fun ω => incr g a k ω ^ 4 +
        4 * incr g a k ω ^ 3 * (g (ω (n + 1)) - g (ω n)) +
        8 * incr g a k ω ^ 2 * (g (ω (n + 1)) - g (ω n)) ^ 2) (C.pathLaw x) := i12.add i3
    have i1234 : Integrable (fun ω => incr g a k ω ^ 4 +
        4 * incr g a k ω ^ 3 * (g (ω (n + 1)) - g (ω n)) +
        8 * incr g a k ω ^ 2 * (g (ω (n + 1)) - g (ω n)) ^ 2 +
        3 * (g (ω (n + 1)) - g (ω n)) ^ 4) (C.pathLaw x) := i123.add i4
    have hmono : ∫ ω, incr g a (k + 1) ω ^ 4 ∂C.pathLaw x ≤
        ∫ ω, (incr g a k ω ^ 4 + 4 * incr g a k ω ^ 3 * (g (ω (n + 1)) - g (ω n)) +
          8 * incr g a k ω ^ 2 * (g (ω (n + 1)) - g (ω n)) ^ 2 +
          3 * (g (ω (n + 1)) - g (ω n)) ^ 4) ∂C.pathLaw x :=
      integral_mono (C.integrable_three x (fun ya _ ym => (g ym - g ya) ^ 4) a 0 (a + (k + 1)))
        i1234 hpt
    rw [integral_add i123 i4, integral_add i12 i3, integral_add i1 i2] at hmono
    have h2 := C.integral_mul_eval_succ_two x n (fun y z => g z - g y)
      (h := fun ω => 4 * incr g a k ω ^ 3) ((hS.pow 3).const_mul 4) (B := 4)
      (fun ω => by
        rw [abs_mul, abs_pow]
        have := abs_incr_le_one hg01 a k ω
        have h3 : |incr g a k ω| ^ 3 ≤ 1 := pow_le_one₀ (abs_nonneg _) this
        norm_num
        linarith)
    have h3 := C.integral_mul_eval_succ_two x n (fun y z => (g z - g y) ^ 2)
      (h := fun ω => 8 * incr g a k ω ^ 2) ((hS.pow 2).const_mul 8) (B := 8)
      (fun ω => by
        rw [abs_mul, abs_pow]
        have := abs_incr_le_one hg01 a k ω
        have h3 : |incr g a k ω| ^ 2 ≤ 1 := pow_le_one₀ (abs_nonneg _) this
        norm_num
        linarith)
    have h4 := C.integral_mul_eval_succ_two x n (fun y z => (g z - g y) ^ 4) (h := fun _ => 3)
      stronglyMeasurable_const (B := 3) (fun ω => by norm_num)
    have e2 : ∫ ω, 4 * incr g a k ω ^ 3 * (g (ω (n + 1)) - g (ω n)) ∂C.pathLaw x = 0 := by
      rw [h2]
      have hz : ∀ ω : ℕ → S,
          4 * incr g a k ω ^ 3 * C.expect (fun z => g z - g (ω n)) (ω n) = 0 := by
        intro ω
        rw [C.expect_sub_const, hg]
        ring
      simp only [hz, integral_zero]
    have e3 : ∫ ω, 8 * incr g a k ω ^ 2 * (g (ω (n + 1)) - g (ω n)) ^ 2 ∂C.pathLaw x ≤
        8 * v * (k * v) := by
      rw [h3]
      calc ∫ ω, 8 * incr g a k ω ^ 2 * C.expect (fun z => (g z - g (ω n)) ^ 2) (ω n)
            ∂C.pathLaw x
          ≤ ∫ ω, 8 * v * incr g a k ω ^ 2 ∂C.pathLaw x := by
            refine integral_mono (C.integrable_three x
              (fun ya yn _ => 8 * (g yn - g ya) ^ 2 * C.expect (fun z => (g z - g yn) ^ 2) yn)
              a n 0)
              ((C.integrable_three x (fun ya yn _ => (g yn - g ya) ^ 2) a n 0).const_mul
                (8 * v)) fun ω => ?_
            change 8 * incr g a k ω ^ 2 * C.expect (fun z => (g z - g (ω n)) ^ 2) (ω n) ≤
              8 * v * incr g a k ω ^ 2
            have := hv (ω n)
            have h0 := sq_nonneg (incr g a k ω)
            nlinarith
        _ = 8 * v * ∫ ω, incr g a k ω ^ 2 ∂C.pathLaw x := integral_const_mul _ _
        _ ≤ 8 * v * (k * v) := by gcongr
    have e4 : ∫ ω, 3 * (g (ω (n + 1)) - g (ω n)) ^ 4 ∂C.pathLaw x ≤ 3 * q := by
      rw [h4]
      calc ∫ ω, 3 * C.expect (fun z => (g z - g (ω n)) ^ 4) (ω n) ∂C.pathLaw x
          ≤ ∫ _ω, 3 * q ∂C.pathLaw x := integral_mono
              (C.integrable_three x (fun _ yn _ => 3 * C.expect (fun z => (g z - g yn) ^ 4) yn)
                0 n 0) (integrable_const _) fun ω =>
                show 3 * C.expect (fun z => (g z - g (ω n)) ^ 4) (ω n) ≤ 3 * q by
                  linarith [hq (ω n)]
        _ = 3 * q := by simp
    push_cast
    nlinarith [sq_nonneg v]

theorem measureReal_exists_abs_incr_ge_le {g : S → ℝ} (hg : C.IsHarmonic g)
    (hg01 : ∀ y, g y ∈ Set.Icc (0 : ℝ) 1) (x : S) (a K : ℕ) {r : ℝ} (hr : 0 < r) :
    (C.pathLaw x).real {ω | ∃ k ≤ K, r ≤ |incr g a k ω|} ≤
      (∫ ω, incr g a K ω ^ 4 ∂C.pathLaw x) / r ^ 4 := by
  classical
  set μ := C.pathLaw x
  let 𝒢 : Filtration ℕ (inferInstance : MeasurableSpace (ℕ → S)) :=
    ⟨fun j => Filtration.piLE (X := fun _ : ℕ => S) (a + j),
      fun i j hij => (Filtration.piLE (X := fun _ : ℕ => S)).mono (Nat.add_le_add_left hij a),
      fun j => Filtration.piLE.le _⟩
  let f : ℕ → (ℕ → S) → ℝ := fun j ω => incr g a j ω ^ 2
  have hS : ∀ j, StronglyMeasurable[𝒢 j] (fun ω : ℕ → S => incr g a j ω) := fun j =>
    stronglyMeasurable_two (S := S) (fun ya yn => g yn - g ya) (Nat.le_add_right a j)
  have hint : ∀ j, Integrable (f j) μ := fun j =>
    C.integrable_three x (fun ya yn _ => (g yn - g ya) ^ 2) a (a + j) 0
  have hsub : Submartingale f 𝒢 μ := by
    refine submartingale_of_setIntegral_le_succ (fun j => (hS j).pow 2) hint fun j s hs => ?_
    have hsm : MeasurableSet s := (𝒢.le j) s hs
    have hind : ∀ (F : (ℕ → S) → ℝ), ∫ ω in s, F ω ∂μ =
        ∫ ω, s.indicator (fun _ => (1 : ℝ)) ω * F ω ∂μ := by
      intro F
      rw [← integral_indicator hsm]
      congr 1
      funext ω
      by_cases h : ω ∈ s <;> simp [h]
    have hIm : StronglyMeasurable[𝒢 j] (s.indicator fun _ : ℕ → S => (1 : ℝ)) :=
      stronglyMeasurable_const.indicator hs
    have hIb : ∀ ω, |s.indicator (fun _ : ℕ → S => (1 : ℝ)) ω| ≤ 1 := by
      intro ω
      by_cases h : ω ∈ s <;> simp [h]
    rw [hind, hind]
    set n := a + j
    have e : ∀ ω : ℕ → S, s.indicator (fun _ => (1 : ℝ)) ω * f (j + 1) ω =
        s.indicator (fun _ => (1 : ℝ)) ω * f j ω +
        (s.indicator (fun _ => (1 : ℝ)) ω * (2 * incr g a j ω)) * (g (ω (n + 1)) - g (ω n)) +
        s.indicator (fun _ => (1 : ℝ)) ω * (g (ω (n + 1)) - g (ω n)) ^ 2 := by
      intro ω
      simp only [f]
      rw [incr_succ]
      ring
    have hIi : ∀ F : (ℕ → S) → ℝ, Integrable F μ →
        Integrable (fun ω => s.indicator (fun _ => (1 : ℝ)) ω * F ω) μ := by
      intro F hF
      have : (fun ω => s.indicator (fun _ => (1 : ℝ)) ω * F ω) = s.indicator F := by
        funext ω
        by_cases h : ω ∈ s <;> simp [h]
      rw [this]
      exact hF.indicator hsm
    have iD : Integrable (fun ω : ℕ → S => 2 * incr g a j ω * (g (ω (n + 1)) - g (ω n))) μ :=
      C.integrable_three x (fun ya yn ym => 2 * (g yn - g ya) * (g ym - g yn)) a n (n + 1)
    have iE : Integrable (fun ω : ℕ → S => (g (ω (n + 1)) - g (ω n)) ^ 2) μ :=
      C.integrable_three x (fun _ yn ym => (g ym - g yn) ^ 2) 0 n (n + 1)
    have jA : Integrable (fun ω => s.indicator (fun _ => (1 : ℝ)) ω * f j ω) μ :=
      hIi _ (hint j)
    have jB : Integrable (fun ω => (s.indicator (fun _ => (1 : ℝ)) ω * (2 * incr g a j ω)) *
        (g (ω (n + 1)) - g (ω n))) μ :=
      (hIi _ iD).congr (Eventually.of_forall fun ω => by ring)
    have jC : Integrable (fun ω => s.indicator (fun _ => (1 : ℝ)) ω *
        (g (ω (n + 1)) - g (ω n)) ^ 2) μ := hIi _ iE
    have jAB : Integrable (fun ω => s.indicator (fun _ => (1 : ℝ)) ω * f j ω +
        (s.indicator (fun _ => (1 : ℝ)) ω * (2 * incr g a j ω)) *
        (g (ω (n + 1)) - g (ω n))) μ := jA.add jB
    simp_rw [e]
    rw [integral_add jAB jC, integral_add jA jB]
    have h1 := C.integral_mul_eval_succ_two x n (fun y z => g z - g y)
      (h := fun ω => s.indicator (fun _ => (1 : ℝ)) ω * (2 * incr g a j ω))
      (hIm.mul ((hS j).const_mul 2)) (B := 2) (fun ω => by
        rw [abs_mul, abs_mul, abs_two]
        have := abs_incr_le_one hg01 a j ω
        have := hIb ω
        have := abs_nonneg (s.indicator (fun _ : ℕ → S => (1 : ℝ)) ω)
        nlinarith)
    rw [h1]
    have hz : ∀ ω : ℕ → S, s.indicator (fun _ => (1 : ℝ)) ω * (2 * incr g a j ω) *
        C.expect (fun z => g z - g (ω n)) (ω n) = 0 := by
      intro ω
      rw [C.expect_sub_const, hg]
      ring
    simp only [hz, integral_zero, add_zero]
    have : 0 ≤ ∫ ω, s.indicator (fun _ => (1 : ℝ)) ω * (g (ω (n + 1)) - g (ω n)) ^ 2 ∂μ :=
      integral_nonneg fun ω => mul_nonneg (by by_cases h : ω ∈ s <;> simp [h]) (sq_nonneg _)
    linarith
  have hnonneg : 0 ≤ f := fun j ω => sq_nonneg _
  set ε : ℝ≥0 := ⟨r ^ 2, by positivity⟩
  set A := {ω : ℕ → S | (ε : ℝ) ≤ (range (K + 1)).sup' nonempty_range_add_one fun k => f k ω}
  have hmax := maximal_ineq hsub hnonneg (ε := ε) K
  have hAm : MeasurableSet A := by
    exact measurableSet_le measurable_const (Finset.measurable_range_sup'' fun k _ =>
      (hsub.stronglyMeasurable k).measurable.le (𝒢.le k))
  have hI0 : 0 ≤ ∫ ω in A, f K ω ∂μ := setIntegral_nonneg hAm fun ω _ => hnonneg K ω
  have hreal : r ^ 2 * μ.real A ≤ ∫ ω in A, f K ω ∂μ := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmax
    rwa [ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_ofReal hI0] at this
  have hpt : ∀ ω, f K ω ≤ incr g a K ω ^ 4 / (2 * r ^ 2) + r ^ 2 / 2 := by
    intro ω
    have hr2 : 0 < r ^ 2 := by positivity
    rw [div_add_div _ _ (by positivity) two_ne_zero, le_div_iff₀ (by positivity)]
    simp only [f]
    nlinarith [sq_nonneg (incr g a K ω ^ 2 - r ^ 2)]
  have i4 : Integrable (fun ω => incr g a K ω ^ 4) μ :=
    C.integrable_three x (fun ya yn _ => (g yn - g ya) ^ 4) a (a + K) 0
  have hbound : ∫ ω in A, f K ω ∂μ ≤
      (∫ ω, incr g a K ω ^ 4 ∂μ) / (2 * r ^ 2) + r ^ 2 / 2 * μ.real A := by
    calc ∫ ω in A, f K ω ∂μ
        ≤ ∫ ω in A, (incr g a K ω ^ 4 / (2 * r ^ 2) + r ^ 2 / 2) ∂μ :=
          setIntegral_mono (hint K).integrableOn
            ((i4.div_const _).add (integrable_const _)).integrableOn hpt
      _ = (∫ ω in A, incr g a K ω ^ 4 ∂μ) / (2 * r ^ 2) + r ^ 2 / 2 * μ.real A := by
          rw [integral_add (i4.div_const _).integrableOn (integrable_const _),
            integral_div, setIntegral_const, smul_eq_mul]
          ring
      _ ≤ (∫ ω, incr g a K ω ^ 4 ∂μ) / (2 * r ^ 2) + r ^ 2 / 2 * μ.real A := by
          gcongr
          all_goals first
            | exact Measure.restrict_le_self
            | exact Eventually.of_forall fun ω => (by positivity : (0 : ℝ) ≤ incr g a K ω ^ 4)
  have hsubset : {ω | ∃ k ≤ K, r ≤ |incr g a k ω|} ⊆ A := by
    rintro ω ⟨k, hk, hkr⟩
    change (ε : ℝ) ≤ _
    refine le_trans ?_
      (Finset.le_sup' (fun k => f k ω) (Finset.mem_range.2 (Nat.lt_succ_of_le hk)))
    change r ^ 2 ≤ incr g a k ω ^ 2
    rw [← sq_abs (incr g a k ω)]
    exact pow_le_pow_left₀ hr.le hkr 2
  have hmono := measureReal_mono (μ := μ) hsubset
  have hr4 : 0 < r ^ 4 := by positivity
  rw [le_div_iff₀ hr4]
  have hr2 : 0 < r ^ 2 := by positivity
  have key : μ.real A * r ^ 4 ≤ ∫ ω, incr g a K ω ^ 4 ∂μ := by
    have h1 : r ^ 2 * μ.real A ≤
        (∫ ω, incr g a K ω ^ 4 ∂μ) / (2 * r ^ 2) + r ^ 2 / 2 * μ.real A := hreal.trans hbound
    have h2 : r ^ 2 / 2 * μ.real A ≤ (∫ ω, incr g a K ω ^ 4 ∂μ) / (2 * r ^ 2) := by linarith
    rw [le_div_iff₀ (by positivity)] at h2
    nlinarith
  nlinarith [measureReal_nonneg (μ := μ) (s := {ω | ∃ k ≤ K, r ≤ |incr g a k ω|})]

end Rhone.MarkovChain.FinChain
