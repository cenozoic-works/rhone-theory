/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Diffusion.PathTightness

/-!
# Tightness of rescaled paths of functions with small drift

Source: ethier_kurtz1986, ch. 3, sec. 7, sec. 8. -/
set_option linter.style.longLine false

@[expose] public section

namespace Rhone

open MeasureTheory ProbabilityTheory Finset Filter Set Analysis MarkovChain
open scoped NNReal ENNReal

namespace MarkovChain.FinChain

variable {S : Type*} [Fintype S] [MeasurableSpace S] [DiscreteMeasurableSpace S] (C : FinChain S)

omit [MeasurableSpace S] [DiscreteMeasurableSpace S] in
theorem expect_mem_Icc {g : S → ℝ} (hg : ∀ y, g y ∈ Icc (0 : ℝ) 1) (y : S) :
    C.expect g y ∈ Icc (0 : ℝ) 1 := by
  rw [expect_apply]
  constructor
  · exact sum_nonneg fun z _ => mul_nonneg (C.nonneg y z) (hg z).1
  · calc ∑ z, C.P y z * g z ≤ ∑ z, C.P y z * 1 :=
          sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (hg z).2 (C.nonneg y z)
      _ = 1 := by simp [C.row_sum]

omit [MeasurableSpace S] [DiscreteMeasurableSpace S] in
theorem expect_affine (F : S → ℝ) (a b : ℝ) (y : S) :
    C.expect (fun z => a * F z + b) y = a * C.expect F y + b := by
  simp only [expect_apply, mul_add, sum_add_distrib, ← sum_mul, C.row_sum, one_mul]
  rw [mul_sum]
  congr 1
  exact sum_congr rfl fun z _ => by ring

omit [MeasurableSpace S] [DiscreteMeasurableSpace S] in
theorem expect_mono {F F' : S → ℝ} (h : ∀ z, F z ≤ F' z) (y : S) :
    C.expect F y ≤ C.expect F' y := by
  rw [expect_apply, expect_apply]
  exact sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (h z) (C.nonneg y z)

omit [MeasurableSpace S] [DiscreteMeasurableSpace S] in
theorem expect_sq_sub_expect_le (g : S → ℝ) (y : S) :
    C.expect (fun z => (g z - C.expect g y) ^ 2) y ≤ C.expect (fun z => (g z - g y) ^ 2) y := by
  set m := C.expect g y with hm
  have h0 : ∑ z, C.P y z * (g z - m) = 0 := by
    simp only [mul_sub, sum_sub_distrib, ← sum_mul, C.row_sum, one_mul]
    rw [hm, expect_apply, sub_self]
  have e : ∀ z, C.P y z * (g z - g y) ^ 2 = C.P y z * (g z - m) ^ 2 +
      C.P y z * (m - g y) ^ 2 + 2 * (m - g y) * (C.P y z * (g z - m)) := fun z => by ring
  rw [expect_apply, expect_apply]
  simp only [e, sum_add_distrib]
  rw [← mul_sum, h0, ← sum_mul, C.row_sum]
  nlinarith [sq_nonneg (m - g y)]

omit [MeasurableSpace S] [DiscreteMeasurableSpace S] in
theorem expect_pow_four_sub_expect_le (g : S → ℝ) (y : S) {β : ℝ}
    (hβ : |C.expect g y - g y| ≤ β) :
    C.expect (fun z => (g z - C.expect g y) ^ 4) y ≤
      8 * C.expect (fun z => (g z - g y) ^ 4) y + 8 * β ^ 4 := by
  set m := C.expect g y with hm
  have hb4 : (m - g y) ^ 4 ≤ β ^ 4 := by
    have h1 : (m - g y) ^ 4 = |m - g y| ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
    rw [h1]
    exact pow_le_pow_left₀ (abs_nonneg _) hβ 4
  have hpt : ∀ z, (g z - m) ^ 4 ≤ 8 * (g z - g y) ^ 4 + 8 * β ^ 4 := by
    intro z
    have key : (g z - m) ^ 4 ≤ 8 * (g z - g y) ^ 4 + 8 * (m - g y) ^ 4 := by
      nlinarith [sq_nonneg ((g z - g y) + (m - g y)), sq_nonneg ((g z - g y) - (m - g y)),
        sq_nonneg ((g z - g y) ^ 2 - (m - g y) ^ 2), sq_nonneg (g z - g y), sq_nonneg (m - g y),
        mul_nonneg (sq_nonneg (g z - g y)) (sq_nonneg (m - g y))]
    linarith
  calc C.expect (fun z => (g z - m) ^ 4) y
      ≤ C.expect (fun z => 8 * (g z - g y) ^ 4 + 8 * β ^ 4) y := C.expect_mono hpt y
    _ = 8 * C.expect (fun z => (g z - g y) ^ 4) y + 8 * β ^ 4 := C.expect_affine _ _ _ y

def compIncr (g : S → ℝ) (a k : ℕ) (ω : ℕ → S) : ℝ :=
  ∑ l ∈ range k, (g (ω (a + l + 1)) - C.expect g (ω (a + l)))

omit [MeasurableSpace S] [DiscreteMeasurableSpace S] in
theorem compIncr_succ (g : S → ℝ) (a k : ℕ) (ω : ℕ → S) :
    C.compIncr g a (k + 1) ω =
      C.compIncr g a k ω + (g (ω (a + k + 1)) - C.expect g (ω (a + k))) := by
  simp only [compIncr, sum_range_succ]

omit [MeasurableSpace S] [DiscreteMeasurableSpace S] in
theorem incr_eq_compIncr_add (g : S → ℝ) (a k : ℕ) (ω : ℕ → S) :
    incr g a k ω = C.compIncr g a k ω +
      ∑ l ∈ range k, (C.expect g (ω (a + l)) - g (ω (a + l))) := by
  induction k with
  | zero => simp [incr, compIncr]
  | succ k ih =>
    rw [incr_succ, compIncr_succ, sum_range_succ, ih]
    ring

omit [MeasurableSpace S] [DiscreteMeasurableSpace S] in
theorem abs_compIncr_le {g : S → ℝ} (hg : ∀ y, g y ∈ Icc (0 : ℝ) 1) (a k : ℕ) (ω : ℕ → S) :
    |C.compIncr g a k ω| ≤ k := by
  unfold compIncr
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ l ∈ range k, |g (ω (a + l + 1)) - C.expect g (ω (a + l))|
      ≤ ∑ _l ∈ range k, (1 : ℝ) := sum_le_sum fun l _ => by
        have h1 := hg (ω (a + l + 1))
        have h2 := C.expect_mem_Icc hg (ω (a + l))
        rw [abs_le]
        constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    _ = k := by simp

theorem stronglyMeasurable_compIncr (g : S → ℝ) (a k : ℕ) :
    StronglyMeasurable[Filtration.piLE (X := fun _ : ℕ => S) (a + k)] (C.compIncr g a k) := by
  unfold compIncr
  refine Finset.stronglyMeasurable_fun_sum _ fun l hl => ?_
  have hl' : a + l + 1 ≤ a + k := by
    have := Finset.mem_range.1 hl
    omega
  exact (stronglyMeasurable_two (S := S) (fun y z => g z - C.expect g y)
    (Nat.le_succ (a + l))).mono ((Filtration.piLE (X := fun _ : ℕ => S)).mono hl')

theorem integrable_of_piLE (x : S) {n : ℕ} {F : (ℕ → S) → ℝ}
    (hF : StronglyMeasurable[Filtration.piLE (X := fun _ : ℕ => S) n] F) {B : ℝ}
    (hB : ∀ ω, |F ω| ≤ B) : Integrable F (C.pathLaw x) :=
  Integrable.of_bound (hF.mono (Filtration.piLE.le n)).aestronglyMeasurable B
    (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hB ω)

theorem integral_mul_compStep (x : S) (n : ℕ) (g : S → ℝ) {h : (ℕ → S) → ℝ}
    (hh : StronglyMeasurable[Filtration.piLE (X := fun _ : ℕ => S) n] h) {B : ℝ}
    (hB : ∀ ω, |h ω| ≤ B) :
    ∫ ω, h ω * (g (ω (n + 1)) - C.expect g (ω n)) ∂C.pathLaw x = 0 := by
  rw [C.integral_mul_eval_succ_two x n (fun y z => g z - C.expect g y) hh hB]
  simp [C.expect_sub_const]

theorem integrable_compIncr_pow_mul {g : S → ℝ} (hg : ∀ y, g y ∈ Icc (0 : ℝ) 1) (x : S)
    (a k n p q : ℕ) (hn : a + k ≤ n + 1) :
    Integrable (fun ω => C.compIncr g a k ω ^ p * (g (ω (n + 1)) - C.expect g (ω n)) ^ q)
      (C.pathLaw x) := by
  refine C.integrable_of_piLE x (n := n + 1) ?_ (B := (k : ℝ) ^ p) fun ω => ?_
  · exact (((C.stronglyMeasurable_compIncr g a k).mono
      ((Filtration.piLE (X := fun _ : ℕ => S)).mono hn)).pow p).mul
      ((stronglyMeasurable_two (S := S) (fun y z => g z - C.expect g y) (Nat.le_succ n)).pow q)
  · have h1 := C.abs_compIncr_le hg a k ω
    have h2 : |g (ω (n + 1)) - C.expect g (ω n)| ≤ 1 := by
      have h3 := hg (ω (n + 1))
      have h4 := C.expect_mem_Icc hg (ω n)
      rw [abs_le]
      constructor <;> linarith [h3.1, h3.2, h4.1, h4.2]
    rw [abs_mul, abs_pow, abs_pow]
    calc |C.compIncr g a k ω| ^ p * |g (ω (n + 1)) - C.expect g (ω n)| ^ q
        ≤ (k : ℝ) ^ p * 1 := mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) h1 p)
          (pow_le_one₀ (abs_nonneg _) h2) (by positivity) (by positivity)
      _ = (k : ℝ) ^ p := mul_one _

theorem integral_compIncr_sq_le {g : S → ℝ} (hg : ∀ y, g y ∈ Icc (0 : ℝ) 1) {v : ℝ}
    (hv : ∀ y, C.expect (fun z => (g z - C.expect g y) ^ 2) y ≤ v) (x : S) (a k : ℕ) :
    ∫ ω, C.compIncr g a k ω ^ 2 ∂C.pathLaw x ≤ k * v := by
  induction k with
  | zero => simp [compIncr]
  | succ k ih =>
    have e : ∀ ω : ℕ → S, C.compIncr g a (k + 1) ω ^ 2 = C.compIncr g a k ω ^ 2 +
        2 * (C.compIncr g a k ω * (g (ω (a + k + 1)) - C.expect g (ω (a + k)))) +
        (g (ω (a + k + 1)) - C.expect g (ω (a + k))) ^ 2 := by
      intro ω
      rw [compIncr_succ]
      ring
    have hn : a + k ≤ a + k + 1 := Nat.le_succ _
    have i1 : Integrable (fun ω => C.compIncr g a k ω ^ 2) (C.pathLaw x) := by
      simpa using C.integrable_compIncr_pow_mul hg x a k (a + k) 2 0 hn
    have i2 : Integrable (fun ω => C.compIncr g a k ω *
        (g (ω (a + k + 1)) - C.expect g (ω (a + k)))) (C.pathLaw x) := by
      simpa using C.integrable_compIncr_pow_mul hg x a k (a + k) 1 1 hn
    have i3 : Integrable (fun ω => (g (ω (a + k + 1)) - C.expect g (ω (a + k))) ^ 2)
        (C.pathLaw x) := by
      simpa using C.integrable_compIncr_pow_mul hg x a k (a + k) 0 2 hn
    simp_rw [e]
    rw [integral_add (i1.fun_add (i2.const_mul 2)) i3, integral_add i1 (i2.const_mul 2),
      integral_const_mul]
    have h1 := C.integral_mul_compStep x (a + k) g (h := fun ω => C.compIncr g a k ω)
      (C.stronglyMeasurable_compIncr g a k) (C.abs_compIncr_le hg a k)
    have h2 := C.integral_mul_eval_succ_two x (a + k) (fun y z => (g z - C.expect g y) ^ 2)
      (h := fun _ => 1) stronglyMeasurable_const (B := 1) (fun ω => by simp)
    simp only [one_mul] at h2
    have hle : ∫ ω, C.expect (fun z => (g z - C.expect g (ω (a + k))) ^ 2) (ω (a + k))
        ∂C.pathLaw x ≤ v := by
      calc ∫ ω, C.expect (fun z => (g z - C.expect g (ω (a + k))) ^ 2) (ω (a + k)) ∂C.pathLaw x
          ≤ ∫ _ω, v ∂C.pathLaw x := integral_mono
              (C.integrable_three x
                (fun _ yn _ => C.expect (fun z => (g z - C.expect g yn) ^ 2) yn) 0 (a + k) 0)
              (integrable_const v) fun ω => hv (ω (a + k))
        _ = v := by simp
    rw [h1, h2]
    push_cast
    linarith

omit [MeasurableSpace S] [DiscreteMeasurableSpace S] in
theorem expect_pow_sub_nonneg (g : S → ℝ) (m : ℝ) (p : ℕ) (y : S) :
    0 ≤ C.expect (fun z => (g z - m) ^ (2 * p)) y := by
  rw [expect_apply]
  exact sum_nonneg fun z _ => mul_nonneg (C.nonneg y z) (by rw [pow_mul]; positivity)

theorem integral_compIncr_pow_four_le {g : S → ℝ} (hg : ∀ y, g y ∈ Icc (0 : ℝ) 1) {v q : ℝ}
    (hv : ∀ y, C.expect (fun z => (g z - C.expect g y) ^ 2) y ≤ v)
    (hq : ∀ y, C.expect (fun z => (g z - C.expect g y) ^ 4) y ≤ q) (x : S) (a k : ℕ) :
    ∫ ω, C.compIncr g a k ω ^ 4 ∂C.pathLaw x ≤ 4 * (k : ℝ) ^ 2 * v ^ 2 + 3 * k * q := by
  have hv0 : 0 ≤ v := (C.expect_pow_sub_nonneg g (C.expect g x) 1 x).trans (hv x)
  induction k with
  | zero => simp [compIncr]
  | succ k ih =>
    have hsq := C.integral_compIncr_sq_le hg hv x a k
    have hn : a + k ≤ a + k + 1 := Nat.le_succ _
    have hpt : ∀ ω : ℕ → S, C.compIncr g a (k + 1) ω ^ 4 ≤ C.compIncr g a k ω ^ 4 +
        4 * (C.compIncr g a k ω ^ 3 * (g (ω (a + k + 1)) - C.expect g (ω (a + k)))) +
        8 * (C.compIncr g a k ω ^ 2 * (g (ω (a + k + 1)) - C.expect g (ω (a + k))) ^ 2) +
        3 * (g (ω (a + k + 1)) - C.expect g (ω (a + k))) ^ 4 := by
      intro ω
      rw [compIncr_succ]
      set s := C.compIncr g a k ω
      set d := g (ω (a + k + 1)) - C.expect g (ω (a + k))
      nlinarith [mul_nonneg (sq_nonneg d) (sq_nonneg (s - d))]
    have i1 : Integrable (fun ω => C.compIncr g a k ω ^ 4) (C.pathLaw x) := by
      simpa using C.integrable_compIncr_pow_mul hg x a k (a + k) 4 0 hn
    have i1' : Integrable (fun ω => C.compIncr g a k ω ^ 2) (C.pathLaw x) := by
      simpa using C.integrable_compIncr_pow_mul hg x a k (a + k) 2 0 hn
    have i2 := C.integrable_compIncr_pow_mul hg x a k (a + k) 3 1 hn
    simp only [pow_one] at i2
    have i3 := C.integrable_compIncr_pow_mul hg x a k (a + k) 2 2 hn
    have i4 : Integrable (fun ω => (g (ω (a + k + 1)) - C.expect g (ω (a + k))) ^ 4)
        (C.pathLaw x) := by
      simpa using C.integrable_compIncr_pow_mul hg x a k (a + k) 0 4 hn
    have i5 : Integrable (fun ω => C.compIncr g a (k + 1) ω ^ 4) (C.pathLaw x) := by
      simpa using C.integrable_compIncr_pow_mul hg x a (k + 1) (a + k) 4 0 (by omega)
    have i12 := i1.fun_add (i2.const_mul 4)
    have i123 := i12.fun_add (i3.const_mul 8)
    have hmono := integral_mono i5 (i123.fun_add (i4.const_mul 3)) hpt
    rw [integral_add i123 (i4.const_mul 3), integral_add i12 (i3.const_mul 8),
      integral_add i1 (i2.const_mul 4), integral_const_mul, integral_const_mul,
      integral_const_mul] at hmono
    have h2 := C.integral_mul_compStep x (a + k) g (h := fun ω => C.compIncr g a k ω ^ 3)
      ((C.stronglyMeasurable_compIncr g a k).pow 3) (B := (k : ℝ) ^ 3) (fun ω => by
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (C.abs_compIncr_le hg a k ω) 3)
    have h3 := C.integral_mul_eval_succ_two x (a + k) (fun y z => (g z - C.expect g y) ^ 2)
      (h := fun ω => C.compIncr g a k ω ^ 2) ((C.stronglyMeasurable_compIncr g a k).pow 2)
      (B := (k : ℝ) ^ 2) (fun ω => by
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (C.abs_compIncr_le hg a k ω) 2)
    have h4 := C.integral_mul_eval_succ_two x (a + k) (fun y z => (g z - C.expect g y) ^ 4)
      (h := fun _ => 1) stronglyMeasurable_const (B := 1) (fun ω => by simp)
    simp only [one_mul] at h4
    have e3 : ∫ ω, C.compIncr g a k ω ^ 2 * (g (ω (a + k + 1)) - C.expect g (ω (a + k))) ^ 2
        ∂C.pathLaw x ≤ v * (k * v) := by
      rw [h3]
      calc ∫ ω, C.compIncr g a k ω ^ 2 *
            C.expect (fun z => (g z - C.expect g (ω (a + k))) ^ 2) (ω (a + k)) ∂C.pathLaw x
          ≤ ∫ ω, v * C.compIncr g a k ω ^ 2 ∂C.pathLaw x := by
            refine integral_mono_of_nonneg (Eventually.of_forall fun ω => ?_)
              (i1'.const_mul v) (Eventually.of_forall fun ω => ?_)
            · exact mul_nonneg (sq_nonneg _) (by
                simpa using C.expect_pow_sub_nonneg g (C.expect g (ω (a + k))) 1 (ω (a + k)))
            · change C.compIncr g a k ω ^ 2 *
                C.expect (fun z => (g z - C.expect g (ω (a + k))) ^ 2) (ω (a + k)) ≤
                v * C.compIncr g a k ω ^ 2
              have := hv (ω (a + k))
              have h0 := sq_nonneg (C.compIncr g a k ω)
              nlinarith
        _ = v * ∫ ω, C.compIncr g a k ω ^ 2 ∂C.pathLaw x := integral_const_mul _ _
        _ ≤ v * (k * v) := by gcongr
    have e4 : ∫ ω, (g (ω (a + k + 1)) - C.expect g (ω (a + k))) ^ 4 ∂C.pathLaw x ≤ q := by
      rw [h4]
      calc ∫ ω, C.expect (fun z => (g z - C.expect g (ω (a + k))) ^ 4) (ω (a + k)) ∂C.pathLaw x
          ≤ ∫ _ω, q ∂C.pathLaw x := integral_mono
              (C.integrable_three x
                (fun _ yn _ => C.expect (fun z => (g z - C.expect g yn) ^ 4) yn) 0 (a + k) 0)
              (integrable_const q) fun ω => hq (ω (a + k))
        _ = q := by simp
    rw [h2] at hmono
    push_cast
    nlinarith [sq_nonneg v]

theorem measureReal_exists_abs_compIncr_ge_le {g : S → ℝ} (hg : ∀ y, g y ∈ Icc (0 : ℝ) 1)
    (x : S) (a K : ℕ) {r : ℝ} (hr : 0 < r) :
    (C.pathLaw x).real {ω | ∃ k ≤ K, r ≤ |C.compIncr g a k ω|} ≤
      (∫ ω, C.compIncr g a K ω ^ 4 ∂C.pathLaw x) / r ^ 4 := by
  classical
  set μ := C.pathLaw x
  let 𝒢 : Filtration ℕ (inferInstance : MeasurableSpace (ℕ → S)) :=
    ⟨fun j => Filtration.piLE (X := fun _ : ℕ => S) (a + j),
      fun i j hij => (Filtration.piLE (X := fun _ : ℕ => S)).mono (Nat.add_le_add_left hij a),
      fun j => Filtration.piLE.le _⟩
  let f : ℕ → (ℕ → S) → ℝ := fun j ω => C.compIncr g a j ω ^ 2
  have hS : ∀ j, StronglyMeasurable[𝒢 j] (fun ω : ℕ → S => C.compIncr g a j ω) := fun j =>
    C.stronglyMeasurable_compIncr g a j
  have hint : ∀ j, Integrable (f j) μ := fun j => by
    simpa using C.integrable_compIncr_pow_mul hg x a j (a + j) 2 0 (Nat.le_succ _)
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
    have e : ∀ ω : ℕ → S, s.indicator (fun _ => (1 : ℝ)) ω * f (j + 1) ω =
        s.indicator (fun _ => (1 : ℝ)) ω * f j ω +
        (s.indicator (fun _ => (1 : ℝ)) ω * (2 * C.compIncr g a j ω)) *
          (g (ω (a + j + 1)) - C.expect g (ω (a + j))) +
        s.indicator (fun _ => (1 : ℝ)) ω * (g (ω (a + j + 1)) - C.expect g (ω (a + j))) ^ 2 := by
      intro ω
      simp only [f]
      rw [compIncr_succ]
      ring
    have hIi : ∀ F : (ℕ → S) → ℝ, Integrable F μ →
        Integrable (fun ω => s.indicator (fun _ => (1 : ℝ)) ω * F ω) μ := by
      intro F hF
      have : (fun ω => s.indicator (fun _ => (1 : ℝ)) ω * F ω) = s.indicator F := by
        funext ω
        by_cases h : ω ∈ s <;> simp [h]
      rw [this]
      exact hF.indicator hsm
    have iD : Integrable (fun ω : ℕ → S => C.compIncr g a j ω *
        (g (ω (a + j + 1)) - C.expect g (ω (a + j)))) μ := by
      simpa using C.integrable_compIncr_pow_mul hg x a j (a + j) 1 1 (Nat.le_succ _)
    have iE : Integrable (fun ω : ℕ → S => (g (ω (a + j + 1)) - C.expect g (ω (a + j))) ^ 2)
        μ := by
      simpa using C.integrable_compIncr_pow_mul hg x a j (a + j) 0 2 (Nat.le_succ _)
    have jA : Integrable (fun ω => s.indicator (fun _ => (1 : ℝ)) ω * f j ω) μ :=
      hIi _ (hint j)
    have jB : Integrable (fun ω => (s.indicator (fun _ => (1 : ℝ)) ω * (2 * C.compIncr g a j ω)) *
        (g (ω (a + j + 1)) - C.expect g (ω (a + j)))) μ :=
      (hIi _ (iD.const_mul 2)).congr (Eventually.of_forall fun ω => by ring)
    have jC : Integrable (fun ω => s.indicator (fun _ => (1 : ℝ)) ω *
        (g (ω (a + j + 1)) - C.expect g (ω (a + j))) ^ 2) μ := hIi _ iE
    simp_rw [e]
    rw [integral_add (jA.fun_add jB) jC, integral_add jA jB]
    have h1 := C.integral_mul_compStep x (a + j) g
      (h := fun ω => s.indicator (fun _ => (1 : ℝ)) ω * (2 * C.compIncr g a j ω))
      (hIm.mul ((hS j).const_mul 2)) (B := 2 * j) (fun ω => by
        rw [abs_mul, abs_mul, abs_two]
        have := C.abs_compIncr_le hg a j ω
        have := hIb ω
        have := abs_nonneg (s.indicator (fun _ : ℕ → S => (1 : ℝ)) ω)
        have := abs_nonneg (C.compIncr g a j ω)
        nlinarith)
    rw [h1, add_zero]
    have : 0 ≤ ∫ ω, s.indicator (fun _ => (1 : ℝ)) ω *
        (g (ω (a + j + 1)) - C.expect g (ω (a + j))) ^ 2 ∂μ :=
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
  have hpt : ∀ ω, f K ω ≤ C.compIncr g a K ω ^ 4 / (2 * r ^ 2) + r ^ 2 / 2 := by
    intro ω
    have hr2 : 0 < r ^ 2 := by positivity
    rw [div_add_div _ _ (by positivity) two_ne_zero, le_div_iff₀ (by positivity)]
    simp only [f]
    nlinarith [sq_nonneg (C.compIncr g a K ω ^ 2 - r ^ 2)]
  have i4 : Integrable (fun ω => C.compIncr g a K ω ^ 4) μ := by
    simpa using C.integrable_compIncr_pow_mul hg x a K (a + K) 4 0 (Nat.le_succ _)
  have hbound : ∫ ω in A, f K ω ∂μ ≤
      (∫ ω, C.compIncr g a K ω ^ 4 ∂μ) / (2 * r ^ 2) + r ^ 2 / 2 * μ.real A := by
    calc ∫ ω in A, f K ω ∂μ
        ≤ ∫ ω in A, (C.compIncr g a K ω ^ 4 / (2 * r ^ 2) + r ^ 2 / 2) ∂μ :=
          setIntegral_mono (hint K).integrableOn
            ((i4.div_const _).add (integrable_const _)).integrableOn hpt
      _ = (∫ ω in A, C.compIncr g a K ω ^ 4 ∂μ) / (2 * r ^ 2) + r ^ 2 / 2 * μ.real A := by
          rw [integral_add (i4.div_const _).integrableOn (integrable_const _),
            integral_div, setIntegral_const, smul_eq_mul]
          ring
      _ ≤ (∫ ω, C.compIncr g a K ω ^ 4 ∂μ) / (2 * r ^ 2) + r ^ 2 / 2 * μ.real A := by
          gcongr
          all_goals first
            | exact Measure.restrict_le_self
            | exact Eventually.of_forall fun ω =>
                (by positivity : (0 : ℝ) ≤ C.compIncr g a K ω ^ 4)
  have hsubset : {ω | ∃ k ≤ K, r ≤ |C.compIncr g a k ω|} ⊆ A := by
    rintro ω ⟨k, hk, hkr⟩
    change (ε : ℝ) ≤ _
    refine le_trans ?_
      (Finset.le_sup' (fun k => f k ω) (Finset.mem_range.2 (Nat.lt_succ_of_le hk)))
    change r ^ 2 ≤ C.compIncr g a k ω ^ 2
    rw [← sq_abs (C.compIncr g a k ω)]
    exact pow_le_pow_left₀ hr.le hkr 2
  have hmono := measureReal_mono (μ := μ) hsubset
  have hr4 : 0 < r ^ 4 := by positivity
  rw [le_div_iff₀ hr4]
  have hr2 : 0 < r ^ 2 := by positivity
  have key : μ.real A * r ^ 4 ≤ ∫ ω, C.compIncr g a K ω ^ 4 ∂μ := by
    have h1 : r ^ 2 * μ.real A ≤
        (∫ ω, C.compIncr g a K ω ^ 4 ∂μ) / (2 * r ^ 2) + r ^ 2 / 2 * μ.real A :=
      hreal.trans hbound
    have h2 : r ^ 2 / 2 * μ.real A ≤ (∫ ω, C.compIncr g a K ω ^ 4 ∂μ) / (2 * r ^ 2) := by
      linarith
    rw [le_div_iff₀ (by positivity)] at h2
    nlinarith
  nlinarith [measureReal_nonneg (μ := μ) (s := {ω | ∃ k ≤ K, r ≤ |C.compIncr g a k ω|})]

theorem measureReal_not_block_le_of_drift {g : S → ℝ} (hg : ∀ y, g y ∈ Icc (0 : ℝ) 1)
    {v q β : ℝ} (hβ : ∀ y, |C.expect g y - g y| ≤ β)
    (hv : ∀ y, C.expect (fun z => (g z - C.expect g y) ^ 2) y ≤ v)
    (hq : ∀ y, C.expect (fun z => (g z - C.expect g y) ^ 4) y ≤ q) (x : S) (b L : ℕ) {ε : ℝ}
    (hε : 0 < ε) (hbβ : b * β ≤ ε / 2) :
    (C.pathLaw x).real {ω | ¬ ∀ i ≤ L, ∀ k ≤ b, |g (ω (i * b + k)) - g (ω (i * b))| ≤ ε} ≤
      (L + 1) * ((4 * (b : ℝ) ^ 2 * v ^ 2 + 3 * b * q) / (ε / 2) ^ 4) := by
  have hβ0 : 0 ≤ β := (abs_nonneg _).trans (hβ x)
  have hsub : {ω : ℕ → S | ¬ ∀ i ≤ L, ∀ k ≤ b, |g (ω (i * b + k)) - g (ω (i * b))| ≤ ε} ⊆
      ⋃ i ∈ Finset.range (L + 1), {ω | ∃ k ≤ b, ε / 2 ≤ |C.compIncr g (i * b) k ω|} := by
    intro ω hω
    simp only [mem_ofPred_eq, not_forall, not_le] at hω
    obtain ⟨i, hi, k, hk, hlt⟩ := hω
    simp only [mem_iUnion, Finset.mem_range, mem_ofPred_eq]
    refine ⟨i, Nat.lt_succ_of_le hi, k, hk, ?_⟩
    change ε < |incr g (i * b) k ω| at hlt
    have he := C.incr_eq_compIncr_add g (i * b) k ω
    set D := ∑ l ∈ range k, (C.expect g (ω (i * b + l)) - g (ω (i * b + l))) with hD_def
    have hD : |D| ≤ ε / 2 := by
      refine (abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ l ∈ range k, |C.expect g (ω (i * b + l)) - g (ω (i * b + l))|
          ≤ ∑ _l ∈ range k, β := sum_le_sum fun l _ => hβ _
        _ = k * β := by simp
        _ ≤ b * β := mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hβ0
        _ ≤ ε / 2 := hbβ
    have hM : C.compIncr g (i * b) k ω = incr g (i * b) k ω - D := by rw [he]; ring
    rw [hM]
    have := abs_sub_abs_le_abs_sub (incr g (i * b) k ω) D
    linarith
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans
    ((measureReal_biUnion_finset_le _ _).trans ?_)
  have hone : ∀ i ∈ Finset.range (L + 1),
      (C.pathLaw x).real {ω | ∃ k ≤ b, ε / 2 ≤ |C.compIncr g (i * b) k ω|} ≤
        (4 * (b : ℝ) ^ 2 * v ^ 2 + 3 * b * q) / (ε / 2) ^ 4 := by
    intro i _
    refine (C.measureReal_exists_abs_compIncr_ge_le hg x (i * b) b (half_pos hε)).trans ?_
    gcongr
    exact C.integral_compIncr_pow_four_le hg hv hq x (i * b) b
  refine (Finset.sum_le_sum hone).trans ?_
  simp

end MarkovChain.FinChain

variable {Sₙ : ℕ → Type*} [∀ n, Fintype (Sₙ n)] [∀ n, MeasurableSpace (Sₙ n)]
  [∀ n, DiscreteMeasurableSpace (Sₙ n)]

theorem Diffusion.drift_block_le {t d0 c ε : ℝ} {b : ℕ} (ht : 0 < t)
    (hblt : (b : ℝ) < t * d0 + 1) (htd : 2 ≤ t * d0) (hd0ε : d0 ≤ ε / (4 * (|c| + 1)))
    (hc0 : 0 ≤ c / t) (hε : 0 < ε) : (b : ℝ) * (c / t) ≤ ε / 2 := by
  have hb2t : (b : ℝ) ≤ 2 * (t * d0) := by linarith
  have hc : 0 ≤ c := by
    rcases div_nonneg_iff.1 hc0 with h | h
    · exact h.1
    · linarith [h.2]
  calc (b : ℝ) * (c / t) ≤ 2 * (t * d0) * (c / t) := by gcongr
    _ = 2 * d0 * c := by field_simp
    _ ≤ 2 * (ε / (4 * (|c| + 1))) * c := by gcongr
    _ ≤ ε / 2 := by
        rw [abs_of_nonneg hc]
        have h1 : 2 * (ε / (4 * (c + 1))) * c = ε / 2 * (c / (c + 1)) := by
          field_simp
          ring
        have h2 : c / (c + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
        rw [h1]
        exact mul_le_of_le_one_right (by positivity) h2

theorem Diffusion.drift_tail_le {A P t c e : ℝ} (hA : 0 < A) (hP : 0 < P) (ht1 : 1 ≤ t)
    (htT : 96 * A * (c ^ 4 + 1) / P ≤ t) (hen : e < P / (96 * A)) :
    3 * A * (8 * e + 8 * c ^ 4 / t ^ 3) ≤ P / 2 := by
  have ht : 0 < t := by linarith
  have h1 : 96 * A * (c ^ 4 + 1) ≤ P * t := by
    have := (div_le_iff₀ hP).1 htT
    linarith
  have ht3 : t ≤ t ^ 3 := by
    nlinarith [mul_nonneg (mul_nonneg ht.le (sub_nonneg.2 ht1)) (by linarith : 0 ≤ t + 1)]
  have h3 : 96 * A * c ^ 4 ≤ P * t ^ 3 := by
    have := mul_le_mul_of_nonneg_left ht3 hP.le
    have : 0 ≤ 96 * A := by positivity
    linarith
  have h4 : 3 * A * (8 * c ^ 4 / t ^ 3) ≤ P / 4 := by
    rw [show 3 * A * (8 * c ^ 4 / t ^ 3) = 24 * A * c ^ 4 / t ^ 3 by ring,
      div_le_iff₀ (by positivity)]
    linarith
  have h5 : 24 * A * e ≤ P / 4 := by
    have := (lt_div_iff₀ (by positivity : (0 : ℝ) < 96 * A)).1 hen
    linarith
  have : 3 * A * (8 * e + 8 * c ^ 4 / t ^ 3) = 24 * A * e + 3 * A * (8 * c ^ 4 / t ^ 3) := by
    ring
  linarith

theorem Diffusion.exists_modulusAt_of_drift (C : ∀ n, FinChain (Sₙ n)) (y : ∀ n, Sₙ n → ℝ)
    (τ : ℕ → ℝ) (hy01 : ∀ n z, y n z ∈ Icc (0 : ℝ) 1) (hτ : Tendsto τ atTop atTop) (c : ℝ)
    (e : ℕ → ℝ) (hβ : ∀ᶠ n in atTop, ∀ z, |(C n).expect (y n) z - y n z| ≤ c / τ n)
    (hv : ∀ᶠ n in atTop, ∀ z, (C n).expect (fun w => (y n w - y n z) ^ 2) z ≤ c / τ n)
    (hq : ∀ᶠ n in atTop, ∀ z, (C n).expect (fun w => (y n w - y n z) ^ 4) z ≤ e n / τ n)
    (he : Tendsto e atTop (nhds 0)) (j : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ d > 0, ∀ n (x : Sₙ n), (C n).pathLaw x
      {ω | ¬ ModulusAt j d (Diffusion.rescaledPath (τ n) fun m => y n (ω m))} ≤ ENNReal.ofReal ρ :=
          by
  set ε : ℝ := 1 / (5 * ((j : ℝ) + 1)) with hε_def
  have hj1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  have hε : 0 < ε := by positivity
  set K : ℝ := (ε / 2) ^ 4 with hK_def
  have hK : 0 < K := by positivity
  set A : ℝ := 2 * ((j : ℝ) + 1) + 4 with hA_def
  have hA : 0 < A := by positivity
  set d0 : ℝ := min (min 1 (ρ * K / (16 * A * (c ^ 2 + 1)))) (ε / (4 * (|c| + 1))) with hd0_def
  have hd0 : 0 < d0 := lt_min (lt_min one_pos (by positivity)) (by positivity)
  have hd01 : d0 ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
  have hd0ε : d0 ≤ ε / (4 * (|c| + 1)) := min_le_right _ _
  have hd0c : 8 * A * d0 * c ^ 2 ≤ ρ * K / 2 := by
    have h1 : d0 ≤ ρ * K / (16 * A * (c ^ 2 + 1)) := (min_le_left _ _).trans (min_le_right _ _)
    have h2 : 8 * A * d0 * c ^ 2 ≤ 8 * A * (ρ * K / (16 * A * (c ^ 2 + 1))) * c ^ 2 := by
      gcongr
    have h3 : 8 * A * (ρ * K / (16 * A * (c ^ 2 + 1))) * c ^ 2 =
        ρ * K / 2 * (c ^ 2 / (c ^ 2 + 1)) := by
      field_simp
      ring
    have h4 : c ^ 2 / (c ^ 2 + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    have h5 : 0 ≤ ρ * K / 2 := by positivity
    linarith [mul_le_of_le_one_right h5 h4]
  set T : ℝ := max (max 1 (2 / d0)) (96 * A * (c ^ 4 + 1) / (ρ * K)) with hT_def
  have hev := ((hβ.and hv).and hq).and ((hτ.eventually_ge_atTop T).and
    (he.eventually (gt_mem_nhds (show (0 : ℝ) < ρ * K / (96 * A) by positivity))))
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hev
  set M : ℝ := ∑ n ∈ Finset.range N0, |τ n| with hM_def
  have hM : 0 ≤ M := Finset.sum_nonneg fun _ _ => abs_nonneg _
  set d : ℝ := min d0 (1 / (((j : ℝ) + 1) * (M + 1))) with hd_def
  refine ⟨d, lt_min hd0 (by positivity), fun n x => ?_⟩
  rcases le_or_gt N0 n with hn | hn
  · obtain ⟨⟨⟨hβn, hvn⟩, hqn⟩, hτn, hen⟩ := hN0 n hn
    set t := τ n with ht_def
    have ht1 : 1 ≤ t := ((le_max_left _ _).trans (le_max_left _ _)).trans hτn
    have ht : 0 < t := by linarith
    have htd : 2 ≤ t * d0 := by
      have := (div_le_iff₀ hd0).1 (((le_max_right _ _).trans (le_max_left _ _)).trans hτn)
      linarith
    have htT : 96 * A * (c ^ 4 + 1) / (ρ * K) ≤ t := (le_max_right _ _).trans hτn
    set b : ℕ := ⌈t * d0⌉₊ with hb_def
    set L : ℕ := ⌈t * ((j : ℝ) + 1) / b⌉₊ with hL_def
    have hbge : t * d0 ≤ b := Nat.le_ceil _
    have hblt : (b : ℝ) < t * d0 + 1 := Nat.ceil_lt_add_one (by positivity)
    have hb2 : 2 ≤ b := by exact_mod_cast htd.trans hbge
    have hbpos : (0 : ℝ) < b := by linarith
    have hLge : t * ((j : ℝ) + 1) / b ≤ L := Nat.le_ceil _
    have hLlt : (L : ℝ) < t * ((j : ℝ) + 1) / b + 1 := Nat.ceil_lt_add_one (by positivity)
    have hLb_ge : t * ((j : ℝ) + 1) + 1 ≤ (((L + 1) * b : ℕ) : ℝ) := by
      have h1 := (div_le_iff₀ hbpos).1 hLge
      have h2 : (((L + 1) * b : ℕ) : ℝ) = (L : ℝ) * b + b := by push_cast; ring
      rw [h2]
      linarith
    have h5ε : 5 * ε ≤ 1 / ((j : ℝ) + 1) := by
      have h : 5 * ε = 1 / ((j : ℝ) + 1) := by
        rw [hε_def]
        field_simp
      exact h.le
    have hsub : {ω : ℕ → Sₙ n | ¬ ModulusAt j d (Diffusion.rescaledPath t fun m => y n (ω m))} ⊆
        {ω | ¬ ∀ i ≤ L, ∀ k ≤ b, |y n (ω (i * b + k)) - y n (ω (i * b))| ≤ ε} := by
      intro ω hω hblock
      exact hω ((Diffusion.modulusAt_rescaledPath_of_block ht.le hb2 hbge hLb_ge h5ε hblock).mono
        (min_le_left _ _))
    have hv' : ∀ z, (C n).expect (fun w => (y n w - (C n).expect (y n) z) ^ 2) z ≤ c / t :=
      fun z => ((C n).expect_sq_sub_expect_le (y n) z).trans (hvn z)
    have hq' : ∀ z, (C n).expect (fun w => (y n w - (C n).expect (y n) z) ^ 4) z ≤
        8 * (e n / t) + 8 * (c / t) ^ 4 := by
      intro z
      have := (C n).expect_pow_four_sub_expect_le (y n) z (hβn z)
      linarith [hqn z]
    have hbβ : (b : ℝ) * (c / t) ≤ ε / 2 :=
      Diffusion.drift_block_le ht hblt htd hd0ε ((abs_nonneg _).trans (hβn x)) hε
    have hprob := (C n).measureReal_not_block_le_of_drift (hy01 n) hβn hv' hq' x b L hε hbβ
    have hq0 : 0 ≤ 8 * (e n / t) + 8 * (c / t) ^ 4 := by
      have : 0 ≤ e n / t := by
        refine le_trans ?_ (hqn x)
        simpa using (C n).expect_pow_sub_nonneg (y n) (y n x) 2 x
      positivity
    have hct : t * (c / t) = c := by field_simp
    have het : t * (8 * (e n / t) + 8 * (c / t) ^ 4) = 8 * e n + 8 * c ^ 4 / t ^ 3 := by
      field_simp
    have i2 : 3 * A * (8 * e n + 8 * c ^ 4 / t ^ 3) ≤ ρ * K / 2 :=
      Diffusion.drift_tail_le hA (by positivity) ht1 htT hen
    have hbound := Diffusion.block_bound_le ht hd01 htd hbge hblt hLlt hA_def hq0 hct het hK hd0c i2
    calc (C n).pathLaw x {ω | ¬ ModulusAt j d (Diffusion.rescaledPath t fun m => y n (ω m))}
        ≤ (C n).pathLaw x
            {ω | ¬ ∀ i ≤ L, ∀ k ≤ b, |y n (ω (i * b + k)) - y n (ω (i * b))| ≤ ε} :=
          measure_mono hsub
      _ = ENNReal.ofReal (((C n).pathLaw x).real
            {ω | ¬ ∀ i ≤ L, ∀ k ≤ b, |y n (ω (i * b + k)) - y n (ω (i * b))| ≤ ε}) :=
          (ofReal_measureReal (measure_ne_top _ _)).symm
      _ ≤ ENNReal.ofReal ρ := ENNReal.ofReal_le_ofReal (hprob.trans hbound)
  · have hall : ∀ ω : ℕ → Sₙ n, ModulusAt j d (Diffusion.rescaledPath (τ n) fun m => y n (ω m)) :=
      by
      intro ω
      rcases le_or_gt (τ n) 0 with hτn | hτn
      · exact Diffusion.modulusAt_rescaledPath_of_nonpos _ hτn j d
      · refine Diffusion.modulusAt_rescaledPath_of_step (fun m => ?_) hτn.le ?_
        · have h1 := hy01 n (ω (m + 1))
          have h2 := hy01 n (ω m)
          rw [abs_le]
          constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
        · have hτM : τ n ≤ M := by
            have := Finset.single_le_sum (f := fun k => |τ k|) (fun _ _ => abs_nonneg _)
              (Finset.mem_range.2 hn)
            exact (le_abs_self _).trans this
          have hdle : d ≤ 1 / (((j : ℝ) + 1) * (M + 1)) := min_le_right _ _
          calc τ n * d ≤ τ n * (1 / (((j : ℝ) + 1) * (M + 1))) := by gcongr
            _ ≤ 1 / ((j : ℝ) + 1) := by
                rw [mul_one_div, div_le_div_iff₀ (by positivity) hj1]
                nlinarith
    have hempty : {ω : ℕ → Sₙ n | ¬ ModulusAt j d (Diffusion.rescaledPath (τ n) fun m => y n (ω m))} =
        ∅ := by
      ext ω
      simp [hall ω]
    rw [hempty, measure_empty]
    exact zero_le

theorem Diffusion.exists_unitModulus_of_drift (C : ∀ n, FinChain (Sₙ n)) (y : ∀ n, Sₙ n → ℝ)
    (τ : ℕ → ℝ) (hy01 : ∀ n z, y n z ∈ Icc (0 : ℝ) 1) (hτ : Tendsto τ atTop atTop) (c : ℝ)
    (e : ℕ → ℝ) (hβ : ∀ᶠ n in atTop, ∀ z, |(C n).expect (y n) z - y n z| ≤ c / τ n)
    (hv : ∀ᶠ n in atTop, ∀ z, (C n).expect (fun w => (y n w - y n z) ^ 2) z ≤ c / τ n)
    (hq : ∀ᶠ n in atTop, ∀ z, (C n).expect (fun w => (y n w - y n z) ^ 4) z ≤ e n / τ n)
    (he : Tendsto e atTop (nhds 0)) {η : ℝ≥0∞} (hη : η ≠ 0) :
    ∃ δ : ℕ → ℝ, (∀ j, 0 < δ j) ∧ ∀ n (x : Sₙ n), (C n).pathLaw x
      {ω | ¬ UnitModulus δ (Diffusion.rescaledPath (τ n) fun m => y n (ω m))} ≤ η := by
  obtain ⟨ρ, hρ, hρη⟩ := ENNReal.exists_pos_sum_of_countable hη ℕ
  have hj := fun j => Diffusion.exists_modulusAt_of_drift C y τ hy01 hτ c e hβ hv hq he j (hρ j)
  choose δ hδ hδn using hj
  refine ⟨δ, hδ, fun n x => ?_⟩
  have hsub : {ω : ℕ → Sₙ n | ¬ UnitModulus δ (Diffusion.rescaledPath (τ n) fun m => y n (ω m))} ⊆
      ⋃ j, {ω | ¬ ModulusAt j (δ j) (Diffusion.rescaledPath (τ n) fun m => y n (ω m))} := by
    intro ω hω
    simp only [mem_ofPred_eq, mem_iUnion]
    by_contra h
    push Not at h
    exact hω ⟨fun t => Diffusion.rescaledPath_mem_Icc (fun m => hy01 n (ω m)) _ t, h⟩
  calc (C n).pathLaw x {ω | ¬ UnitModulus δ (Diffusion.rescaledPath (τ n) fun m => y n (ω m))}
      ≤ ∑' j, (C n).pathLaw x
          {ω | ¬ ModulusAt j (δ j) (Diffusion.rescaledPath (τ n) fun m => y n (ω m))} :=
        (measure_mono hsub).trans (measure_iUnion_le _)
    _ ≤ ∑' j, (ρ j : ℝ≥0∞) := by
        exact ENNReal.tsum_le_tsum fun j =>
          (hδn j n x).trans (le_of_eq ENNReal.ofReal_coe_nnreal)
    _ ≤ η := hρη.le

end Rhone
