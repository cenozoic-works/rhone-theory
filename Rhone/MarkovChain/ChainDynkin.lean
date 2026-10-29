/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.ChainIncrements

/-! # Dynkin's formula for a finite chain against a function of the past -/

@[expose] public section

namespace Rhone.MarkovChain.FinChain

open MeasureTheory Finset Filter

variable {S : Type*} [Fintype S] [MeasurableSpace S] [DiscreteMeasurableSpace S] (C : FinChain S)

theorem integrable_mul_eval (x : S) {H : (ℕ → S) → ℝ} (hH : Measurable H) {B : ℝ}
    (hB : ∀ ω, |H ω| ≤ B) (G : S → ℝ) (l : ℕ) :
    Integrable (fun ω => H ω * G (ω l)) (C.pathLaw x) := by
  refine Integrable.of_bound (hH.mul ((Measurable.of_discrete (f := G)).comp
    (measurable_pi_apply l))).aestronglyMeasurable (B * ∑ z, |G z|)
    (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (hB ω) (abs_le_sum_abs G _) (abs_nonneg _) ((abs_nonneg _).trans (hB ω))

theorem integrable_mul_dynkin (x : S) (F : S → ℝ) (k : ℕ) {H : (ℕ → S) → ℝ}
    (hH : Measurable H) {B : ℝ} (hB : ∀ ω, |H ω| ≤ B) (m : ℕ) :
    Integrable (fun ω => H ω * (F (ω m) - F (ω k) -
      ∑ l ∈ Ico k m, (C.expect F (ω l) - F (ω l)))) (C.pathLaw x) := by
  have hc := C.integrable_mul_eval x hH hB
  have e : (fun ω => H ω * (F (ω m) - F (ω k) -
      ∑ l ∈ Ico k m, (C.expect F (ω l) - F (ω l)))) = fun ω => H ω * F (ω m) -
      H ω * F (ω k) - ∑ l ∈ Ico k m, H ω * (fun z => C.expect F z - F z) (ω l) := by
    funext ω
    rw [mul_sub, mul_sub, Finset.mul_sum]
  rw [e]
  exact ((hc F m).sub (hc F k)).sub
    (integrable_finsetSum _ fun l _ => hc (fun z => C.expect F z - F z) l)

theorem integral_mul_dynkin (x : S) (F : S → ℝ) {k : ℕ} {H : (ℕ → S) → ℝ}
    (hH : StronglyMeasurable[Filtration.piLE (X := fun _ : ℕ => S) k] H) {B : ℝ}
    (hB : ∀ ω, |H ω| ≤ B) (m : ℕ) (hkm : k ≤ m) :
    ∫ ω, H ω * (F (ω m) - F (ω k) - ∑ l ∈ Ico k m, (C.expect F (ω l) - F (ω l)))
      ∂C.pathLaw x = 0 := by
  have hmeasH : Measurable H := (hH.mono (Filtration.piLE.le k)).measurable
  have hc := C.integrable_mul_eval x hmeasH hB
  induction m, hkm using Nat.le_induction with
  | base => simp
  | succ m hkm ih =>
    have hle : Filtration.piLE (X := fun _ : ℕ => S) k ≤ Filtration.piLE m :=
      (Filtration.piLE (X := fun _ : ℕ => S)).mono hkm
    have hstep := C.integral_mul_eval_succ x m F (hH.mono hle) hB
    have hI : Integrable (fun ω => H ω * (F (ω m) - F (ω k) -
        ∑ l ∈ Ico k m, (C.expect F (ω l) - F (ω l)))) (C.pathLaw x) := by
      have e : (fun ω => H ω * (F (ω m) - F (ω k) -
          ∑ l ∈ Ico k m, (C.expect F (ω l) - F (ω l)))) = fun ω => H ω * F (ω m) -
          H ω * F (ω k) - ∑ l ∈ Ico k m, H ω * (fun z => C.expect F z - F z) (ω l) := by
        funext ω
        rw [mul_sub, mul_sub, Finset.mul_sum]
      rw [e]
      exact ((hc F m).sub (hc F k)).sub
        (integrable_finsetSum _ fun l _ => hc (fun z => C.expect F z - F z) l)
    have e : ∀ ω : ℕ → S, H ω * (F (ω (m + 1)) - F (ω k) -
        ∑ l ∈ Ico k (m + 1), (C.expect F (ω l) - F (ω l))) =
        H ω * (F (ω m) - F (ω k) - ∑ l ∈ Ico k m, (C.expect F (ω l) - F (ω l))) +
          (H ω * F (ω (m + 1)) - H ω * C.expect F (ω m)) := by
      intro ω
      rw [Finset.sum_Ico_succ_top hkm]
      ring
    have hJ : Integrable (fun ω => H ω * F (ω (m + 1)) - H ω * C.expect F (ω m))
        (C.pathLaw x) := (hc F (m + 1)).sub (hc (C.expect F) m)
    calc ∫ ω, H ω * (F (ω (m + 1)) - F (ω k) -
          ∑ l ∈ Ico k (m + 1), (C.expect F (ω l) - F (ω l))) ∂C.pathLaw x
        = ∫ ω, (H ω * (F (ω m) - F (ω k) - ∑ l ∈ Ico k m, (C.expect F (ω l) - F (ω l))) +
            (H ω * F (ω (m + 1)) - H ω * C.expect F (ω m))) ∂C.pathLaw x :=
          integral_congr_ae (Eventually.of_forall e)
      _ = 0 := by
          rw [integral_add hI hJ, ih, integral_sub (hc F (m + 1)) (hc (C.expect F) m), hstep,
            sub_self, add_zero]

end Rhone.MarkovChain.FinChain
