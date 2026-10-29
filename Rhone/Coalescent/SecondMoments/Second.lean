/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SecondMoments.Shift

/-! # The second-moment occupation identity -/

@[expose] public section

namespace Rhone.Coalescent.SecondMoments

open Finset TwoLocusGenealogy TypedAncestralChain BranchLengthMoments
open MeasureTheory
open ProbabilityTheory
open scoped ENNReal

variable {n KA KB : ℕ} {θA θB ρ : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ}

theorem tsum_split_nat (f : ℕ → ℝ≥0∞) (j : ℕ) :
    (∑' k : ℕ, f k) = (∑ i ∈ Finset.range j, f i) + ∑' m : ℕ, f (m + j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [ih, tsum_eq_zero_add' (f := fun m => f (m + j)) ENNReal.summable,
      Finset.sum_range_succ, ← add_assoc]
    congr 1
    · congr 1
      rw [Nat.zero_add]
    · exact tsum_congr fun m => by rw [show m + 1 + j = m + (j + 1) by omega]

theorem tsum_sum_comm {α : Type*} [Fintype α] (G : ℕ → α → ℝ≥0∞) :
    (∑' m : ℕ, ∑ t : α, G m t) = ∑ t : α, ∑' m : ℕ, G m t := by
  have h1 : (∑' m : ℕ, ∑ t : α, G m t) = ∑' m : ℕ, ∑' t : α, G m t :=
    tsum_congr fun m => (tsum_fintype (G m)).symm
  rw [h1, ENNReal.tsum_comm, tsum_fintype]

theorem tsum_triangle (F : ℕ → ℕ → ℝ≥0∞) :
    (∑' j : ℕ, ∑' k : ℕ, F j k) + (∑' j : ℕ, F j j)
      = (∑' j : ℕ, ∑' m : ℕ, F j (m + j)) + (∑' k : ℕ, ∑' m : ℕ, F (m + k) k) := by
  have hA : (∑' j : ℕ, ∑' k : ℕ, F j k)
      = (∑' j : ℕ, ∑ i ∈ Finset.range j, F j i) + ∑' j : ℕ, ∑' m : ℕ, F j (m + j) := by
    rw [← ENNReal.tsum_add]
    exact tsum_congr fun j => tsum_split_nat (F j) j
  have hB : (∑' k : ℕ, ∑' m : ℕ, F (m + k) k)
      = (∑' k : ℕ, F k k) + ∑' k : ℕ, ∑' m : ℕ, F (m + 1 + k) k := by
    rw [← ENNReal.tsum_add]
    refine tsum_congr fun k => ?_
    rw [tsum_eq_zero_add' (f := fun m => F (m + k) k) ENNReal.summable]
    congr 1
    · rw [Nat.zero_add]
  have hT : (∑' j : ℕ, ∑ i ∈ Finset.range j, F j i)
      = ∑' k : ℕ, ∑' m : ℕ, F (m + 1 + k) k := by
    have hfin : ∀ j : ℕ, (∑ i ∈ Finset.range j, F j i)
        = ∑' i : ℕ, (if i < j then F j i else 0) := by
      intro j
      rw [tsum_eq_sum (s := Finset.range j)
        (f := fun i => if i < j then F j i else 0)
        (fun b hb => ite_eq_right (by simpa using hb))]
      exact Finset.sum_congr rfl fun i hi => (ite_eq_left (Finset.mem_range.1 hi)).symm
    simp only [hfin]
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun i => ?_
    rw [tsum_split_nat (fun j => if i < j then F j i else 0) (i + 1)]
    have h0 : (∑ l ∈ Finset.range (i + 1), if i < l then F l i else 0) = 0 :=
      Finset.sum_eq_zero fun l hl => ite_eq_right (by have := Finset.mem_range.1 hl; omega)
    rw [h0, zero_add]
    refine tsum_congr fun m => ?_
    rw [ite_eq_left (by omega : i < m + (i + 1))]
    congr 1
    omega
  rw [hA, hB, hT]
  ring

noncomputable def pairExp (θA θB ρ : ℝ) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ)
    (h : Adm θA θB ρ πA πB) (g u : TS n KA KB → ℝ) (s : TS n KA KB) (j k : ℕ) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.ofReal (g (ω j)) * ENNReal.ofReal (u (ω k)) ∂(argTrajT θA θB ρ πA πB h s)

theorem pairExp_comm (h : Adm θA θB ρ πA πB) (g u : TS n KA KB → ℝ) (s : TS n KA KB)
    (j k : ℕ) : pairExp θA θB ρ πA πB h g u s j k = pairExp θA θB ρ πA πB h u g s k j :=
  lintegral_congr fun _ => mul_comm _ _

theorem pairExp_shift (h : Adm θA θB ρ πA πB) {g u : TS n KA KB → ℝ}
    (hg : ∀ t, 0 ≤ g t) (hu : ∀ t, 0 ≤ u t) (s : TS n KA KB) (j m : ℕ) :
    pairExp θA θB ρ πA πB h g u s j (m + j)
      = ENNReal.ofReal (mstep θA θB ρ πA πB j
          (fun x => g x * mstep θA θB ρ πA πB m u x) s) := by
  rw [pairExp, show m + j = j + m by omega]
  exact lintegral_two_time h j m hg hu s

theorem tsum_ofReal_mstep_mul (h : Adm θA θB ρ πA πB) {C : TS n KA KB → Prop}
    (hC : Closed θA θB ρ πA πB C) {g w : TS n KA KB → ℝ} (hg : ∀ t, 0 ≤ g t)
    (hw : ∀ t, 0 ≤ w t) (U : ℕ → TS n KA KB → ℝ) (hU : ∀ m t, 0 ≤ U m t)
    (hlimU : ∀ t, C t → (∑' m : ℕ, ENNReal.ofReal (U m t)) = ENNReal.ofReal (w t))
    (j : ℕ) {s : TS n KA KB} (hs : C s) :
    (∑' m : ℕ, ENNReal.ofReal (mstep θA θB ρ πA πB j (fun x => g x * U m x) s))
      = ENNReal.ofReal (mstep θA θB ρ πA πB j (fun x => g x * w x) s) := by
  have hexp : ∀ m : ℕ, ENNReal.ofReal (mstep θA θB ρ πA πB j (fun x => g x * U m x) s)
      = ∑ t : TS n KA KB, ENNReal.ofReal (pk θA θB ρ πA πB j s t)
          * (ENNReal.ofReal (g t) * ENNReal.ofReal (U m t)) := by
    intro m
    rw [mstep_eq_sum_pk, ENNReal.ofReal_sum_of_nonneg fun t _ =>
      mul_nonneg (pk_nonneg h j s t) (mul_nonneg (hg t) (hU m t))]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [ENNReal.ofReal_mul (pk_nonneg h j s t), ENNReal.ofReal_mul (hg t)]
  have hrhs : ENNReal.ofReal (mstep θA θB ρ πA πB j (fun x => g x * w x) s)
      = ∑ t : TS n KA KB, ENNReal.ofReal (pk θA θB ρ πA πB j s t)
          * (ENNReal.ofReal (g t) * ENNReal.ofReal (w t)) := by
    rw [mstep_eq_sum_pk, ENNReal.ofReal_sum_of_nonneg fun t _ =>
      mul_nonneg (pk_nonneg h j s t) (mul_nonneg (hg t) (hw t))]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [ENNReal.ofReal_mul (pk_nonneg h j s t), ENNReal.ofReal_mul (hg t)]
  simp only [hexp]
  rw [tsum_sum_comm, hrhs]
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases hCt : C t
  · rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, hlimU t hCt]
  · rw [pk_eq_zero_of_closed hC j hs hCt, ENNReal.ofReal_zero, zero_mul]
    simp

theorem lintegral_occAll_mul_eq_tsum (h : Adm θA θB ρ πA πB) (g u : TS n KA KB → ℝ)
    (s : TS n KA KB) :
    (∫⁻ ω, occAll g ω * occAll u ω ∂(argTrajT θA θB ρ πA πB h s))
      = ∑' j : ℕ, ∑' k : ℕ, pairExp θA θB ρ πA πB h g u s j k := by
  have hmeas : ∀ (v : TS n KA KB → ℝ) (k : ℕ),
      Measurable fun ω : (_ : ℕ) → TS n KA KB => ENNReal.ofReal (v (ω k)) := by
    intro v k
    exact (Measurable.of_discrete
      (f := fun t : TS n KA KB => ENNReal.ofReal (v t))).comp (measurable_pi_apply k)
  have hpt : ∀ ω : (_ : ℕ) → TS n KA KB, occAll g ω * occAll u ω
      = ∑' j : ℕ, ∑' k : ℕ, ENNReal.ofReal (g (ω j)) * ENNReal.ofReal (u (ω k)) := by
    intro ω
    rw [occAll, occAll, ← ENNReal.tsum_mul_right]
    exact tsum_congr fun _ => ENNReal.tsum_mul_left.symm
  rw [lintegral_congr hpt]
  have h1 : (∫⁻ ω, ∑' j : ℕ,
        (∑' k : ℕ, ENNReal.ofReal (g (ω j)) * ENNReal.ofReal (u (ω k)))
        ∂(argTrajT θA θB ρ πA πB h s))
      = ∑' j : ℕ, ∫⁻ ω, (∑' k : ℕ, ENNReal.ofReal (g (ω j)) * ENNReal.ofReal (u (ω k)))
        ∂(argTrajT θA θB ρ πA πB h s) :=
    lintegral_tsum fun j =>
      (Measurable.tsum fun k => (hmeas g j).mul (hmeas u k)).aemeasurable
  rw [h1]
  refine tsum_congr fun j => ?_
  have h2 : (∫⁻ ω, ∑' k : ℕ, ENNReal.ofReal (g (ω j)) * ENNReal.ofReal (u (ω k))
        ∂(argTrajT θA θB ρ πA πB h s))
      = ∑' k : ℕ, ∫⁻ ω, ENNReal.ofReal (g (ω j)) * ENNReal.ofReal (u (ω k))
        ∂(argTrajT θA θB ρ πA πB h s) :=
    lintegral_tsum fun k => ((hmeas g j).mul (hmeas u k)).aemeasurable
  rw [h2]
  rfl

theorem tsum_pairExp_diag (h : Adm θA θB ρ πA πB) {g u : TS n KA KB → ℝ}
    (hg : ∀ t, 0 ≤ g t) (hu : ∀ t, 0 ≤ u t) (s : TS n KA KB) :
    (∑' j : ℕ, pairExp θA θB ρ πA πB h g u s j j)
      = ∫⁻ ω, occAll (fun t => g t * u t) ω ∂(argTrajT θA θB ρ πA πB h s) := by
  rw [lintegral_occAll_eq_tsum h (fun t => mul_nonneg (hg t) (hu t)) s]
  refine tsum_congr fun j => ?_
  have hj : pairExp θA θB ρ πA πB h g u s j (0 + j)
      = ENNReal.ofReal (mstep θA θB ρ πA πB j
          (fun x => g x * mstep θA θB ρ πA πB 0 u x) s) := pairExp_shift h hg hu s j 0
  rw [Nat.zero_add] at hj
  rw [hj]
  simp only [mstep_zero]

theorem tsum_pairExp_upper (h : Adm θA θB ρ πA πB) {C : TS n KA KB → Prop}
    (hC : Closed θA θB ρ πA πB C) {g u v : TS n KA KB → ℝ} (hg : ∀ t, 0 ≤ g t)
    (hu : ∀ t, 0 ≤ u t) (hvnn : ∀ t, 0 ≤ v t)
    (hv : ∀ t, C t → v t = u t + ∑ t', transS θA θB ρ πA πB t t' * v t')
    (hlim : ∀ t, C t →
      Filter.Tendsto (fun N => mstep θA θB ρ πA πB N v t) Filter.atTop (nhds 0))
    {s : TS n KA KB} (hs : C s) :
    (∑' j : ℕ, ∑' m : ℕ, pairExp θA θB ρ πA πB h g u s j (m + j))
      = ∫⁻ ω, occAll (fun t => g t * v t) ω ∂(argTrajT θA θB ρ πA πB h s) := by
  rw [lintegral_occAll_eq_tsum h (fun t => mul_nonneg (hg t) (hvnn t)) s]
  refine tsum_congr fun j => ?_
  have hshift : ∀ m : ℕ, pairExp θA θB ρ πA πB h g u s j (m + j)
      = ENNReal.ofReal (mstep θA θB ρ πA πB j
          (fun x => g x * mstep θA θB ρ πA πB m u x) s) :=
    fun m => pairExp_shift h hg hu s j m
  simp only [hshift]
  exact tsum_ofReal_mstep_mul h hC hg hvnn (fun m => mstep θA θB ρ πA πB m u)
    (fun m t => mstep_nonneg h m hu t)
    (fun t ht => tsum_ofReal_mstep_of_tendsto h hC hu hv (hlim t ht) ht) j hs

theorem lintegral_occAll_mul (h : Adm θA θB ρ πA πB) {C : TS n KA KB → Prop}
    (hC : Closed θA θB ρ πA πB C) {g u vg vu : TS n KA KB → ℝ}
    (hg : ∀ t, 0 ≤ g t) (hu : ∀ t, 0 ≤ u t) (hvg : ∀ t, 0 ≤ vg t) (hvu : ∀ t, 0 ≤ vu t)
    (hfg : ∀ t, C t → vg t = g t + ∑ t', transS θA θB ρ πA πB t t' * vg t')
    (hfu : ∀ t, C t → vu t = u t + ∑ t', transS θA θB ρ πA πB t t' * vu t')
    (hlg : ∀ t, C t →
      Filter.Tendsto (fun N => mstep θA θB ρ πA πB N vg t) Filter.atTop (nhds 0))
    (hlu : ∀ t, C t →
      Filter.Tendsto (fun N => mstep θA θB ρ πA πB N vu t) Filter.atTop (nhds 0))
    {s : TS n KA KB} (hs : C s) :
    (∫⁻ ω, occAll g ω * occAll u ω ∂(argTrajT θA θB ρ πA πB h s))
        + (∫⁻ ω, occAll (fun t => g t * u t) ω ∂(argTrajT θA θB ρ πA πB h s))
      = (∫⁻ ω, occAll (fun t => g t * vu t) ω ∂(argTrajT θA θB ρ πA πB h s))
        + ∫⁻ ω, occAll (fun t => u t * vg t) ω ∂(argTrajT θA θB ρ πA πB h s) := by
  rw [lintegral_occAll_mul_eq_tsum h g u s, ← tsum_pairExp_diag h hg hu s,
    ← tsum_pairExp_upper h hC hg hu hvu hfu hlu hs,
    ← tsum_pairExp_upper h hC hu hg hvg hfg hlg hs]
  rw [tsum_triangle fun j k => pairExp θA θB ρ πA πB h g u s j k]
  congr 1
  exact tsum_congr fun k => tsum_congr fun m => pairExp_comm h g u s (m + k) k

theorem lintegral_occAll_mul_eq (h : Adm θA θB ρ πA πB) {C : TS n KA KB → Prop}
    (hC : Closed θA θB ρ πA πB C) {g u vg vu w : TS n KA KB → ℝ}
    (hg : ∀ t, 0 ≤ g t) (hu : ∀ t, 0 ≤ u t) (hvg : ∀ t, 0 ≤ vg t) (hvu : ∀ t, 0 ≤ vu t)
    (hfg : ∀ t, C t → vg t = g t + ∑ t', transS θA θB ρ πA πB t t' * vg t')
    (hfu : ∀ t, C t → vu t = u t + ∑ t', transS θA θB ρ πA πB t t' * vu t')
    (hlg : ∀ t, C t →
      Filter.Tendsto (fun N => mstep θA θB ρ πA πB N vg t) Filter.atTop (nhds 0))
    (hlu : ∀ t, C t →
      Filter.Tendsto (fun N => mstep θA θB ρ πA πB N vu t) Filter.atTop (nhds 0))
    (hfw : ∀ t, C t → w t = (g t * vu t + u t * vg t)
      + ∑ t', transS θA θB ρ πA πB t t' * w t')
    {s : TS n KA KB}
    (hlw : Filter.Tendsto (fun N => mstep θA θB ρ πA πB N w s) Filter.atTop (nhds 0))
    (hs : C s) :
    (∫⁻ ω, occAll g ω * occAll u ω ∂(argTrajT θA θB ρ πA πB h s))
        + (∫⁻ ω, occAll (fun t => g t * u t) ω ∂(argTrajT θA θB ρ πA πB h s))
      = ENNReal.ofReal (w s) := by
  have hsrc : (∫⁻ ω, occAll (fun t => g t * vu t + u t * vg t) ω
      ∂(argTrajT θA θB ρ πA πB h s)) = ENNReal.ofReal (w s) :=
    lintegral_occAll_eq h hC
      (fun t => add_nonneg (mul_nonneg (hg t) (hvu t)) (mul_nonneg (hu t) (hvg t)))
      hfw hlw hs
  have hsplit : (∫⁻ ω, occAll (fun t => g t * vu t + u t * vg t) ω
        ∂(argTrajT θA θB ρ πA πB h s))
      = (∫⁻ ω, occAll (fun t => g t * vu t) ω ∂(argTrajT θA θB ρ πA πB h s))
        + ∫⁻ ω, occAll (fun t => u t * vg t) ω ∂(argTrajT θA θB ρ πA πB h s) := by
    rw [lintegral_congr fun ω => occAll_add (fun t => mul_nonneg (hg t) (hvu t))
      (fun t => mul_nonneg (hu t) (hvg t)) ω]
    exact lintegral_add_left (measurable_occAll (fun t => g t * vu t)) _
  rw [lintegral_occAll_mul h hC hg hu hvg hvu hfg hfu hlg hlu hs, ← hsplit, hsrc]

end Rhone.Coalescent.SecondMoments
