/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeKingmanMarkLaw
public import Rhone.Coalescent.KingmanChain

/-!
# Kingman waiting times as the holding times of the block-counting chain

Source: kingman1982, eq. (1.7), (1.9). -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open MeasureTheory ProbabilityTheory MarkovChain SmcSupport
open scoped ENNReal

noncomputable def blockHoldTimes (N : ℕ) (p : (ℕ → Fin (N + 1)) × (ℕ → ℝ)) : Fin (N - 1) → ℝ :=
  fun j => (blockChain N).holdTime p j.val

def blockDet (N k : ℕ) : Fin (N + 1) := ⟨max (N - k) (min 1 N), by omega⟩

theorem expMeasure_one_map_div {c : ℝ} (hc : 0 < c) :
    (expMeasure 1).map (fun x => x / c) = expMeasure c := by
  rw [← inverseClock_law 1 one_pos, Measure.map_map (by fun_prop) (by fun_prop),
    ← inverseClock_law c hc]
  congr 1
  funext u
  simp

theorem clockLaw_scaled_law (n : ℕ) (c : ℕ → ℝ) (hc : ∀ j < n, 0 < c j) :
    clockLaw.map (fun e : ℕ → ℝ => fun j : Fin n => e j.val / c j.val) =
      Measure.pi fun j : Fin n => expMeasure (c j.val) := by
  have : ∀ j : Fin n, IsProbabilityMeasure (expMeasure (c j.val)) :=
    fun j => isProbabilityMeasure_expMeasure (hc j j.isLt)
  have hG : Measurable (fun e : ℕ → ℝ => fun j : Fin n => e j.val / c j.val) :=
    measurable_pi_iff.mpr fun j => (measurable_pi_apply j.val).div_const _
  symm
  apply Measure.pi_eq
  intro s hs
  let t : ℕ → Set ℝ := fun i =>
    if hi : i < n then (fun x => x / c i) ⁻¹' s ⟨i, hi⟩ else Set.univ
  have ht : ∀ i ∈ Finset.range n, MeasurableSet (t i) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    simp only [t, dite_eq_left hi']
    exact (by fun_prop : Measurable fun x : ℝ => x / c i) (hs _)
  have hset : (fun e : ℕ → ℝ => fun j : Fin n => e j.val / c j.val) ⁻¹' Set.pi Set.univ s =
      Set.pi (Finset.range n) t := by
    ext e
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Finset.coe_range,
      Set.mem_Iio]
    constructor
    · intro h i hi
      simpa only [t, dite_eq_left hi, Set.mem_preimage] using h ⟨i, hi⟩
    · intro h j
      simpa only [t, dite_eq_left j.isLt, Set.mem_preimage] using h j.val j.isLt
  rw [Measure.map_apply hG (MeasurableSet.univ_pi hs), hset, clockLaw,
    Measure.infinitePi_pi _ ht, ← Fin.prod_univ_eq_prod_range (fun i => expMeasure 1 (t i))]
  apply Finset.prod_congr rfl
  intro j _
  simp only [t, dite_eq_left j.isLt]
  have hd : Measurable fun x : ℝ => x / c j.val := by fun_prop
  rw [← Measure.map_apply hd (hs j), expMeasure_one_map_div (hc j j.isLt)]

theorem blockChain_jump_det (N k : ℕ) :
    (blockChain N).jumpChain.P (blockDet N k) (blockDet N (k + 1)) = 1 := by
  by_cases h2 : 2 ≤ N - k
  · have hk : blockDet N k ∉ coalesced N := by
      rw [mem_coalesced]
      simp only [blockDet]
      omega
    have hpos := blockChain_rate_pos hk
    have hne : blockDet N k ≠ blockDet N (k + 1) := by
      intro h
      have := congrArg Fin.val h
      simp only [blockDet] at this
      omega
    rw [RateChain.jumpChain_P_of_ne hpos.ne' hne, blockChain_Q, blockQ,
      ite_eq_left (by simp only [blockDet]; omega), ite_eq_right hne.symm, sub_zero, mul_one,
      ← blockChain_rate]
    exact div_self hpos.ne'
  · have he : blockDet N (k + 1) = blockDet N k := by
      apply Fin.ext
      simp only [blockDet]
      omega
    have hr : (blockChain N).rate (blockDet N k) = 0 := by
      rw [blockChain_rate, coalRate_eq_zero (by simp only [blockDet]; omega), Rat.cast_zero]
    rw [he]
    simp [RateChain.jumpChain_P, RateChain.jumpMatrix, hr]

theorem blockChain_stepN_det (N k : ℕ) :
    (blockChain N).jumpChain.stepN k (Fin.last N) (blockDet N k) = 1 := by
  induction k with
  | zero =>
    have h0 : blockDet N 0 = Fin.last N := by
      apply Fin.ext
      simp only [blockDet, Fin.val_last]
      omega
    rw [FinChain.stepN_zero, h0, Matrix.one_apply_eq]
  | succ k ih =>
    apply le_antisymm (FinChain.stepN_le_one _ _ _ _)
    rw [FinChain.stepN_succ', Matrix.mul_apply]
    calc (1 : ℝ) = (blockChain N).jumpChain.stepN k (Fin.last N) (blockDet N k) *
          (blockChain N).jumpChain.P (blockDet N k) (blockDet N (k + 1)) := by
          rw [ih, blockChain_jump_det, mul_one]
      _ ≤ _ := Finset.single_le_sum (f := fun z => (blockChain N).jumpChain.stepN k (Fin.last N) z *
          (blockChain N).jumpChain.P z (blockDet N (k + 1)))
          (fun z _ => mul_nonneg (FinChain.stepN_nonneg _ _ _ _)
            ((blockChain N).jumpChain.nonneg _ _))
          (Finset.mem_univ _)

theorem blockChain_path_ae (N : ℕ) :
    ∀ᵐ ω ∂(blockChain N).jumpChain.pathLaw (Fin.last N), ∀ k, ω k = blockDet N k := by
  rw [ae_all_iff]
  intro k
  have hm : MeasurableSet {ω : ℕ → Fin (N + 1) | ω k = blockDet N k} :=
    (measurable_pi_apply k) (measurableSet_singleton _)
  change {ω : ℕ → Fin (N + 1) | ω k = blockDet N k} ∈ ae _
  rw [mem_ae_iff_prob_eq_one hm]
  have h := FinChain.map_eval_singleton (blockChain N).jumpChain k (Fin.last N) (blockDet N k)
  rw [Measure.map_apply (measurable_pi_apply k) (measurableSet_singleton _),
    blockChain_stepN_det, ENNReal.ofReal_one] at h
  exact h

theorem blockChain_holdTimes_law (N : ℕ) :
    ((blockChain N).jumpHoldLaw (Fin.last N)).map (blockHoldTimes N) =
      Measure.pi fun j : Fin (N - 1) =>
        expMeasure (Rhone.Coalescent.coalRate (N - j.val) : ℝ) := by
  let G : (ℕ → ℝ) → Fin (N - 1) → ℝ :=
    fun e j => e j.val / (Rhone.Coalescent.coalRate (N - j.val) : ℝ)
  have hG : Measurable G :=
    measurable_pi_iff.mpr fun j => (measurable_pi_apply j.val).div_const _
  have hae : blockHoldTimes N =ᵐ[(blockChain N).jumpHoldLaw (Fin.last N)] G ∘ Prod.snd := by
    rw [RateChain.jumpHoldLaw]
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (blockChain_path_ae N)] with p hp
    funext j
    have hv : ((blockDet N j.val : Fin (N + 1)) : ℕ) = N - j.val := by
      simp only [blockDet]
      omega
    simp only [blockHoldTimes, RateChain.holdTime, Function.comp_apply, G]
    rw [hp j.val, blockChain_rate, hv]
  rw [Measure.map_congr hae, ← Measure.map_map hG measurable_snd, RateChain.jumpHoldLaw,
    Measure.map_snd_prod, measure_univ, one_smul]
  exact clockLaw_scaled_law (N - 1) (fun j => (Rhone.Coalescent.coalRate (N - j) : ℝ))
    (fun j hj => by exact_mod_cast Rhone.Coalescent.coalRate_pos (by omega))

/-- Source: kingman1982, eq. (1.7), (1.9). -/
theorem kingmanHistoryLaw_waitingTimes_eq_blockChain (N : ℕ) :
    (kingmanHistoryLaw N).map (kingmanWaitingTimes N) =
      ((blockChain N).jumpHoldLaw (Fin.last N)).map (blockHoldTimes N) := by
  rw [kingmanHistoryLaw_waitingTimes, blockChain_holdTimes_law]

end Rhone.Coalescent.SmcPrime
