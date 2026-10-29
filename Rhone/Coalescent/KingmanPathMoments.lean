/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanChain
public import Rhone.Coalescent.KingmanClockMoments
public import Mathlib.Tactic.Ring
/-!
# Second moments under the existing Kingman jump-and-hold path law

Source: kingman1982, sec. 1, eq. (1.1)–(1.4), (1.7). -/
@[expose] public section
namespace Rhone.Coalescent
open MeasureTheory Finset MarkovChain
open scoped ENNReal
private def nextBlock {n : ℕ} (k : Fin (n + 1)) : Fin (n + 1) :=
  if k.val ≤ 1 then k else ⟨k.val - 1, by omega⟩
private theorem block_jump_row (n : ℕ) (k j : Fin (n + 1)) :
    (blockChain n).jumpChain.P k j = if nextBlock k = j then 1 else 0 := by
  classical
  by_cases hk : k.val ≤ 1
  · have hc : (blockChain n).rate k = 0 := by
      rw [blockChain_rate, coalRate_eq_zero hk, Rat.cast_zero]
    simp [RateChain.jumpChain_P, RateChain.jumpMatrix, hc, nextBlock, hk]
  · have hpos : 0 < (blockChain n).rate k :=
      blockChain_rate_pos (by simpa only [mem_coalesced] using hk)
    have hne : nextBlock k ≠ k := by
      simp only [nextBlock, hk, ↓reduceIte]
      intro h
      have := congrArg Fin.val h
      simp only at this
      omega
    rw [RateChain.jumpChain_P, RateChain.jumpMatrix, ite_eq_right hpos.ne']
    by_cases hj : k = j
    · subst j
      simp [hne]
    · rw [ite_eq_right hj, blockChain_Q, blockQ]
      have heq : ((j : ℕ) + 1 = k) ↔ nextBlock k = j := by
        simp only [nextBlock, hk, ↓reduceIte, Fin.ext_iff]
        omega
      rw [ite_eq_right (Ne.symm hj), sub_zero, ← blockChain_rate]
      simp only [heq]
      by_cases hn : nextBlock k = j
      · simp [hn, hpos.ne']
      · simp [hn]
private theorem block_step_deterministic (n t : ℕ) (k j : Fin (n + 1)) :
    (blockChain n).jumpChain.stepN t k j = if ((nextBlock)^[t]) k = j then 1 else 0 := by
  classical
  induction t generalizing k with
  | zero =>
    simp only [FinChain.stepN_zero, Matrix.one_apply, Function.iterate_zero, id_eq]
    by_cases h : k = j <;> simp_all only [ite_true, ite_false]
  | succ t ih =>
    rw [FinChain.stepN_succ, Matrix.mul_apply]
    simp only [block_jump_row]
    rw [sum_eq_single (nextBlock k)]
    · simp only [ite_true, one_mul, Function.iterate_succ_apply]
      have hh := ih (nextBlock k)
      by_cases h : ((nextBlock)^[t]) (nextBlock k) = j
      · simpa only [h, ite_true] using hh
      · simpa only [h, ite_false] using hh
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
private theorem iterate_nextBlock_val (n t : ℕ) (k : Fin (n + 1)) :
    (((nextBlock)^[t]) k : ℕ) = max (k.val - t) (min k.val 1) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    simp only [nextBlock]
    split_ifs with h
    · simpa only [ih] using (show max (k.val - t) (min k.val 1) =
        max (k.val - (t + 1)) (min k.val 1) from by rw [ih] at h; omega)
    · simp only [ih]
      omega
/-- Source: kingman1982, eq. (1.8)–(1.9). -/
theorem blockChain_path_countdown (n : ℕ) :
    ∀ᵐ ω ∂(blockChain n).jumpChain.pathLaw (Fin.last n),
      ∀ k : ℕ, (ω k : ℕ) = max (n - k) (min n 1) := by
  rw [ae_all_iff]
  intro k
  have h := (blockChain n).jumpChain.map_eval_singleton k (Fin.last n)
    (((nextBlock)^[k]) (Fin.last n))
  simp only [block_step_deterministic, ite_true, ENNReal.ofReal_one] at h
  rw [Measure.map_apply (measurable_pi_apply k) MeasurableSet.of_discrete] at h
  have hae : ∀ᵐ ω ∂(blockChain n).jumpChain.pathLaw (Fin.last n),
      ω k = ((nextBlock)^[k]) (Fin.last n) := by
    exact (ae_iff_prob_eq_one (by measurability)).2 h
  filter_upwards [hae] with ω hω
  rw [hω, iterate_nextBlock_val]
  rfl
private theorem cost_clock_formula (n : ℕ) (g : ℕ → ℝ) (hg : ∀ k, 0 ≤ g k)
    (ω : ℕ → Fin (n + 1)) (e : ℕ → ℝ)
    (hω : ∀ k, (ω k : ℕ) = max (n - k) (min n 1)) :
    (blockChain n).costBefore (coalesced n) (fun k => g k) (ω, e) =
      ∑ k ∈ range (n - 1), ENNReal.ofReal (g (n - k) * (holdingTime (n - k) : ℝ)) *
        ENNReal.ofReal (e k) := by
  classical
  unfold RateChain.costBefore
  rw [tsum_eq_sum (s := range (n - 1))]
  · apply sum_congr rfl
    intro k hk
    have hk2 : 2 ≤ n - k := by have := mem_range.mp hk; omega
    have hv : (ω k : ℕ) = n - k := by rw [hω]; omega
    have hnmem : ω k ∉ coalesced n := by rw [mem_coalesced, hv]; omega
    rw [ite_eq_right hnmem, RateChain.holdTime, blockChain_rate]
    simp only [hv]
    have hcoef : g (n - k) / (coalRate (n - k) : ℝ) =
        g (n - k) * (holdingTime (n - k) : ℝ) := by
      simp [holdingTime, div_eq_mul_inv]
    have hc : 0 ≤ (coalRate (n - k) : ℝ) := by exact_mod_cast coalRate_nonneg (n - k)
    rw [show g (n - k) * (e k / (coalRate (n - k) : ℝ)) =
      (g (n - k) / (coalRate (n - k) : ℝ)) * e k by ring,
      ENNReal.ofReal_mul (div_nonneg (hg _) hc), hcoef]
  · intro k hk
    have hv : (ω k : ℕ) ≤ 1 := by
      have := hω k
      simp only [mem_range, not_lt] at hk
      omega
    simp [mem_coalesced.mpr hv]
private theorem sum_countdown (n : ℕ) (f : ℕ → ℝ) :
    (∑ k ∈ range (n - 1), f (n - k)) = ∑ k ∈ Icc 2 n, f k := by
  apply sum_bij (fun k _ => n - k)
  · intro k hk
    have := mem_range.mp hk
    simp only [mem_Icc]
    omega
  · intro k hk l hl he
    have := mem_range.mp hk
    have := mem_range.mp hl
    omega
  · intro j hj
    have := mem_Icc.mp hj
    refine ⟨n - j, ?_, ?_⟩
    · simp only [mem_range]; omega
    · omega
  · intro k hk
    rfl
private theorem lintegral_cost_clock_sq (n : ℕ) (g : ℕ → ℝ) (hg : ∀ k, 0 ≤ g k) :
    (∫⁻ p, ((blockChain n).costBefore (coalesced n) (fun k => g k) p)^2
      ∂(blockChain n).jumpHoldLaw (Fin.last n)) =
      ENNReal.ofReal ((∑ k ∈ Icc 2 n, g k * (holdingTime k : ℝ))^2 +
        ∑ k ∈ Icc 2 n, (g k * (holdingTime k : ℝ))^2) := by
  let a : ℕ → ℝ := fun k => g (n - k) * (holdingTime (n - k) : ℝ)
  have ha : ∀ k ∈ range (n - 1), 0 ≤ a k := by
    intro k hk
    apply mul_nonneg (hg _)
    have : (0 : ℚ) ≤ holdingTime (n - k) := by
      exact div_nonneg (by norm_num) (coalRate_nonneg _)
    exact_mod_cast this
  have hae : ∀ᵐ p ∂(blockChain n).jumpHoldLaw (Fin.last n),
      ∀ k, (p.1 k : ℕ) = max (n - k) (min n 1) := by
    exact Measure.quasiMeasurePreserving_fst.ae (blockChain_path_countdown n)
  have heq : (fun p => ((blockChain n).costBefore (coalesced n) (fun k => g k) p)^2) =ᵐ[
      (blockChain n).jumpHoldLaw (Fin.last n)]
      (fun p => (∑ k ∈ range (n - 1), ENNReal.ofReal (a k) *
        ENNReal.ofReal (p.2 k))^2) := by
    filter_upwards [hae] with p hp
    rw [cost_clock_formula n g hg p.1 p.2 hp]
  rw [lintegral_congr_ae heq, RateChain.jumpHoldLaw]
  have hm : Measurable (fun e : ℕ → ℝ =>
      (∑ k ∈ range (n - 1), ENNReal.ofReal (a k) * ENNReal.ofReal (e k))^2) := by
    apply Measurable.pow_const
    apply Finset.measurable_sum
    intro k hk
    exact measurable_const.mul (ENNReal.measurable_ofReal.comp (measurable_pi_apply k))
  have hprod := lintegral_prod_mul
    (μ := (blockChain n).jumpChain.pathLaw (Fin.last n)) (ν := Rhone.MarkovChain.clockLaw)
    (f := fun _ => 1)
    (g := fun e => (∑ k ∈ range (n - 1), ENNReal.ofReal (a k) * ENNReal.ofReal (e k))^2)
    (by fun_prop) hm.aemeasurable
  simp only [one_mul, lintegral_const, measure_univ] at hprod
  rw [hprod, lintegral_weighted_clock_sum_sq _ _ ha]
  congr 1
  dsimp only [a]
  rw [sum_countdown n (fun k => g k * (holdingTime k : ℝ)),
    sum_countdown n (fun k => (g k * (holdingTime k : ℝ))^2)]
theorem lintegral_treeLength_sq (n : ℕ) :
    ∫⁻ p, (treeLength n p)^2 ∂(blockChain n).jumpHoldLaw (Fin.last n) =
      ENNReal.ofReal ((expLength n : ℝ)^2 + (varLength n : ℝ)) := by
  have h := lintegral_cost_clock_sq n (fun k => (k : ℝ)) (fun k => Nat.cast_nonneg k)
  simpa only [treeLength, expLength, varLength, Rat.cast_sum, Rat.cast_mul,
    Rat.cast_natCast, Rat.cast_pow] using h
theorem lintegral_tmrca_sq (n : ℕ) :
    ∫⁻ p, (tmrca n p)^2 ∂(blockChain n).jumpHoldLaw (Fin.last n) =
      ENNReal.ofReal ((expTMRCA n : ℝ)^2 + (varTMRCA n : ℝ)) := by
  have h := lintegral_cost_clock_sq n (fun _ => 1) (fun _ => le_of_lt zero_lt_one)
  simpa only [tmrca, RateChain.timeBefore, expTMRCA, varTMRCA,
    Rat.cast_sum, Rat.cast_pow, one_mul] using h
end Rhone.Coalescent
