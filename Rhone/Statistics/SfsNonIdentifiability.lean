/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Statistics.VariableSizeSfsReduction
public import Rhone.Statistics.UnderdeterminedSystem

/-!
# Distinct piecewise population-size histories can give the same site frequency spectrum

Source: myers_fefferman_patterson2008, secs. 3–5, Appendix Thm 1. -/

@[expose] public section

namespace Rhone.Statistics

open MeasureTheory ProbabilityTheory Finset MarkovChain Coalescent Rhone.Combinatorics Probability
open Filter
open scoped ENNReal NNReal Topology

noncomputable def gridChangePoint (x a : ℕ → ℝ) (e : ℕ) : ℝ :=
  ∑ e' ∈ range e, a e' * (x (e' + 1) - x e')

noncomputable def epochWeight (K : ℕ) (x : ℕ → ℝ) (r : ℝ) (e : ℕ) : ℝ :=
  if e < K then Real.exp (-(r * x e)) - Real.exp (-(r * x (e + 1)))
  else Real.exp (-(r * x K))

theorem epochWeight_congr {K : ℕ} {x y : ℕ → ℝ} (hxy : ∀ e, e ≤ K → x e = y e) (r : ℝ)
    {e : ℕ} (he : e ≤ K) : epochWeight K x r e = epochWeight K y r e := by
  unfold epochWeight
  split_ifs with h
  · rw [hxy e he, hxy (e + 1) (by omega)]
  · rw [hxy K le_rfl]

variable {K : ℕ} {c a : ℕ → ℝ}

theorem clockLaplace_piecewiseSize (h : IsEpochSchedule K c a) {r : ℝ} (hr : 0 < r) :
    clockLaplace (piecewiseSize K c a) r =
      1 / r * ∑ e ∈ range (K + 1), a e * epochWeight K (epochIntensity c a) r e := by
  rw [clockLaplace, (integral_exp_neg_cumIntensity_piecewiseSize h hr).2,
    Finset.sum_range_succ]
  congr 2
  · refine Finset.sum_congr rfl fun e he => ?_
    rw [epochWeight, ite_eq_left (mem_range.1 he)]
  · rw [epochWeight, ite_eq_right (lt_irrefl K)]

theorem gridChangePoint_succ (x a : ℕ → ℝ) (e : ℕ) :
    gridChangePoint x a (e + 1) = gridChangePoint x a e + a e * (x (e + 1) - x e) :=
  Finset.sum_range_succ _ _

theorem isEpochSchedule_gridChangePoint {x : ℕ → ℝ} (hx : ∀ e, e < K → x e < x (e + 1))
    (ha : ∀ e, e ≤ K → 0 < a e) : IsEpochSchedule K (gridChangePoint x a) a where
  start := Finset.sum_range_zero _
  lt_succ := fun e he => by
    rw [gridChangePoint_succ]
    have := mul_pos (ha e he.le) (sub_pos.2 (hx e he))
    linarith
  size_pos := ha

theorem epochIntensity_gridChangePoint {x : ℕ → ℝ} (hx0 : x 0 = 0)
    (ha : ∀ e, e ≤ K → 0 < a e) {e : ℕ} (he : e ≤ K) :
    epochIntensity (gridChangePoint x a) a e = x e := by
  induction e with
  | zero => rw [epochIntensity, Finset.sum_range_zero, hx0]
  | succ e ih =>
    have hae := (ha e (by omega)).ne'
    rw [epochIntensity_succ, ih (by omega), gridChangePoint_succ, add_sub_cancel_left,
      mul_div_cancel_left₀ _ hae]
    ring

theorem gridChangePoint_epochIntensity (h : IsEpochSchedule K c a) {e : ℕ} (he : e ≤ K) :
    gridChangePoint (epochIntensity c a) a e = c e := by
  induction e with
  | zero => rw [gridChangePoint, Finset.sum_range_zero, h.start]
  | succ e ih =>
    have hae := (h.size_pos e (by omega)).ne'
    rw [gridChangePoint_succ, ih (by omega), epochIntensity_succ, add_sub_cancel_left,
      mul_div_cancel₀ _ hae]
    ring

theorem exists_piecewiseSize_ne_same_sfs {K : ℕ} {c₀ a₀ : ℕ → ℝ}
    (h₀ : IsEpochSchedule K c₀ a₀) {n : ℕ} (hn : n ≤ K + 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ c a : ℕ → ℝ, IsEpochSchedule K c a ∧
      (∀ e, e ≤ K → |a e - a₀ e| ≤ ε * a₀ e) ∧
      (∃ s t : ℝ, 0 ≤ s ∧ s < t ∧
        ∀ u ∈ Set.Ioo s t, piecewiseSize K c a u ≠ piecewiseSize K c₀ a₀ u) ∧
      ∀ m i : ℕ, m ≤ n → 1 ≤ i → i < m → ∀ θ : ℝ≥0,
        ∫⁻ x, ENNReal.ofReal (markedKingmanSfs m i x)
            ∂variableSizeMarkedLaw m (piecewiseSize K c a) θ =
          ∫⁻ x, ENNReal.ofReal (markedKingmanSfs m i x)
            ∂variableSizeMarkedLaw m (piecewiseSize K c₀ a₀) θ := by
  classical
  obtain ⟨x, hx⟩ : ∃ x : ℕ → ℝ, x = epochIntensity c₀ a₀ := ⟨_, rfl⟩
  have hx0 : x 0 = 0 := by rw [hx, epochIntensity, Finset.sum_range_zero]
  have hxlt : ∀ e, e < K → x e < x (e + 1) := by
    intro e he
    rw [hx, epochIntensity_succ]
    have := div_pos (sub_pos.2 (h₀.lt_succ e he)) (h₀.size_pos e he.le)
    linarith
  obtain ⟨β, hβne, hβ⟩ := exists_ne_zero_sum_mul_eq_zero K
    (fun m e => a₀ e * epochWeight K x (coalRate (m + 2) : ℝ) e)
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = ∑ e ∈ range (K + 1), |β e| := ⟨_, rfl⟩
  have hβM : ∀ e, e ≤ K → |β e| ≤ M := fun e he => by
    rw [hM]
    exact Finset.single_le_sum (f := fun e => |β e|) (fun e _ => abs_nonneg _)
      (mem_range.2 (by omega))
  have hMpos : 0 < M := by
    obtain ⟨e, he, hne⟩ := hβne
    exact lt_of_lt_of_le (abs_pos.2 hne) (hβM e he)
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = min ε (1 / 2) := ⟨_, rfl⟩
  have hηpos : 0 < η := hη ▸ lt_min hε (by norm_num)
  have hηε : η ≤ ε := hη ▸ min_le_left _ _
  have hηhalf : η ≤ 1 / 2 := hη ▸ min_le_right _ _
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = η / M := ⟨_, rfl⟩
  have hδpos : 0 < δ := hδ ▸ div_pos hηpos hMpos
  have hδβ : ∀ e, e ≤ K → |δ * β e| ≤ η := by
    intro e he
    rw [abs_mul, abs_of_pos hδpos, hδ, div_mul_eq_mul_div, div_le_iff₀ hMpos]
    exact mul_le_mul_of_nonneg_left (hβM e he) hηpos.le
  obtain ⟨a, ha⟩ : ∃ a : ℕ → ℝ, ∀ e, a e = a₀ e * (1 + δ * β e) := ⟨_, fun _ => rfl⟩
  have hapos : ∀ e, e ≤ K → 0 < a e := by
    intro e he
    have h1 := abs_le.1 (hδβ e he)
    rw [ha]
    exact mul_pos (h₀.size_pos e he) (by linarith)
  have h : IsEpochSchedule K (gridChangePoint x a) a :=
    isEpochSchedule_gridChangePoint hxlt hapos
  have hxe : ∀ e, e ≤ K → epochIntensity (gridChangePoint x a) a e = x e := fun e he =>
    epochIntensity_gridChangePoint hx0 hapos he
  refine ⟨gridChangePoint x a, a, h, ?_, ?_, ?_⟩
  · intro e he
    have h1 : a e - a₀ e = a₀ e * (δ * β e) := by rw [ha]; ring
    rw [h1, abs_mul, abs_of_pos (h₀.size_pos e he), mul_comm ε]
    exact mul_le_mul_of_nonneg_left ((hδβ e he).trans hηε) (h₀.size_pos e he).le
  · obtain ⟨he₀K, hβe₀⟩ := Nat.find_spec hβne
    have hbelow : ∀ e, e < Nat.find hβne → a e = a₀ e := by
      intro e he
      have h1 := Nat.find_min hβne he
      have h2 : β e = 0 := by
        by_contra hne
        exact h1 ⟨by omega, hne⟩
      rw [ha, h2]
      ring
    have hce₀ : gridChangePoint x a (Nat.find hβne) = c₀ (Nat.find hβne) := by
      rw [← gridChangePoint_epochIntensity h₀ he₀K, ← hx]
      exact Finset.sum_congr rfl fun e he => by rw [hbelow e (mem_range.1 he)]
    have hae₀ : a (Nat.find hβne) ≠ a₀ (Nat.find hβne) := by
      intro heq
      have h1 : a₀ (Nat.find hβne) * (δ * β (Nat.find hβne)) = 0 := by
        have h2 := ha (Nat.find hβne)
        linarith
      rcases mul_eq_zero.1 h1 with h2 | h2
      · exact (h₀.size_pos _ he₀K).ne' h2
      · rcases mul_eq_zero.1 h2 with h3 | h3
        · exact hδpos.ne' h3
        · exact hβe₀ h3
    rcases Nat.lt_or_eq_of_le he₀K with hlt | heq
    · have hlt₀ := h₀.lt_succ _ hlt
      rw [← hce₀] at hlt₀
      refine ⟨gridChangePoint x a (Nat.find hβne),
        min (gridChangePoint x a (Nat.find hβne + 1)) (c₀ (Nat.find hβne + 1)),
        h.nonneg he₀K, lt_min (h.lt_succ _ hlt) hlt₀, fun u hu => ?_⟩
      rw [piecewiseSize_of_mem_Ioc h hlt ⟨hu.1, (hu.2.trans_le (min_le_left _ _)).le⟩,
        piecewiseSize_of_mem_Ioc h₀ hlt
          ⟨hce₀ ▸ hu.1, (hu.2.trans_le (min_le_right _ _)).le⟩]
      exact hae₀
    · rw [heq] at hce₀ hae₀
      refine ⟨gridChangePoint x a K, gridChangePoint x a K + 1, h.nonneg le_rfl, by linarith,
        fun u hu => ?_⟩
      rw [piecewiseSize_of_lt h hu.1, piecewiseSize_of_lt h₀ (hce₀ ▸ hu.1)]
      exact hae₀
  · intro m i hmn hi him θ
    have hint : IntegrableOn
        (fun t => Real.exp (-cumIntensity (piecewiseSize K (gridChangePoint x a) a) t))
        (Set.Ioi 0) := by
      simpa using (integral_exp_neg_cumIntensity_piecewiseSize h one_pos).1
    have hint₀ : IntegrableOn
        (fun t => Real.exp (-cumIntensity (piecewiseSize K c₀ a₀) t)) (Set.Ioi 0) := by
      simpa using (integral_exp_neg_cumIntensity_piecewiseSize h₀ one_pos).1
    refine lintegral_variableSizeMarkedLaw_sfs_congr_clockLaplace
      (isSizeFunction_piecewiseSize h) (isSizeFunction_piecewiseSize h₀) hint hint₀ ?_ hi him θ
    intro j hj
    obtain ⟨hj2, hjm⟩ := mem_Icc.1 hj
    have hr : (0 : ℝ) < (coalRate j : ℝ) := by exact_mod_cast coalRate_pos hj2
    rw [clockLaplace_piecewiseSize h hr, clockLaplace_piecewiseSize h₀ hr, ← hx]
    congr 1
    have hw : ∀ e ∈ range (K + 1),
        a e * epochWeight K (epochIntensity (gridChangePoint x a) a) (coalRate j) e =
          a₀ e * epochWeight K x (coalRate j) e +
            δ * (β e * (a₀ e * epochWeight K x (coalRate j) e)) := by
      intro e he
      have heK : e ≤ K := by
        have := mem_range.1 he
        omega
      rw [epochWeight_congr hxe _ heK, ha]
      ring
    have hz := hβ (j - 2) (by omega)
    simp only [show j - 2 + 2 = j from by omega] at hz
    rw [Finset.sum_congr rfl hw, Finset.sum_add_distrib, ← Finset.mul_sum, hz, mul_zero,
      add_zero]

theorem exists_size_ne_one_sfs_eq_constant (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ ν : ℝ → ℝ, IsSizeFunction ν ∧ Measurable ν ∧ (∀ t, |ν t - 1| ≤ ε) ∧
      (∃ s t : ℝ, 0 ≤ s ∧ s < t ∧ ∀ u ∈ Set.Ioo s t, ν u ≠ 1) ∧
      ∀ m i : ℕ, m ≤ n → 1 ≤ i → i < m → ∀ θ : ℝ≥0,
        ∫ x, markedKingmanSfs m i x ∂variableSizeMarkedLaw m ν θ = (θ : ℝ) / i := by
  have h₀ : IsEpochSchedule n (fun e => (e : ℝ)) (fun _ => 1) :=
    ⟨Nat.cast_zero, fun e _ => by push_cast; linarith, fun _ _ => one_pos⟩
  have hone : piecewiseSize n (fun e => (e : ℝ)) (fun _ => 1) = fun _ => 1 := rfl
  obtain ⟨c, a, h, hclose, ⟨s, t, hs, hst, hne⟩, hsfs⟩ :=
    exists_piecewiseSize_ne_same_sfs h₀ (Nat.le_succ n) hε
  refine ⟨piecewiseSize n c a, isSizeFunction_piecewiseSize h, measurable_piecewiseSize n c a,
    ?_, ⟨s, t, hs, hst, fun u hu => ?_⟩, ?_⟩
  · intro t
    have h1 := hclose _ (card_filter_changePoint_le n c t)
    rw [mul_one] at h1
    exact h1
  · have h1 := hne u hu
    rwa [hone] at h1
  · intro m i hmn hi him θ
    have hl := hsfs m i hmn hi him θ
    rw [hone] at hl
    rw [integral_eq_lintegral_of_nonneg_ae
        (Eventually.of_forall fun x => markedKingmanSfs_nonneg m i x)
        (measurable_markedKingmanSfs m i).aestronglyMeasurable, hl,
      ← integral_eq_lintegral_of_nonneg_ae
        (Eventually.of_forall fun x => markedKingmanSfs_nonneg m i x)
        (measurable_markedKingmanSfs m i).aestronglyMeasurable,
      variableSizeMarkedLaw_one_sfs_mean hi him θ]

end Rhone.Statistics
