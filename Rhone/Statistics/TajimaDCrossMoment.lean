/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Statistics.TajimaDCrossPotential

/-!
# Joint moment of pair-separation exposure and tree length

Source: tajima1989, p. 587, eq. (24). -/

@[expose] public section
namespace Rhone.Statistics
open MeasureTheory ProbabilityTheory Finset Coalescent Rhone.Combinatorics MarkovChain Probability
open Filter

private theorem sum_range_mul_add_diag (T : ℕ) (a b : ℕ → ℝ) :
    (∑ k ∈ range T, a k) * (∑ k ∈ range T, b k) + ∑ k ∈ range T, a k * b k =
      ∑ t ∈ range T, (∑ k ∈ range (t + 1), a k) * b t +
        ∑ t ∈ range T, (∑ k ∈ range (t + 1), b k) * a t := by
  induction T with
  | zero => simp
  | succ T ih =>
    simp only [Finset.sum_range_succ] at ih ⊢
    linear_combination ih

private theorem cross_add (T : ℕ) (a b : ℕ → ℝ) :
    (∑ k ∈ range T, (a k + b k)) * (∑ k ∈ range T, (a k + b k)) +
        ∑ k ∈ range T, (a k + b k) * (a k + b k) =
      (((∑ k ∈ range T, a k) * (∑ k ∈ range T, a k) + ∑ k ∈ range T, a k * a k) +
        ((∑ k ∈ range T, b k) * (∑ k ∈ range T, b k) + ∑ k ∈ range T, b k * b k)) +
      2 * ((∑ k ∈ range T, a k) * (∑ k ∈ range T, b k) + ∑ k ∈ range T, a k * b k) := by
  have hq : ∑ k ∈ range T, (a k + b k) * (a k + b k) =
      ∑ k ∈ range T, a k * a k + ∑ k ∈ range T, b k * b k +
        2 * ∑ k ∈ range T, a k * b k := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hq, Finset.sum_add_distrib]
  ring

theorem partitionChain_integral_cross_jumpReward (n : ℕ)
    (g₁ g₂ u₁ u₂ w : Finpartition (Finset.univ : Finset (Fin n)) → ℝ)
    (h₁ : ∀ π, u₁ π - (partitionChain (Fin n)).jumpChain.expect u₁ π = g₁ π)
    (h₂ : ∀ π, u₂ π - (partitionChain (Fin n)).jumpChain.expect u₂ π = g₂ π)
    (hw : ∀ π, w π - (partitionChain (Fin n)).jumpChain.expect w π =
      g₁ π * u₂ π + g₂ π * u₁ π)
    (z₁ : ∀ π ∈ coalescedPartitions (Fin n), u₁ π = 0)
    (z₂ : ∀ π ∈ coalescedPartitions (Fin n), u₂ π = 0)
    (zw : ∀ π ∈ coalescedPartitions (Fin n), w π = 0) :
    ∫ ω, ((∑ k ∈ Finset.range (n - 1), g₁ (ω k)) * (∑ k ∈ Finset.range (n - 1), g₂ (ω k)) +
      ∑ k ∈ Finset.range (n - 1), g₁ (ω k) * g₂ (ω k))
      ∂(partitionChain (Fin n)).jumpChain.pathLaw ⊥ = w ⊥ := by
  classical
  have hi (f g : Finpartition (Finset.univ : Finset (Fin n)) → ℝ) (k t : ℕ) :
      Integrable (fun ω => f (ω k) * g (ω t))
        ((partitionChain (Fin n)).jumpChain.pathLaw ⊥) :=
    partitionChain_integrable_eval_mul n ⊥ k t f g
  have hd (f u : Finpartition (Finset.univ : Finset (Fin n)) → ℝ) (k t : ℕ) :
      Integrable (fun ω => f (ω k) * (u (ω t) - u (ω (t + 1))))
        ((partitionChain (Fin n)).jumpChain.pathLaw ⊥) := by
    have he : (fun ω : ℕ → Finpartition (Finset.univ : Finset (Fin n)) =>
        f (ω k) * (u (ω t) - u (ω (t + 1)))) =
        (fun ω => f (ω k) * u (ω t) - f (ω k) * u (ω (t + 1))) := by
      funext ω; ring
    rw [he]
    exact (hi f u k t).sub (hi f u k (t + 1))
  have hstep (f g u : Finpartition (Finset.univ : Finset (Fin n)) → ℝ)
      (hu : ∀ π, u π - (partitionChain (Fin n)).jumpChain.expect u π = g π)
      (k t : ℕ) (hkt : k ≤ t) :
      ∫ ω, f (ω k) * g (ω t) ∂(partitionChain (Fin n)).jumpChain.pathLaw ⊥ =
        ∫ ω, f (ω k) * (u (ω t) - u (ω (t + 1)))
          ∂(partitionChain (Fin n)).jumpChain.pathLaw ⊥ := by
    have h := partitionChain_integral_eval_difference n ⊥ k (t - k) f u
    have hadd : k + (t - k) = t := by omega
    rw [hadd] at h
    rw [h]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    change f (ω k) * g (ω t) =
      f (ω k) * (u (ω t) - (partitionChain (Fin n)).jumpChain.expect u (ω t))
    rw [hu]
  have hprefix (f g u : Finpartition (Finset.univ : Finset (Fin n)) → ℝ)
      (hu : ∀ π, u π - (partitionChain (Fin n)).jumpChain.expect u π = g π) :
      (∫ ω, ∑ t ∈ range (n - 1), ∑ k ∈ range (t + 1), f (ω k) * g (ω t)
        ∂(partitionChain (Fin n)).jumpChain.pathLaw ⊥) =
      ∫ ω, ∑ t ∈ range (n - 1), ∑ k ∈ range (t + 1),
        f (ω k) * (u (ω t) - u (ω (t + 1)))
        ∂(partitionChain (Fin n)).jumpChain.pathLaw ⊥ := by
    rw [integral_finsetSum _ (fun t _ => integrable_finsetSum _ (fun k _ => hi f g k t)),
      integral_finsetSum _ (fun t _ => integrable_finsetSum _ (fun k _ => hd f u k t))]
    apply sum_congr rfl
    intro t ht
    rw [integral_finsetSum _ (fun k _ => hi f g k t),
      integral_finsetSum _ (fun k _ => hd f u k t)]
    apply sum_congr rfl
    intro k hk
    exact hstep f g u hu k t (by have := mem_range.mp hk; omega)
  have hterminal : ∀ᵐ ω ∂(partitionChain (Fin n)).jumpChain.pathLaw ⊥,
      ω (n - 1) ∈ coalescedPartitions (Fin n) := partition_path_terminal_coalesced n
  have hsum : ∫ ω, ∑ t ∈ range (n - 1),
      (w (ω t) - (partitionChain (Fin n)).jumpChain.expect w (ω t))
      ∂(partitionChain (Fin n)).jumpChain.pathLaw ⊥ = w ⊥ := by
    have hint (t : ℕ) : Integrable
        (fun ω => w (ω t) - (partitionChain (Fin n)).jumpChain.expect w (ω t))
        ((partitionChain (Fin n)).jumpChain.pathLaw ⊥) := by
      convert ((partitionChain (Fin n)).jumpChain.integrable_eval w t ⊥).sub
        ((partitionChain (Fin n)).jumpChain.integrable_eval
          ((partitionChain (Fin n)).jumpChain.expect w) t ⊥) using 1
    rw [integral_finsetSum _ (fun t _ => hint t)]
    have he (t : ℕ) :
        (∫ ω, w (ω t) - (partitionChain (Fin n)).jumpChain.expect w (ω t)
          ∂(partitionChain (Fin n)).jumpChain.pathLaw ⊥) =
        (∫ ω, w (ω t) - w (ω (t + 1)) ∂(partitionChain (Fin n)).jumpChain.pathLaw ⊥) := by
      rw [integral_sub ((partitionChain (Fin n)).jumpChain.integrable_eval w t ⊥)
          ((partitionChain (Fin n)).jumpChain.integrable_eval
            ((partitionChain (Fin n)).jumpChain.expect w) t ⊥),
        integral_sub ((partitionChain (Fin n)).jumpChain.integrable_eval w t ⊥)
          ((partitionChain (Fin n)).jumpChain.integrable_eval w (t + 1) ⊥)]
      simp only [FinChain.integral_eval, FinChain.expectN_succ']
    simp_rw [he]
    have hint' (t : ℕ) : Integrable (fun ω => w (ω t) - w (ω (t + 1)))
        ((partitionChain (Fin n)).jumpChain.pathLaw ⊥) := by
      convert ((partitionChain (Fin n)).jumpChain.integrable_eval w t ⊥).sub
        ((partitionChain (Fin n)).jumpChain.integrable_eval w (t + 1) ⊥) using 1
    rw [← integral_finsetSum _ (fun t _ => hint' t)]
    simp_rw [sum_range_sub']
    have heterm : (fun ω : ℕ → Finpartition (Finset.univ : Finset (Fin n)) =>
        w (ω 0) - w (ω (n - 1))) =ᵐ[(partitionChain (Fin n)).jumpChain.pathLaw ⊥]
        (fun ω => w (ω 0)) := by
      filter_upwards [hterminal] with ω hω
      rw [zw _ hω, sub_zero]
    rw [integral_congr_ae heterm, FinChain.integral_eval, FinChain.expectN_zero]
  simp_rw [sum_range_mul_add_diag, sum_mul]
  rw [integral_add
      (integrable_finsetSum _ fun t _ => integrable_finsetSum _ fun k _ => hi g₁ g₂ k t)
      (integrable_finsetSum _ fun t _ => integrable_finsetSum _ fun k _ => hi g₂ g₁ k t),
    hprefix g₁ g₂ u₂ h₂, hprefix g₂ g₁ u₁ h₁,
    ← integral_add
      (integrable_finsetSum _ fun t _ => integrable_finsetSum _ fun k _ => hd g₁ u₂ k t)
      (integrable_finsetSum _ fun t _ => integrable_finsetSum _ fun k _ => hd g₂ u₁ k t)]
  have he : (fun ω : ℕ → Finpartition (Finset.univ : Finset (Fin n)) =>
      (∑ t ∈ range (n - 1), ∑ k ∈ range (t + 1), g₁ (ω k) * (u₂ (ω t) - u₂ (ω (t + 1)))) +
        ∑ t ∈ range (n - 1), ∑ k ∈ range (t + 1),
          g₂ (ω k) * (u₁ (ω t) - u₁ (ω (t + 1))))
      =ᵐ[(partitionChain (Fin n)).jumpChain.pathLaw ⊥]
      (fun ω => ∑ t ∈ range (n - 1),
        (w (ω t) - (partitionChain (Fin n)).jumpChain.expect w (ω t))) := by
    filter_upwards [hterminal] with ω hω
    simp_rw [← sum_mul]
    rw [sum_range_prefix_mul_difference, sum_range_prefix_mul_difference]
    simp only [z₁ _ hω, z₂ _ hω, mul_zero, sub_zero]
    rw [← sum_add_distrib]
    exact sum_congr rfl fun t _ => (hw (ω t)).symm
  rw [integral_congr_ae he, hsum]

private theorem integrable_cross_path (n : ℕ)
    (a b : Finpartition (Finset.univ : Finset (Fin n)) → ℝ) :
    Integrable (fun ω : ℕ → Finpartition (Finset.univ : Finset (Fin n)) =>
      (∑ k ∈ range (n - 1), a (ω k)) * (∑ k ∈ range (n - 1), b (ω k)) +
        ∑ k ∈ range (n - 1), a (ω k) * b (ω k))
      ((partitionChain (Fin n)).jumpChain.pathLaw ⊥) := by
  have he : (fun ω : ℕ → Finpartition (Finset.univ : Finset (Fin n)) =>
      (∑ k ∈ range (n - 1), a (ω k)) * (∑ k ∈ range (n - 1), b (ω k)) +
        ∑ k ∈ range (n - 1), a (ω k) * b (ω k)) =
      fun ω => (∑ i ∈ range (n - 1), ∑ j ∈ range (n - 1), a (ω i) * b (ω j)) +
        ∑ k ∈ range (n - 1), a (ω k) * b (ω k) := by
    funext ω
    rw [Finset.sum_mul_sum]
  rw [he]
  exact (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    partitionChain_integrable_eval_mul n ⊥ i j a b).add
    (integrable_finsetSum _ fun k _ => partitionChain_integrable_eval_mul n ⊥ k k a b)

theorem lintegral_kingmanFiniteReward_sq (n : ℕ)
    (c : Finpartition (Finset.univ : Finset (Fin n)) → ℝ) (hc : ∀ π, 0 ≤ c π) :
    ∫⁻ h, ENNReal.ofReal (kingmanFiniteReward n c h ^ 2)
      ∂(partitionChain (Fin n)).jumpHoldLaw ⊥ =
    ENNReal.ofReal (∫ ω, ((∑ k ∈ range (n - 1), kingmanJumpReward n c (ω k)) *
        (∑ k ∈ range (n - 1), kingmanJumpReward n c (ω k)) +
      ∑ k ∈ range (n - 1), kingmanJumpReward n c (ω k) * kingmanJumpReward n c (ω k))
      ∂(partitionChain (Fin n)).jumpChain.pathLaw ⊥) := by
  classical
  have h1 : (∫⁻ h, ENNReal.ofReal (kingmanFiniteReward n c h ^ 2)
      ∂(partitionChain (Fin n)).jumpHoldLaw ⊥) =
      ∫⁻ h, ((partitionChain (Fin n)).costBefore (coalescedPartitions (Fin n)) c h) ^ 2
        ∂(partitionChain (Fin n)).jumpHoldLaw ⊥ := by
    apply lintegral_congr_ae
    filter_upwards [partition_costBefore_eq_finite_clamped_sum n c hc] with h hh
    rw [hh]
    exact ENNReal.ofReal_pow (kingmanFiniteReward_nonneg n c hc h) 2
  have hnn : ∀ᵐ ω ∂(partitionChain (Fin n)).jumpChain.pathLaw ⊥,
      0 ≤ (∑ k ∈ range (n - 1), kingmanJumpReward n c (ω k)) *
        (∑ k ∈ range (n - 1), kingmanJumpReward n c (ω k)) +
      ∑ k ∈ range (n - 1), kingmanJumpReward n c (ω k) * kingmanJumpReward n c (ω k) :=
    Eventually.of_forall fun ω => add_nonneg (mul_self_nonneg _)
      (sum_nonneg fun k _ => mul_self_nonneg _)
  rw [h1, lintegral_partition_costBefore_sq n c hc,
    ofReal_integral_eq_lintegral_ofReal (integrable_cross_path n _ _) hnn]
  apply lintegral_congr
  intro ω
  have e1 := Fin.sum_univ_eq_sum_range (fun k => kingmanJumpReward n c (ω k)) (n - 1)
  have e2 := Fin.sum_univ_eq_sum_range (fun k => kingmanJumpReward n c (ω k) ^ 2) (n - 1)
  change ENNReal.ofReal ((∑ k : Fin (n - 1), kingmanJumpReward n c (ω k.val)) ^ 2 +
    ∑ k : Fin (n - 1), kingmanJumpReward n c (ω k.val) ^ 2) = _
  rw [e1, e2]
  simp only [pow_two]

theorem integrable_kingmanFiniteReward_sq (n : ℕ)
    (c : Finpartition (Finset.univ : Finset (Fin n)) → ℝ) (hc : ∀ π, 0 ≤ c π) :
    Integrable (fun h => kingmanFiniteReward n c h ^ 2)
      ((partitionChain (Fin n)).jumpHoldLaw ⊥) := by
  apply (lintegral_ofReal_ne_top_iff_integrable
    ((measurable_kingmanFiniteReward n _).pow_const 2).aestronglyMeasurable
    (Eventually.of_forall fun h => sq_nonneg _)).mp
  rw [lintegral_kingmanFiniteReward_sq n c hc]
  exact ENNReal.ofReal_ne_top

theorem integral_kingmanFiniteReward_sq (n : ℕ)
    (c : Finpartition (Finset.univ : Finset (Fin n)) → ℝ) (hc : ∀ π, 0 ≤ c π) :
    ∫ h, kingmanFiniteReward n c h ^ 2 ∂(partitionChain (Fin n)).jumpHoldLaw ⊥ =
    ∫ ω, ((∑ k ∈ range (n - 1), kingmanJumpReward n c (ω k)) *
        (∑ k ∈ range (n - 1), kingmanJumpReward n c (ω k)) +
      ∑ k ∈ range (n - 1), kingmanJumpReward n c (ω k) * kingmanJumpReward n c (ω k))
      ∂(partitionChain (Fin n)).jumpChain.pathLaw ⊥ := by
  have hp : 0 ≤ ∫ ω, ((∑ k ∈ range (n - 1), kingmanJumpReward n c (ω k)) *
        (∑ k ∈ range (n - 1), kingmanJumpReward n c (ω k)) +
      ∑ k ∈ range (n - 1), kingmanJumpReward n c (ω k) * kingmanJumpReward n c (ω k))
      ∂(partitionChain (Fin n)).jumpChain.pathLaw ⊥ :=
    integral_nonneg fun ω => add_nonneg (mul_self_nonneg _)
      (sum_nonneg fun k _ => mul_self_nonneg _)
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun h => sq_nonneg _)
    ((measurable_kingmanFiniteReward n _).pow_const 2).aestronglyMeasurable,
    lintegral_kingmanFiniteReward_sq n c hc, ENNReal.toReal_ofReal hp]

private theorem kingmanFiniteReward_add (n : ℕ)
    (c₁ c₂ : Finpartition (Finset.univ : Finset (Fin n)) → ℝ)
    (h : KingmanMutationHistory n) :
    kingmanFiniteReward n (fun π => c₁ π + c₂ π) h =
      kingmanFiniteReward n c₁ h + kingmanFiniteReward n c₂ h := by
  unfold kingmanFiniteReward
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> ring

private theorem kingmanJumpReward_add (n : ℕ)
    (c₁ c₂ : Finpartition (Finset.univ : Finset (Fin n)) → ℝ)
    (π : Finpartition (Finset.univ : Finset (Fin n))) :
    kingmanJumpReward n (fun π => c₁ π + c₂ π) π =
      kingmanJumpReward n c₁ π + kingmanJumpReward n c₂ π := by
  unfold kingmanJumpReward
  split_ifs <;> ring

theorem integrable_kingmanFiniteReward_mul (n : ℕ)
    (c₁ c₂ : Finpartition (Finset.univ : Finset (Fin n)) → ℝ)
    (hc₁ : ∀ π, 0 ≤ c₁ π) (hc₂ : ∀ π, 0 ≤ c₂ π) :
    Integrable (fun h => kingmanFiniteReward n c₁ h * kingmanFiniteReward n c₂ h)
      ((partitionChain (Fin n)).jumpHoldLaw ⊥) := by
  have hs := integrable_kingmanFiniteReward_sq n (fun π => c₁ π + c₂ π)
    (fun π => add_nonneg (hc₁ π) (hc₂ π))
  have i1 := integrable_kingmanFiniteReward_sq n c₁ hc₁
  have i2 := integrable_kingmanFiniteReward_sq n c₂ hc₂
  have he : (fun h => kingmanFiniteReward n c₁ h * kingmanFiniteReward n c₂ h) =
      fun h => (1 / 2 : ℝ) * ((kingmanFiniteReward n (fun π => c₁ π + c₂ π) h ^ 2 -
        kingmanFiniteReward n c₁ h ^ 2) - kingmanFiniteReward n c₂ h ^ 2) := by
    funext h
    rw [kingmanFiniteReward_add]
    ring
  rw [he]
  exact ((hs.sub i1).sub i2).const_mul _

theorem integral_kingmanFiniteReward_mul (n : ℕ)
    (c₁ c₂ : Finpartition (Finset.univ : Finset (Fin n)) → ℝ)
    (hc₁ : ∀ π, 0 ≤ c₁ π) (hc₂ : ∀ π, 0 ≤ c₂ π) :
    ∫ h, kingmanFiniteReward n c₁ h * kingmanFiniteReward n c₂ h
      ∂(partitionChain (Fin n)).jumpHoldLaw ⊥ =
    ∫ ω, ((∑ k ∈ Finset.range (n - 1), kingmanJumpReward n c₁ (ω k)) *
        (∑ k ∈ Finset.range (n - 1), kingmanJumpReward n c₂ (ω k)) +
      ∑ k ∈ Finset.range (n - 1), kingmanJumpReward n c₁ (ω k) * kingmanJumpReward n c₂ (ω k))
      ∂(partitionChain (Fin n)).jumpChain.pathLaw ⊥ := by
  have hs := integral_kingmanFiniteReward_sq n (fun π => c₁ π + c₂ π)
    (fun π => add_nonneg (hc₁ π) (hc₂ π))
  have s1 := integral_kingmanFiniteReward_sq n c₁ hc₁
  have s2 := integral_kingmanFiniteReward_sq n c₂ hc₂
  have i1 := integrable_kingmanFiniteReward_sq n c₁ hc₁
  have i2 := integrable_kingmanFiniteReward_sq n c₂ hc₂
  have i12 : Integrable (fun h => kingmanFiniteReward n c₁ h ^ 2 +
      kingmanFiniteReward n c₂ h ^ 2) ((partitionChain (Fin n)).jumpHoldLaw ⊥) := i1.add i2
  have im := integrable_kingmanFiniteReward_mul n c₁ c₂ hc₁ hc₂
  have im2 : Integrable (fun h => 2 * (kingmanFiniteReward n c₁ h *
      kingmanFiniteReward n c₂ h)) ((partitionChain (Fin n)).jumpHoldLaw ⊥) := im.const_mul 2
  have hL : ∫ h, kingmanFiniteReward n (fun π => c₁ π + c₂ π) h ^ 2
        ∂(partitionChain (Fin n)).jumpHoldLaw ⊥ =
      (∫ h, kingmanFiniteReward n c₁ h ^ 2 ∂(partitionChain (Fin n)).jumpHoldLaw ⊥) +
      (∫ h, kingmanFiniteReward n c₂ h ^ 2 ∂(partitionChain (Fin n)).jumpHoldLaw ⊥) +
      2 * ∫ h, kingmanFiniteReward n c₁ h * kingmanFiniteReward n c₂ h
        ∂(partitionChain (Fin n)).jumpHoldLaw ⊥ := by
    have he : (fun h => kingmanFiniteReward n (fun π => c₁ π + c₂ π) h ^ 2) =
        fun h => (kingmanFiniteReward n c₁ h ^ 2 + kingmanFiniteReward n c₂ h ^ 2) +
          2 * (kingmanFiniteReward n c₁ h * kingmanFiniteReward n c₂ h) := by
      funext h
      rw [kingmanFiniteReward_add]
      ring
    rw [he, integral_add i12 im2, integral_add i1 i2, integral_const_mul]
  have p1 := integrable_cross_path n (kingmanJumpReward n c₁) (kingmanJumpReward n c₁)
  have p2 := integrable_cross_path n (kingmanJumpReward n c₂) (kingmanJumpReward n c₂)
  have p3 := integrable_cross_path n (kingmanJumpReward n c₁) (kingmanJumpReward n c₂)
  have p12 : Integrable (fun ω : ℕ → Finpartition (Finset.univ : Finset (Fin n)) =>
      ((∑ k ∈ range (n - 1), kingmanJumpReward n c₁ (ω k)) *
          (∑ k ∈ range (n - 1), kingmanJumpReward n c₁ (ω k)) +
        ∑ k ∈ range (n - 1), kingmanJumpReward n c₁ (ω k) * kingmanJumpReward n c₁ (ω k)) +
      ((∑ k ∈ range (n - 1), kingmanJumpReward n c₂ (ω k)) *
          (∑ k ∈ range (n - 1), kingmanJumpReward n c₂ (ω k)) +
        ∑ k ∈ range (n - 1), kingmanJumpReward n c₂ (ω k) * kingmanJumpReward n c₂ (ω k)))
      ((partitionChain (Fin n)).jumpChain.pathLaw ⊥) := p1.add p2
  have p32 := p3.const_mul 2
  have hR : ∫ ω, ((∑ k ∈ range (n - 1), kingmanJumpReward n (fun π => c₁ π + c₂ π) (ω k)) *
        (∑ k ∈ range (n - 1), kingmanJumpReward n (fun π => c₁ π + c₂ π) (ω k)) +
      ∑ k ∈ range (n - 1), kingmanJumpReward n (fun π => c₁ π + c₂ π) (ω k) *
        kingmanJumpReward n (fun π => c₁ π + c₂ π) (ω k))
      ∂(partitionChain (Fin n)).jumpChain.pathLaw ⊥ =
      (∫ ω, ((∑ k ∈ range (n - 1), kingmanJumpReward n c₁ (ω k)) *
          (∑ k ∈ range (n - 1), kingmanJumpReward n c₁ (ω k)) +
        ∑ k ∈ range (n - 1), kingmanJumpReward n c₁ (ω k) * kingmanJumpReward n c₁ (ω k))
        ∂(partitionChain (Fin n)).jumpChain.pathLaw ⊥) +
      (∫ ω, ((∑ k ∈ range (n - 1), kingmanJumpReward n c₂ (ω k)) *
          (∑ k ∈ range (n - 1), kingmanJumpReward n c₂ (ω k)) +
        ∑ k ∈ range (n - 1), kingmanJumpReward n c₂ (ω k) * kingmanJumpReward n c₂ (ω k))
        ∂(partitionChain (Fin n)).jumpChain.pathLaw ⊥) +
      2 * ∫ ω, ((∑ k ∈ range (n - 1), kingmanJumpReward n c₁ (ω k)) *
          (∑ k ∈ range (n - 1), kingmanJumpReward n c₂ (ω k)) +
        ∑ k ∈ range (n - 1), kingmanJumpReward n c₁ (ω k) * kingmanJumpReward n c₂ (ω k))
        ∂(partitionChain (Fin n)).jumpChain.pathLaw ⊥ := by
    simp_rw [kingmanJumpReward_add, cross_add]
    rw [integral_add p12 p32, integral_add p1 p2, integral_const_mul]
  linarith

theorem integrable_kingmanFiniteDiversityReward_mul_length {n : ℕ} (hn : 2 ≤ n) :
    Integrable (fun h => kingmanFiniteReward n (kingmanDiversityReward n) h *
        kingmanFiniteReward n (fun π => (π.parts.card : ℝ)) h)
      ((partitionChain (Fin n)).jumpHoldLaw ⊥) :=
  integrable_kingmanFiniteReward_mul n _ _ (kingmanDiversityReward_nonneg hn)
    (fun π => Nat.cast_nonneg π.parts.card)

theorem integral_kingmanFiniteDiversityReward_mul_length {n : ℕ} (hn : 2 ≤ n) :
    ∫ h, kingmanFiniteReward n (kingmanDiversityReward n) h *
        kingmanFiniteReward n (fun π => (π.parts.card : ℝ)) h
      ∂(partitionChain (Fin n)).jumpHoldLaw ⊥ =
    2 * (((n : ℝ) + 2) / n + 2 * (tajimaA1 n : ℝ)) := by
  have hn0 : 0 < n := by omega
  rw [integral_kingmanFiniteReward_mul n _ _ (kingmanDiversityReward_nonneg hn)
      (fun π => Nat.cast_nonneg π.parts.card),
    partitionChain_integral_cross_jumpReward n
      (kingmanJumpReward n (kingmanDiversityReward n))
      (kingmanJumpReward n (fun π => (π.parts.card : ℝ)))
      (kingmanDiversityReward n) (kingmanLengthPotential n)
      (kingmanDiversityLengthPotential n)
      (kingmanDiversityReward_jumpReward_drift hn0)
      (kingmanLengthPotential_jump_drift n)
      (kingmanDiversityLengthPotential_jump_drift hn0)
      (kingmanDiversityReward_coalesced hn0)
      (kingmanLengthPotential_coalesced n)
      (kingmanDiversityLengthPotential_coalesced hn0),
    kingmanDiversityLengthPotential_bot hn]

end Rhone.Statistics
