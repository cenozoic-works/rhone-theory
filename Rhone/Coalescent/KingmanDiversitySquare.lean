/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.KingmanDiversityMoments
public import Rhone.Coalescent.KingmanPartitionRewardMoments

/-!
# Genealogy reward square for Kingman pairwise diversity

Source: kingman1982, sec. 1, eq. (1.1)–(1.4), (1.7); tajima1989, p. 585, eq. (6)–(7). -/

@[expose] public section
namespace Rhone.Coalescent
open MeasureTheory ProbabilityTheory Finset Rhone.Combinatorics MarkovChain Filter

noncomputable def kingmanDiversityJumpReward (n : ℕ)
    (π : Finpartition (Finset.univ : Finset (Fin n))) : ℝ :=
  if π ∈ coalescedPartitions (Fin n) then 0
    else kingmanDiversityReward n π / (partitionChain (Fin n)).rate π

theorem integral_kingmanDiversityJumpReward_mul_drift {n : ℕ} (hn : 0 < n)
    (x : Finpartition (Finset.univ : Finset (Fin n))) (k t : ℕ) (hkt : k ≤ t) :
    ∫ ω, kingmanDiversityJumpReward n (ω k) * kingmanDiversityJumpReward n (ω t)
      ∂(partitionChain (Fin n)).jumpChain.pathLaw x =
    ∫ ω, kingmanDiversityJumpReward n (ω k) *
      (kingmanDiversityReward n (ω t) - kingmanDiversityReward n (ω (t + 1)))
      ∂(partitionChain (Fin n)).jumpChain.pathLaw x := by
  have h := partitionChain_integral_eval_difference n x k (t - k)
    (kingmanDiversityJumpReward n) (kingmanDiversityReward n)
  have hadd : k + (t - k) = t := by omega
  rw [hadd] at h
  rw [h]
  apply integral_congr_ae
  filter_upwards [] with ω
  rw [kingmanDiversityReward_jump_drift hn]
  rfl

theorem integral_kingmanDiversityJumpReward_square {n : ℕ} (hn : 2 ≤ n) :
    ∫ ω, ((∑ k ∈ Finset.range (n - 1), kingmanDiversityJumpReward n (ω k)) ^ 2 +
      ∑ k ∈ Finset.range (n - 1), kingmanDiversityJumpReward n (ω k) ^ 2)
      ∂(partitionChain (Fin n)).jumpChain.pathLaw ⊥ =
    kingmanDiversitySquarePotential n ⊥ := by
  classical
  let C := (partitionChain (Fin n)).jumpChain
  let g := kingmanDiversityJumpReward n
  let u := kingmanDiversityReward n
  let v := kingmanDiversitySquarePotential n
  let T := n - 1
  have hn0 : 0 < n := by omega
  have hi (k t : ℕ) : Integrable (fun ω => g (ω k) * g (ω t)) (C.pathLaw ⊥) :=
    partitionChain_integrable_eval_mul n ⊥ k t g g
  have hd (k t : ℕ) : Integrable
      (fun ω => g (ω k) * (u (ω t) - u (ω (t + 1)))) (C.pathLaw ⊥) := by
    have he : (fun ω : ℕ → Finpartition (Finset.univ : Finset (Fin n)) =>
        g (ω k) * (u (ω t) - u (ω (t + 1)))) =
        (fun ω => g (ω k) * u (ω t) - g (ω k) * u (ω (t + 1))) := by
      funext ω; ring
    rw [he]
    exact (partitionChain_integrable_eval_mul n ⊥ k t g u).sub
      (partitionChain_integrable_eval_mul n ⊥ k (t + 1) g u)
  have hprefix :
      (∫ ω, ∑ t ∈ range T, ∑ k ∈ range (t + 1), g (ω k) * g (ω t) ∂C.pathLaw ⊥) =
      ∫ ω, ∑ t ∈ range T, ∑ k ∈ range (t + 1),
        g (ω k) * (u (ω t) - u (ω (t + 1))) ∂C.pathLaw ⊥ := by
    rw [integral_finsetSum _ (fun t _ => integrable_finsetSum _ (fun k _ => hi k t)),
      integral_finsetSum _ (fun t _ => integrable_finsetSum _ (fun k _ => hd k t))]
    apply sum_congr rfl
    intro t ht
    rw [integral_finsetSum _ (fun k _ => hi k t),
      integral_finsetSum _ (fun k _ => hd k t)]
    apply sum_congr rfl
    intro k hk
    exact integral_kingmanDiversityJumpReward_mul_drift hn0 ⊥ k t (by
      have := mem_range.mp hk; omega)
  have hterminal : ∀ᵐ ω ∂C.pathLaw ⊥, u (ω T) = 0 ∧ v (ω T) = 0 := by
    filter_upwards [partition_path_terminal_coalesced n] with ω hω
    simp [u, v, T, kingmanDiversityReward, kingmanDiversitySquarePotential,
      kingmanBlockMassMoment_coalesced hn0 _ _ hω]
  have hproduct (π : Finpartition (Finset.univ : Finset (Fin n))) :
      2 * g π * u π = v π - C.expect v π := by
    rw [kingmanDiversitySquarePotential_jump_drift hn0]
    by_cases hπ : π ∈ coalescedPartitions (Fin n)
    · simp [g, kingmanDiversityJumpReward, hπ]
    · simp only [g, kingmanDiversityJumpReward, hπ, ↓reduceIte]
      ring
  have hsum : ∫ ω, ∑ t ∈ range T, (v (ω t) - C.expect v (ω t)) ∂C.pathLaw ⊥ =
      v ⊥ := by
    have hint (t : ℕ) : Integrable
        (fun ω => v (ω t) - C.expect v (ω t)) (C.pathLaw ⊥) := by
      convert (C.integrable_eval v t ⊥).sub (C.integrable_eval (C.expect v) t ⊥) using 1
    rw [integral_finsetSum _ (fun t _ => hint t)]
    have he (t : ℕ) :
        (∫ ω, v (ω t) - C.expect v (ω t) ∂C.pathLaw ⊥) =
        (∫ ω, v (ω t) - v (ω (t + 1)) ∂C.pathLaw ⊥) := by
      rw [integral_sub (C.integrable_eval v t ⊥) (C.integrable_eval (C.expect v) t ⊥),
        integral_sub (C.integrable_eval v t ⊥) (C.integrable_eval v (t + 1) ⊥)]
      simp only [C.integral_eval, C.expectN_succ']
    simp_rw [he]
    have hint' (t : ℕ) : Integrable
        (fun ω => v (ω t) - v (ω (t + 1))) (C.pathLaw ⊥) := by
      convert (C.integrable_eval v t ⊥).sub (C.integrable_eval v (t + 1) ⊥) using 1
    rw [← integral_finsetSum _ (fun t _ => hint' t)]
    simp_rw [sum_range_sub']
    have heterm : (fun ω => v (ω 0) - v (ω T)) =ᵐ[C.pathLaw ⊥]
        (fun ω => v (ω 0)) := by
      filter_upwards [hterminal] with ω hω
      rw [hω.2, sub_zero]
    rw [integral_congr_ae heterm, C.integral_eval, C.expectN_zero]
  change (∫ ω, ((∑ k ∈ range T, g (ω k)) ^ 2 +
    ∑ k ∈ range T, g (ω k) ^ 2) ∂C.pathLaw ⊥) = _
  simp_rw [sum_range_square_add_sq, sum_mul]
  rw [integral_const_mul, hprefix, ← integral_const_mul]
  have he : (fun ω => 2 * ∑ t ∈ range T, ∑ k ∈ range (t + 1),
      g (ω k) * (u (ω t) - u (ω (t + 1)))) =ᵐ[C.pathLaw ⊥]
      (fun ω => ∑ t ∈ range T, (v (ω t) - C.expect v (ω t))) := by
    filter_upwards [hterminal] with ω hω
    simp_rw [← sum_mul]
    rw [sum_range_prefix_mul_difference, hω.1, mul_zero, sub_zero, mul_sum]
    apply sum_congr rfl
    intro t _
    simpa only [mul_assoc] using hproduct (ω t)
  rw [integral_congr_ae he, hsum]

theorem lintegral_kingmanDiversityReward_sq {n : ℕ} (hn : 2 ≤ n) :
    ∫⁻ h, ((partitionChain (Fin n)).costBefore (coalescedPartitions (Fin n))
      (kingmanDiversityReward n) h) ^ 2 ∂(partitionChain (Fin n)).jumpHoldLaw ⊥ =
    ENNReal.ofReal (kingmanDiversitySquarePotential n ⊥) := by
  classical
  rw [lintegral_partition_costBefore_sq n (kingmanDiversityReward n)
    (kingmanDiversityReward_nonneg hn)]
  let C := (partitionChain (Fin n)).jumpChain
  let g := kingmanDiversityJumpReward n
  let F := fun ω : ℕ → Finpartition (Finset.univ : Finset (Fin n)) =>
    (∑ k ∈ range (n - 1), g (ω k)) ^ 2 + ∑ k ∈ range (n - 1), g (ω k) ^ 2
  have he : F = (fun ω => 2 * ∑ t ∈ range (n - 1),
      ∑ k ∈ range (t + 1), g (ω k) * g (ω t)) := by
    funext ω
    simp only [F, sum_range_square_add_sq, sum_mul]
  have hint : Integrable F (C.pathLaw ⊥) := by
    rw [he]
    exact (integrable_finsetSum _ (fun t _ => integrable_finsetSum _ (fun k _ =>
      partitionChain_integrable_eval_mul n ⊥ k t g g))).const_mul 2
  have hnn : ∀ᵐ ω ∂C.pathLaw ⊥, 0 ≤ F ω := Eventually.of_forall fun ω =>
    add_nonneg (sq_nonneg _) (sum_nonneg fun k _ => sq_nonneg _)
  have hi := integral_kingmanDiversityJumpReward_square hn
  change (∫ ω, F ω ∂C.pathLaw ⊥) = kingmanDiversitySquarePotential n ⊥ at hi
  rw [← hi, ofReal_integral_eq_lintegral_ofReal hint hnn]
  apply lintegral_congr
  intro ω
  simp only [F, g, kingmanDiversityJumpReward]
  rw [← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range]

end Rhone.Coalescent
