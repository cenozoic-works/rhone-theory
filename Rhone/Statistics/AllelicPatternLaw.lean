/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Statistics.KillPatternWeight
public import Rhone.Coalescent.TajimaVarianceModel
public import Rhone.MarkovChain.PathProduct
public import Rhone.Coalescent.KingmanPartitionJumpKernel

/-!
# Mutated blocks, marking rates, and kill-level integrands for allelic patterns

Source: tajima1989, pp. 588–589, eq. (39)–(42). -/

@[expose] public section
namespace Rhone.Statistics
open MeasureTheory ProbabilityTheory Finset MarkovChain Coalescent Rhone.Combinatorics
open scoped NNReal

variable {n : ℕ}

def mutatedBlocks (n : ℕ) (m : KingmanMutationBranch n → ℕ) (k : Fin (n - 1)) :
    Finset (Finset (Fin n)) :=
  univ.filter fun B => m (k, B) ≠ 0

theorem mem_mutatedBlocks {m : KingmanMutationBranch n → ℕ} {k : Fin (n - 1)}
    {B : Finset (Fin n)} : B ∈ mutatedBlocks n m k ↔ m (k, B) ≠ 0 := by
  simp only [mutatedBlocks, mem_filter, mem_univ, true_and]

noncomputable def markRate (θ : ℝ≥0) (π : Finpartition (univ : Finset (Fin n)))
    (B : Finset (Fin n)) (t : ℝ) : ℝ :=
  if B ∈ π.parts ∧ 1 < π.parts.card then
    max 0 ((θ : ℝ) / 2 * (t / (partitionChain (Fin n)).rate π))
  else 0

theorem coe_kingmanBranchMutationRate (θ : ℝ≥0)
    (ω : ℕ → Finpartition (univ : Finset (Fin n))) (e : ℕ → ℝ) (k : Fin (n - 1))
    (B : Finset (Fin n)) :
    (kingmanBranchMutationRate n θ (ω, e) (k, B) : ℝ) = markRate θ (ω k) B (e k) := rfl

theorem kingmanBranchMutationKernel_real_mutatedBlocks (θ : ℝ≥0)
    (h : KingmanMutationHistory n) (z : Fin (n - 1) → Finset (Finset (Fin n))) :
    (kingmanBranchMutationKernel n θ h).real {m | mutatedBlocks n m = z} =
      ∏ k : Fin (n - 1), ∏ B : Finset (Fin n),
        (if B ∈ z k then 1 - Real.exp (-(kingmanBranchMutationRate n θ h (k, B) : ℝ))
          else Real.exp (-(kingmanBranchMutationRate n θ h (k, B) : ℝ))) := by
  have hset : {m : KingmanMutationBranch n → ℕ | mutatedBlocks n m = z} =
      Set.pi Set.univ (fun br : KingmanMutationBranch n =>
        if br.2 ∈ z br.1 then ({0}ᶜ : Set ℕ) else {0}) := by
    ext m
    constructor
    · intro hm br _
      have hbr : br.2 ∈ z br.1 ↔ m br ≠ 0 := by
        rw [← (show mutatedBlocks n m = z from hm)]
        exact mem_mutatedBlocks
      change m br ∈ (if br.2 ∈ z br.1 then ({0}ᶜ : Set ℕ) else {0})
      by_cases hb : br.2 ∈ z br.1
      · rw [ite_eq_left hb]
        exact hbr.1 hb
      · rw [ite_eq_right hb]
        exact not_not.1 (mt hbr.2 hb)
    · intro hm
      change mutatedBlocks n m = z
      funext k
      ext B
      have hkB : m (k, B) ∈ (if B ∈ z k then ({0}ᶜ : Set ℕ) else {0}) :=
        hm (k, B) (Set.mem_univ _)
      rw [mem_mutatedBlocks]
      by_cases hb : B ∈ z k
      · rw [ite_eq_left hb] at hkB
        exact ⟨fun _ => hb, fun _ => hkB⟩
      · rw [ite_eq_right hb] at hkB
        exact ⟨fun h0 => absurd hkB h0, fun h1 => absurd h1 hb⟩
  change (Measure.pi (fun b : KingmanMutationBranch n =>
    poissonMeasure (kingmanBranchMutationRate n θ h b))).real _ = _
  rw [hset, measureReal_def, Measure.pi_pi, ENNReal.toReal_prod, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun k _ => Finset.prod_congr rfl fun B _ => ?_
  have h0 : (poissonMeasure (kingmanBranchMutationRate n θ h (k, B))).real {0} =
      Real.exp (-(kingmanBranchMutationRate n θ h (k, B) : ℝ)) := by
    rw [poissonMeasure_real_singleton]
    simp
  change ((poissonMeasure (kingmanBranchMutationRate n θ h (k, B)))
    (if B ∈ z k then ({0}ᶜ : Set ℕ) else {0})).toReal = _
  by_cases hb : B ∈ z k
  · rw [ite_eq_left hb, ite_eq_left hb, ← measureReal_def,
      probReal_compl_eq_one_sub (measurableSet_singleton 0), h0]
  · rw [ite_eq_right hb, ite_eq_right hb, ← measureReal_def, h0]

noncomputable def killLevelIntegrand (θ : ℝ≥0) (π : Finpartition (univ : Finset (Fin n)))
    (D : Finset (Finset (Fin n))) (t : ℝ) : ℝ :=
  if 1 < π.parts.card then
    (if D ⊆ π.parts then
      (1 - Real.exp (-((θ : ℝ) / ((π.parts.card : ℝ) * ((π.parts.card : ℝ) - 1)) *
          max 0 t))) ^ D.card *
        Real.exp (-((θ : ℝ) / ((π.parts.card : ℝ) * ((π.parts.card : ℝ) - 1)) *
          max 0 t)) ^ (π.parts.card - D.card)
    else 0)
  else (if D = ∅ then 1 else 0)

noncomputable def killLevelFactor (θ : ℝ) (π : Finpartition (univ : Finset (Fin n)))
    (D : Finset (Finset (Fin n))) : ℝ :=
  if 1 < π.parts.card then
    (if D ⊆ π.parts then
      killPatternWeight (θ / ((π.parts.card : ℝ) * ((π.parts.card : ℝ) - 1))) D.card
        (π.parts.card - D.card)
    else 0)
  else (if D = ∅ then 1 else 0)

theorem killRate_nonneg (θ : ℝ≥0) (m : ℕ) : 0 ≤ (θ : ℝ) / ((m : ℝ) * ((m : ℝ) - 1)) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have h1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    exact div_nonneg θ.coe_nonneg (mul_nonneg (by linarith) (by linarith))

theorem prod_markFactor (θ : ℝ≥0) (π : Finpartition (univ : Finset (Fin n)))
    (D : Finset (Finset (Fin n))) (t : ℝ) :
    ∏ B : Finset (Fin n), (if B ∈ D then 1 - Real.exp (-(markRate θ π B t))
      else Real.exp (-(markRate θ π B t))) = killLevelIntegrand θ π D t := by
  unfold killLevelIntegrand
  by_cases hm : 1 < π.parts.card
  · rw [ite_eq_left hm]
    set x : ℝ := (θ : ℝ) / ((π.parts.card : ℝ) * ((π.parts.card : ℝ) - 1)) * max 0 t with hx
    have hrate : ∀ B, markRate θ π B t = if B ∈ π.parts then x else 0 := by
      intro B
      unfold markRate
      by_cases hB : B ∈ π.parts
      · rw [ite_eq_left ⟨hB, hm⟩, ite_eq_left hB, partitionChain_rate, hx]
        have hβ := killRate_nonneg θ π.parts.card
        rw [mul_max_of_nonneg _ _ hβ, mul_zero]
        congr 1
        have h1 : (1 : ℝ) < π.parts.card := by exact_mod_cast hm
        have hne : (π.parts.card : ℝ) * ((π.parts.card : ℝ) - 1) ≠ 0 :=
          mul_ne_zero (by linarith) (by linarith)
        unfold coalRate
        push_cast
        field_simp
      · rw [ite_eq_right (fun h => hB h.1), ite_eq_right hB]
    simp only [hrate]
    by_cases hD : D ⊆ π.parts
    · rw [ite_eq_left hD, ← Finset.prod_subset (Finset.subset_univ π.parts) (by
        intro B _ hB
        rw [ite_eq_right (fun h => hB (hD h)), ite_eq_right hB]
        simp)]
      have hin : ∀ B ∈ π.parts, (if B ∈ D then 1 - Real.exp (-(if B ∈ π.parts then x else 0))
          else Real.exp (-(if B ∈ π.parts then x else 0))) =
          if B ∈ D then 1 - Real.exp (-x) else Real.exp (-x) := by
        intro B hB
        rw [ite_eq_left hB]
      rw [Finset.prod_congr rfl hin, Finset.prod_ite, Finset.prod_const, Finset.prod_const]
      have h1 : π.parts.filter (fun B => B ∈ D) = D := by
        ext B
        simp only [mem_filter]
        exact ⟨fun h => h.2, fun h => ⟨hD h, h⟩⟩
      have h2 := Finset.card_filter_add_card_filter_not (s := π.parts) (fun B => B ∈ D)
      rw [h1] at h2
      rw [h1, show (π.parts.filter fun B => ¬ B ∈ D).card = π.parts.card - D.card by omega]
    · rw [ite_eq_right hD]
      obtain ⟨B, hBD, hBπ⟩ := Finset.not_subset.1 hD
      apply Finset.prod_eq_zero (mem_univ B)
      rw [ite_eq_left hBD, ite_eq_right hBπ]
      simp
  · rw [ite_eq_right hm]
    have hrate : ∀ B, markRate θ π B t = 0 := fun B => by
      unfold markRate
      rw [ite_eq_right (fun h => hm h.2)]
    simp only [hrate, neg_zero, Real.exp_zero, sub_self]
    by_cases hD : D = ∅
    · subst hD
      simp
    · rw [ite_eq_right hD]
      obtain ⟨B, hB⟩ := Finset.nonempty_iff_ne_empty.2 hD
      apply Finset.prod_eq_zero (mem_univ B)
      rw [ite_eq_left hB]

theorem measurable_killLevelIntegrand (θ : ℝ≥0) (π : Finpartition (univ : Finset (Fin n)))
    (D : Finset (Finset (Fin n))) : Measurable (killLevelIntegrand θ π D) := by
  unfold killLevelIntegrand
  by_cases hm : 1 < π.parts.card
  · by_cases hD : D ⊆ π.parts
    · simp only [hm, hD, ↓reduceIte]
      fun_prop
    · simp only [hm, hD, ↓reduceIte]
      exact measurable_const
  · simp only [hm, ↓reduceIte]
    exact measurable_const

theorem integral_killLevelIntegrand (θ : ℝ≥0) (π : Finpartition (univ : Finset (Fin n)))
    (D : Finset (Finset (Fin n))) :
    ∫ t, killLevelIntegrand θ π D t ∂expMeasure 1 = killLevelFactor (θ : ℝ) π D := by
  unfold killLevelIntegrand killLevelFactor
  by_cases hm : 1 < π.parts.card
  · by_cases hD : D ⊆ π.parts
    · simp only [hm, hD, ↓reduceIte]
      exact integral_killPattern (killRate_nonneg θ π.parts.card) _ _
    · simp only [hm, hD, ↓reduceIte, integral_zero]
  · simp only [hm, ↓reduceIte, integral_const, probReal_univ, smul_eq_mul, one_mul]

theorem integral_clockLaw_prod (N : ℕ) (g : Fin N → ℝ → ℝ) (hg : ∀ k, Measurable (g k)) :
    ∫ e, ∏ k : Fin N, g k (e k) ∂clockLaw = ∏ k : Fin N, ∫ t, g k t ∂expMeasure 1 := by
  have hind : iIndepFun (fun (k : Fin N) (e : ℕ → ℝ) => e k.val) clockLaw :=
    (iIndepFun_infinitePi (P := fun _ : ℕ => expMeasure 1) (X := fun _ => id)
      (fun _ => measurable_id)).precomp Fin.val_injective
  have hprod := hind.integral_prod_comp (𝕜 := ℝ) (f := g)
    (fun k => (measurable_pi_apply k.val).aemeasurable)
    (fun k => (hg k).aestronglyMeasurable)
  simp only [Finset.prod_apply, Function.comp_apply] at hprod
  rw [hprod]
  exact Finset.prod_congr rfl fun k _ => integral_clockLaw_eval k.val (hg k)

theorem integral_clockLaw_kernel_mutatedBlocks (θ : ℝ≥0)
    (ω : ℕ → Finpartition (univ : Finset (Fin n)))
    (z : Fin (n - 1) → Finset (Finset (Fin n))) :
    ∫ e, (kingmanBranchMutationKernel n θ (ω, e)).real {m | mutatedBlocks n m = z} ∂clockLaw =
      ∏ k : Fin (n - 1), killLevelFactor (θ : ℝ) (ω k) (z k) := by
  have h1 : ∀ e : ℕ → ℝ,
      (kingmanBranchMutationKernel n θ (ω, e)).real {m | mutatedBlocks n m = z} =
        ∏ k : Fin (n - 1), killLevelIntegrand θ (ω k) (z k) (e k) := by
    intro e
    rw [kingmanBranchMutationKernel_real_mutatedBlocks]
    refine Finset.prod_congr rfl fun k _ => ?_
    simp only [coe_kingmanBranchMutationRate]
    exact prod_markFactor θ (ω k) (z k) (e k)
  rw [integral_congr_ae (ae_of_all _ h1),
    integral_clockLaw_prod (n - 1) (fun k => killLevelIntegrand θ (ω k) (z k))
      (fun k => measurable_killLevelIntegrand θ (ω k) (z k))]
  exact Finset.prod_congr rfl fun k _ => integral_killLevelIntegrand θ (ω k) (z k)

theorem measurableSet_mutatedBlocks_eq (z : Fin (n - 1) → Finset (Finset (Fin n))) :
    MeasurableSet {x : KingmanMutationHistory n × (KingmanMutationBranch n → ℕ) |
      mutatedBlocks n x.2 = z} := by
  have hS : MeasurableSet {m : KingmanMutationBranch n → ℕ | mutatedBlocks n m = z} :=
    MeasurableSet.of_discrete
  exact measurable_snd hS

theorem markedKingmanLaw_real_mutatedBlocks (θ : ℝ≥0)
    (z : Fin (n - 1) → Finset (Finset (Fin n))) :
    (markedKingmanLaw n θ).real {x | mutatedBlocks n x.2 = z} =
      (partitionChain (Fin n)).jumpChain.pathProduct (n - 1)
        (fun k π => killLevelFactor (θ : ℝ) π (z k)) ⊥ := by
  have hS := measurableSet_mutatedBlocks_eq z
  have hSm : MeasurableSet {m : KingmanMutationBranch n → ℕ | mutatedBlocks n m = z} :=
    MeasurableSet.of_discrete
  have hI : Integrable
      ({x : KingmanMutationHistory n × (KingmanMutationBranch n → ℕ) |
        mutatedBlocks n x.2 = z}.indicator
        (1 : KingmanMutationHistory n × (KingmanMutationBranch n → ℕ) → ℝ))
      (((partitionChain (Fin n)).jumpHoldLaw ⊥).compProd
        (kingmanBranchMutationKernel n θ)) :=
    (integrable_const (1 : ℝ)).indicator hS
  have hK : ∀ h : KingmanMutationHistory n,
      ∫ m, {x : KingmanMutationHistory n × (KingmanMutationBranch n → ℕ) |
        mutatedBlocks n x.2 = z}.indicator
        (1 : KingmanMutationHistory n × (KingmanMutationBranch n → ℕ) → ℝ) (h, m)
        ∂kingmanBranchMutationKernel n θ h =
      (kingmanBranchMutationKernel n θ h).real {m | mutatedBlocks n m = z} := by
    intro h
    refine Eq.trans ?_ (integral_indicator_one hSm)
    rfl
  have hmeas : Measurable (fun h : KingmanMutationHistory n =>
      (kingmanBranchMutationKernel n θ h).real {m | mutatedBlocks n m = z}) :=
    ((kingmanBranchMutationKernel n θ).measurable_coe hSm).ennreal_toReal
  have hint : Integrable (fun h : KingmanMutationHistory n =>
      (kingmanBranchMutationKernel n θ h).real {m | mutatedBlocks n m = z})
      (((partitionChain (Fin n)).jumpChain.pathLaw ⊥).prod clockLaw) := by
    refine Integrable.of_bound hmeas.aestronglyMeasurable 1 (ae_of_all _ fun h => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact (measureReal_mono (Set.subset_univ _)).trans_eq probReal_univ
  rw [← integral_indicator_one hS,
    show markedKingmanLaw n θ =
      ((partitionChain (Fin n)).jumpHoldLaw ⊥).compProd
        (kingmanBranchMutationKernel n θ) from rfl,
    Measure.integral_compProd hI, integral_congr_ae (ae_of_all _ hK),
    RateChain.jumpHoldLaw, integral_prod _ hint,
    integral_congr_ae (ae_of_all _ fun ω => integral_clockLaw_kernel_mutatedBlocks θ ω z)]
  exact FinChain.integral_prod_eval _ (n - 1) (fun k π => killLevelFactor (θ : ℝ) π (z k)) ⊥

theorem markedKingmanLaw_real_mutatedBlocks_prop (θ : ℝ≥0)
    (p : (Fin (n - 1) → Finset (Finset (Fin n))) → Prop) [DecidablePred p] :
    (markedKingmanLaw n θ).real {x | p (mutatedBlocks n x.2)} =
      ∑ z : Fin (n - 1) → Finset (Finset (Fin n)), if p z then
        (partitionChain (Fin n)).jumpChain.pathProduct (n - 1)
          (fun k π => killLevelFactor (θ : ℝ) π (z k)) ⊥ else 0 := by
  have hset : {x : KingmanMutationHistory n × (KingmanMutationBranch n → ℕ) |
      p (mutatedBlocks n x.2)} =
      ⋃ z ∈ (univ.filter p : Finset (Fin (n - 1) → Finset (Finset (Fin n)))),
        {x | mutatedBlocks n x.2 = z} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, mem_filter, mem_univ, true_and, exists_prop,
      exists_eq_right']
  have hd : Set.PairwiseDisjoint
      (↑(univ.filter p : Finset (Fin (n - 1) → Finset (Finset (Fin n)))))
      (fun z => {x : KingmanMutationHistory n × (KingmanMutationBranch n → ℕ) |
        mutatedBlocks n x.2 = z}) := by
    intro z _ z' _ hzz'
    refine Set.disjoint_left.2 fun x hx hx' => hzz' ?_
    exact (show mutatedBlocks n x.2 = z from hx).symm.trans hx'
  rw [hset, measureReal_biUnion_finset hd (fun z _ => measurableSet_mutatedBlocks_eq z),
    Finset.sum_filter]
  exact Finset.sum_congr rfl fun z _ => by rw [markedKingmanLaw_real_mutatedBlocks]

end Rhone.Statistics
