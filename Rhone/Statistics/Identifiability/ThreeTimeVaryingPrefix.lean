/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.ThreeTimeVaryingOnset
public import Rhone.Statistics.Identifiability.ThreeMigrationFlow
public import Rhone.Statistics.Identifiability.FiniteFlowRestart
public import Rhone.Statistics.Identifiability.DelayedPrefixMasses

/-! # Literal migration-free prefixes and exact restart of the three-sample witness -/

@[expose] public section

noncomputable section
open Set Matrix MeasureTheory
open scoped BigOperators Topology Matrix
namespace Rhone.Statistics.Identifiability.ThreeTimeVarying

lemma zero_migration_pre_support (k : ℕ) (c : ℝ → ℝ) (hc : Continuous c)
    (t : ℝ) (i : ThreeState) (hi : i ≠ 0) : preRow k c (fun _ => 0) t i = 0 := by
  apply inhomogeneousTransition_zero_outside_closed _
    (preGenerator_continuous k c (fun _ => 0) hc continuous_const)
    (fun i : ThreeState => i = 0) _ 0 t 0 i rfl hi
  intro u j l hj hl
  subst j
  fin_cases l <;> simp_all [threeGenerator, MarkovChain.Identifiability.totalMigration]

lemma pre_prefix_zero_migration (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) {a : ℝ} (ha : 0 ≤ a)
    (hbefore : ∀ u ∈ Ioo 0 a, q u = 0) :
    preRow k c q a = Pi.single 0 (preRow k c q a 0) := by
  by_cases ha0 : a = 0
  · subst a
    ext i
    fin_cases i <;>
      simp [preRow, inhomogeneousTransition_self _ (preGenerator_continuous k c q hc hq)]
  have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hclosed : EqOn q (fun _ => 0) (Icc 0 a) := by
    have he : EqOn q (fun _ => 0) (Ioo 0 a) := hbefore
    simpa only [closure_Ioo (ne_of_lt hap)] using he.closure hq continuous_const
  have he := inhomogeneousTransition_eq_of_eqOn
    (fun u => threeGenerator k (c u) (q u)) (fun u => threeGenerator k (c u) 0)
    (preGenerator_continuous k c q hc hq)
    (preGenerator_continuous k c (fun _ => 0) hc continuous_const) ha
    (fun u hu => by dsimp only; rw [hclosed hu])
  ext i
  by_cases hi : i = 0
  · subst i
    simp
  · have hp : preRow k c q a i = preRow k c (fun _ => 0) a i :=
      congrArg (fun M => M 0 i) he
    rw [hp, zero_migration_pre_support k c hc a i hi]
    simp [hi]

lemma initial_pre_coordinate_positive (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    {a : ℝ} (ha : 0 ≤ a) : 0 < preRow k c q a 0 :=
  inhomogeneousTransition_diagonal_positive _ (preGenerator_continuous k c q hc hq)
    (fun u hu => threeGenerator_metzler k (c u) (hqn u hu)) 0 ha

lemma witness_restart (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) (a t : ℝ) :
    witness k c q (a + t) =
      rowPayoff (fun i : ProductState => preRow k c q a i.1 * preRow k c q a i.2)
        (inhomogeneousTransition (fun u => productGenerator k (c (a + u)) (q (a + u))) 0 t)
        witnessVec := by
  rw [witness_eq_product_output k c q hc hq,
    rowPayoff_restart _ (productGenerator_continuous k c q hc hq) 0 a t]
  congr 1
  funext i
  exact productRow_factorization k c q hc hq a i

theorem witness_after_zero_migration_prefix (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q) {a : ℝ} (ha : 0 ≤ a)
    (hbefore : ∀ u ∈ Ioo 0 a, q u = 0) (t : ℝ) :
    witness k c q (a + t) = (preRow k c q a 0)^2 *
      witness k (fun u => c (a + u)) (fun u => q (a + u)) t := by
  have hpre := pre_prefix_zero_migration k c q hc hq ha hbefore
  have htensor : (fun i : ProductState => preRow k c q a i.1 * preRow k c q a i.2) =
      Pi.single (0, 0) ((preRow k c q a 0)^2) := by
    have hz (i : ThreeState) (hi : i ≠ 0) : preRow k c q a i = 0 := by
      simpa [hi] using congrFun hpre i
    funext i
    rcases i with ⟨i,j⟩
    by_cases hi : i = 0
    · subst i
      by_cases hj : j = 0
      · subst j
        simp [pow_two]
      · rw [hz j hj]
        simp [hj]
    · rw [hz i hi]
      simp [hi]
  rw [witness_restart k c q hc hq, htensor, rowPayoff_single,
    ← witness_eq_product_output k (fun u => c (a + u)) (fun u => q (a + u))
      (hc.comp (continuous_const.add continuous_id)) (hq.comp (continuous_const.add continuous_id))]

theorem witness_positive_after_migration_onset (k : ℕ) (c q : ℝ → ℝ)
    (hc : Continuous c) (hq : Continuous q)
    (hcn : ∀ t, 0 ≤ t → 0 ≤ c t) (hqn : ∀ t, 0 ≤ t → 0 ≤ q t)
    {a : ℝ} (ha : 0 ≤ a) (hbefore : ∀ u ∈ Ioo 0 a, q u = 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t, 0 < t → t < δ →
      (0 < ∫ u in (0 : ℝ)..t, q (a + u)) → 0 < witness k c q (a + t) := by
  obtain ⟨δ, hδ, hpos⟩ := witness_positive_near_migration_onset k
    (fun u => c (a + u)) (fun u => q (a + u))
    (hc.comp (continuous_const.add continuous_id)) (hq.comp (continuous_const.add continuous_id))
    (fun u hu => hcn _ (add_nonneg ha hu)) (fun u hu => hqn _ (add_nonneg ha hu))
  refine ⟨δ, hδ, fun t ht htδ hQ => ?_⟩
  rw [witness_after_zero_migration_prefix k c q hc hq ha hbefore]
  exact mul_pos (sq_pos_of_pos (initial_pre_coordinate_positive k c q hc hq hqn ha))
    (hpos t ht htδ hQ)

end Rhone.Statistics.Identifiability.ThreeTimeVarying
