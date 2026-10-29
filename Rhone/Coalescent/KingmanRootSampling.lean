/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.KingmanRootSampleEvent
public import Rhone.Coalescent.KingmanRootSamplingAlgebra
/-!
# Finite sample-root events in Kingman population genealogies

Source: kingman1982, sec. 1, eq. (1.1)–(1.4), (1.7). -/
@[expose] public section
namespace Rhone.Coalescent
open Finset
theorem history_payoff_one {L : Type*} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) (hF : ADR11.IsForest F) (t : ℕ)
    (ht : t ≤ (ADR11.roots F).card - 1) :
    Combinatorics.historyPayoff F t (fun _ => (1 : ℝ)) = 1 := by
  induction t generalizing F with
  | zero =>
    unfold Combinatorics.historyPayoff
    change (∑ h : PUnit, (1 : ℝ) * 1) = 1
    simp
  | succ t ih =>
    have hk : 2 ≤ (ADR11.roots F).card := by omega
    rw [Combinatorics.history_payoff_succ]
    have hs : ∀ G ∈ ADR11.merges F,
        ADR11.jumpMatrix F G * Combinatorics.historyPayoff G t (fun _ => (1 : ℝ)) =
          ((ADR11.roots F).card.choose 2 : ℝ)⁻¹ := by
      intro G hG
      obtain ⟨hGf, hGr, _⟩ := hF.of_mem_merges hG
      rw [ih G hGf (by omega), mul_one,
        ADR11.jumpMatrix_apply_of_isForest (by omega), ite_eq_left hG]
    rw [sum_congr rfl hs, sum_const, nsmul_eq_mul, hF.card_merges]
    exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Nat.choose_ne_zero hk))
noncomputable def samplePopulationRootMass (N : ℕ) (S : Finset (Fin N)) : ℝ :=
  ∑ h : Combinatorics.RankedLabelledHistory N,
    if ((ADR11.roots
        ((Combinatorics.historyEnd (ADR11.singletonForest N) (N - 1) h).erase univ)).filter
      (fun R => ¬Disjoint R S)).card = 2 then
      Combinatorics.historyMass (ADR11.singletonForest N) (N - 1) h else 0
theorem sample_population_root_mass_decomposition (N : ℕ) (hN : 2 ≤ N)
    (S : Finset (Fin N)) (hS : 1 ≤ S.card) :
    samplePopulationRootMass N S =
      1 - ∑ A ∈ (univ : Finset (Finset (Fin N))).erase univ,
        if S ⊆ A then rootSplitMass N A else 0 := by
  classical
  have hmass : (∑ h : Combinatorics.RankedLabelledHistory N,
      Combinatorics.historyMass (ADR11.singletonForest N) (N - 1) h) = 1 := by
    have hm := history_payoff_one (ADR11.singletonForest N)
      (ADR11.isForest_singletonForest N) (N - 1)
      (by rw [ADR11.card_roots_singletonForest])
    simpa only [Combinatorics.historyPayoff, mul_one] using hm
  unfold samplePopulationRootMass
  have hterm : ∀ h : Combinatorics.RankedLabelledHistory N,
      (if ((ADR11.roots
          ((Combinatorics.historyEnd (ADR11.singletonForest N) (N - 1) h).erase univ)).filter
        (fun R => ¬Disjoint R S)).card = 2 then
          Combinatorics.historyMass (ADR11.singletonForest N) (N - 1) h else 0) =
      Combinatorics.historyMass (ADR11.singletonForest N) (N - 1) h *
        (1 - ∑ A ∈ (univ : Finset (Finset (Fin N))).erase univ,
          if S ⊆ A then
            (if ADR11.roots
                ((Combinatorics.historyEnd (ADR11.singletonForest N) (N - 1) h).erase univ) =
              {A, univ \ A} then (1 : ℝ) else 0) else 0) := by
    intro h
    rw [← root_pair_sample_indicator _ (Combinatorics.historyEnd_isBinaryHierarchy N (by omega) h)
      (by simpa using hN) S (card_pos.mp (by omega : 0 < S.card))]
    split_ifs <;> simp
  rw [sum_congr rfl (fun h _ => hterm h)]
  simp_rw [mul_sub, mul_one, mul_sum]
  rw [sum_sub_distrib, hmass, sum_comm]
  congr 1
  apply sum_congr rfl
  intro A hA
  unfold rootSplitMass
  by_cases hs : S ⊆ A
  · simp only [hs, ite_true]
    apply sum_congr rfl
    intro h hh
    split_ifs <;> simp
  · simp only [hs, ite_false, mul_zero, sum_const_zero]
theorem sample_population_root_probability (N : ℕ) (hN : 2 ≤ N)
    (S : Finset (Fin N)) (hS : 1 ≤ S.card) :
    samplePopulationRootMass N S =
      ((S.card - 1 : ℕ) : ℝ) * (N + 1 : ℕ) /
        (((S.card + 1 : ℕ) : ℝ) * (N - 1 : ℕ)) := by
  classical
  have hterm : ∀ A ∈ (univ : Finset (Finset (Fin N))).erase univ,
      (if S ⊆ A then rootSplitMass N A else 0) =
        (2 / (N - 1 : ℕ) : ℝ) *
          (if S ⊆ A then (N.choose A.card : ℝ)⁻¹ else 0) := by
    intro A hA
    by_cases hs : S ⊆ A
    · have ha : 0 < A.card := lt_of_lt_of_le (by omega) (card_le_card hs)
      have han : A.card < N := by
        have hAu := (mem_erase.mp hA).1
        have hle : A.card ≤ N := by simpa using card_le_card (subset_univ A)
        have hne : A.card ≠ N := by
          intro he
          have hfull : A = univ := eq_of_subset_of_card_le (subset_univ A)
            (by simpa using he.ge)
          exact hAu hfull
        omega
      rw [ite_eq_left hs, ite_eq_left hs, root_split_mass N hN A ha han]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    · rw [ite_eq_right hs, ite_eq_right hs, mul_zero]
  have hsum : (∑ A ∈ (univ : Finset (Finset (Fin N))).erase univ,
      if S ⊆ A then (N.choose A.card : ℝ)⁻¹ else 0) =
        ((N + 1 : ℕ) : ℝ) / (S.card + 1 : ℕ) - 1 := by
    have hm := sum_erase_add (univ : Finset (Finset (Fin N)))
      (fun A => if S ⊆ A then (N.choose A.card : ℝ)⁻¹ else 0) (mem_univ univ)
    rw [sum_reciprocal_choose_supersets N S] at hm
    simp only [subset_univ, ite_true, card_univ, Fintype.card_fin,
      Nat.choose_self, Nat.cast_one, inv_one] at hm
    linarith
  rw [sample_population_root_mass_decomposition N hN S hS,
    sum_congr rfl hterm, ← mul_sum, hsum]
  have hNm : ((N - 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hSp : ((S.card + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [Nat.cast_sub hS, Nat.cast_one]
  field_simp
  rw [Nat.cast_sub (by omega : 1 ≤ N)]
  simp only [Nat.cast_add, Nat.cast_one]
  ring
end Rhone.Coalescent
