/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.ContinuousTime.Interpolation
public import Mathlib.MeasureTheory.Order.Lattice
public import Mathlib.Algebra.Order.Archimedean.Basic

/-! # Measurable real-time coordinates -/

@[expose] public section

namespace Rhone.Coalescent.ContinuousTime

open Finset MeasureTheory TypedAncestralChain BranchLengthMoments ContinuousTimeGenealogy

variable {n KA KB : ℕ} {θA θB ρ : ℝ}

theorem measurable_select {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (f : ℕ → Ω → α) (hf : ∀ k, Measurable (f k)) (i : Ω → ℕ) (hi : Measurable i) :
    Measurable (fun z => f (i z) z) := by
  intro E hE
  have heq : (fun z => f (i z) z) ⁻¹' E = ⋃ k : ℕ, i ⁻¹' {k} ∩ (f k ⁻¹' E) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_singleton_iff]
    constructor
    · intro hz; exact ⟨i z, rfl, hz⟩
    · rintro ⟨k, hk, hz⟩; simpa [hk] using hz
  rw [heq]
  exact MeasurableSet.iUnion fun k => (hi (MeasurableSet.singleton k)).inter (hf k hE)

theorem measurable_holding (k : ℕ) :
    Measurable (fun z : CtPath n KA KB => holding θA θB ρ z k) := by
  have hr : Measurable (fun z : CtPath n KA KB => rateTotS θA θB ρ (z.1 k)) :=
    (Measurable.of_discrete (f := fun s : TS n KA KB => rateTotS θA θB ρ s)).comp
      ((measurable_pi_apply k).comp measurable_fst)
  exact measurable_const.max (((measurable_pi_apply k).comp measurable_snd).div hr)

theorem measurable_arrival (k : ℕ) :
    Measurable (fun z : CtPath n KA KB => arrival θA θB ρ z k) := by
  simpa only [arrival, Finset.sum_apply] using
    Finset.measurable_sum (range k) (fun j _ => measurable_holding (θA := θA) (θB := θB) (ρ := ρ) j)

theorem measurable_bounded_index (N : ℕ) (t : ℝ) :
    Measurable (fun z : CtPath n KA KB =>
      ((range (N + 1)).filter (fun k => arrival θA θB ρ z k ≤ t)).sup id) := by
  classical
  have hm (k : ℕ) : Measurable (fun z : CtPath n KA KB =>
      if arrival θA θB ρ z k ≤ t then k else 0) :=
    Measurable.ite (measurableSet_le (measurable_arrival k) measurable_const)
      measurable_const measurable_const
  have hfinite (S : Finset ℕ) : Measurable (fun z : CtPath n KA KB =>
      S.sup (fun k => if arrival θA θB ρ z k ≤ t then k else 0)) := by
    induction S using Finset.induction_on with
    | empty => simp only [Finset.sup_empty]; exact measurable_const
    | @insert k S _hk ih => simpa only [Finset.sup_insert, Pi.sup_def] using (hm k).sup ih
  convert hfinite (range (N + 1)) using 1
  funext z
  change ((range (N + 1)).filter (fun k => arrival θA θB ρ z k ≤ t)).sup id =
    (range (N + 1)).sup (fun k => if arrival θA θB ρ z k ≤ t then k else (⊥ : ℕ))
  rw [Finset.sup_ite, Finset.sup_bot, sup_bot_eq]
  rfl

theorem measurable_timeIndex (t : ℝ) :
    Measurable (fun z : CtPath n KA KB => timeIndex θA θB ρ z t) :=
  measurable_select (fun N (z : CtPath n KA KB) => ((range (N + 1)).filter
    (fun k => arrival θA θB ρ z k ≤ t)).sup id)
    (fun N => measurable_bounded_index N t) (fun z : CtPath n KA KB => absTime z.1)
    (measurable_absTime.comp measurable_fst)

theorem measurable_process (t : ℝ) :
    Measurable (fun z : CtPath n KA KB => process θA θB ρ z t) :=
  measurable_select (fun k (z : CtPath n KA KB) => z.1 k)
    (fun k => (measurable_pi_apply k).comp measurable_fst)
    (fun z : CtPath n KA KB => timeIndex θA θB ρ z t) (measurable_timeIndex t)

theorem measurable_bounded_index_joint (N : ℕ) :
    Measurable (fun p : CtPath n KA KB × ℝ =>
      ((range (N + 1)).filter (fun k => arrival θA θB ρ p.1 k ≤ p.2)).sup id) := by
  classical
  have hm (k : ℕ) : Measurable (fun p : CtPath n KA KB × ℝ =>
      if arrival θA θB ρ p.1 k ≤ p.2 then k else 0) :=
    Measurable.ite (measurableSet_le ((measurable_arrival k).comp measurable_fst) measurable_snd)
      measurable_const measurable_const
  have hfinite (S : Finset ℕ) : Measurable (fun p : CtPath n KA KB × ℝ =>
      S.sup (fun k => if arrival θA θB ρ p.1 k ≤ p.2 then k else 0)) := by
    induction S using Finset.induction_on with
    | empty => simp only [Finset.sup_empty]; exact measurable_const
    | @insert k S _hk ih => simpa only [Finset.sup_insert, Pi.sup_def] using (hm k).sup ih
  convert hfinite (range (N + 1)) using 1
  funext p
  change ((range (N + 1)).filter (fun k => arrival θA θB ρ p.1 k ≤ p.2)).sup id =
    (range (N + 1)).sup (fun k => if arrival θA θB ρ p.1 k ≤ p.2 then k else (⊥ : ℕ))
  rw [Finset.sup_ite, Finset.sup_bot, sup_bot_eq]
  rfl

theorem measurable_timeIndex_joint :
    Measurable (fun p : CtPath n KA KB × ℝ => timeIndex θA θB ρ p.1 p.2) := by
  unfold timeIndex
  exact measurable_select (Ω := CtPath n KA KB × ℝ) (α := ℕ)
    (fun N (p : CtPath n KA KB × ℝ) => ((range (N + 1)).filter
    (fun k => arrival θA θB ρ p.1 k ≤ p.2)).sup id)
    (fun N => measurable_bounded_index_joint N) (fun p : CtPath n KA KB × ℝ => absTime p.1.1)
    (measurable_absTime.comp (measurable_fst.comp measurable_fst))

theorem measurable_process_joint :
    Measurable (fun p : CtPath n KA KB × ℝ => process θA θB ρ p.1 p.2) := by
  unfold process
  exact measurable_select (Ω := CtPath n KA KB × ℝ) (α := TS n KA KB)
    (fun k (p : CtPath n KA KB × ℝ) => p.1.1 k)
    (fun k => (measurable_pi_apply k).comp (measurable_fst.comp measurable_fst))
    (fun p : CtPath n KA KB × ℝ => timeIndex θA θB ρ p.1 p.2) measurable_timeIndex_joint

theorem process_hit_iff_rational (z : CtPath n KA KB) (E : Set (TS n KA KB)) :
    (∃ t : ℝ, 0 ≤ t ∧ process θA θB ρ z t ∈ E) ↔
      ∃ q : ℚ, 0 ≤ (q : ℝ) ∧ process θA θB ρ z (q : ℝ) ∈ E := by
  constructor
  · rintro ⟨t, ht, hz⟩
    obtain ⟨ε, hε, hconst⟩ := process_locally_constant_right z ht
    obtain ⟨q, htq, hqt⟩ := exists_rat_btwn (lt_add_of_pos_right t hε)
    refine ⟨q, ht.trans (le_of_lt htq), ?_⟩
    rw [hconst (q : ℝ) (le_of_lt htq) hqt]
    exact hz
  · rintro ⟨q, hq, hz⟩
    exact ⟨(q : ℝ), hq, hz⟩

theorem measurableSet_process_hit (E : Set (TS n KA KB)) :
    MeasurableSet {z : CtPath n KA KB | ∃ t : ℝ, 0 ≤ t ∧ process θA θB ρ z t ∈ E} := by
  have heq : {z : CtPath n KA KB | ∃ t : ℝ, 0 ≤ t ∧ process θA θB ρ z t ∈ E}
      = ⋃ q : ℚ, {z : CtPath n KA KB | 0 ≤ (q : ℝ) ∧ process θA θB ρ z (q : ℝ) ∈ E} := by
    ext z
    simpa only [Set.mem_iUnion, Set.mem_ofPred_eq] using process_hit_iff_rational z E
  rw [heq]
  exact MeasurableSet.iUnion fun q => (MeasurableSet.const _).inter
    ((measurable_process (q : ℝ)) MeasurableSet.of_discrete)

end Rhone.Coalescent.ContinuousTime
