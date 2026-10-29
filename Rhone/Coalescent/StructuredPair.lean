/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.StructuredCoalescent
public import Rhone.MarkovChain.RateReach
public import Rhone.Coalescent.IslandPairRates

/-!
# Two lineages in a structured population with a general migration matrix

Source: notohara1990, sec. 2; sampson2006, sec. 2, eq. (2.2). -/

@[expose] public section

namespace Rhone.Coalescent.StructuredPair

open Finset
open IslandPair (State destinationRate)
open Structured (MigAdj MigIrreducible)

variable {d : ℕ}

noncomputable def eventRate (M : Fin d → Fin d → ℝ) (c : Fin d → ℝ) : State d → State d → ℝ
  | none, _ => 0
  | some (a, b), none => if a = b then c a else 0
  | some (a, b), some (x, y) =>
      (if b = y ∧ a ≠ x then M a x else 0) + (if a = x ∧ b ≠ y then M b y else 0)

noncomputable def generator (M : Fin d → Fin d → ℝ) (c : Fin d → ℝ) (s t : State d) : ℝ :=
  eventRate M c s t - if s = t then ∑ y, eventRate M c s y else 0

theorem eventRate_self (M : Fin d → Fin d → ℝ) (c : Fin d → ℝ) (s : State d) :
    eventRate M c s s = 0 := by
  rcases s with _ | ⟨a, b⟩
  · rfl
  · simp [eventRate]

theorem eventRate_nonneg (M : Fin d → Fin d → ℝ) (c : Fin d → ℝ)
    (hM : ∀ a b, a ≠ b → 0 ≤ M a b) (hc : ∀ a, 0 ≤ c a) (s t : State d) :
    0 ≤ eventRate M c s t := by
  rcases s with _ | ⟨a, b⟩
  · exact le_rfl
  · rcases t with _ | ⟨x, y⟩
    · simp only [eventRate]
      split_ifs
      · exact hc a
      · exact le_rfl
    · simp only [eventRate]
      refine add_nonneg ?_ ?_
      · split_ifs with h
        · exact hM a x h.2
        · exact le_rfl
      · split_ifs with h
        · exact hM b y h.2
        · exact le_rfl

noncomputable def chain (M : Fin d → Fin d → ℝ) (c : Fin d → ℝ)
    (hM : ∀ a b, a ≠ b → 0 ≤ M a b) (hc : ∀ a, 0 ≤ c a) : Rhone.MarkovChain.RateChain (State d)
        where
  Q := generator M c
  off_diag_nonneg s t hst := by
    simp only [generator, hst, ↓reduceIte, sub_zero]
    exact eventRate_nonneg M c hM hc s t
  row_sum s := by simp [generator, Finset.sum_sub_distrib]

theorem chain_const_eq_island (d : ℕ) (m c : ℝ) (hm : 0 ≤ m) (hc : 0 ≤ c) :
    chain (fun _ _ : Fin d => Rhone.Coalescent.IslandPair.destinationRate d m) (fun _ => c)
        (fun _ _ _ => div_nonneg hm (Nat.cast_nonneg _)) (fun _ => hc) =
      Rhone.Coalescent.IslandPair.chain d m c hm hc := by
  have he : eventRate (fun _ _ : Fin d => Rhone.Coalescent.IslandPair.destinationRate d m)
      (fun _ => c) = Rhone.Coalescent.IslandPair.eventRate d m c := by
    funext s t
    rcases s with _ | ⟨a, b⟩
    · rfl
    · rcases t with _ | ⟨x, y⟩ <;> rfl
  have hg : generator (fun _ _ : Fin d => Rhone.Coalescent.IslandPair.destinationRate d m)
      (fun _ => c) = Rhone.Coalescent.IslandPair.generator d m c := by
    funext s t
    simp only [generator, Rhone.Coalescent.IslandPair.generator, he]
  simp only [chain, Rhone.Coalescent.IslandPair.chain, hg]

private theorem sum_eventRate_mul (M : Fin d → Fin d → ℝ) (c : Fin d → ℝ) (a b : Fin d)
    (f : State d → ℝ) :
    ∑ t, eventRate M c (some (a, b)) t * f t =
      (if a = b then c a * f none else 0) +
      (∑ x, if a ≠ x then M a x * f (some (x, b)) else 0) +
      ∑ y, if b ≠ y then M b y * f (some (a, y)) else 0 := by
  simp only [Fintype.sum_option, Fintype.sum_prod_type, eventRate, add_mul,
    Finset.sum_add_distrib]
  have hleft : (∑ x : Fin d, ∑ y : Fin d,
      (if b = y ∧ a ≠ x then M a x else 0) * f (some (x, y))) =
      ∑ x, if a ≠ x then M a x * f (some (x, b)) else 0 := by
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hax : a = x <;> simp [hax]
  have hright : (∑ x : Fin d, ∑ y : Fin d,
      (if a = x ∧ b ≠ y then M b y else 0) * f (some (x, y))) =
      ∑ y, if b ≠ y then M b y * f (some (a, y)) else 0 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases hby : b = y <;> simp [hby]
  rw [hleft, hright, ite_mul, zero_mul, add_assoc]

theorem sum_generator_mul (M : Fin d → Fin d → ℝ) (c : Fin d → ℝ) (a b : Fin d)
    (f : State d → ℝ) :
    ∑ t, generator M c (some (a, b)) t * f t =
      (if a = b then c a * (f none - f (some (a, b))) else 0) +
      (∑ x, if a ≠ x then M a x * (f (some (x, b)) - f (some (a, b))) else 0) +
      ∑ y, if b ≠ y then M b y * (f (some (a, y)) - f (some (a, b))) else 0 := by
  have h0 : ∑ t, generator M c (some (a, b)) t * f t =
      (∑ t, eventRate M c (some (a, b)) t * f t) -
        (∑ t, eventRate M c (some (a, b)) t) * f (some (a, b)) := by
    simp only [generator, sub_mul, Finset.sum_sub_distrib]
    congr 1
    simp [ite_mul]
  have h1 := sum_eventRate_mul M c a b fun _ => 1
  simp only [mul_one] at h1
  rw [h0, sum_eventRate_mul, h1, add_mul, add_mul, add_sub_add_comm, add_sub_add_comm]
  congr 1
  · congr 1
    · split_ifs <;> ring
    · rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      split_ifs <;> ring
  · rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    split_ifs <;> ring

theorem chain_Q_first (M : Fin d → Fin d → ℝ) (c : Fin d → ℝ)
    (hM : ∀ a b, a ≠ b → 0 ≤ M a b) (hc : ∀ a, 0 ≤ c a) {a x : Fin d} (hax : a ≠ x)
    (b : Fin d) : (chain M c hM hc).Q (some (a, b)) (some (x, b)) = M a x := by
  simp [chain, generator, eventRate, hax]

theorem chain_Q_coalesce (M : Fin d → Fin d → ℝ) (c : Fin d → ℝ)
    (hM : ∀ a b, a ≠ b → 0 ≤ M a b) (hc : ∀ a, 0 ≤ c a) (a : Fin d) :
    (chain M c hM hc).Q (some (a, a)) none = c a := by
  simp [chain, generator, eventRate]

theorem absorbing_set (M : Fin d → Fin d → ℝ) (c : Fin d → ℝ)
    (hM : ∀ a b, a ≠ b → 0 ≤ M a b) (hc : ∀ a, 0 ≤ c a) :
    (chain M c hM hc).jumpChain.IsAbsorbingSet {none} := by
  intro s hs
  rw [Finset.mem_singleton.1 hs]
  exact Rhone.MarkovChain.RateChain.jumpChain_isAbsorbing
    (by simp [Rhone.MarkovChain.RateChain.rate, chain, generator, eventRate])

theorem reflTransGen_none (M : Fin d → Fin d → ℝ) (c : Fin d → ℝ)
    (hM : ∀ a b, a ≠ b → 0 ≤ M a b) (hirr : MigIrreducible M) (hc : ∀ a, 0 < c a)
    (s : State d) :
    Relation.ReflTransGen (chain M c hM fun a => (hc a).le).Adj s none := by
  rcases s with _ | ⟨a, b⟩
  · exact Relation.ReflTransGen.refl
  · have hpath : ∀ {x : Fin d}, Relation.ReflTransGen (MigAdj M) a x →
        Relation.ReflTransGen (chain M c hM fun a => (hc a).le).Adj (some (a, b))
          (some (x, b)) := by
      intro x hx
      induction hx with
      | refl => exact Relation.ReflTransGen.refl
      | @tail y z _ hyz ih =>
        refine ih.tail ⟨?_, ?_⟩
        · exact fun h => hyz.1 (Prod.mk.inj (Option.some.inj h)).1
        · rw [chain_Q_first M c hM _ hyz.1]
          exact hyz.2
    refine (hpath (hirr a b)).tail ⟨by simp, ?_⟩
    rw [chain_Q_coalesce]
    exact hc b

theorem reaches (M : Fin d → Fin d → ℝ) (c : Fin d → ℝ)
    (hM : ∀ a b, a ≠ b → 0 ≤ M a b) (hirr : MigIrreducible M) (hc : ∀ a, 0 < c a) :
    (chain M c hM fun a => (hc a).le).jumpChain.Reaches {none} :=
  Rhone.MarkovChain.RateChain.reaches_of_reflTransGen fun s =>
    ⟨none, Finset.mem_singleton_self _, reflTransGen_none M c hM hirr hc s⟩

theorem rate_some_pos (M : Fin d → Fin d → ℝ) (c : Fin d → ℝ)
    (hM : ∀ a b, a ≠ b → 0 ≤ M a b) (hirr : MigIrreducible M) (hc : ∀ a, 0 < c a)
    (a b : Fin d) : 0 < (chain M c hM fun a => (hc a).le).rate (some (a, b)) :=
  Rhone.MarkovChain.RateChain.rate_pos_of_reflTransGen_of_ne
    (reflTransGen_none M c hM hirr hc (some (a, b))) (by simp)

theorem expectedTime_generator (M : Fin d → Fin d → ℝ) (c : Fin d → ℝ)
    (hM : ∀ a b, a ≠ b → 0 ≤ M a b) (hirr : MigIrreducible M) (hc : ∀ a, 0 < c a)
    (a b : Fin d) :
    ∑ t, generator M c (some (a, b)) t *
      (chain M c hM fun a => (hc a).le).expectedTime {none} t = -1 :=
  Rhone.MarkovChain.RateChain.expectedCost_generator (absorbing_set M c hM fun a => (hc a).le)
    (reaches M c hM hirr hc) (fun _ => 1) (x := some (a, b)) (by simp)
    (rate_some_pos M c hM hirr hc a b).ne'

theorem expectedTime_none (M : Fin d → Fin d → ℝ) (c : Fin d → ℝ)
    (hM : ∀ a b, a ≠ b → 0 ≤ M a b) (hc : ∀ a, 0 ≤ c a) :
    (chain M c hM hc).expectedTime {none} none = 0 :=
  Rhone.MarkovChain.RateChain.expectedCost_of_mem (absorbing_set M c hM hc)
    (Finset.mem_singleton_self _) _

theorem eq_expectedTime_of_generator (M : Fin d → Fin d → ℝ) (c : Fin d → ℝ)
    (hM : ∀ a b, a ≠ b → 0 ≤ M a b) (hirr : MigIrreducible M) (hc : ∀ a, 0 < c a)
    {u : State d → ℝ} (h0 : u none = 0)
    (hgen : ∀ a b, ∑ t, generator M c (some (a, b)) t * u t = -1) :
    u = (chain M c hM fun a => (hc a).le).expectedTime {none} := by
  refine Rhone.MarkovChain.RateChain.eq_expectedCost_of_generator
    (absorbing_set M c hM fun a => (hc a).le) (reaches M c hM hirr hc) ?_ ?_ ?_
  · intro s hs
    rcases s with _ | ⟨a, b⟩
    · simp at hs
    · exact (rate_some_pos M c hM hirr hc a b).ne'
  · intro s hs
    rw [Finset.mem_singleton.1 hs, h0]
  · intro s hs
    rcases s with _ | ⟨a, b⟩
    · simp at hs
    · exact hgen a b

end Rhone.Coalescent.StructuredPair
