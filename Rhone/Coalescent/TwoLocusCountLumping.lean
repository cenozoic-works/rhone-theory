/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.TwoLocusIntervalGenerator
public import Rhone.Coalescent.TwoLocusChain

/-!
# The labelled two-locus ancestral process lumped to counts, and the interval sampler

Source: griffiths1991_two_locus_graph, pp. 106–107. -/

@[expose] public section

namespace Rhone.Coalescent.IntervalCounts

open Finset TwoLocusGenealogy Rhone.LinearAlgebra MarkovChain MeasureTheory IntervalProcess
  MarkovChain.IntervalProcess

variable {n : ℕ}

def linType (p : Lin n) : Bool × Bool := (decide p.1.Nonempty, decide p.2.Nonempty)

def linCount (t : Bool × Bool) (L : Finset (Lin n)) : ℕ :=
  ∑ p ∈ L, if linType p = t then 1 else 0

def astCounts (L : Finset (Lin n)) : Counts :=
  (linCount (true, false) L, linCount (false, true) L, linCount (true, true) L)

theorem linType_coal (p q : Lin n) :
    linType ((p.1 ∪ q.1, p.2 ∪ q.2) : Lin n) = mergeType (linType p) (linType q) := by
  simp [linType, mergeType, Finset.union_nonempty, Bool.decide_or]

theorem linCount_coalL {L : Finset (Lin n)} (h : WF L) {p q : Lin n} (hp : p ∈ L)
    (hq : q ∈ L.erase p) (t : Bool × Bool) :
    linCount t (coalL L p q) + (if linType p = t then 1 else 0) +
        (if linType q = t then 1 else 0) =
      linCount t L + (if mergeType (linType p) (linType q) = t then 1 else 0) := by
  have hqL := Finset.mem_of_mem_erase hq
  have hnm := coal_not_mem h hp hqL
  rw [← linType_coal]
  set F : Lin n → ℕ := fun r => if linType r = t then 1 else 0 with hF
  change ∑ r ∈ insert ((p.1 ∪ q.1, p.2 ∪ q.2) : Lin n) ((L.erase p).erase q), F r + F p + F q =
    ∑ r ∈ L, F r + F ((p.1 ∪ q.1, p.2 ∪ q.2) : Lin n)
  rw [Finset.sum_insert hnm]
  have e1 : F p + ∑ r ∈ L.erase p, F r = ∑ r ∈ L, F r := Finset.add_sum_erase L F hp
  have e2 : F q + ∑ r ∈ (L.erase p).erase q, F r = ∑ r ∈ L.erase p, F r :=
    Finset.add_sum_erase (L.erase p) F hq
  generalize ∑ r ∈ (L.erase p).erase q, F r = s2 at e2 ⊢
  generalize ∑ r ∈ L.erase p, F r = s1 at e1 e2 ⊢
  omega

theorem astCounts_coalL {L : Finset (Lin n)} (h : WF L) {p q : Lin n} (hp : p ∈ L)
    (hq : q ∈ L.erase p) :
    astCounts (coalL L p q) = mergeCounts (astCounts L) (linType p) (linType q) := by
  have h1 := linCount_coalL h hp hq (true, false)
  have h2 := linCount_coalL h hp hq (false, true)
  have h3 := linCount_coalL h hp hq (true, true)
  simp only [astCounts, mergeCounts, typeVec]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> dsimp only <;> omega

theorem astCounts_recL {L : Finset (Lin n)} (h : WF L) {p : Lin n} (hp : p ∈ carC L) :
    astCounts (recL L p) = recCounts (astCounts L) := by
  obtain ⟨hpL, h1, h2⟩ := mem_carC.1 hp
  have hB : ((∅ : Finset (Fin n)), p.2) ∉ L.erase p := by
    intro hm
    have hd := h.disjB _ (Finset.mem_of_mem_erase hm) p hpL (Finset.ne_of_mem_erase hm)
    have : p.2 = ∅ := by simpa using disjoint_self.1 hd
    exact absurd this (Finset.nonempty_iff_ne_empty.1 h2)
  have hA : (p.1, (∅ : Finset (Fin n))) ∉ insert ((∅ : Finset (Fin n)), p.2) (L.erase p) := by
    intro hm
    rcases Finset.mem_insert.1 hm with he | hm
    · exact rec_ne h1 he
    · have hd := h.disjA _ (Finset.mem_of_mem_erase hm) p hpL (Finset.ne_of_mem_erase hm)
      have : p.1 = ∅ := by simpa using disjoint_self.1 hd
      exact absurd this (Finset.nonempty_iff_ne_empty.1 h1)
  have hp11 : linType p = (true, true) := by simp [linType, h1, h2]
  have hA' : linType ((p.1, ∅) : Lin n) = (true, false) := by simp [linType, h1]
  have hB' : linType ((∅, p.2) : Lin n) = (false, true) := by simp [linType, h2]
  have key : ∀ t : Bool × Bool, linCount t (recL L p) + (if linType p = t then 1 else 0) =
      linCount t L + (if linType ((p.1, ∅) : Lin n) = t then 1 else 0) +
        (if linType ((∅, p.2) : Lin n) = t then 1 else 0) := by
    intro t
    set F : Lin n → ℕ := fun r => if linType r = t then 1 else 0 with hF
    change ∑ r ∈ insert ((p.1, ∅) : Lin n) (insert ((∅, p.2) : Lin n) (L.erase p)), F r + F p =
      ∑ r ∈ L, F r + F ((p.1, ∅) : Lin n) + F ((∅, p.2) : Lin n)
    rw [Finset.sum_insert hA, Finset.sum_insert hB]
    have e1 : F p + ∑ r ∈ L.erase p, F r = ∑ r ∈ L, F r := Finset.add_sum_erase L F hpL
    generalize ∑ r ∈ L.erase p, F r = s1 at e1 ⊢
    omega
  have k1 := key (true, false)
  have k2 := key (false, true)
  have k3 := key (true, true)
  simp only [hp11, hA', hB', Prod.mk.injEq, Bool.true_eq_false, Bool.false_eq_true,
    and_self, and_false, false_and, ite_true, ite_false] at k1 k2 k3
  simp only [astCounts, recCounts]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> dsimp only <;> omega

theorem tt_eq_astCounts (L : Finset (Lin n)) : tt L = (astCounts L).2.2 := by
  classical
  unfold tt carC astCounts linCount
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases h1 : p.1.Nonempty <;> by_cases h2 : p.2.Nonempty <;> simp [linType, h1, h2]

theorem na_eq_astCounts (L : Finset (Lin n)) : na L = (astCounts L).1 + (astCounts L).2.2 := by
  classical
  unfold na carA astCounts linCount
  rw [Finset.card_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases h1 : p.1.Nonempty <;> by_cases h2 : p.2.Nonempty <;> simp [linType, h1, h2]

theorem nb_eq_astCounts (L : Finset (Lin n)) : nb L = (astCounts L).2.1 + (astCounts L).2.2 := by
  classical
  unfold nb carB astCounts linCount
  rw [Finset.card_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases h1 : p.1.Nonempty <;> by_cases h2 : p.2.Nonempty <;> simp [linType, h1, h2]

theorem card_eq_astCounts {L : Finset (Lin n)} (h : WF L) :
    L.card = (astCounts L).1 + (astCounts L).2.1 + (astCounts L).2.2 := by
  classical
  rw [Finset.card_eq_sum_ones]
  unfold astCounts linCount
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  rcases h.carries p hp with h1 | h1 <;>
    by_cases h2 : p.1.Nonempty <;> by_cases h3 : p.2.Nonempty <;>
    simp_all [linType]

theorem sum_type_eq {α : Type*} (L : Finset α) (τ : α → Bool × Bool) (f : Bool × Bool → ℝ) :
    ∑ q ∈ L, f (τ q) = ∑ t, ((∑ q ∈ L, if τ q = t then 1 else 0 : ℕ) : ℝ) * f t := by
  push_cast
  simp only [Finset.sum_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_ite_eq]
  simp

theorem sum_erase_pair_type_eq {α : Type*} [DecidableEq α] (L : Finset α)
    (τ : α → Bool × Bool) (F : Bool × Bool → Bool × Bool → ℝ) :
    ∑ p ∈ L, ∑ q ∈ L.erase p, F (τ p) (τ q) =
      ∑ t, ∑ t', ((∑ q ∈ L, if τ q = t then 1 else 0 : ℕ) : ℝ) *
          ((∑ q ∈ L, if τ q = t' then 1 else 0 : ℕ) : ℝ) * F t t' -
        ∑ t, ((∑ q ∈ L, if τ q = t then 1 else 0 : ℕ) : ℝ) * F t t := by
  have h1 : ∀ p ∈ L, ∑ q ∈ L.erase p, F (τ p) (τ q) =
      ∑ q ∈ L, F (τ p) (τ q) - F (τ p) (τ p) := fun p hp =>
    Finset.sum_erase_eq_sub hp
  rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib,
    sum_type_eq L τ (fun t => F t t)]
  congr 1
  rw [Finset.sum_congr rfl (fun p _ => sum_type_eq L τ (fun t' => F (τ p) t')),
    sum_type_eq L τ (fun t => ∑ t', ((∑ q ∈ L, if τ q = t' then 1 else 0 : ℕ) : ℝ) * F t t')]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun t' _ => ?_
  ring

theorem stepU_const_mul (θA θB ρ c : ℝ) (f : Finset (Lin n) → ℝ) (L : Finset (Lin n)) :
    stepU θA θB ρ (fun M => c * f M) L = c * stepU θA θB ρ f L := by
  simp only [stepU, Finset.mul_sum, mul_add, mul_left_comm c]

theorem sum_mul_stepU_indicator (θA θB ρ : ℝ) (h : Finset (Lin n) → ℝ) (L : Finset (Lin n)) :
    ∑ M : Finset (Lin n), h M * stepU θA θB ρ (fun M' => if M' = M then 1 else 0) L =
      stepU θA θB ρ h L := by
  simp_rw [← stepU_const_mul]
  rw [stepU_finsetSum]
  congr 1
  funext M'
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  simp

theorem argRateChain_generator (ρ : ℝ) (hρ : 0 ≤ ρ) {L : Finset (Lin n)}
    (hL : WF (L : Finset (Lin n))) (g : Counts → ℝ) :
    ∑ M : ASt n, (argRateChain 0 0 ρ le_rfl le_rfl hρ).Q L M * g (astCounts M) =
      countGen ρ g (astCounts L) := by
  set k := astCounts (L : Finset (Lin n)) with hk
  set h : Finset (Lin n) → ℝ := fun M => g (astCounts M) with hh
  have hterm : ∀ M : Finset (Lin n), (argRateChain 0 0 ρ le_rfl le_rfl hρ).Q L M * h M =
      h M * stepU 0 0 ρ (fun M' => if M' = M then 1 else 0) L / 2 -
        (if (L : Finset (Lin n)) = M then dtot 0 0 ρ (L : Finset (Lin n)) / 2 * h M else 0) := by
    intro M
    by_cases hLM : (L : Finset (Lin n)) = M
    · have hQ : (argRateChain 0 0 ρ le_rfl le_rfl hρ).Q L M = -(dtot 0 0 ρ L / 2) := by
        rw [← hLM]
        exact argRateChain_Q_self le_rfl le_rfl hρ L
      rw [hQ, ite_eq_left hLM]
      have h0 : stepU 0 0 ρ (fun M' => if M' = M then (1 : ℝ) else 0) L = 0 := by
        rw [← hLM]
        exact stepU_indicator_self 0 0 ρ _
      rw [h0]
      ring
    · rw [argRateChain_Q_of_ne le_rfl le_rfl hρ hLM, ite_eq_right hLM]
      ring
  have hsum : ∑ M : ASt n, (argRateChain 0 0 ρ le_rfl le_rfl hρ).Q L M * g (astCounts M) =
      stepU 0 0 ρ h L / 2 - dtot 0 0 ρ (L : Finset (Lin n)) / 2 * h L := by
    change ∑ M : Finset (Lin n), (argRateChain 0 0 ρ le_rfl le_rfl hρ).Q L M * h M = _
    rw [Finset.sum_congr rfl (fun M _ => hterm M), Finset.sum_sub_distrib, ← Finset.sum_div]
    have h1 : ∑ M : Finset (Lin n), h M * stepU 0 0 ρ
        (fun M' => if M' = M then 1 else 0) L =
        stepU 0 0 ρ h L := sum_mul_stepU_indicator 0 0 ρ h L
    have h2 : ∑ M : Finset (Lin n),
        (if (L : Finset (Lin n)) = M then dtot 0 0 ρ (L : Finset (Lin n)) / 2 * h M else 0) =
        dtot 0 0 ρ (L : Finset (Lin n)) / 2 * h L := by
      rw [Finset.sum_ite_eq]
      simp
    rw [h1, h2]
  rw [hsum]
  have hcoal : ∑ p ∈ (L : Finset (Lin n)), ∑ q ∈ (L : Finset (Lin n)).erase p,
      h (coalL L p q) =
      ∑ p ∈ (L : Finset (Lin n)), ∑ q ∈ (L : Finset (Lin n)).erase p,
        g (mergeCounts k (linType p) (linType q)) := by
    refine Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun q hq => ?_
    simp only [hh, astCounts_coalL hL hp hq, hk]
  have hrec : ∑ p ∈ carC (L : Finset (Lin n)), h (recL L p) =
      (k.2.2 : ℝ) * g (recCounts k) := by
    have hc : ∀ p ∈ carC (L : Finset (Lin n)), h (recL L p) = g (recCounts k) := fun p hp => by
      simp only [hh, astCounts_recL hL hp, hk]
    rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul]
    congr 1
    exact_mod_cast tt_eq_astCounts (L : Finset (Lin n))
  have hcard := card_eq_astCounts hL
  have htt := tt_eq_astCounts (L : Finset (Lin n))
  have hcast : (((L : Finset (Lin n)).card * ((L : Finset (Lin n)).card - 1) : ℕ) : ℝ) =
      ((L : Finset (Lin n)).card : ℝ) * (((L : Finset (Lin n)).card : ℝ) - 1) := by
    rcases Nat.eq_zero_or_pos (L : Finset (Lin n)).card with h0 | h0
    · simp [h0]
    · rw [Nat.cast_mul, Nat.cast_sub h0]
      simp
  have hstep : stepU 0 0 ρ h L = ∑ p ∈ (L : Finset (Lin n)), ∑ q ∈ (L : Finset (Lin n)).erase p,
      g (mergeCounts k (linType p) (linType q)) + ρ * ((k.2.2 : ℝ) * g (recCounts k)) := by
    simp only [stepU, zero_mul, add_zero]
    rw [hcoal, hrec]
  have hdtot : dtot 0 0 ρ (L : Finset (Lin n)) =
      ((k.1 + k.2.1 + k.2.2 : ℕ) : ℝ) * (((k.1 + k.2.1 + k.2.2 : ℕ) : ℝ) - 1) +
        ρ * (k.2.2 : ℝ) := by
    simp only [dtot, zero_mul, add_zero]
    rw [hcast, htt, hcard]
  have hhL : h L = g k := rfl
  rw [hstep, hdtot, hhL,
    sum_erase_pair_type_eq (L : Finset (Lin n)) linType (fun t t' => g (mergeCounts k t t'))]
  have hN : ∀ t, ((∑ q ∈ (L : Finset (Lin n)), if linType q = t then 1 else 0 : ℕ) : ℝ) =
      (linCount t (L : Finset (Lin n)) : ℝ) := fun t => rfl
  have hFF : linCount (false, false) (L : Finset (Lin n)) = 0 := by
    unfold linCount
    refine Finset.sum_eq_zero fun p hp => ?_
    rcases hL.carries p hp with h1 | h1 <;> simp [linType, h1]
  have hA : linCount (true, false) (L : Finset (Lin n)) = k.1 := rfl
  have hB : linCount (false, true) (L : Finset (Lin n)) = k.2.1 := rfl
  have hC : linCount (true, true) (L : Finset (Lin n)) = k.2.2 := rfl
  have m1 : mergeCounts k (true, false) (true, false) = (k.1 - 1, k.2.1, k.2.2) := by
    simp [mergeCounts, mergeType, typeVec]
  have m2 : mergeCounts k (false, true) (false, true) = (k.1, k.2.1 - 1, k.2.2) := by
    simp [mergeCounts, mergeType, typeVec]
  have m3 : mergeCounts k (true, true) (true, true) = (k.1, k.2.1, k.2.2 - 1) := by
    simp [mergeCounts, mergeType, typeVec]
  have m4 : mergeCounts k (true, false) (false, true) = (k.1 - 1, k.2.1 - 1, k.2.2 + 1) := by
    simp [mergeCounts, mergeType, typeVec]
  have m4' : mergeCounts k (false, true) (true, false) = (k.1 - 1, k.2.1 - 1, k.2.2 + 1) := by
    simp [mergeCounts, mergeType, typeVec]
  have m5 : mergeCounts k (true, false) (true, true) = (k.1 - 1, k.2.1, k.2.2) := by
    simp [mergeCounts, mergeType, typeVec]
  have m5' : mergeCounts k (true, true) (true, false) = (k.1 - 1, k.2.1, k.2.2) := by
    simp [mergeCounts, mergeType, typeVec]
  have m6 : mergeCounts k (false, true) (true, true) = (k.1, k.2.1 - 1, k.2.2) := by
    simp [mergeCounts, mergeType, typeVec]
  have m6' : mergeCounts k (true, true) (false, true) = (k.1, k.2.1 - 1, k.2.2) := by
    simp [mergeCounts, mergeType, typeVec]
  simp only [hN, Fintype.sum_prod_type, Fintype.sum_bool, hFF, hA, hB, hC, m1, m2, m3, m4, m4',
    m5, m5', m6, m6', Nat.cast_zero, zero_mul, mul_zero, add_zero, countGen]
  push_cast
  ring

theorem eventKernel_generator_eq_argRateChain (R : ℝ) (hR : 0 ≤ R) (x y : ℝ) (hxy : x < y)
    (z : AugmentedState) (hm : 2 ≤ z.1.2.2.1) (L : ASt n) (hL : WF (L : Finset (Lin n)))
    (hzL : astCounts (L : Finset (Lin n)) = typeCounts x y z.1) (g : Counts → ℝ)
    (hg : ∃ C, ∀ k, |g k| ≤ C) :
    (totalRate false R z.1 : ℝ) *
        (∫ w, g (typeCounts x y w.1) ∂eventKernel false R z - g (typeCounts x y z.1)) =
      ∑ M : ASt n, (argRateChain 0 0 (R * (y - x)) le_rfl le_rfl
        (mul_nonneg hR (sub_nonneg.mpr hxy.le))).Q L M * g (astCounts M) := by
  rw [totalRate_mul_eventKernel_sub_eq_countGen R hR x y hxy z hm g hg,
    argRateChain_generator _ _ hL g, hzL]

end Rhone.Coalescent.IntervalCounts
