/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Statistics.EwensLabelWeight

/-!
# The first-event recursion of the coalescent with killing, for labelled blocks

Source: durrett2008, sec. 1.3.1. -/

@[expose] public section
namespace Rhone.Statistics
open Finset

variable {ι κ : Type*} [DecidableEq κ] {θ : ℝ} {T : Finset ι} {ℓ : ι → Finset κ} {i k r : ι}

noncomputable def cfgWeight (θ : ℝ) (T : Finset ι) (ℓ : ι → Finset κ) : ℝ :=
  if ∀ i ∈ T, (ℓ i).card ≤ 1 then labelWeight θ (∑ i ∈ T, (ℓ i).val) else 0

theorem cfgWeight_congr' {ι' : Type*} (θ : ℝ) {T' : Finset ι'} {ℓ' : ι' → Finset κ}
    (h1 : (∀ i ∈ T, (ℓ i).card ≤ 1) ↔ ∀ i ∈ T', (ℓ' i).card ≤ 1)
    (h2 : ∑ i ∈ T, (ℓ i).val = ∑ i ∈ T', (ℓ' i).val) :
    cfgWeight θ T ℓ = cfgWeight θ T' ℓ' := by
  unfold cfgWeight
  rw [h2]
  exact if_congr h1 rfl rfl

theorem cfgWeight_congr (θ : ℝ) {ℓ' : ι → Finset κ} (h : ∀ i ∈ T, ℓ i = ℓ' i) :
    cfgWeight θ T ℓ = cfgWeight θ T ℓ' := by
  refine cfgWeight_congr' θ ?_ (Finset.sum_congr rfl fun i hi => by rw [h i hi])
  exact forall₂_congr fun i hi => by rw [h i hi]

theorem cfgWeight_eq_zero (θ : ℝ) (hi : i ∈ T) (h : 1 < (ℓ i).card) : cfgWeight θ T ℓ = 0 :=
  ite_eq_right fun hv => absurd (hv i hi) (not_le.2 h)

theorem cfgWeight_of_valid (θ : ℝ) (hv : ∀ i ∈ T, (ℓ i).card ≤ 1) :
    cfgWeight θ T ℓ = labelWeight θ (∑ i ∈ T, (ℓ i).val) :=
  ite_eq_left hv

def labelFull (T : Finset ι) (ℓ : ι → Finset κ) (i : ι) : Prop :=
  (ℓ i).card ≤ 1 ∧ ∀ k ∈ T, k ≠ i → Disjoint (ℓ i) (ℓ k)

variable [DecidableEq ι]

instance instDecidableLabelFull (T : Finset ι) (ℓ : ι → Finset κ) (i : ι) :
    Decidable (labelFull T ℓ i) := by
  unfold labelFull
  infer_instance

def mergeLabels (ℓ : ι → Finset κ) (i k : ι) : ι → Finset κ :=
  Function.update (Function.update ℓ k ∅) i (ℓ i ∪ ℓ k)

theorem mergeLabels_left : mergeLabels ℓ i k i = ℓ i ∪ ℓ k :=
  Function.update_self ..

theorem mergeLabels_right (h : k ≠ i) : mergeLabels ℓ i k k = ∅ := by
  rw [mergeLabels, Function.update_of_ne h, Function.update_self]

theorem mergeLabels_of_ne (hi : r ≠ i) (hk : r ≠ k) : mergeLabels ℓ i k r = ℓ r := by
  rw [mergeLabels, Function.update_of_ne hi, Function.update_of_ne hk]

theorem valid_mergeLabels (hi : i ∈ T) (hk : k ∈ T.erase i) :
    (∀ r ∈ T, (mergeLabels ℓ i k r).card ≤ 1) ↔
      (ℓ i ∪ ℓ k).card ≤ 1 ∧ ∀ r ∈ (T.erase i).erase k, (ℓ r).card ≤ 1 := by
  have hki : k ≠ i := (mem_erase.1 hk).1
  constructor
  · intro h
    refine ⟨by simpa only [mergeLabels_left] using h i hi, fun r hr => ?_⟩
    obtain ⟨hrk, hr'⟩ := mem_erase.1 hr
    obtain ⟨hri, hrT⟩ := mem_erase.1 hr'
    have h' := h r hrT
    rwa [mergeLabels_of_ne hri hrk] at h'
  · rintro ⟨h1, h2⟩ r hr
    by_cases hri : r = i
    · rw [hri, mergeLabels_left]
      exact h1
    · by_cases hrk : r = k
      · rw [hrk, mergeLabels_right hki]
        simp
      · rw [mergeLabels_of_ne hri hrk]
        exact h2 r (mem_erase.2 ⟨hrk, mem_erase.2 ⟨hri, hr⟩⟩)

theorem sum_mergeLabels (hi : i ∈ T) (hk : k ∈ T.erase i) :
    ∑ r ∈ T, (mergeLabels ℓ i k r).val =
      (ℓ i ∪ ℓ k).val + ∑ r ∈ (T.erase i).erase k, (ℓ r).val := by
  have hki : k ≠ i := (mem_erase.1 hk).1
  rw [← Finset.add_sum_erase T _ hi, ← Finset.add_sum_erase (T.erase i) _ hk, mergeLabels_left,
    mergeLabels_right hki, Finset.empty_val, zero_add]
  congr 1
  refine Finset.sum_congr rfl fun r hr => ?_
  obtain ⟨hrk, hr'⟩ := mem_erase.1 hr
  rw [mergeLabels_of_ne (mem_erase.1 hr').1 hrk]

omit [DecidableEq κ] in
theorem sum_labels_split (hi : i ∈ T) (hk : k ∈ T.erase i) :
    ∑ r ∈ T, (ℓ r).val =
      (ℓ i).val + ((ℓ k).val + ∑ r ∈ (T.erase i).erase k, (ℓ r).val) := by
  rw [← Finset.add_sum_erase T _ hi, ← Finset.add_sum_erase (T.erase i) _ hk]

theorem cfgWeight_update_empty (θ : ℝ) (hv : ∀ r ∈ T, (ℓ r).card ≤ 1) (hk : k ∈ T) {t : κ}
    (hkt : ℓ k = {t}) {X : Multiset κ} (hX : t ::ₘ X = ∑ r ∈ T, (ℓ r).val) :
    cfgWeight θ T (Function.update ℓ k ∅) = labelWeight θ X := by
  have hsum : ∑ r ∈ T, (Function.update ℓ k ∅ r).val = ∑ r ∈ T.erase k, (ℓ r).val := by
    rw [← Finset.add_sum_erase T _ hk, Function.update_self, Finset.empty_val, zero_add]
    exact Finset.sum_congr rfl fun r hr => by rw [Function.update_of_ne (mem_erase.1 hr).1]
  have hXe : X = ∑ r ∈ T.erase k, (ℓ r).val := by
    rw [← Finset.add_sum_erase T _ hk, hkt, Finset.singleton_val, Multiset.singleton_add] at hX
    exact (Multiset.cons_inj_right t).1 hX
  have hv' : ∀ r ∈ T, (Function.update ℓ k ∅ r).card ≤ 1 := by
    intro r hr
    by_cases hrk : r = k
    · rw [hrk, Function.update_self]
      simp
    · rw [Function.update_of_ne hrk]
      exact hv r hr
  rw [cfgWeight_of_valid θ hv', hsum, hXe]

theorem sum_cfgWeight_mergeLabels (hθ : 0 < θ) (hi : i ∈ T) :
    ∑ k ∈ T.erase i, cfgWeight θ T (mergeLabels ℓ i k) +
      (if labelFull T ℓ i then θ * cfgWeight θ T (Function.update ℓ i ∅) else 0) =
      ((T.card : ℝ) - 1 + θ) * cfgWeight θ T ℓ := by
  have hcard : ((T.erase i).card : ℝ) = (T.card : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem hi, Nat.cast_sub (Finset.card_pos.2 ⟨i, hi⟩), Nat.cast_one]
  by_cases hv : ∀ r ∈ T, (ℓ r).card ≤ 1
  · rcases (ℓ i).eq_empty_or_nonempty with h0 | ⟨t, ht⟩
    · have hm : ∀ k ∈ T.erase i, cfgWeight θ T (mergeLabels ℓ i k) = cfgWeight θ T ℓ := by
        intro k hk
        refine cfgWeight_congr' θ ?_ ?_
        · rw [valid_mergeLabels hi hk, h0, Finset.empty_union]
          exact iff_of_true ⟨hv k (mem_of_mem_erase hk), fun r hr =>
            hv r (mem_of_mem_erase (mem_of_mem_erase hr))⟩ hv
        · rw [sum_mergeLabels hi hk, sum_labels_split hi hk, h0, Finset.empty_union,
            Finset.empty_val, zero_add]
      have hfull : labelFull T ℓ i :=
        ⟨hv i hi, fun k _ _ => by rw [h0]; exact Finset.disjoint_empty_left _⟩
      have hupd : Function.update ℓ i ∅ = ℓ := by
        rw [← h0]
        exact Function.update_eq_self i ℓ
      rw [Finset.sum_congr rfl hm, Finset.sum_const, nsmul_eq_mul, hcard, ite_eq_left hfull,
        hupd]
      ring
    · have hit : ℓ i = {t} := Finset.eq_singleton_iff_unique_mem.2
        ⟨ht, fun y hy => Finset.card_le_one.1 (hv i hi) y hy t ht⟩
      have hM : t ::ₘ (∑ k ∈ T.erase i, (ℓ k).val) = ∑ r ∈ T, (ℓ r).val := by
        rw [← Finset.add_sum_erase T _ hi, hit, Finset.singleton_val, Multiset.singleton_add]
      have hsing : ∀ k ∈ T.erase i, t ∈ ℓ k → ℓ k = {t} := fun k hk htk =>
        Finset.eq_singleton_iff_unique_mem.2
          ⟨htk, fun y hy => Finset.card_le_one.1 (hv k (mem_of_mem_erase hk)) y hy t htk⟩
      have he : cfgWeight θ T ℓ = labelWeight θ (t ::ₘ (∑ k ∈ T.erase i, (ℓ k).val)) := by
        rw [cfgWeight_of_valid θ hv, hM]
      have hterm : ∀ k ∈ T.erase i, cfgWeight θ T (mergeLabels ℓ i k) =
          (if ℓ k = ∅ then cfgWeight θ T ℓ else 0) +
            (if ℓ k = {t} then labelWeight θ (∑ k ∈ T.erase i, (ℓ k).val) else 0) := by
        intro k hk
        have hkT : k ∈ T := mem_of_mem_erase hk
        have hki : k ≠ i := (mem_erase.1 hk).1
        by_cases hk0 : ℓ k = ∅
        · have hne : ℓ k ≠ {t} := by
            rw [hk0]
            exact (Finset.singleton_ne_empty t).symm
          rw [ite_eq_left hk0, ite_eq_right hne, add_zero]
          refine cfgWeight_congr θ fun r _ => ?_
          by_cases hri : r = i
          · rw [hri, mergeLabels_left, hk0, Finset.union_empty]
          · by_cases hrk : r = k
            · rw [hrk, mergeLabels_right hki, hk0]
            · rw [mergeLabels_of_ne hri hrk]
        · by_cases hkt : ℓ k = {t}
          · rw [ite_eq_right hk0, ite_eq_left hkt, zero_add,
              ← cfgWeight_update_empty θ hv hkT hkt hM]
            refine cfgWeight_congr θ fun r _ => ?_
            by_cases hri : r = i
            · rw [hri, mergeLabels_left, hkt, Function.update_of_ne hki.symm, hit,
                Finset.union_self]
            · by_cases hrk : r = k
              · rw [hrk, mergeLabels_right hki, Function.update_self]
              · rw [mergeLabels_of_ne hri hrk, Function.update_of_ne hrk]
          · rw [ite_eq_right hk0, ite_eq_right hkt, add_zero]
            obtain ⟨u, hu⟩ := Finset.nonempty_iff_ne_empty.2 hk0
            have hut : t ≠ u := fun h => hkt (hsing k hk (h ▸ hu))
            refine cfgWeight_eq_zero θ hi ?_
            rw [mergeLabels_left]
            exact Finset.one_lt_card.2 ⟨t, mem_union_left _ ht, u, mem_union_right _ hu, hut⟩
      have hboole : ∀ (p : ι → Prop) [DecidablePred p] (v : ℝ),
          ∑ k ∈ T.erase i, (if p k then v else 0) = (((T.erase i).filter p).card : ℝ) * v :=
        fun p _ v => by rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      have hsum : ∑ k ∈ T.erase i, cfgWeight θ T (mergeLabels ℓ i k) =
          (((T.erase i).filter fun k => ℓ k = ∅).card : ℝ) * cfgWeight θ T ℓ +
            (((T.erase i).filter fun k => ℓ k = {t}).card : ℝ) *
              labelWeight θ (∑ k ∈ T.erase i, (ℓ k).val) := by
        rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, hboole, hboole]
      have hcount : (∑ k ∈ T.erase i, (ℓ k).val).count t =
          ((T.erase i).filter fun k => ℓ k = {t}).card := by
        rw [Multiset.count_sum', Finset.card_filter]
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [Multiset.count_eq_of_nodup (ℓ k).nodup]
        by_cases htk : t ∈ ℓ k
        · rw [ite_eq_left (show t ∈ (ℓ k).val from htk), ite_eq_left (hsing k hk htk)]
        · have hne : ℓ k ≠ {t} := fun h => htk (by rw [h]; exact mem_singleton_self t)
          rw [ite_eq_right (show ¬ t ∈ (ℓ k).val from htk), ite_eq_right hne]
      have hcardM : (∑ k ∈ T.erase i, (ℓ k).val).card +
          ((T.erase i).filter fun k => ℓ k = ∅).card = (T.erase i).card := by
        rw [Multiset.card_sum, Finset.card_filter, ← Finset.sum_add_distrib,
          Finset.card_eq_sum_ones]
        refine Finset.sum_congr rfl fun k hk => ?_
        by_cases hk0 : ℓ k = ∅
        · rw [ite_eq_left hk0, hk0]
          simp
        · rw [ite_eq_right hk0, add_zero]
          exact le_antisymm (hv k (mem_of_mem_erase hk))
            (Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 hk0))
      have hcR : ((∑ k ∈ T.erase i, (ℓ k).val).card : ℝ) +
          (((T.erase i).filter fun k => ℓ k = ∅).card : ℝ) = (T.card : ℝ) - 1 := by
        rw [← hcard]
        exact_mod_cast hcardM
      rw [hsum, he]
      by_cases hc : ((T.erase i).filter fun k => ℓ k = {t}).card = 0
      · have htM : t ∉ ∑ k ∈ T.erase i, (ℓ k).val := by
          rw [← Multiset.count_eq_zero, hcount, hc]
        have hfull : labelFull T ℓ i := by
          refine ⟨hv i hi, fun k hk hki => ?_⟩
          rw [hit, Finset.disjoint_singleton_left]
          intro htk
          have hkR : k ∈ T.erase i := mem_erase.2 ⟨hki, hk⟩
          have hkf : k ∈ (T.erase i).filter fun k => ℓ k = {t} :=
            mem_filter.2 ⟨hkR, hsing k hkR htk⟩
          exact (Finset.card_pos.2 ⟨k, hkf⟩).ne' hc
        have hrec := labelWeight_cons_of_notMem hθ htM
        rw [ite_eq_left hfull, cfgWeight_update_empty θ hv hi hit hM, hc, ← hcR]
        push_cast
        linear_combination (-1 : ℝ) * hrec
      · have htM : t ∈ ∑ k ∈ T.erase i, (ℓ k).val := by
          rw [← Multiset.count_pos, hcount]
          omega
        obtain ⟨k, hk⟩ := Finset.card_pos.1 (Nat.pos_of_ne_zero hc)
        obtain ⟨hkR, hkt⟩ := mem_filter.1 hk
        have hnf : ¬ labelFull T ℓ i := fun hf => by
          have hd := hf.2 k (mem_of_mem_erase hkR) (mem_erase.1 hkR).1
          rw [hit, hkt, Finset.disjoint_singleton] at hd
          exact hd rfl
        have hrec := labelWeight_cons_of_mem hθ htM
        rw [hcount] at hrec
        rw [ite_eq_right hnf, add_zero, ← hcR]
        linear_combination (-1 : ℝ) * hrec
  · push Not at hv
    obtain ⟨i0, hi0, hc0⟩ := hv
    have hm : ∀ k ∈ T.erase i, cfgWeight θ T (mergeLabels ℓ i k) = 0 := by
      intro k _
      rcases eq_or_ne i0 i with rfl | h1
      · refine cfgWeight_eq_zero θ hi ?_
        rw [mergeLabels_left]
        exact lt_of_lt_of_le hc0 (Finset.card_le_card Finset.subset_union_left)
      · rcases eq_or_ne i0 k with rfl | h2
        · refine cfgWeight_eq_zero θ hi ?_
          rw [mergeLabels_left]
          exact lt_of_lt_of_le hc0 (Finset.card_le_card Finset.subset_union_right)
        · refine cfgWeight_eq_zero θ hi0 ?_
          rwa [mergeLabels_of_ne h1 h2]
    have hkill : (if labelFull T ℓ i then θ * cfgWeight θ T (Function.update ℓ i ∅) else 0) =
        0 := by
      by_cases hf : labelFull T ℓ i
      · have hne : i0 ≠ i := by
          rintro rfl
          exact absurd hf.1 (not_le.2 hc0)
        rw [ite_eq_left hf, cfgWeight_eq_zero θ hi0 (by rwa [Function.update_of_ne hne]),
          mul_zero]
      · exact ite_eq_right hf
    rw [Finset.sum_congr rfl hm, Finset.sum_const_zero, hkill, cfgWeight_eq_zero θ hi0 hc0]
    ring

/-- Source: durrett2008, sec. 1.3.1. -/
theorem cfgWeight_recursion (hθ : 0 < θ) (T : Finset ι) (ℓ : ι → Finset κ) :
    (T.card : ℝ) * ((T.card : ℝ) - 1 + θ) * cfgWeight θ T ℓ =
      ∑ i ∈ T, ∑ k ∈ T.erase i, cfgWeight θ T (mergeLabels ℓ i k) +
        θ * ∑ i ∈ T.filter (labelFull T ℓ), cfgWeight θ T (Function.update ℓ i ∅) := by
  have h := Finset.sum_congr (s₁ := T) rfl fun i hi =>
    sum_cfgWeight_mergeLabels (ℓ := ℓ) hθ hi
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.sum_filter,
    ← Finset.mul_sum] at h
  linear_combination (-1 : ℝ) * h

end Rhone.Statistics
