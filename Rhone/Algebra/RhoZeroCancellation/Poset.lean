/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib

/-! # A disconnected dependency poset cancels -/

@[expose] public section

namespace Rhone.Algebra.RhoZeroCancellation

open Finset

variable {F : Type*} [Field F] {ι : Type*}

def prefixVal (x : ι → F) (L : List ι) (m : ℕ) : F := ((L.take m).map x).sum

def Gword (x : ι → F) (L : List ι) : F :=
  ∏ m ∈ Finset.range L.length, (prefixVal x L (m + 1))⁻¹

def Fword (x : ι → F) (L : List ι) : F :=
  ∏ m ∈ Finset.range (L.length - 1), (prefixVal x L (m + 1))⁻¹

@[simp] theorem Gword_nil (x : ι → F) : Gword x [] = 1 := by simp [Gword]

@[simp] theorem Fword_nil (x : ι → F) : Fword x [] = 1 := by simp [Fword]

theorem prefixVal_append_singleton_of_le (x : ι → F) (L : List ι) (v : ι) {m : ℕ}
    (hm : m ≤ L.length) : prefixVal x (L ++ [v]) m = prefixVal x L m := by
  simp [prefixVal, List.take_append_of_le_length hm]

theorem prefixVal_length (x : ι → F) (L : List ι) :
    prefixVal x L L.length = (L.map x).sum := by
  simp [prefixVal]

theorem Fword_append_singleton (x : ι → F) (L : List ι) (v : ι) :
    Fword x (L ++ [v]) = Gword x L := by
  simp only [Fword, Gword, List.length_append, List.length_singleton, Nat.add_sub_cancel]
  refine Finset.prod_congr rfl fun m hm => ?_
  rw [Finset.mem_range] at hm
  rw [prefixVal_append_singleton_of_le x L v (by omega)]

theorem Gword_append_singleton (x : ι → F) (L : List ι) (v : ι) :
    Gword x (L ++ [v]) = Gword x L * (((L ++ [v]).map x).sum)⁻¹ := by
  have hlen : (L ++ [v]).length = L.length + 1 := by simp
  rw [Gword, hlen, Finset.prod_range_succ, ← prefixVal_length x (L ++ [v]), hlen]
  congr 1
  refine Finset.prod_congr rfl fun m hm => ?_
  rw [Finset.mem_range] at hm
  rw [prefixVal_append_singleton_of_le x L v (by omega)]

noncomputable def linExts (R : ι → ι → Prop) (T : Finset ι) : Finset (List ι) :=
  open scoped Classical in
  T.toList.permutations.toFinset.filter fun L => L.Pairwise fun a b => ¬ R b a

noncomputable def maximals (R : ι → ι → Prop) (T : Finset ι) : Finset ι :=
  open scoped Classical in
  T.filter fun v => ∀ a ∈ T, ¬ R v a

variable {R : ι → ι → Prop}

theorem mem_linExts {T : Finset ι} {L : List ι} :
    L ∈ linExts R T ↔ (L : Multiset ι) = T.val ∧ L.Pairwise fun a b => ¬ R b a := by
  classical
  rw [linExts, Finset.mem_filter, List.mem_toFinset, List.mem_permutations,
    ← Multiset.coe_eq_coe, Finset.coe_toList]

theorem mem_maximals {T : Finset ι} {v : ι} :
    v ∈ maximals R T ↔ v ∈ T ∧ ∀ a ∈ T, ¬ R v a := by
  classical
  rw [maximals, Finset.mem_filter]

theorem maximals_subset (T : Finset ι) : maximals R T ⊆ T := fun _ hv => (mem_maximals.mp hv).1

@[simp] theorem linExts_empty : linExts R (∅ : Finset ι) = {[]} := by
  ext L
  rw [mem_linExts, Finset.mem_singleton]
  constructor
  · rintro ⟨h, -⟩
    exact (Multiset.coe_eq_zero L).mp h
  · rintro rfl
    exact ⟨rfl, List.Pairwise.nil⟩

theorem sum_map_of_mem_linExts {T : Finset ι} {L : List ι} (h : (L : Multiset ι) = T.val)
    (x : ι → F) : (L.map x).sum = ∑ i ∈ T, x i := by
  rw [Finset.sum_eq_multiset_sum, ← h]
  rfl

theorem mem_of_mem_linExts {T : Finset ι} {L : List ι} (h : (L : Multiset ι) = T.val) {a : ι}
    (ha : a ∈ L) : a ∈ T := by
  have hL : a ∈ (L : Multiset ι) := ha
  rwa [h, Finset.mem_val] at hL

theorem coe_append_singleton (L : List ι) (v : ι) :
    ((L ++ [v] : List ι) : Multiset ι) = v ::ₘ (L : Multiset ι) := by
  have h : ((L ++ [v] : List ι) : Multiset ι) = (L : Multiset ι) + ({v} : Multiset ι) := rfl
  rw [h, add_comm, Multiset.singleton_add]

noncomputable def Gsum (R : ι → ι → Prop) (x : ι → F) (T : Finset ι) : F :=
  ∑ L ∈ linExts R T, Gword x L

noncomputable def Fsum (R : ι → ι → Prop) (x : ι → F) (T : Finset ι) : F :=
  ∑ L ∈ linExts R T, Fword x L

@[simp] theorem Gsum_empty (x : ι → F) : Gsum R x (∅ : Finset ι) = 1 := by
  simp [Gsum]

@[simp] theorem Fsum_empty (x : ι → F) : Fsum R x (∅ : Finset ι) = 1 := by
  simp [Fsum]

theorem linExts_eq_biUnion [DecidableEq ι] (hirr : ∀ a, ¬ R a a) {T : Finset ι}
    (hT : T.Nonempty) :
    linExts R T
      = (maximals R T).biUnion fun v => (linExts R (T.erase v)).image fun L => L ++ [v] := by
  ext L
  simp only [Finset.mem_biUnion, Finset.mem_image]
  constructor
  · intro hL
    rw [mem_linExts] at hL
    obtain ⟨hmul, hpw⟩ := hL
    have hne : L ≠ [] := by
      rintro rfl
      obtain ⟨a, ha⟩ := hT
      have hmem : a ∈ ((([] : List ι) : Multiset ι)) := by rw [hmul, Finset.mem_val]; exact ha
      simp at hmem
    obtain ⟨D, v, rfl⟩ : ∃ D v, L = D ++ [v] :=
      ⟨L.dropLast, L.getLast hne, (List.dropLast_append_getLast hne).symm⟩
    rw [List.pairwise_append] at hpw
    obtain ⟨hpwd, -, hcross⟩ := hpw
    have hvT : v ∈ T := mem_of_mem_linExts hmul (by simp)
    have hmax : v ∈ maximals R T := by
      rw [mem_maximals]
      refine ⟨hvT, fun a ha => ?_⟩
      have haL : a ∈ D ++ [v] := by
        have hm : a ∈ ((D ++ [v] : List ι) : Multiset ι) := by rw [hmul, Finset.mem_val]; exact ha
        exact hm
      rw [List.mem_append, List.mem_singleton] at haL
      rcases haL with h | rfl
      · exact hcross a h v (List.mem_singleton_self v)
      · exact hirr a
    refine ⟨v, hmax, D, ?_, rfl⟩
    rw [mem_linExts]
    refine ⟨?_, hpwd⟩
    rw [Finset.erase_val, ← hmul, coe_append_singleton, Multiset.erase_cons_head]
  · rintro ⟨v, hv, L', hL', rfl⟩
    rw [mem_maximals] at hv
    rw [mem_linExts] at hL'
    obtain ⟨hvT, hvmax⟩ := hv
    obtain ⟨hmul', hpw'⟩ := hL'
    rw [mem_linExts]
    constructor
    · rw [coe_append_singleton, hmul', Finset.erase_val,
        Multiset.cons_erase (Finset.mem_val.mpr hvT)]
    · rw [List.pairwise_append]
      refine ⟨hpw', List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
      rw [List.mem_singleton] at hb
      subst hb
      exact hvmax a (Finset.mem_of_mem_erase (mem_of_mem_linExts hmul' ha))

theorem sum_linExts_last [DecidableEq ι] (hirr : ∀ a, ¬ R a a) {T : Finset ι} (hT : T.Nonempty)
    (f : List ι → F) :
    ∑ L ∈ linExts R T, f L
      = ∑ v ∈ maximals R T, ∑ L ∈ linExts R (T.erase v), f (L ++ [v]) := by
  rw [linExts_eq_biUnion hirr hT, Finset.sum_biUnion]
  · refine Finset.sum_congr rfl fun v _ => ?_
    exact Finset.sum_image fun L _ L' _ h => List.append_cancel_right h
  · intro v _ w _ hvw
    simp only [Function.onFun, Finset.disjoint_left, Finset.mem_image]
    rintro L ⟨L₁, -, rfl⟩ ⟨L₂, -, hL₂⟩
    have hg : (L₁ ++ [v]).getLast? = (L₂ ++ [w]).getLast? := by rw [hL₂]
    rw [List.getLast?_concat, List.getLast?_concat] at hg
    exact hvw (Option.some.inj hg)

theorem Fsum_eq_sum_maximals_erase [DecidableEq ι] (hirr : ∀ a, ¬ R a a) (x : ι → F)
    {T : Finset ι} (hT : T.Nonempty) :
    Fsum R x T = ∑ v ∈ maximals R T, Gsum R x (T.erase v) := by
  rw [Fsum, sum_linExts_last hirr hT]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Gsum]
  exact Finset.sum_congr rfl fun L _ => Fword_append_singleton x L v

theorem Fsum_eq_total_mul_Gsum (x : ι → F) {T : Finset ι} (hT : T.Nonempty)
    (htot : ∑ i ∈ T, x i ≠ 0) : Fsum R x T = (∑ i ∈ T, x i) * Gsum R x T := by
  rw [Fsum, Gsum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun L hL => ?_
  rw [mem_linExts] at hL
  obtain ⟨hmul, -⟩ := hL
  have hlen : L.length = T.card := by
    rw [← Multiset.coe_card, hmul, Finset.card_def]
  have hlenpos : 0 < L.length := by
    rw [hlen, Finset.card_pos]; exact hT
  have hsum : prefixVal x L L.length = ∑ i ∈ T, x i := by
    rw [prefixVal_length, sum_map_of_mem_linExts hmul]
  rw [Gword, Fword, show L.length = (L.length - 1) + 1 from by omega, Finset.prod_range_succ,
    show L.length - 1 + 1 = L.length from by omega, hsum, mul_comm, mul_assoc,
    inv_mul_cancel₀ htot, mul_one]

theorem sum_maximals_erase [DecidableEq ι] (hirr : ∀ a, ¬ R a a) (x : ι → F) {T : Finset ι}
    (hT : T.Nonempty) (htot : ∑ i ∈ T, x i ≠ 0) :
    ∑ v ∈ maximals R T, Gsum R x (T.erase v) = (∑ i ∈ T, x i) * Gsum R x T := by
  rw [← Fsum_eq_sum_maximals_erase hirr x hT, Fsum_eq_total_mul_Gsum x hT htot]

theorem Gsum_eq_inv_mul_sum_maximals_erase [DecidableEq ι] (hirr : ∀ a, ¬ R a a) (x : ι → F)
    {T : Finset ι} (hT : T.Nonempty) (htot : ∑ i ∈ T, x i ≠ 0) :
    Gsum R x T = (∑ i ∈ T, x i)⁻¹ * ∑ v ∈ maximals R T, Gsum R x (T.erase v) := by
  rw [sum_maximals_erase hirr x hT htot, ← mul_assoc, inv_mul_cancel₀ htot, one_mul]

theorem maximals_union [DecidableEq ι] {A B : Finset ι}
    (hcross : ∀ a ∈ A, ∀ b ∈ B, ¬ R a b ∧ ¬ R b a) :
    maximals R (A ∪ B) = maximals R A ∪ maximals R B := by
  ext v
  simp only [mem_maximals, Finset.mem_union]
  constructor
  · rintro ⟨hv | hv, hmax⟩
    · exact Or.inl ⟨hv, fun a ha => hmax a (Or.inl ha)⟩
    · exact Or.inr ⟨hv, fun a ha => hmax a (Or.inr ha)⟩
  · rintro (⟨hv, hmax⟩ | ⟨hv, hmax⟩)
    · refine ⟨Or.inl hv, fun a ha => ?_⟩
      rcases ha with h | h
      · exact hmax a h
      · exact (hcross v hv a h).1
    · refine ⟨Or.inr hv, fun a ha => ?_⟩
      rcases ha with h | h
      · exact (hcross a h v hv).2
      · exact hmax a h

theorem erase_union_of_notMem_right [DecidableEq ι] {A B : Finset ι} {v : ι} (hvB : v ∉ B) :
    (A ∪ B).erase v = A.erase v ∪ B := by
  ext a
  simp only [Finset.mem_erase, Finset.mem_union]
  constructor
  · rintro ⟨hav, h | h⟩
    · exact Or.inl ⟨hav, h⟩
    · exact Or.inr h
  · rintro (⟨hav, h⟩ | h)
    · exact ⟨hav, Or.inl h⟩
    · exact ⟨fun hh => hvB (hh ▸ h), Or.inr h⟩

theorem Gsum_union [DecidableEq ι] (hirr : ∀ a, ¬ R a a) (x : ι → F) :
    ∀ (n : ℕ) (A B : Finset ι), (A ∪ B).card = n → Disjoint A B →
      (∀ a ∈ A, ∀ b ∈ B, ¬ R a b ∧ ¬ R b a) →
      (∀ U ⊆ A ∪ B, U.Nonempty → ∑ i ∈ U, x i ≠ 0) →
      Gsum R x (A ∪ B) = Gsum R x A * Gsum R x B := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro A B hcard hdisj hcross hne
    rcases A.eq_empty_or_nonempty with rfl | hAne
    · simp
    rcases B.eq_empty_or_nonempty with rfl | hBne
    · simp
    have hABne : (A ∪ B).Nonempty := hAne.mono Finset.subset_union_left
    have htotAB : ∑ i ∈ A ∪ B, x i ≠ 0 := hne _ (subset_refl _) hABne
    have htotA : ∑ i ∈ A, x i ≠ 0 := hne _ Finset.subset_union_left hAne
    have htotB : ∑ i ∈ B, x i ≠ 0 := hne _ Finset.subset_union_right hBne
    have e1 : ∀ v ∈ maximals R A,
        Gsum R x ((A ∪ B).erase v) = Gsum R x (A.erase v) * Gsum R x B := by
      intro v hv
      have hvA : v ∈ A := (mem_maximals.mp hv).1
      have hvB : v ∉ B := Finset.disjoint_left.mp hdisj hvA
      have heq : (A ∪ B).erase v = A.erase v ∪ B := erase_union_of_notMem_right hvB
      rw [heq]
      refine IH ((A.erase v ∪ B).card) ?_ (A.erase v) B rfl ?_ ?_ ?_
      · rw [← hcard, ← heq]
        exact Finset.card_erase_lt_of_mem (Finset.mem_union_left _ hvA)
      · exact Finset.disjoint_of_subset_left (Finset.erase_subset _ _) hdisj
      · exact fun a ha b hb => hcross a (Finset.mem_of_mem_erase ha) b hb
      · intro U hU hUne
        refine hne U (hU.trans ?_) hUne
        rw [← heq]
        exact Finset.erase_subset _ _
    have e2 : ∀ v ∈ maximals R B,
        Gsum R x ((A ∪ B).erase v) = Gsum R x A * Gsum R x (B.erase v) := by
      intro v hv
      have hvB : v ∈ B := (mem_maximals.mp hv).1
      have hvA : v ∉ A := Finset.disjoint_right.mp hdisj hvB
      have heq : (A ∪ B).erase v = A ∪ B.erase v := by
        rw [Finset.union_comm, erase_union_of_notMem_right hvA, Finset.union_comm]
      rw [heq]
      refine IH ((A ∪ B.erase v).card) ?_ A (B.erase v) rfl ?_ ?_ ?_
      · rw [← hcard, ← heq]
        exact Finset.card_erase_lt_of_mem (Finset.mem_union_right _ hvB)
      · exact Finset.disjoint_of_subset_right (Finset.erase_subset _ _) hdisj
      · exact fun a ha b hb => hcross a ha b (Finset.mem_of_mem_erase hb)
      · intro U hU hUne
        refine hne U (hU.trans ?_) hUne
        rw [← heq]
        exact Finset.erase_subset _ _
    have hmaxdisj : Disjoint (maximals R A) (maximals R B) :=
      Finset.disjoint_of_subset_left (maximals_subset A)
        (Finset.disjoint_of_subset_right (maximals_subset B) hdisj)
    have hab : (∑ i ∈ A, x i) + ∑ i ∈ B, x i ≠ 0 := by
      rw [← Finset.sum_union hdisj]; exact htotAB
    rw [Gsum_eq_inv_mul_sum_maximals_erase hirr x hABne htotAB, maximals_union hcross,
      Finset.sum_union hmaxdisj, Finset.sum_congr rfl e1, Finset.sum_congr rfl e2,
      ← Finset.sum_mul, ← Finset.mul_sum,
      sum_maximals_erase hirr x hAne htotA, sum_maximals_erase hirr x hBne htotB,
      Finset.sum_union hdisj]
    field_simp

theorem Fsum_eq_zero_of_disconnected [DecidableEq ι] (hirr : ∀ a, ¬ R a a) (x : ι → F)
    {T S : Finset ι} (hST : S ⊆ T) (hS : S.Nonempty) (hSc : (T \ S).Nonempty)
    (hsplit : ∀ a ∈ S, ∀ b ∈ T \ S, ¬ R a b ∧ ¬ R b a)
    (htot : ∑ i ∈ T, x i = 0)
    (hproper : ∀ U ⊆ T, U.Nonempty → U ≠ T → ∑ i ∈ U, x i ≠ 0) :
    Fsum R x T = 0 := by
  have hTeq : S ∪ (T \ S) = T := Finset.union_sdiff_of_subset hST
  have hdisj : Disjoint S (T \ S) := Finset.disjoint_sdiff
  have hTne : T.Nonempty := hS.mono hST
  have hScT : T \ S ⊆ T := Finset.sdiff_subset
  have hSneT : S ≠ T := by
    obtain ⟨b, hb⟩ := hSc
    rintro rfl
    exact (Finset.mem_sdiff.mp hb).2 (Finset.mem_sdiff.mp hb).1
  have hScneT : T \ S ≠ T := by
    obtain ⟨a, ha⟩ := hS
    intro h
    have haT : a ∈ T \ S := by rw [h]; exact hST ha
    exact (Finset.mem_sdiff.mp haT).2 ha
  have htotS : ∑ i ∈ S, x i ≠ 0 := hproper S hST hS hSneT
  have htotSc : ∑ i ∈ T \ S, x i ≠ 0 := hproper (T \ S) hScT hSc hScneT
  have hfac : ∀ C D : Finset ι, C ⊆ S → D ⊆ T \ S → C ∪ D ≠ T →
      Gsum R x (C ∪ D) = Gsum R x C * Gsum R x D := by
    intro C D hC hD hCD
    refine Gsum_union hirr x ((C ∪ D).card) C D rfl
      (Finset.disjoint_of_subset_left hC (Finset.disjoint_of_subset_right hD hdisj))
      (fun a ha b hb => hsplit a (hC ha) b (hD hb)) ?_
    intro U hU hUne
    have hUT : U ⊆ T := hU.trans (Finset.union_subset (hC.trans hST) (hD.trans hScT))
    refine hproper U hUT hUne ?_
    intro hUeq
    exact hCD (Finset.Subset.antisymm (Finset.union_subset (hC.trans hST) (hD.trans hScT))
      (hUeq ▸ hU))
  have e1 : ∀ v ∈ maximals R S,
      Gsum R x (T.erase v) = Gsum R x (S.erase v) * Gsum R x (T \ S) := by
    intro v hv
    have hvS : v ∈ S := (mem_maximals.mp hv).1
    have heq : T.erase v = S.erase v ∪ (T \ S) := by
      ext a
      simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_sdiff]
      constructor
      · rintro ⟨hav, haT⟩
        by_cases haS : a ∈ S
        · exact Or.inl ⟨hav, haS⟩
        · exact Or.inr ⟨haT, haS⟩
      · rintro (⟨hav, haS⟩ | ⟨haT, haS⟩)
        · exact ⟨hav, hST haS⟩
        · exact ⟨fun hh => haS (by rw [hh]; exact hvS), haT⟩
    rw [heq]
    refine hfac _ _ (Finset.erase_subset _ _) (subset_refl _) ?_
    intro h
    have hvT : v ∈ T := hST hvS
    have hnot : v ∉ T.erase v := Finset.notMem_erase v T
    rw [← heq] at h
    rw [h] at hnot
    exact hnot hvT
  have e2 : ∀ v ∈ maximals R (T \ S),
      Gsum R x (T.erase v) = Gsum R x S * Gsum R x ((T \ S).erase v) := by
    intro v hv
    have hvSc : v ∈ T \ S := (mem_maximals.mp hv).1
    have hvS : v ∉ S := (Finset.mem_sdiff.mp hvSc).2
    have heq : T.erase v = S ∪ ((T \ S).erase v) := by
      ext a
      simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_sdiff]
      constructor
      · rintro ⟨hav, haT⟩
        by_cases haS : a ∈ S
        · exact Or.inl haS
        · exact Or.inr ⟨hav, haT, haS⟩
      · rintro (haS | ⟨hav, haT, -⟩)
        · exact ⟨fun hh => hvS (by rw [← hh]; exact haS), hST haS⟩
        · exact ⟨hav, haT⟩
    rw [heq]
    refine hfac _ _ (subset_refl _) (Finset.erase_subset _ _) ?_
    intro h
    have hvT : v ∈ T := hScT hvSc
    have hnot : v ∉ T.erase v := Finset.notMem_erase v T
    rw [← heq] at h
    rw [h] at hnot
    exact hnot hvT
  have hmaxdisj : Disjoint (maximals R S) (maximals R (T \ S)) :=
    Finset.disjoint_of_subset_left (maximals_subset S)
      (Finset.disjoint_of_subset_right (maximals_subset (T \ S)) hdisj)
  have hmaxT : maximals R T = maximals R S ∪ maximals R (T \ S) := by
    have h := maximals_union (R := R) hsplit
    rwa [hTeq] at h
  rw [Fsum_eq_sum_maximals_erase hirr x hTne, hmaxT, Finset.sum_union hmaxdisj,
    Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, ← Finset.sum_mul, ← Finset.mul_sum,
    sum_maximals_erase hirr x hS htotS, sum_maximals_erase hirr x hSc htotSc]
  have hsplitsum : (∑ i ∈ S, x i) + ∑ i ∈ T \ S, x i = 0 := by
    rw [← Finset.sum_union hdisj, hTeq]; exact htot
  have hgoal : (∑ i ∈ S, x i) * Gsum R x S * Gsum R x (T \ S)
      + Gsum R x S * ((∑ i ∈ T \ S, x i) * Gsum R x (T \ S))
      = ((∑ i ∈ S, x i) + ∑ i ∈ T \ S, x i) * (Gsum R x S * Gsum R x (T \ S)) := by ring
  rw [hgoal, hsplitsum, zero_mul]

theorem Fsum_univ_eq_zero_of_disconnected [Fintype ι] (hirr : ∀ a, ¬ R a a)
    (x : ι → F) (htot : ∑ i, x i = 0)
    (hproper : ∀ U : Finset ι, U.Nonempty → U ≠ Finset.univ → ∑ i ∈ U, x i ≠ 0)
    {S : Finset ι} (hS : S.Nonempty) (hSc : S ≠ Finset.univ)
    (hsplit : ∀ a ∈ S, ∀ b ∉ S, ¬ R a b ∧ ¬ R b a) :
    Fsum R x Finset.univ = 0 := by
  classical
  refine Fsum_eq_zero_of_disconnected hirr x (Finset.subset_univ S) hS ?_ ?_ htot
    (fun U _ hUne hUuniv => hproper U hUne hUuniv)
  · rw [Finset.sdiff_nonempty]
    intro h
    exact hSc (Finset.Subset.antisymm (Finset.subset_univ S) h)
  · intro a ha b hb
    exact hsplit a ha b (Finset.mem_sdiff.mp hb).2

end Rhone.Algebra.RhoZeroCancellation
