/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Statistics.EwensLabelWeight
public import Rhone.Statistics.EwensUrn

/-! # Sums over labellings of a block-size type in the Ewens urn weights -/

@[expose] public section
namespace Rhone.Statistics
open Finset Polynomial Rhone.Combinatorics MarkovChain Probability

variable {κ : Type*} [DecidableEq κ]

def labelType (M : Multiset κ) : Multiset ℕ :=
  M.toFinset.val.map fun t => M.count t

theorem labelType_cons_of_notMem {t : κ} {M : Multiset κ} (ht : t ∉ M) :
    labelType (t ::ₘ M) = 1 ::ₘ labelType M := by
  have htf : t ∉ M.toFinset := fun h => ht (Multiset.mem_toFinset.1 h)
  unfold labelType
  rw [Multiset.toFinset_cons, Finset.insert_val_of_notMem htf, Multiset.map_cons,
    Multiset.count_cons_self, Multiset.count_eq_zero_of_notMem ht, zero_add]
  congr 1
  exact Multiset.map_congr rfl fun s hs =>
    Multiset.count_cons_of_ne (by rintro rfl; exact htf (Finset.mem_def.2 hs)) M

theorem labelType_cons_of_mem {t : κ} {M : Multiset κ} (ht : t ∈ M) :
    labelType (t ::ₘ M) = (M.count t + 1) ::ₘ (labelType M).erase (M.count t) := by
  have htf : t ∈ M.toFinset := Multiset.mem_toFinset.2 ht
  have hval : M.toFinset.val = t ::ₘ (M.toFinset.erase t).val := by
    conv_lhs => rw [← Finset.insert_erase htf]
    exact Finset.insert_val_of_notMem (Finset.notMem_erase t _)
  unfold labelType
  rw [Multiset.toFinset_cons, Finset.insert_eq_of_mem htf, hval, Multiset.map_cons,
    Multiset.map_cons, Multiset.erase_cons_head, Multiset.count_cons_self]
  congr 1
  exact Multiset.map_congr rfl fun s hs =>
    Multiset.count_cons_of_ne (Finset.ne_of_mem_erase (Finset.mem_def.2 hs)) M

theorem card_labelType (M : Multiset κ) : (labelType M).card = M.toFinset.card :=
  Multiset.card_map _ _

theorem sum_labelType (M : Multiset κ) : (labelType M).sum = M.card :=
  Multiset.toFinset_sum_count_eq M

theorem pos_of_mem_labelType {M : Multiset κ} {i : ℕ} (hi : i ∈ labelType M) : 0 < i := by
  obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.1 hi
  exact Multiset.count_pos.2 (Multiset.mem_toFinset.1 (Finset.mem_def.2 ht))

theorem sum_toFinset_count (M : Multiset κ) (G : ℕ → ℝ) :
    ∑ t ∈ M.toFinset, G (M.count t) =
      ∑ j ∈ (labelType M).toFinset, ((labelType M).count j : ℝ) * G j := by
  calc ∑ t ∈ M.toFinset, G (M.count t) = ((labelType M).map G).sum := by
        rw [labelType, Multiset.map_map]
        rfl
    _ = ∑ j ∈ (labelType M).toFinset, (labelType M).count j • G j :=
        Finset.sum_multiset_map_count _ _
    _ = ∑ j ∈ (labelType M).toFinset, ((labelType M).count j : ℝ) * G j :=
        Finset.sum_congr rfl fun j _ => nsmul_eq_mul _ _

def labelPartition {n : ℕ} (c : Fin n → κ) : Nat.Partition n where
  parts := labelType (univ.val.map c)
  parts_pos := fun hi => pos_of_mem_labelType hi
  parts_sum := by
    rw [sum_labelType, Multiset.card_map]
    exact (Finset.card_univ).trans (Fintype.card_fin n)

noncomputable def urnFactor (N : ℕ) (θ : ℝ) {n : ℕ} (q : Nat.Partition n)
    (p : Nat.Partition (n + 1)) : ℝ :=
  ((N - q.parts.card : ℕ) : ℝ) * (if p.parts = 1 ::ₘ q.parts then θ else 0) +
    ∑ j ∈ q.parts.toFinset,
      if p.parts = (j + 1) ::ₘ q.parts.erase j then (j : ℝ) * q.parts.count j else 0

theorem urnFactor_mul_descFactorial {θ : ℝ} (hθ : 0 < θ) (N : ℕ) {n : ℕ}
    (q : Nat.Partition n) (p : Nat.Partition (n + 1)) :
    urnFactor N θ q p * (N.descFactorial q.parts.card : ℝ) =
      (N.descFactorial p.parts.card : ℝ) * ((θ + n) * ewensUrnStep θ q p) := by
  have hq0 : θ + (n : ℝ) ≠ 0 := by positivity
  have he : (θ + n) * ewensUrnStep θ q p =
      (if p.parts = 1 ::ₘ q.parts then θ else 0) +
        ∑ j ∈ q.parts.toFinset,
          if p.parts = (j + 1) ::ₘ q.parts.erase j then (j : ℝ) * q.parts.count j else 0 := by
    unfold ewensUrnStep
    rw [mul_add, Finset.mul_sum]
    congr 1
    · by_cases h : p.parts = 1 ::ₘ q.parts
      · rw [ite_eq_left h, ite_eq_left h]
        field_simp
      · rw [ite_eq_right h, ite_eq_right h, mul_zero]
    · refine Finset.sum_congr rfl fun j _ => ?_
      by_cases h : p.parts = (j + 1) ::ₘ q.parts.erase j
      · rw [ite_eq_left h, ite_eq_left h]
        field_simp
      · rw [ite_eq_right h, ite_eq_right h, mul_zero]
  have ha : ((N - q.parts.card : ℕ) : ℝ) * (if p.parts = 1 ::ₘ q.parts then θ else 0) *
      (N.descFactorial q.parts.card : ℝ) =
      (N.descFactorial p.parts.card : ℝ) * (if p.parts = 1 ::ₘ q.parts then θ else 0) := by
    by_cases h : p.parts = 1 ::ₘ q.parts
    · have hc : p.parts.card = q.parts.card + 1 := by rw [h, Multiset.card_cons]
      rw [ite_eq_left h, hc, Nat.descFactorial_succ]
      push_cast
      ring
    · rw [ite_eq_right h, mul_zero, zero_mul, mul_zero]
  have hb : ∀ j ∈ q.parts.toFinset,
      (if p.parts = (j + 1) ::ₘ q.parts.erase j then (j : ℝ) * q.parts.count j else 0) *
        (N.descFactorial q.parts.card : ℝ) =
      (N.descFactorial p.parts.card : ℝ) *
        (if p.parts = (j + 1) ::ₘ q.parts.erase j then (j : ℝ) * q.parts.count j else 0) := by
    intro j hj
    have hjq := Multiset.mem_toFinset.1 hj
    by_cases h : p.parts = (j + 1) ::ₘ q.parts.erase j
    · have hc : p.parts.card = q.parts.card := by
        have hpos := Multiset.card_pos_iff_exists_mem.2 ⟨j, hjq⟩
        rw [h, Multiset.card_cons, Multiset.card_erase_of_mem hjq, Nat.pred_eq_sub_one]
        omega
      rw [ite_eq_left h, hc, mul_comm]
    · rw [ite_eq_right h, zero_mul, mul_zero]
  unfold urnFactor
  rw [he, add_mul, Finset.sum_mul, ha, Finset.sum_congr rfl hb, mul_add, Finset.mul_sum]

variable (κ) [Fintype κ]

noncomputable def labellingSum (θ : ℝ) {n : ℕ} (p : Nat.Partition n) : ℝ :=
  ∑ c : Fin n → κ,
    if labelType (univ.val.map c) = p.parts then labelWeight θ (univ.val.map c) else 0

theorem labellingSum_eq {θ : ℝ} (hθ : 0 < θ) :
    ∀ (n : ℕ) (p : Nat.Partition n), labellingSum κ θ p =
      ((Fintype.card κ).descFactorial p.parts.card : ℝ) * esf θ p := by
  intro n
  induction n with
  | zero =>
    intro p
    have hp : p = default := Subsingleton.elim _ _
    subst p
    simp [labellingSum, labelType, labelWeight_zero, esf, partWeight]
  | succ n ih =>
    intro p
    have hq0 : θ + (n : ℝ) ≠ 0 := by positivity
    have hcons : ∀ F : (Fin (n + 1) → κ) → ℝ,
        ∑ c, F c = ∑ c' : Fin n → κ, ∑ t : κ, F (Fin.cons t c') := by
      intro F
      rw [Finset.sum_comm, ← Fintype.sum_prod_type']
      exact (Fintype.sum_equiv (Fin.consEquiv fun _ => κ) _ _ fun _ => rfl).symm
    have hmap : ∀ (t : κ) (c' : Fin n → κ),
        (univ : Finset (Fin (n + 1))).val.map (Fin.cons t c' : Fin (n + 1) → κ) =
          t ::ₘ univ.val.map c' := by
      intro t c'
      rw [Fin.univ_succ, Finset.cons_val, Multiset.map_cons, Fin.cons_zero, Finset.map_val,
        Multiset.map_map]
      rfl
    have hinner : ∀ c' : Fin n → κ,
        (∑ t : κ, if labelType (t ::ₘ univ.val.map c') = p.parts then
          labelWeight θ (t ::ₘ univ.val.map c') else 0) * (θ + n) =
          labelWeight θ (univ.val.map c') *
            urnFactor (Fintype.card κ) θ (labelPartition c') p := by
      intro c'
      have hparts : (labelPartition c').parts = labelType (univ.val.map c') := rfl
      have hMc : (((univ : Finset (Fin n)).val.map c').card : ℝ) = n := by
        rw [Multiset.card_map]
        exact_mod_cast (Finset.card_univ).trans (Fintype.card_fin n)
      unfold urnFactor
      rw [hparts]
      generalize (univ : Finset (Fin n)).val.map c' = M at hMc ⊢
      have h1 : ∀ t ∈ M.toFinset,
          (if labelType (t ::ₘ M) = p.parts then labelWeight θ (t ::ₘ M) else 0) * (θ + n) =
            labelWeight θ M *
              (if p.parts = (M.count t + 1) ::ₘ (labelType M).erase (M.count t) then
                (M.count t : ℝ) else 0) := by
        intro t ht
        have htM := Multiset.mem_toFinset.1 ht
        rw [labelType_cons_of_mem htM]
        by_cases hc : p.parts = (M.count t + 1) ::ₘ (labelType M).erase (M.count t)
        · rw [ite_eq_left hc, ite_eq_left hc.symm, ← hMc, labelWeight_cons_of_mem hθ htM]
          ring
        · rw [ite_eq_right hc, ite_eq_right (fun h => hc h.symm), zero_mul, mul_zero]
      have h2 : ∀ t ∈ M.toFinsetᶜ,
          (if labelType (t ::ₘ M) = p.parts then labelWeight θ (t ::ₘ M) else 0) * (θ + n) =
            labelWeight θ M * (if p.parts = 1 ::ₘ labelType M then θ else 0) := by
        intro t ht
        have htM : t ∉ M := fun h => (Finset.mem_compl.1 ht) (Multiset.mem_toFinset.2 h)
        rw [labelType_cons_of_notMem htM]
        by_cases hc : p.parts = 1 ::ₘ labelType M
        · rw [ite_eq_left hc, ite_eq_left hc.symm, ← hMc, labelWeight_cons_of_notMem hθ htM]
          ring
        · rw [ite_eq_right hc, ite_eq_right (fun h => hc h.symm), zero_mul, mul_zero]
      have h3 : ∀ j ∈ (labelType M).toFinset, ((labelType M).count j : ℝ) *
          (if p.parts = (j + 1) ::ₘ (labelType M).erase j then (j : ℝ) else 0) =
          if p.parts = (j + 1) ::ₘ (labelType M).erase j then
            (j : ℝ) * (labelType M).count j else 0 := fun j _ => by
        rw [mul_ite, mul_zero, mul_comm]
      rw [← Finset.sum_add_sum_compl M.toFinset, add_mul, Finset.sum_mul, Finset.sum_mul,
        Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, ← Finset.mul_sum, ← Finset.mul_sum,
        Finset.sum_const, Finset.card_compl, nsmul_eq_mul,
        sum_toFinset_count M (fun j =>
          if p.parts = (j + 1) ::ₘ (labelType M).erase j then (j : ℝ) else 0),
        Finset.sum_congr rfl h3, card_labelType]
      ring
    have hstep : labellingSum κ θ p * (θ + n) =
        ∑ q : Nat.Partition n, labellingSum κ θ q * urnFactor (Fintype.card κ) θ q p := by
      calc labellingSum κ θ p * (θ + n)
          = ∑ c' : Fin n → κ, (∑ t : κ, if labelType (t ::ₘ univ.val.map c') = p.parts then
              labelWeight θ (t ::ₘ univ.val.map c') else 0) * (θ + n) := by
            unfold labellingSum
            rw [hcons, Finset.sum_mul]
            refine Finset.sum_congr rfl fun c' _ => ?_
            simp only [hmap]
        _ = ∑ c' : Fin n → κ, labelWeight θ (univ.val.map c') *
              urnFactor (Fintype.card κ) θ (labelPartition c') p :=
            Finset.sum_congr rfl fun c' _ => hinner c'
        _ = ∑ c' : Fin n → κ, ∑ q : Nat.Partition n, if labelPartition c' = q then
              labelWeight θ (univ.val.map c') * urnFactor (Fintype.card κ) θ q p else 0 :=
            Finset.sum_congr rfl fun c' _ => by
              rw [Finset.sum_ite_eq, ite_eq_left (mem_univ _)]
        _ = ∑ q : Nat.Partition n, ∑ c' : Fin n → κ, if labelPartition c' = q then
              labelWeight θ (univ.val.map c') * urnFactor (Fintype.card κ) θ q p else 0 :=
            Finset.sum_comm
        _ = ∑ q : Nat.Partition n, labellingSum κ θ q * urnFactor (Fintype.card κ) θ q p := by
            refine Finset.sum_congr rfl fun q _ => ?_
            unfold labellingSum
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun c' _ => ?_
            by_cases h : labelPartition c' = q
            · rw [ite_eq_left h, ite_eq_left (show labelType (univ.val.map c') = q.parts from
                congrArg Nat.Partition.parts h)]
            · rw [ite_eq_right h, ite_eq_right (show ¬ labelType (univ.val.map c') = q.parts from
                fun h' => h (Nat.Partition.ext h')), zero_mul]
    have hfwd := esf_urn_forward hθ p
    have hsum : ∑ q : Nat.Partition n, labellingSum κ θ q * urnFactor (Fintype.card κ) θ q p =
        ((Fintype.card κ).descFactorial p.parts.card : ℝ) * (θ + n) * esf θ p := by
      rw [← hfwd, Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [ih q]
      linear_combination esf θ q * urnFactor_mul_descFactorial hθ (Fintype.card κ) q p
    rw [hsum] at hstep
    exact mul_right_cancel₀ hq0 (hstep.trans (by ring))

end Rhone.Statistics
