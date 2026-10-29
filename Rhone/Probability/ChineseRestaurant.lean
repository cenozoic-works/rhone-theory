/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Combinatorics.StirlingSetPartitions
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# The Chinese restaurant process on set partitions

Source: ewens1972, eq. (18), eq. (A3), pp. 94, 107; hoppe1984, sec. 1, p. 91; aldous1985, (11.19),
Thm 11.14; durrett2008, sec. 1.3.2. -/

@[expose] public section

namespace Rhone.Probability

set_option linter.unusedDecidableInType false
set_option linter.style.openClassical false

open Finset
open scoped ENNReal Classical

def initSeg (N m : ℕ) : Finset (Fin N) := univ.filter (fun i => i.val < m)

theorem mem_initSeg {N m : ℕ} {i : Fin N} : i ∈ initSeg N m ↔ i.val < m := by
  simp [initSeg]

theorem initSeg_self (N : ℕ) : initSeg N N = univ := by
  ext i
  simp [mem_initSeg]

theorem initSeg_zero (N : ℕ) : initSeg N 0 = ∅ := by
  ext i
  simp [mem_initSeg]

theorem insert_initSeg {N m : ℕ} (h : m < N) :
    insert (⟨m, h⟩ : Fin N) (initSeg N m) = initSeg N (m + 1) := by
  ext i
  simp only [mem_insert, mem_initSeg, Fin.ext_iff]
  omega

theorem notMem_initSeg {N m : ℕ} (h : m < N) : (⟨m, h⟩ : Fin N) ∉ initSeg N m := by
  simp [mem_initSeg]

theorem card_initSeg {N m : ℕ} (h : m ≤ N) : (initSeg N m).card = m := by
  have : (initSeg N m).map Fin.valEmbedding = range m := by
    ext x
    simp only [mem_map, mem_initSeg, Fin.valEmbedding_apply, mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact hi
    · intro hx
      exact ⟨⟨x, lt_of_lt_of_le hx h⟩, hx, rfl⟩
  rw [← card_map Fin.valEmbedding, this, card_range]

theorem sum_card_of_isSetPartition {α : Type*} [DecidableEq α] {s : Finset α}
    {ζ : Finset (Finset α)} (hζ : Combinatorics.IsSetPartition s ζ) : ∑ B ∈ ζ, B.card = s.card := by
  have hbi : ζ.biUnion id = s := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨B, hB, hxB⟩ := mem_biUnion.1 hx
      exact hζ.2.1 B hB hxB
    · intro x hx
      obtain ⟨B, hB, hxB⟩ := hζ.2.2.2 x hx
      exact mem_biUnion.2 ⟨B, hB, hxB⟩
  rw [← hbi, card_biUnion]
  · rfl
  · intro B hB C hC hne
    exact hζ.2.2.1 B hB C hC hne

noncomputable def ewensSetWeight {α : Type*} (θ : ℝ) (m : ℕ) (ζ : Finset (Finset α)) : ℝ :=
  θ ^ ζ.card * (∏ B ∈ ζ, (((B.card - 1).factorial : ℕ) : ℝ)) / (ascPochhammer ℝ m).eval θ

theorem rising_pos {θ : ℝ} (hθ : 0 < θ) (m : ℕ) : 0 < (ascPochhammer ℝ m).eval θ := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [ascPochhammer_succ_eval]
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    positivity

theorem ewensSetWeight_nonneg {α : Type*} {θ : ℝ} (hθ : 0 < θ) (m : ℕ)
    (ζ : Finset (Finset α)) : 0 ≤ ewensSetWeight θ m ζ := by
  have := rising_pos hθ m
  unfold ewensSetWeight
  positivity

section Weights

variable {α : Type*} [DecidableEq α] {s : Finset α} {ζ : Finset (Finset α)} {a : α}

theorem ewensSetWeight_addElem_none {θ : ℝ} (hθ : 0 < θ) (m : ℕ)
    (hζ : Combinatorics.IsSetPartition s ζ)
    (ha : a ∉ s) :
    ewensSetWeight θ (m + 1) (Combinatorics.addElem a ζ none) = ewensSetWeight θ m ζ *
        (θ / (θ + m)) := by
  have hsing : {a} ∉ ζ := fun h => ha (hζ.2.1 _ h (mem_singleton_self a))
  have hr := rising_pos hθ m
  have hm : (θ + m) ≠ 0 := by
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    positivity
  unfold ewensSetWeight Combinatorics.addElem
  rw [card_insert_of_notMem hsing, prod_insert hsing, ascPochhammer_succ_eval]
  simp only [card_singleton, Nat.sub_self, Nat.factorial_zero, Nat.cast_one, one_mul, pow_succ]
  field_simp

theorem ewensSetWeight_addElem_some {θ : ℝ} (hθ : 0 < θ) (m : ℕ)
    (hζ : Combinatorics.IsSetPartition s ζ)
    (ha : a ∉ s) {B : Finset α} (hB : B ∈ ζ) :
    ewensSetWeight θ (m + 1) (Combinatorics.addElem a ζ (some B)) =
      ewensSetWeight θ m ζ * ((B.card : ℝ) / (θ + m)) := by
  have hr := rising_pos hθ m
  have hm : (θ + m) ≠ 0 := by
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    positivity
  have hBa : a ∉ B := hζ.notMem_of_mem ha hB
  have hnot : insert a B ∉ ζ.erase B := fun h =>
    ha (hζ.2.1 _ (mem_of_mem_erase h) (mem_insert_self a B))
  obtain ⟨c, hc⟩ : ∃ c, B.card = c + 1 :=
    Nat.exists_eq_succ_of_ne_zero (card_pos.2 (hζ.nonempty_of_mem hB)).ne'
  have hprod := mul_prod_erase ζ (fun C => (((C.card - 1).factorial : ℕ) : ℝ)) hB
  unfold ewensSetWeight Combinatorics.addElem
  rw [card_insert_of_notMem hnot, card_erase_of_mem hB, prod_insert hnot,
    card_insert_of_notMem hBa, ascPochhammer_succ_eval]
  obtain ⟨j, hj⟩ : ∃ j, ζ.card = j + 1 :=
    Nat.exists_eq_succ_of_ne_zero (card_pos.2 ⟨B, hB⟩).ne'
  rw [← hprod, hc]
  simp only [hj, Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, pow_succ]
  field_simp

end Weights

noncomputable def crpWeight {α : Type*} (θ : ℝ) (m : ℕ) (ζ : Finset (Finset α)) :
    Option (Finset α) → ℝ≥0∞
  | none => ENNReal.ofReal (θ / (θ + m))
  | some B => if B ∈ ζ then ENNReal.ofReal ((B.card : ℝ) / (θ + m)) else 0

theorem sum_crpWeight {α : Type*} [DecidableEq α] {θ : ℝ} (hθ : 0 < θ) {m : ℕ}
    (ζ : Finset (Finset α)) (hζ : ∑ B ∈ ζ, B.card = m) :
    ∑ o ∈ insertNone ζ, crpWeight θ m ζ o = 1 := by
  have hm : 0 < θ + m := by
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    positivity
  have hs : ∀ B ∈ ζ, crpWeight θ m ζ (some B) = ENNReal.ofReal ((B.card : ℝ) / (θ + m)) :=
    fun B hB => by simp [crpWeight, hB]
  rw [sum_insertNone, sum_congr rfl hs]
  change ENNReal.ofReal (θ / (θ + m)) + _ = 1
  rw [← ENNReal.ofReal_sum_of_nonneg (fun B _ => by positivity),
    ← ENNReal.ofReal_add (by positivity) (sum_nonneg (fun B _ => by positivity)),
    ← sum_div]
  have : ((∑ B ∈ ζ, (B.card : ℝ))) = m := by exact_mod_cast hζ
  rw [this, ← add_div, div_self hm.ne', ENNReal.ofReal_one]

noncomputable def crpStep (θ : ℝ) (N m : ℕ) (ζ : Finset (Finset (Fin N))) :
    PMF (Finset (Finset (Fin N))) :=
  if h : 0 < θ ∧ m < N ∧ ∑ B ∈ ζ, B.card = m then
    (PMF.ofFinset (crpWeight θ m ζ) (insertNone ζ) (sum_crpWeight h.1 ζ h.2.2)
      (by
        intro o ho
        cases o with
        | none => simp at ho
        | some B =>
          have : B ∉ ζ := fun hB => ho (by simpa using hB)
          simp [crpWeight, this])).map (Combinatorics.addElem ⟨m, h.2.1⟩ ζ)
  else PMF.pure ζ

noncomputable def crp (θ : ℝ) (N : ℕ) : ℕ → PMF (Finset (Finset (Fin N)))
  | 0 => PMF.pure ∅
  | m + 1 => (crp θ N m).bind (crpStep θ N m)

theorem crpStep_apply {θ : ℝ} (hθ : 0 < θ) {N m : ℕ} (hm : m < N)
    {ζ : Finset (Finset (Fin N))} (hζ : Combinatorics.IsSetPartition (initSeg N m) ζ)
    (η : Finset (Finset (Fin N))) :
    crpStep θ N m ζ η = ∑ o ∈ insertNone ζ,
      if η = Combinatorics.addElem ⟨m, hm⟩ ζ o then crpWeight θ m ζ o else 0 := by
  have hsum : ∑ B ∈ ζ, B.card = m := by
    rw [sum_card_of_isSetPartition hζ, card_initSeg hm.le]
  unfold crpStep
  rw [dite_eq_left ⟨hθ, hm, hsum⟩, PMF.map_apply]
  rw [tsum_eq_sum (s := insertNone ζ)]
  · exact sum_congr rfl (fun o _ => by
    rw [PMF.ofFinset_apply]
    congr)
  · intro o ho
    rw [PMF.ofFinset_apply]
    cases o with
    | none => simp at ho
    | some B =>
      have : B ∉ ζ := fun hB => ho (by simpa using hB)
      simp [crpWeight, this]

theorem crp_apply {θ : ℝ} (hθ : 0 < θ) (N : ℕ) :
    ∀ {m : ℕ}, m ≤ N → ∀ ζ : Finset (Finset (Fin N)),
      crp θ N m ζ =
        if Combinatorics.IsSetPartition (initSeg N m) ζ then ENNReal.ofReal (ewensSetWeight θ m ζ)
            else 0 := by
  intro m
  induction m with
  | zero =>
    intro _ ζ
    rw [crp, PMF.pure_apply, initSeg_zero]
    by_cases h : ζ = ∅
    · subst h
      have : Combinatorics.IsSetPartition (∅ : Finset (Fin N)) (∅ : Finset (Finset (Fin N))) :=
        ⟨by simp, by simp, by simp, by simp⟩
      simp [this, ewensSetWeight]
    · have : ¬ Combinatorics.IsSetPartition (∅ : Finset (Fin N)) ζ := by
        rintro ⟨h0, hsub, -, -⟩
        apply h
        apply eq_empty_of_forall_notMem
        intro B hB
        have := hsub B hB
        rw [subset_empty] at this
        exact h0 (this ▸ hB)
      simp [h, this]
  | succ m ih =>
    intro hm ζ'
    have hlt : m < N := hm
    set a : Fin N := ⟨m, hlt⟩ with ha_def
    have ha : a ∉ initSeg N m := notMem_initSeg hlt
    have hins : initSeg N (m + 1) = insert a (initSeg N m) := (insert_initSeg hlt).symm
    rw [crp, PMF.bind_apply]
    rw [tsum_eq_sum (s := Combinatorics.allSetPartitions (initSeg N m))]
    swap
    · intro ζ hζ
      rw [ih hlt.le, ite_eq_right (fun h => hζ (Combinatorics.mem_allSetPartitions.2 h))]
      simp
    have hstep : ∀ ζ ∈ Combinatorics.allSetPartitions (initSeg N m),
        crp θ N m ζ * crpStep θ N m ζ ζ' =
          ∑ o ∈ insertNone ζ, if ζ' = Combinatorics.addElem a ζ o then
            ENNReal.ofReal (ewensSetWeight θ m ζ) * crpWeight θ m ζ o else 0 := by
      intro ζ hζ
      have hζ' := Combinatorics.mem_allSetPartitions.1 hζ
      rw [ih hlt.le, ite_eq_left hζ', crpStep_apply hθ hlt hζ', mul_sum]
      exact sum_congr rfl (fun o _ => by split_ifs <;> simp)
    rw [sum_congr rfl hstep, hins]
    by_cases hη : Combinatorics.IsSetPartition (insert a (initSeg N m)) ζ'
    · rw [ite_eq_left hη]
      obtain ⟨ζ0, hζ0, o0, ho0, rfl⟩ := Combinatorics.exists_addElem hη ha
      have hζ0m : ζ0 ∈ Combinatorics.allSetPartitions (initSeg N m) :=
          Combinatorics.mem_allSetPartitions.2 hζ0
      rw [sum_sigma' (Combinatorics.allSetPartitions (initSeg N m)) (fun ζ => insertNone ζ)
        (fun ζ o => if Combinatorics.addElem a ζ0 o0 = Combinatorics.addElem a ζ o then
          ENNReal.ofReal (ewensSetWeight θ m ζ) * crpWeight θ m ζ o else 0)]
      rw [sum_eq_single (⟨ζ0, o0⟩ : Σ _ : Finset (Finset (Fin N)), Option (Finset (Fin N)))]
      · rw [ite_eq_left rfl]
        cases o0 with
        | none =>
          rw [ewensSetWeight_addElem_none hθ m hζ0 ha, crpWeight,
            ← ENNReal.ofReal_mul (ewensSetWeight_nonneg hθ m ζ0)]
        | some B =>
          have hB : B ∈ ζ0 := by simpa using ho0
          rw [ewensSetWeight_addElem_some hθ m hζ0 ha hB, crpWeight, ite_eq_left hB,
            ← ENNReal.ofReal_mul (ewensSetWeight_nonneg hθ m ζ0)]
      · rintro ⟨ζ, o⟩ hp hne
        simp only [mem_sigma, Combinatorics.mem_allSetPartitions] at hp
        rw [ite_eq_right]
        intro h
        obtain ⟨rfl, rfl⟩ := Combinatorics.addElem_inj hζ0 hp.1 ha ho0 hp.2 h
        exact hne rfl
      · intro h
        exact absurd (mem_sigma.2 ⟨hζ0m, ho0⟩) h
    · rw [ite_eq_right hη]
      refine sum_eq_zero (fun ζ hζ => sum_eq_zero (fun o ho => ?_))
      rw [ite_eq_right]
      intro h
      exact hη (h ▸ Combinatorics.isSetPartition_addElem (Combinatorics.mem_allSetPartitions.1 hζ)
          ha ho)

noncomputable def crpPartition {θ : ℝ} (hθ : 0 < θ) (N : ℕ) :
    PMF (Finpartition (Finset.univ : Finset (Fin N))) :=
  PMF.ofFintype (fun P => crp θ N N P.parts) (by
    have hsupp : ∀ ζ ∉ Combinatorics.allSetPartitions (Finset.univ : Finset (Fin N)), crp θ N N ζ =
        0 := by
      intro ζ hζ
      rw [crp_apply hθ N le_rfl, initSeg_self,
        ite_eq_right (fun h => hζ (Combinatorics.mem_allSetPartitions.2 h))]
    have h1 : ∑ ζ ∈ Combinatorics.allSetPartitions (Finset.univ : Finset (Fin N)), crp θ N N ζ =
        1 := by
      have := (crp θ N N).tsum_coe
      rwa [tsum_eq_sum (s := Combinatorics.allSetPartitions (Finset.univ : Finset (Fin N))) hsupp]
          at this
    rw [← h1]
    refine sum_nbij' (fun P => P.parts)
      (fun ζ => if h : Combinatorics.IsSetPartition (Finset.univ : Finset (Fin N)) ζ then
        Combinatorics.finpartitionOfSetPartition h else ⊥) ?_ ?_ ?_ ?_ ?_
    · intro P _
      exact Combinatorics.mem_allSetPartitions.2 (Combinatorics.isSetPartition_parts P)
    · intro ζ hζ
      exact mem_univ _
    · intro P _
      rw [dite_eq_left (Combinatorics.isSetPartition_parts P)]
      exact Finpartition.ext rfl
    · intro ζ hζ
      rw [dite_eq_left (Combinatorics.mem_allSetPartitions.1 hζ)]
      rfl
    · intro P _
      rfl)

theorem crpPartition_apply {θ : ℝ} (hθ : 0 < θ) (N : ℕ)
    (P : Finpartition (Finset.univ : Finset (Fin N))) :
    crpPartition hθ N P =
      ENNReal.ofReal (θ ^ P.parts.card * (∏ B ∈ P.parts, (((B.card - 1).factorial : ℕ) : ℝ)) /
        (ascPochhammer ℝ N).eval θ) := by
  unfold crpPartition
  rw [PMF.ofFintype_apply, crp_apply hθ N le_rfl, initSeg_self,
    ite_eq_left (Combinatorics.isSetPartition_parts P)]
  rfl

end Rhone.Probability
