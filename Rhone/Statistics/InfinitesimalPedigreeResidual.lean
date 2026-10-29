/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Statistics.InfinitesimalPedigree
/-!
# Pedigree causality and one-locus residual algebra

Source: barton_etheridge_veber2017, sec. 3.1. -/

@[expose] public section
namespace Rhone.Statistics
open Rhone.Combinatorics

theorem geneFounder_congr_prefix {n : Nat} (P : Pedigree n) (i : Fin n)
    (c d : Fin n → Bool) (h : ∀ j : Fin n, j.val ≤ i.val → c j = d j) :
    geneFounder P c i = geneFounder P d i := by
  induction i using (measure (fun j : Fin n => j.val)).wf.induction with
  | h i ih =>
    cases hp : P.parents i with
    | none => rw [geneFounder_of_founder P c hp, geneFounder_of_founder P d hp]
    | some p =>
      have hlt := P.parents_lt i p hp
      have hc := h i (by omega)
      rw [geneFounder, hp, geneFounder, hp]
      simp only [hc]
      split_ifs with hcoin
      · apply ih p.1 hlt.1
        intro j hj
        exact h j (by omega)
      · apply ih p.2 hlt.2
        intro j hj
        exact h j (by omega)

theorem geneFounder_le_birth {n : Nat} (P : Pedigree n) (c : Fin n → Bool) (i : Fin n) :
    (geneFounder P c i).val ≤ i.val := by
  induction i using (measure (fun j : Fin n => j.val)).wf.induction with
  | h i ih =>
    cases hp : P.parents i with
    | none => rw [geneFounder_of_founder P c hp]
    | some p =>
      have hlt := P.parents_lt i p hp
      rw [geneFounder, hp]
      split_ifs
      · exact le_trans (ih p.1 hlt.1) (Nat.le_of_lt hlt.1)
      · exact le_trans (ih p.2 hlt.2) (Nat.le_of_lt hlt.2)

theorem geneFounder_before_current_coin {n : Nat} (P : Pedigree n) (i j : Fin n)
    (hji : j < i) (c : Fin n → Bool) (choice : Bool) :
    geneFounder P (Function.update c i choice) j = geneFounder P c j := by
  apply geneFounder_congr_prefix
  intro k hk
  have hki : k ≠ i := by
    intro heq
    subst heq
    omega
  exact Function.update_of_ne hki choice c

noncomputable def locusTraitDeviation {n : Nat} (P : Pedigree n) (m : Real)
    (e : Fin n → Real) (c : Fin n → Bool) : Fin n → Real :=
  fun i => e (geneFounder P c i) - m

noncomputable def locusSegregationResidual {n : Nat} (P : Pedigree n) (m : Real)
    (e : Fin n → Real) (c : Fin n → Bool) : Fin n → Real :=
  segregationResidual P (locusTraitDeviation P m e c)

theorem locusSegregationResidual_founder {n : Nat} (P : Pedigree n) (i : Fin n)
    (hi : P.parents i = none) (m : Real) (e : Fin n → Real) (c : Fin n → Bool) :
    locusSegregationResidual P m e c i = e i - m := by
  simp only [locusSegregationResidual, segregationResidual, hi, locusTraitDeviation]
  rw [geneFounder_of_founder P c hi]

theorem locusSegregationResidual_nonfounder {n : Nat} (P : Pedigree n) (i : Fin n)
    (parents : Fin n × Fin n) (hi : P.parents i = some parents)
    (m : Real) (e : Fin n → Real) (c : Fin n → Bool) :
    locusSegregationResidual P m e c i =
      (if c i then (1 / 2 : Real) else -1 / 2) *
        (e (geneFounder P c parents.1) - e (geneFounder P c parents.2)) := by
  simp only [locusSegregationResidual, segregationResidual, hi, locusTraitDeviation]
  rw [geneFounder, hi]
  split_ifs <;> ring

theorem locusSegregationResidual_coin_pair_zero {n : Nat} (P : Pedigree n) (i : Fin n)
    (parents : Fin n × Fin n) (hi : P.parents i = some parents)
    (m : Real) (e : Fin n → Real) (c : Fin n → Bool) :
    locusSegregationResidual P m e (Function.update c i false) i +
      locusSegregationResidual P m e (Function.update c i true) i = 0 := by
  have hlt := P.parents_lt i parents hi
  rw [locusSegregationResidual_nonfounder P i parents hi,
    locusSegregationResidual_nonfounder P i parents hi]
  simp only [Function.update_self, Bool.false_eq_true, ↓reduceIte]
  rw [geneFounder_before_current_coin P i parents.1 hlt.1,
    geneFounder_before_current_coin P i parents.2 hlt.2,
    geneFounder_before_current_coin P i parents.1 hlt.1,
    geneFounder_before_current_coin P i parents.2 hlt.2]
  ring

theorem segregationResidual_const_mul {n : Nat} (P : Pedigree n) (a : Real)
    (z : Fin n → Real) :
    segregationResidual P (fun i => a * z i) = fun i => a * segregationResidual P z i := by
  funext i
  cases hi : P.parents i with
  | none => simp only [segregationResidual, hi]
  | some parents =>
    simp only [segregationResidual, hi]
    ring

theorem segregationResidual_sum {n M : Nat} (P : Pedigree n)
    (z : Fin M → Fin n → Real) :
    segregationResidual P (fun i => ∑ l, z l i) =
      fun i => ∑ l, segregationResidual P (z l) i := by
  funext i
  cases hi : P.parents i with
  | none => simp only [segregationResidual, hi]
  | some parents =>
    simp only [segregationResidual, hi]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_div]

theorem segregationResidual_traitDeviation_sum {n : Nat} (P : Pedigree n) (m : Real)
    (M : Nat) (omega : Fin M → (Fin n → Real) × (Fin n → Bool)) :
    segregationResidual P (traitDeviation P m M omega) =
      fun i => (Real.sqrt (M : Real))⁻¹ *
        ∑ l, locusSegregationResidual P m (omega l).1 (omega l).2 i := by
  change segregationResidual P
    (fun i => (Real.sqrt (M : Real))⁻¹ * ∑ l, locusTraitDeviation P m (omega l).1 (omega l).2 i) = _
  rw [segregationResidual_const_mul, segregationResidual_sum]
  rfl

def flipInheritanceCoin {n : Nat} (i : Fin n) (c : Fin n → Bool) : Fin n → Bool :=
  Function.update c i (!(c i))

theorem flipInheritanceCoin_involutive {n : Nat} (i : Fin n) :
    Function.Involutive (flipInheritanceCoin i) := by
  intro c
  funext j
  by_cases hj : j = i
  · subst j
    simp [flipInheritanceCoin, Function.update_self]
  · simp [flipInheritanceCoin, Function.update_of_ne hj]

theorem locusSegregationResidual_congr_prefix {n : Nat} (P : Pedigree n) (i : Fin n)
    (m : Real) (e : Fin n → Real) (c d : Fin n → Bool)
    (h : ∀ j : Fin n, j.val ≤ i.val → c j = d j) :
    locusSegregationResidual P m e c i = locusSegregationResidual P m e d i := by
  cases hi : P.parents i with
  | none => rw [locusSegregationResidual_founder P i hi,
      locusSegregationResidual_founder P i hi]
  | some parents =>
    have hlt := P.parents_lt i parents hi
    have h1 : geneFounder P c parents.1 = geneFounder P d parents.1 :=
      geneFounder_congr_prefix P parents.1 c d (fun j hj => h j (by omega))
    have h2 : geneFounder P c parents.2 = geneFounder P d parents.2 :=
      geneFounder_congr_prefix P parents.2 c d (fun j hj => h j (by omega))
    rw [locusSegregationResidual_nonfounder P i parents hi,
      locusSegregationResidual_nonfounder P i parents hi, h1, h2, h i (by omega)]

theorem locusSegregationResidual_before_current_coin {n : Nat} (P : Pedigree n)
    (i j : Fin n) (hji : j < i) (m : Real) (e : Fin n → Real) (c : Fin n → Bool)
    (choice : Bool) :
    locusSegregationResidual P m e (Function.update c i choice) j =
      locusSegregationResidual P m e c j := by
  apply locusSegregationResidual_congr_prefix
  intro k hk
  have hki : k ≠ i := by
    intro heq
    subst heq
    omega
  exact Function.update_of_ne hki choice c

theorem locusSegregationResidual_flip_neg {n : Nat} (P : Pedigree n) (i : Fin n)
    (parents : Fin n × Fin n) (hi : P.parents i = some parents)
    (m : Real) (e : Fin n → Real) (c : Fin n → Bool) :
    locusSegregationResidual P m e (flipInheritanceCoin i c) i =
      -locusSegregationResidual P m e c i := by
  have hlt := P.parents_lt i parents hi
  rw [locusSegregationResidual_nonfounder P i parents hi,
    locusSegregationResidual_nonfounder P i parents hi]
  simp only [flipInheritanceCoin, Function.update_self]
  rw [geneFounder_before_current_coin P i parents.1 hlt.1,
    geneFounder_before_current_coin P i parents.2 hlt.2]
  cases c i <;> simp <;> ring

end Rhone.Statistics
