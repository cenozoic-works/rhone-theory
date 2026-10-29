/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.FiniteIntervalGenealogyLawSupport

/-! # Material, carrier, and joint carrier counts of an interval state -/
@[expose] public section

namespace Rhone.Coalescent.IntervalProcess
open SmcSupport MeasureTheory

open scoped Classical in
noncomputable def materialCount (P : Material → Prop) (s : State) : ℕ :=
  (Finset.univ.filter fun i : Fin s.2.2.1 => P (s.2.2.2 i).2).card

open scoped Classical in
noncomputable def carrierCount (q : ℝ) (s : State) : ℕ :=
  materialCount (fun a => materialContains a q) s

open scoped Classical in
noncomputable def jointCarrierCount (x y : ℝ) (s : State) : ℕ :=
  materialCount (fun a => materialContains a x ∧ materialContains a y) s

open scoped Classical in
theorem materialCount_eq_sum (P : Material → Prop) (s : State) :
    materialCount P s = ∑ i : Fin s.2.2.1, if P (s.2.2.2 i).2 then 1 else 0 := by
  rw [materialCount, Finset.card_filter]

open scoped Classical in
theorem materialCount_le (P : Material → Prop) (s : State) :
    materialCount P s ≤ s.2.2.1 := by
  have h := Finset.card_filter_le (Finset.univ : Finset (Fin s.2.2.1))
    (fun i => P (s.2.2.2 i).2)
  rw [Finset.card_univ, Fintype.card_fin] at h
  exact h

open scoped Classical in
theorem materialCount_mono {P Q : Material → Prop} (h : ∀ a, P a → Q a) (s : State) :
    materialCount P s ≤ materialCount Q s :=
  Finset.card_le_card fun i hi => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact h _ hi

open scoped Classical in
theorem materialCount_atTime (P : Material → Prop) (t : ℝ) (s : State) :
    materialCount P (atTime t s) = materialCount P s := rfl

open scoped Classical in
theorem sum_get_ite_eq_countP {α : Type*} (p : α → Prop) (l : List α) :
    (∑ i : Fin l.length, if p (l.get i) then 1 else 0) = l.countP (fun a => decide (p a)) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.length_cons]
    rw [Fin.sum_univ_succ]
    change ((if p a then 1 else 0) + ∑ i : Fin l.length, (if p (l.get i) then 1 else 0)) = _
    rw [ih, List.countP_cons]
    simp only [decide_eq_true_eq]
    exact add_comm _ _

open scoped Classical in
theorem materialCount_liveOfList (P : Material → Prop) (t : ℝ) (n : ℕ)
    (l : List (ℕ × Material)) :
    materialCount P (t, n, liveOfList l) = l.countP (fun p => decide (P p.2)) := by
  rw [materialCount_eq_sum]
  exact sum_get_ite_eq_countP (fun p : ℕ × Material => P p.2) l

open scoped Classical in
theorem countP_finRange_eq_sum {m : ℕ} (q : Fin m → Bool) :
    (List.finRange m).countP q = ∑ k : Fin m, if q k then 1 else 0 := by
  have h := sum_get_ite_eq_countP (fun k : Fin m => q k = true) (List.finRange m)
  refine Eq.trans ?_ (h.symm.trans ?_)
  · congr 1
    funext a
    simp
  refine (Fintype.sum_equiv (finCongr (List.length_finRange (n := m)))
    _ _ fun i => ?_)
  simp

open scoped Classical in
theorem materialCount_coalSuccessor (P : Material → Prop) (s : State)
    (i j : Fin s.2.2.1) (hij : i.val < j.val) :
    materialCount P (coalSuccessor s i j) + (if P (s.2.2.2 i).2 then 1 else 0) +
        (if P (s.2.2.2 j).2 then 1 else 0) =
      materialCount P s +
        (if P (mergeMaterial (s.2.2.2 i).2 (s.2.2.2 j).2) then 1 else 0) := by
  have hne : i ≠ j := fun h => by rw [h] at hij; exact lt_irrefl _ hij
  unfold coalSuccessor
  rw [ite_eq_left hij]
  dsimp only
  rw [materialCount_liveOfList, List.countP_append, List.countP_map, List.countP_filter,
    countP_finRange_eq_sum, materialCount_eq_sum]
  simp only [List.countP_cons, List.countP_nil, zero_add, Function.comp_apply,
    Bool.and_eq_true, decide_eq_true_eq]
  have hpt : ∀ k : Fin s.2.2.1, (if P (s.2.2.2 k).2 then 1 else 0) =
      (if P (s.2.2.2 k).2 ∧ k ≠ i ∧ k ≠ j then 1 else 0) +
        (if k = i then (if P (s.2.2.2 i).2 then 1 else 0) else 0) +
        (if k = j then (if P (s.2.2.2 j).2 then 1 else 0) else 0) := by
    intro k
    by_cases hki : k = i
    · subst hki
      simp [hne]
    · by_cases hkj : k = j
      · subst hkj
        simp [hki]
      · simp [hki, hkj]
  rw [Finset.sum_congr rfl (fun k _ => hpt k), Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true]
  omega

open scoped Classical in
theorem materialCount_splitSuccessor (P : Material → Prop) (s : State)
    (i : Fin s.2.2.1) (c : ℝ) :
    materialCount P (splitSuccessor s i c) + (if P (s.2.2.2 i).2 then 1 else 0) =
      materialCount P s + (if P (splitMaterial (s.2.2.2 i).2 c).1 then 1 else 0) +
        (if P (splitMaterial (s.2.2.2 i).2 c).2 then 1 else 0) := by
  unfold splitSuccessor
  dsimp only
  rw [materialCount_liveOfList, List.countP_append, List.countP_map, List.countP_filter,
    countP_finRange_eq_sum, materialCount_eq_sum]
  simp only [List.countP_cons, List.countP_nil, zero_add, Function.comp_apply,
    Bool.and_eq_true, decide_eq_true_eq]
  have hpt : ∀ k : Fin s.2.2.1, (if P (s.2.2.2 k).2 then 1 else 0) =
      (if P (s.2.2.2 k).2 ∧ k ≠ i then 1 else 0) +
        (if k = i then (if P (s.2.2.2 i).2 then 1 else 0) else 0) := by
    intro k
    by_cases hki : k = i
    · subst hki
      simp
    · simp [hki]
  rw [Finset.sum_congr rfl (fun k _ => hpt k), Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true]
  omega

open scoped Classical in
theorem materialCount_measurable (P : Material → Prop) (hP : MeasurableSet {a | P a}) :
    Measurable (materialCount P) := by
  apply measurable_to_countable'
  intro n
  change MeasurableSet {s : State | materialCount P s = n}
  apply statePredicate_measurable
  intro m
  have hsum : Measurable fun p : FiberState m =>
      ∑ i : Fin m, if P (p.2.2 i).2 then 1 else 0 := by
    refine Finset.measurable_sum _ fun i _ => ?_
    exact Measurable.ite
      (hP.preimage (((measurable_pi_apply i).comp measurable_snd.snd).snd))
      measurable_const measurable_const
  have heq : {p : FiberState m | materialCount P (stateOfFiber m p) = n} =
      (fun p : FiberState m => ∑ i : Fin m, if P (p.2.2 i).2 then 1 else 0) ⁻¹' {n} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
    rw [materialCount_eq_sum]
  rw [heq]
  exact hsum (measurableSet_singleton n)

open scoped Classical in
theorem carrierCount_measurable (q : ℝ) : Measurable (carrierCount q) :=
  materialCount_measurable _ (materialContains_measurable q)

open scoped Classical in
theorem jointCarrierCount_measurable (x y : ℝ) : Measurable (jointCarrierCount x y) :=
  materialCount_measurable _
    ((materialContains_measurable x).inter (materialContains_measurable y))

theorem sum_comp_type_eq {m : ℕ} {T : Type*} [Fintype T] [DecidableEq T] (τ : Fin m → T)
    (g : T → ℝ) :
    ∑ i, g (τ i) = ∑ t, ((Finset.univ.filter fun i => τ i = t).card : ℝ) * g t := by
  rw [← Finset.sum_fiberwise (s := Finset.univ) (g := τ) (f := fun i => g (τ i))]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_congr rfl (fun i hi => by rw [(Finset.mem_filter.mp hi).2]),
    Finset.sum_const, nsmul_eq_mul]

theorem sum_lt_pair_eq {m : ℕ} {T : Type*} [Fintype T] [DecidableEq T] (τ : Fin m → T)
    (Ψ : T → T → ℝ)
    (hΨ : ∀ t t', Ψ t t' = Ψ t' t) :
    ∑ p : Fin m × Fin m, (if p.1.val < p.2.val then Ψ (τ p.1) (τ p.2) else 0) =
      (∑ t, ∑ t', ((Finset.univ.filter fun i => τ i = t).card : ℝ) *
          ((Finset.univ.filter fun i => τ i = t').card : ℝ) * Ψ t t' -
        ∑ t, ((Finset.univ.filter fun i => τ i = t).card : ℝ) * Ψ t t) / 2 := by
  have hall : ∑ p : Fin m × Fin m, Ψ (τ p.1) (τ p.2) =
      ∑ t, ∑ t', ((Finset.univ.filter fun i => τ i = t).card : ℝ) *
          ((Finset.univ.filter fun i => τ i = t').card : ℝ) * Ψ t t' := by
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_congr rfl (fun i _ => sum_comp_type_eq τ (fun t' => Ψ (τ i) t'))]
    rw [sum_comp_type_eq τ (fun t => ∑ t', ((Finset.univ.filter fun i => τ i = t').card : ℝ) *
      Ψ t t')]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t' _ => ?_
    ring
  have hdiag : ∑ p : Fin m × Fin m, (if p.1 = p.2 then Ψ (τ p.1) (τ p.2) else 0) =
      ∑ t, ((Finset.univ.filter fun i => τ i = t).card : ℝ) * Ψ t t := by
    rw [Fintype.sum_prod_type, ← sum_comp_type_eq τ (fun t => Ψ t t)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_ite_eq]
    simp
  have hswap : ∑ p : Fin m × Fin m, (if p.2.val < p.1.val then Ψ (τ p.1) (τ p.2) else 0) =
      ∑ p : Fin m × Fin m, (if p.1.val < p.2.val then Ψ (τ p.1) (τ p.2) else 0) := by
    refine Fintype.sum_equiv (Equiv.prodComm _ _) _ _ fun p => ?_
    simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
    by_cases h : p.2.val < p.1.val <;> simp [h, hΨ (τ p.1)]
  have hpt : ∀ p : Fin m × Fin m, Ψ (τ p.1) (τ p.2) =
      (if p.1.val < p.2.val then Ψ (τ p.1) (τ p.2) else 0) +
        (if p.2.val < p.1.val then Ψ (τ p.1) (τ p.2) else 0) +
        (if p.1 = p.2 then Ψ (τ p.1) (τ p.2) else 0) := by
    intro p
    rcases lt_trichotomy p.1.val p.2.val with h | h | h
    · have hne : p.1 ≠ p.2 := fun e => by rw [e] at h; exact lt_irrefl _ h
      simp [h, hne, Nat.lt_asymm h]
    · have he : p.1 = p.2 := Fin.ext h
      simp [he]
    · have hne : p.1 ≠ p.2 := fun e => by rw [e] at h; exact lt_irrefl _ h
      simp [h, hne, Nat.lt_asymm h]
  have htot := hall
  rw [Finset.sum_congr rfl (fun p _ => hpt p), Finset.sum_add_distrib, Finset.sum_add_distrib,
    hswap, hdiag] at htot
  linarith

end Rhone.Coalescent.IntervalProcess
