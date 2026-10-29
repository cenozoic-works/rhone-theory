/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Dynamics.PedigreeKinship
public import Rhone.Dynamics.MendelianIBD
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.WellFounded

/-!
# Mendelian gene dropping on a finite pedigree

Source: malecot1969, ch. 1, pp. 8–10; felsenstein_teg2019, pp. 226–227, eq. (V-13)–(V-18). -/

@[expose] public section

namespace Rhone.Combinatorics.Pedigree

open Dynamics.MendelianIBD Finset

variable {n : ℕ}

def geneDrop (P : Pedigree n) (ω : Fin n × Fin 2 → Fin 2) (i : Fin n) :
    Fin 2 → Fin n × Fin 2 :=
  match _h : P.parents i with
  | none => fun c => (i, c)
  | some p => mendelianChild (geneDrop P ω p.1) (geneDrop P ω p.2) (ω (i, 0)) (ω (i, 1))
termination_by i.val
decreasing_by
  · exact (P.parents_lt _ _ (by assumption)).1
  · exact (P.parents_lt _ _ (by assumption)).2

noncomputable def geneDropWeight (n : ℕ) : (Fin n × Fin 2 → Fin 2) → ℝ :=
  fun _ => (1 / 4) ^ n

theorem geneDropWeight_sum (n : ℕ) : ∑ ω, geneDropWeight n ω = 1 := by
  have h2 : ((2 : ℝ) ^ (n * 2)) = 4 ^ n := by
    rw [mul_comm, pow_mul]
    norm_num
  simp only [geneDropWeight, sum_const, card_univ, Fintype.card_pi, Fintype.card_fin,
    prod_const, Fintype.card_prod, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [h2, ← mul_pow]
  norm_num

theorem geneDrop_founder (P : Pedigree n) (ω : Fin n × Fin 2 → Fin 2) {i : Fin n}
    (hi : P.parents i = none) : P.geneDrop ω i = fun c => (i, c) := by
  rw [geneDrop]
  split
  · rfl
  · next p h => rw [hi] at h; cases h

theorem geneDrop_of_parents (P : Pedigree n) (ω : Fin n × Fin 2 → Fin 2) {i : Fin n}
    {p : Fin n × Fin n} (hi : P.parents i = some p) :
    P.geneDrop ω i =
      mendelianChild (P.geneDrop ω p.1) (P.geneDrop ω p.2) (ω (i, 0)) (ω (i, 1)) := by
  rw [geneDrop]
  split
  · next h => rw [hi] at h; cases h
  · next q h =>
    rw [hi] at h
    cases h
    rfl

theorem geneDrop_zero (P : Pedigree n) (ω : Fin n × Fin 2 → Fin 2) {i : Fin n}
    {p : Fin n × Fin n} (hi : P.parents i = some p) :
    P.geneDrop ω i 0 = P.geneDrop ω p.1 (ω (i, 0)) := by
  rw [geneDrop_of_parents P ω hi]
  rfl

theorem geneDrop_one (P : Pedigree n) (ω : Fin n × Fin 2 → Fin 2) {i : Fin n}
    {p : Fin n × Fin n} (hi : P.parents i = some p) :
    P.geneDrop ω i 1 = P.geneDrop ω p.2 (ω (i, 1)) := by
  rw [geneDrop_of_parents P ω hi]
  rfl

theorem geneDrop_congr (P : Pedigree n) {ω ω' : Fin n × Fin 2 → Fin 2} (i : Fin n)
    (h : ∀ k, k ≤ i → ∀ t, ω (k, t) = ω' (k, t)) : P.geneDrop ω i = P.geneDrop ω' i := by
  induction i using WellFoundedLT.induction with
  | _ i ih =>
    cases hi : P.parents i with
    | none => rw [geneDrop_founder P ω hi, geneDrop_founder P ω' hi]
    | some p =>
      have hlt := P.parents_lt i p hi
      rw [geneDrop_of_parents P ω hi, geneDrop_of_parents P ω' hi,
        ih p.1 hlt.1 fun k hk t => h k (hk.trans hlt.1.le) t,
        ih p.2 hlt.2 fun k hk t => h k (hk.trans hlt.2.le) t, h i le_rfl 0, h i le_rfl 1]

theorem geneDrop_fst_le (P : Pedigree n) (ω : Fin n × Fin 2 → Fin 2) (i : Fin n)
    (c : Fin 2) : (P.geneDrop ω i c).1 ≤ i := by
  induction i using WellFoundedLT.induction generalizing c with
  | _ i ih =>
    cases hi : P.parents i with
    | none => rw [geneDrop_founder P ω hi]
    | some p =>
      have hlt := P.parents_lt i p hi
      by_cases hc : c = 0
      · subst hc
        rw [geneDrop_zero P ω hi]
        exact (ih p.1 hlt.1 _).trans hlt.1.le
      · have hc1 : c = 1 := by omega
        subst hc1
        rw [geneDrop_one P ω hi]
        exact (ih p.2 hlt.2 _).trans hlt.2.le

private def flipBit (x : Fin n × Fin 2) (ω : Fin n × Fin 2 → Fin 2) :
    Fin n × Fin 2 → Fin 2 :=
  Function.update ω x (ω x + 1)

private theorem flipBit_self (x : Fin n × Fin 2) (ω : Fin n × Fin 2 → Fin 2) :
    flipBit x ω x = ω x + 1 := by
  simp [flipBit]

private theorem flipBit_of_ne {x y : Fin n × Fin 2} (h : y ≠ x)
    (ω : Fin n × Fin 2 → Fin 2) : flipBit x ω y = ω y := by
  simp [flipBit, h]

private theorem flipBit_involutive (x : Fin n × Fin 2) :
    Function.Involutive (flipBit (n := n) x) := by
  intro ω
  funext y
  by_cases h : y = x
  · subst h
    rw [flipBit_self, flipBit_self]
    have h2 : ∀ b : Fin 2, b + 1 + 1 = b := by decide
    exact h2 _
  · rw [flipBit_of_ne h, flipBit_of_ne h]

private theorem geneDrop_flip (P : Pedigree n) {j q : Fin n} (s : Fin 2) (hq : q < j)
    (ω : Fin n × Fin 2 → Fin 2) : P.geneDrop (flipBit (j, s) ω) q = P.geneDrop ω q := by
  refine geneDrop_congr P q fun k hk t => flipBit_of_ne ?_ ω
  intro h
  have hkj : k = j := congrArg Prod.fst h
  exact absurd (hkj ▸ hk) (not_le.mpr hq)

private theorem sum_transmit (P : Pedigree n) {j q : Fin n} (s : Fin 2) (hq : q < j)
    (h : (Fin n × Fin 2 → Fin 2) → Fin n × Fin 2 → ℝ)
    (hh : ∀ ω lab, h (flipBit (j, s) ω) lab = h ω lab) :
    ∑ ω, h ω (P.geneDrop ω q (ω (j, s))) = (1 / 2) * ∑ ω, ∑ b, h ω (P.geneDrop ω q b) := by
  have hflip : ∑ ω, h ω (P.geneDrop ω q (ω (j, s))) =
      ∑ ω, h ω (P.geneDrop ω q (ω (j, s) + 1)) := by
    rw [← Equiv.sum_comp ((flipBit_involutive (j, s)).toPerm)
      (fun ω => h ω (P.geneDrop ω q (ω (j, s))))]
    refine sum_congr rfl fun ω _ => ?_
    change h (flipBit (j, s) ω) (P.geneDrop (flipBit (j, s) ω) q (flipBit (j, s) ω (j, s))) = _
    rw [hh, geneDrop_flip P s hq, flipBit_self]
  have hfin : ∀ (f : Fin 2 → ℝ) (b : Fin 2), ∑ c, f c = f b + f (b + 1) := by
    intro f b
    rw [Fin.sum_univ_two]
    by_cases hb : b = 0
    · subst hb
      rfl
    · have hb1 : b = 1 := by omega
      subst hb1
      exact add_comm _ _
  rw [sum_congr rfl fun ω _ => hfin (fun b => h ω (P.geneDrop ω q b)) (ω (j, s)),
    sum_add_distrib, ← hflip]
  ring

private noncomputable def colMatch (X : Fin 2 → Fin n × Fin 2) (y : Fin n × Fin 2) : ℝ :=
  ((if X 0 = y then 1 else 0) + (if X 1 = y then 1 else 0)) / 2

private theorem founderKinship_eq_colMatch (w : (Fin n × Fin 2 → Fin 2) → ℝ)
    (X Y : (Fin n × Fin 2 → Fin 2) → Fin 2 → Fin n × Fin 2) :
    founderKinship w X Y =
      ∑ ω, w ω * ((colMatch (X ω) (Y ω 0) + colMatch (X ω) (Y ω 1)) / 2) := by
  unfold founderKinship colMatch
  refine sum_congr rfl fun ω _ => ?_
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  ring

theorem founderKinship_comm {O A : Type*} [Fintype O] [Fintype A] [DecidableEq A]
    (w : O → ℝ) (X Y : O → Fin 2 → A) : founderKinship w X Y = founderKinship w Y X := by
  unfold founderKinship
  refine sum_congr rfl fun o _ => ?_
  rw [sum_comm]
  simp only [eq_comm]

theorem founderKinship_self {O A : Type*} [Fintype O] [Fintype A] [DecidableEq A]
    (w : O → ℝ) (X : O → Fin 2 → A) (hw : ∑ o, w o = 1) :
    founderKinship w X X = (1 + founderIbd w X) / 2 := by
  have hpoint : ∀ o, w o * ∑ i : Fin 2, ∑ j : Fin 2, (if X o i = X o j then 1 else 0) / 4 =
      (w o + w o * (if X o 0 = X o 1 then 1 else 0)) / 2 := by
    intro o
    by_cases h : X o 0 = X o 1
    · simp only [Fin.sum_univ_two, h, ↓reduceIte]
      ring
    · simp only [Fin.sum_univ_two, h, Ne.symm h, ↓reduceIte]
      ring
  unfold founderKinship founderIbd
  rw [sum_congr rfl fun o _ => hpoint o, ← sum_div, sum_add_distrib, hw]

theorem geneDrop_kinship_of_lt_founder (P : Pedigree n) {i j : Fin n} (hij : i < j)
    (hj : P.parents j = none) :
    founderKinship (geneDropWeight n) (fun ω => P.geneDrop ω i) (fun ω => P.geneDrop ω j) =
      0 := by
  have hne : ∀ ω a b, P.geneDrop ω i a ≠ P.geneDrop ω j b := by
    intro ω a b h
    have hle := geneDrop_fst_le P ω i a
    rw [h, geneDrop_founder P ω hj] at hle
    exact absurd hle (not_le.mpr hij)
  rw [founderKinship_eq_colMatch]
  refine sum_eq_zero fun ω _ => ?_
  simp [colMatch, hne]

theorem geneDrop_kinship_of_lt (P : Pedigree n) {i j : Fin n} {p : Fin n × Fin n}
    (hij : i < j) (hj : P.parents j = some p) :
    founderKinship (geneDropWeight n) (fun ω => P.geneDrop ω i) (fun ω => P.geneDrop ω j) =
      (founderKinship (geneDropWeight n) (fun ω => P.geneDrop ω i)
          (fun ω => P.geneDrop ω p.1) +
        founderKinship (geneDropWeight n) (fun ω => P.geneDrop ω i)
          (fun ω => P.geneDrop ω p.2)) / 2 := by
  have hlt := P.parents_lt j p hj
  have hinv : ∀ (s : Fin 2) ω lab,
      geneDropWeight n (flipBit (j, s) ω) / 2 * colMatch (P.geneDrop (flipBit (j, s) ω) i) lab =
        geneDropWeight n ω / 2 * colMatch (P.geneDrop ω i) lab := by
    intro s ω lab
    rw [geneDrop_flip P s hij]
    rfl
  have t1 : ∑ ω, geneDropWeight n ω / 2 *
        colMatch (P.geneDrop ω i) (P.geneDrop ω p.1 (ω (j, 0))) =
      (1 / 2) * ∑ ω, ∑ b, geneDropWeight n ω / 2 *
        colMatch (P.geneDrop ω i) (P.geneDrop ω p.1 b) :=
    sum_transmit P 0 hlt.1 (fun ω lab => geneDropWeight n ω / 2 *
      colMatch (P.geneDrop ω i) lab) (hinv 0)
  have t2 : ∑ ω, geneDropWeight n ω / 2 *
        colMatch (P.geneDrop ω i) (P.geneDrop ω p.2 (ω (j, 1))) =
      (1 / 2) * ∑ ω, ∑ b, geneDropWeight n ω / 2 *
        colMatch (P.geneDrop ω i) (P.geneDrop ω p.2 b) :=
    sum_transmit P 1 hlt.2 (fun ω lab => geneDropWeight n ω / 2 *
      colMatch (P.geneDrop ω i) lab) (hinv 1)
  have e : ∀ ω, geneDropWeight n ω *
        ((colMatch (P.geneDrop ω i) (P.geneDrop ω j 0) +
          colMatch (P.geneDrop ω i) (P.geneDrop ω j 1)) / 2) =
      geneDropWeight n ω / 2 * colMatch (P.geneDrop ω i) (P.geneDrop ω p.1 (ω (j, 0))) +
      geneDropWeight n ω / 2 * colMatch (P.geneDrop ω i) (P.geneDrop ω p.2 (ω (j, 1))) := by
    intro ω
    rw [geneDrop_zero P ω hj, geneDrop_one P ω hj]
    ring
  rw [founderKinship_eq_colMatch, founderKinship_eq_colMatch, founderKinship_eq_colMatch,
    sum_congr rfl fun ω _ => e ω, sum_add_distrib, t1, t2, mul_sum, mul_sum, add_div,
    sum_div, sum_div]
  congr 1 <;> refine sum_congr rfl fun ω _ => ?_ <;> rw [Fin.sum_univ_two] <;> ring

theorem geneDrop_inbreeding_founder (P : Pedigree n) {i : Fin n} (hi : P.parents i = none) :
    founderIbd (geneDropWeight n) (fun ω => P.geneDrop ω i) = 0 := by
  unfold founderIbd
  refine sum_eq_zero fun ω _ => ?_
  simp [geneDrop_founder P ω hi]

theorem geneDrop_inbreeding_of_parents (P : Pedigree n) {i : Fin n} {p : Fin n × Fin n}
    (hi : P.parents i = some p) :
    founderIbd (geneDropWeight n) (fun ω => P.geneDrop ω i) =
      founderKinship (geneDropWeight n) (fun ω => P.geneDrop ω p.1)
        (fun ω => P.geneDrop ω p.2) := by
  have hlt := P.parents_lt i p hi
  have hne : ((i, 0) : Fin n × Fin 2) ≠ (i, 1) := by simp
  have t1 : ∑ ω, geneDropWeight n ω *
        (if P.geneDrop ω p.1 (ω (i, 0)) = P.geneDrop ω p.2 (ω (i, 1)) then 1 else 0) =
      (1 / 2) * ∑ ω, ∑ b, geneDropWeight n ω *
        (if P.geneDrop ω p.1 (ω (i, 0)) = P.geneDrop ω p.2 b then 1 else 0) := by
    refine sum_transmit P 1 hlt.2 (fun ω lab => geneDropWeight n ω *
      (if P.geneDrop ω p.1 (ω (i, 0)) = lab then 1 else 0)) ?_
    intro ω lab
    rw [geneDrop_flip P 1 hlt.1, flipBit_of_ne hne]
    rfl
  have t2 : ∀ b : Fin 2, ∑ ω, geneDropWeight n ω *
        (if P.geneDrop ω p.1 (ω (i, 0)) = P.geneDrop ω p.2 b then 1 else 0) =
      (1 / 2) * ∑ ω, ∑ a, geneDropWeight n ω *
        (if P.geneDrop ω p.1 a = P.geneDrop ω p.2 b then 1 else 0) := by
    intro b
    refine sum_transmit P 0 hlt.1 (fun ω lab => geneDropWeight n ω *
      (if lab = P.geneDrop ω p.2 b then 1 else 0)) ?_
    intro ω lab
    rw [geneDrop_flip P 0 hlt.2]
    rfl
  have e : ∀ ω, geneDropWeight n ω *
        (if P.geneDrop ω i 0 = P.geneDrop ω i 1 then 1 else 0) =
      geneDropWeight n ω *
        (if P.geneDrop ω p.1 (ω (i, 0)) = P.geneDrop ω p.2 (ω (i, 1)) then 1 else 0) := by
    intro ω
    rw [geneDrop_zero P ω hi, geneDrop_one P ω hi]
  unfold founderIbd founderKinship
  rw [sum_congr rfl fun ω _ => e ω, t1, sum_comm, Fin.sum_univ_two, t2 0, t2 1]
  simp only [Fin.sum_univ_two, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun ω _ => ?_
  ring

theorem geneDrop_kinship (P : Pedigree n) (i j : Fin n) :
    founderKinship (geneDropWeight n) (fun ω => P.geneDrop ω i) (fun ω => P.geneDrop ω j) =
      ((P.kinship i j : ℚ) : ℝ) := by
  refine pair_induction (motive := fun i j =>
    founderKinship (geneDropWeight n) (fun ω => P.geneDrop ω i) (fun ω => P.geneDrop ω j) =
      ((P.kinship i j : ℚ) : ℝ)) ?_ i j
  intro i j ih
  rcases lt_trichotomy i j with hij | rfl | hji
  · cases hj : P.parents j with
    | none =>
      rw [geneDrop_kinship_of_lt_founder P hij hj, kinship_of_lt_founder P hij hj,
        Rat.cast_zero]
    | some p =>
      have hlt := P.parents_lt j p hj
      rw [geneDrop_kinship_of_lt P hij hj, kinship_of_lt P hij hj,
        ih i p.1 (Nat.add_lt_add_left (Fin.lt_def.mp hlt.1) _),
        ih i p.2 (Nat.add_lt_add_left (Fin.lt_def.mp hlt.2) _)]
      push_cast
      ring
  · rw [founderKinship_self _ _ (geneDropWeight_sum n), kinship_self]
    cases hi : P.parents i with
    | none =>
      rw [geneDrop_inbreeding_founder P hi, inbreeding_founder P hi]
      push_cast
      ring
    | some p =>
      have hlt := P.parents_lt i p hi
      rw [geneDrop_inbreeding_of_parents P hi, inbreeding_of_parents P hi,
        ih p.1 p.2 (Nat.add_lt_add (Fin.lt_def.mp hlt.1) (Fin.lt_def.mp hlt.2))]
      push_cast
      ring
  · rw [founderKinship_comm, kinship_comm]
    cases hi : P.parents i with
    | none =>
      rw [geneDrop_kinship_of_lt_founder P hji hi, kinship_of_lt_founder P hji hi,
        Rat.cast_zero]
    | some p =>
      have hlt := P.parents_lt i p hi
      have h1 := Fin.lt_def.mp hlt.1
      have h2 := Fin.lt_def.mp hlt.2
      rw [geneDrop_kinship_of_lt P hji hi, kinship_of_lt P hji hi,
        ih j p.1 (by omega), ih j p.2 (by omega)]
      push_cast
      ring

theorem geneDrop_inbreeding (P : Pedigree n) (i : Fin n) :
    founderIbd (geneDropWeight n) (fun ω => P.geneDrop ω i) =
      ((P.inbreeding i : ℚ) : ℝ) := by
  cases hi : P.parents i with
  | none => rw [geneDrop_inbreeding_founder P hi, inbreeding_founder P hi, Rat.cast_zero]
  | some p =>
    rw [geneDrop_inbreeding_of_parents P hi, inbreeding_of_parents P hi, geneDrop_kinship]

end Rhone.Combinatorics.Pedigree
