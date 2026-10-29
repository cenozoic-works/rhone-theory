/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.GenericKernel
public import Rhone.Computation.GenericWire
public import Std.Data.HashMap.Lemmas

/-! # The core-library general-allele checker equals the Mathlib one -/

@[expose] public section
namespace Rhone.Computation.GenericKernel
open Lean LinearAlgebra.Recursion

theorem lsum_eq (f : Nat → Rat) (n : Nat) : lsum f n = ∑ i : Fin n, f i := by
  induction n with
  | zero => simp [lsum]
  | succ k ih => rw [lsum, ih, Fin.sum_univ_castSucc]; simp

theorem nsum_eq (f : Nat → Nat) (n : Nat) : nsum f n = ∑ i : Fin n, f i := by
  induction n with
  | zero => simp [nsum]
  | succ k ih => rw [nsum, ih, Fin.sum_univ_castSucc]; simp

theorem term_eq (k : Nat) (v : Unit → Rat) : term k v = (k : Rat) * v () := by
  unfold term
  split <;> simp_all

def toFin (d : Nat) (l : List Nat) : Fin d → Nat := fun i => l.getD i.val 0

theorem countsL_map (d N : Nat) : (countsL d N).map (toFin d) = GenericClosure.counts d N := by
  induction d generalizing N with
  | zero =>
    simp only [countsL, GenericClosure.counts, List.map_cons, List.map_nil, List.cons.injEq,
      and_true]
    funext i
    exact Fin.elim0 i
  | succ d ih =>
    simp only [countsL, GenericClosure.counts, List.map_flatMap, List.map_map]
    congr 1
    funext a
    rw [← ih (N - a), List.map_map]
    congr 1
    funext l
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [toFin]
    · simp [toFin]

theorem length_of_mem_countsL {d N : Nat} {l : List Nat} (h : l ∈ countsL d N) :
    l.length = d := by
  induction d generalizing N l with
  | zero => simp [countsL] at h; simp [h]
  | succ d ih =>
    simp only [countsL, List.mem_flatMap, List.mem_map] at h
    obtain ⟨a, _, t, ht, rfl⟩ := h
    simp [ih ht]

theorem sum_toFin {d : Nat} {l : List Nat} (h : l.length = d) :
    ∑ i : Fin d, toFin d l i = l.sum := by
  induction l generalizing d with
  | nil => subst h; simp
  | cons a l ih =>
    cases d with
    | zero => simp at h
    | succ d =>
      rw [Fin.sum_univ_succ, List.sum_cons, ← ih (d := d) (by simpa using h)]
      simp [toFin]

def Shaped (ka kb : Nat) (x : Config) : Prop :=
  x.a.size = ka ∧ x.b.size = kb ∧ x.c.size = ka * kb

theorem toSpec_zero (ka kb : Nat) : GenericWire.toSpec ka kb (zero ka kb) = 0 := by
  apply Config.ext <;> funext <;> simp [GenericWire.toSpec, zero, Array.getD]

theorem configs_map (ka kb N : Nat) :
    (configs ka kb N).map (GenericWire.toSpec ka kb) = GenericClosure.configs ka kb N := by
  unfold configs GenericClosure.configs
  by_cases hN : N = 0
  · simp [hN, toSpec_zero]
  · simp only [hN, ↓reduceIte, ← countsL_map, List.flatMap_map, List.map_flatMap, List.map_map]
    apply List.flatMap_congr
    intro c hc
    rw [sum_toFin (length_of_mem_countsL hc)]
    apply List.flatMap_congr
    intro a _
    apply List.map_congr_left
    intro b _
    simp only [Function.comp_apply, GenericWire.toSpec]
    congr 1
    · funext i; simp [toFin]
    · funext j; simp [toFin]
    · funext i j
      simp only [GenericClosure.matrix, toFin, finProdFinEquiv_apply_val,
        Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getD_eq_getElem?_getD]
      rw [show (i : Nat) * kb + j = j + kb * i by ring]

theorem shaped_of_mem_configs {ka kb N : Nat} {x : Config} (h : x ∈ configs ka kb N) :
    Shaped ka kb x := by
  unfold configs at h
  split at h
  · simp only [List.mem_singleton] at h
    subst h
    simp [Shaped, zero]
  · simp only [List.mem_flatMap, List.mem_map] at h
    obtain ⟨c, hc, a, ha, b, hb, rfl⟩ := h
    exact ⟨by simp [length_of_mem_countsL ha], by simp [length_of_mem_countsL hb],
      by simp [length_of_mem_countsL hc]⟩

theorem tC_eq (ka kb : Nat) (x : Config) : tC ka kb x = (GenericWire.toSpec ka kb x).t := by
  simp only [tC, nsum_eq, cc, Config.t, GenericWire.toSpec]

theorem nA_eq (ka kb : Nat) (x : Config) : nA ka kb x = (GenericWire.toSpec ka kb x).nA := by
  simp only [nA, tC_eq, nsum_eq, ca, Config.nA, Config.sumA, GenericWire.toSpec]

theorem nB_eq (ka kb : Nat) (x : Config) : nB ka kb x = (GenericWire.toSpec ka kb x).nB := by
  simp only [nB, tC_eq, nsum_eq, cb, Config.nB, Config.sumB, GenericWire.toSpec]

theorem nL_eq (ka kb : Nat) (x : Config) : nL ka kb x = (GenericWire.toSpec ka kb x).n := by
  simp only [nL, tC_eq, nsum_eq, ca, cb, Config.n, Config.sumA, Config.sumB,
    GenericWire.toSpec]

theorem diag_eq (p : Params) (x : Config) :
    diag p x = Rhone.LinearAlgebra.Recursion.diag p.thetaA p.thetaB p.rho
      (GenericWire.toSpec p.piA.size p.piB.size x) := by
  simp only [diag, Rhone.LinearAlgebra.Recursion.diag, nL_eq, nA_eq, nB_eq, tC_eq]

theorem boundary_eq (p : Params) (x : Config) :
    boundary p x = GenericClosure.boundary (GenericWire.pi p.piA) (GenericWire.pi p.piB)
      (GenericWire.toSpec p.piA.size p.piB.size x) := by
  simp only [boundary, GenericClosure.boundary, nL_eq, lsum_eq, ca, cb, cc, GenericWire.pi,
    GenericWire.toSpec]
  rfl

theorem getD_set {xs : Array Nat} {i : Nat} (k v : Nat) (hi : i < xs.size) :
    (xs.set! i v).getD k 0 = if i = k then v else xs.getD k 0 := by
  simp only [Array.set!, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  by_cases h : i = k
  · subst h; simp [hi]
  · simp [h]

theorem index_inj {kb i j i' j' : Nat} (hj : j < kb) (hj' : j' < kb) :
    i * kb + j = i' * kb + j' ↔ i = i' ∧ j = j' := by
  constructor
  · intro h
    have h1 : (i * kb + j) / kb = i := by
      rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hj, Nat.add_zero]
    have h2 : (i' * kb + j') / kb = i' := by
      rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hj', Nat.add_zero]
    have hi : i = i' := by rw [← h1, ← h2, h]
    subst hi
    exact ⟨rfl, by omega⟩
  · rintro ⟨rfl, rfl⟩; rfl

theorem toFn_dec {n : Nat} (xs : Array Nat) (hs : xs.size = n) (i : Fin n) :
    (fun k : Fin n => (dec xs i).getD k 0) = decf (fun k : Fin n => xs.getD k 0) i := by
  funext k
  rw [dec, getD_set _ _ (by omega), decf]
  by_cases h : (i : Nat) = k
  · have : i = k := Fin.ext h
    subst this; simp
  · have : k ≠ i := fun e => h (by rw [e])
    simp [h, Function.update_of_ne this]

theorem toFn_inc {n : Nat} (xs : Array Nat) (hs : xs.size = n) (i : Fin n) :
    (fun k : Fin n => (inc xs i).getD k 0) = incf (fun k : Fin n => xs.getD k 0) i := by
  funext k
  rw [inc, getD_set _ _ (by omega), incf]
  by_cases h : (i : Nat) = k
  · have : i = k := Fin.ext h
    subst this; simp
  · have : k ≠ i := fun e => h (by rw [e])
    simp [h, Function.update_of_ne this]

theorem index_lt {ka kb : Nat} (i : Fin ka) (j : Fin kb) : (i : Nat) * kb + j < ka * kb := by
  have hi := i.isLt
  have hj := j.isLt
  calc (i : Nat) * kb + j < (i : Nat) * kb + kb := by omega
    _ = ((i : Nat) + 1) * kb := by ring
    _ ≤ ka * kb := Nat.mul_le_mul_right _ hi

theorem toFn2_dec {ka kb : Nat} (xs : Array Nat) (hs : xs.size = ka * kb) (i : Fin ka)
    (j : Fin kb) :
    (fun (i' : Fin ka) (j' : Fin kb) => (dec xs (i * kb + j)).getD (i' * kb + j') 0) =
      Rhone.LinearAlgebra.Recursion.Config.decC
        (fun (i' : Fin ka) (j' : Fin kb) => xs.getD (i' * kb + j') 0) i j := by
  funext i' j'
  rw [dec, getD_set _ _ (by have := index_lt i j; omega),
    Rhone.LinearAlgebra.Recursion.Config.decC]
  simp only [index_inj j.isLt j'.isLt]
  by_cases hi : i' = i
  · subst hi
    by_cases hj : j' = j
    · subst hj; simp [decf]
    · have : (j : Nat) ≠ j' := fun e => hj (Fin.ext e.symm)
      simp [this, decf, Function.update_of_ne hj]
  · have : (i : Nat) ≠ i' := fun e => hi (Fin.ext e.symm)
    simp [this, Function.update_of_ne hi]

theorem toFn2_inc {ka kb : Nat} (xs : Array Nat) (hs : xs.size = ka * kb) (i : Fin ka)
    (j : Fin kb) :
    (fun (i' : Fin ka) (j' : Fin kb) => (inc xs (i * kb + j)).getD (i' * kb + j') 0) =
      Rhone.LinearAlgebra.Recursion.Config.incC
        (fun (i' : Fin ka) (j' : Fin kb) => xs.getD (i' * kb + j') 0) i j := by
  funext i' j'
  rw [inc, getD_set _ _ (by have := index_lt i j; omega),
    Rhone.LinearAlgebra.Recursion.Config.incC]
  simp only [index_inj j.isLt j'.isLt]
  by_cases hi : i' = i
  · subst hi
    by_cases hj : j' = j
    · subst hj; simp [incf]
    · have : (j : Nat) ≠ j' := fun e => hj (Fin.ext e.symm)
      simp [this, incf, Function.update_of_ne hj]
  · have : (i : Nat) ≠ i' := fun e => hi (Fin.ext e.symm)
    simp [this, Function.update_of_ne hi]

section Moves
variable {ka kb : Nat} {x : Config} (hx : Shaped ka kb x) (i : Fin ka) (j : Fin kb)
include hx

theorem toSpec_dropA : GenericWire.toSpec ka kb (dropA x i) =
    (GenericWire.toSpec ka kb x).dropA i := by
  simp only [GenericWire.toSpec, dropA, Config.dropA, toFn_dec x.a hx.1 i]

theorem toSpec_dropB : GenericWire.toSpec ka kb (dropB x j) =
    (GenericWire.toSpec ka kb x).dropB j := by
  simp only [GenericWire.toSpec, dropB, Config.dropB, toFn_dec x.b hx.2.1 j]

theorem toSpec_dropC : GenericWire.toSpec ka kb (dropC kb x i j) =
    (GenericWire.toSpec ka kb x).dropC i j := by
  simp only [GenericWire.toSpec, dropC, Config.dropC, toFn2_dec x.c hx.2.2 i j]

theorem toSpec_mergeAB : GenericWire.toSpec ka kb (mergeAB kb x i j) =
    (GenericWire.toSpec ka kb x).mergeAB i j := by
  simp only [GenericWire.toSpec, mergeAB, Config.mergeAB, toFn_dec x.a hx.1 i,
    toFn_dec x.b hx.2.1 j, toFn2_inc x.c hx.2.2 i j]

theorem toSpec_killA : GenericWire.toSpec ka kb (killA kb x i j) =
    (GenericWire.toSpec ka kb x).killA i j := by
  simp only [GenericWire.toSpec, killA, Config.killA, toFn_inc x.b hx.2.1 j,
    toFn2_dec x.c hx.2.2 i j]

theorem toSpec_killB : GenericWire.toSpec ka kb (killB kb x i j) =
    (GenericWire.toSpec ka kb x).killB i j := by
  simp only [GenericWire.toSpec, killB, Config.killB, toFn_inc x.a hx.1 i,
    toFn2_dec x.c hx.2.2 i j]

theorem toSpec_split : GenericWire.toSpec ka kb (split kb x i j) =
    (GenericWire.toSpec ka kb x).split i j := by
  simp only [GenericWire.toSpec, split, Config.split, toFn_inc x.a hx.1 i,
    toFn_inc x.b hx.2.1 j, toFn2_dec x.c hx.2.2 i j]

end Moves

theorem shaped_moves {ka kb : Nat} {x : Config} (hx : Shaped ka kb x) (kb' i j : Nat) :
    Shaped ka kb (dropA x i) ∧ Shaped ka kb (dropB x j) ∧ Shaped ka kb (dropC kb' x i j) ∧
      Shaped ka kb (mergeAB kb' x i j) ∧ Shaped ka kb (killA kb' x i j) ∧
      Shaped ka kb (killB kb' x i j) ∧ Shaped ka kb (split kb' x i j) := by
  obtain ⟨ha, hb, hc⟩ := hx
  simp [Shaped, dropA, dropB, dropC, mergeAB, killA, killB, split, dec, inc, ha, hb, hc]

theorem rhs_eq (p : Params) (value : Config → Rat)
    (f : Rhone.LinearAlgebra.Recursion.Config p.piA.size p.piB.size → Rat) {x : Config}
    (hx : Shaped p.piA.size p.piB.size x)
    (hv : ∀ y, Shaped p.piA.size p.piB.size y →
      value y = f (GenericWire.toSpec p.piA.size p.piB.size y)) :
    rhs p value x = Rhone.LinearAlgebra.Recursion.rhs p.thetaA p.thetaB p.rho
      (GenericWire.pi p.piA) (GenericWire.pi p.piB) f
      (GenericWire.toSpec p.piA.size p.piB.size x) := by
  have hm := shaped_moves hx p.piB.size
  have hA : ∀ i : Fin p.piA.size, value (dropA x i) =
      f ((GenericWire.toSpec _ _ x).dropA i) := fun i => by
    rw [hv _ (hm i 0).1, toSpec_dropA hx]
  have hB : ∀ j : Fin p.piB.size, value (dropB x j) =
      f ((GenericWire.toSpec _ _ x).dropB j) := fun j => by
    rw [hv _ (hm 0 j).2.1, toSpec_dropB hx]
  have hC : ∀ (i : Fin p.piA.size) (j : Fin p.piB.size), value (dropC p.piB.size x i j) =
      f ((GenericWire.toSpec _ _ x).dropC i j) := fun i j => by
    rw [hv _ (hm i j).2.2.1, toSpec_dropC hx]
  have hAB : ∀ (i : Fin p.piA.size) (j : Fin p.piB.size), value (mergeAB p.piB.size x i j) =
      f ((GenericWire.toSpec _ _ x).mergeAB i j) := fun i j => by
    rw [hv _ (hm i j).2.2.2.1, toSpec_mergeAB hx]
  have hkA : ∀ (i : Fin p.piA.size) (j : Fin p.piB.size), value (killA p.piB.size x i j) =
      f ((GenericWire.toSpec _ _ x).killA i j) := fun i j => by
    rw [hv _ (hm i j).2.2.2.2.1, toSpec_killA hx]
  have hkB : ∀ (i : Fin p.piA.size) (j : Fin p.piB.size), value (killB p.piB.size x i j) =
      f ((GenericWire.toSpec _ _ x).killB i j) := fun i j => by
    rw [hv _ (hm i j).2.2.2.2.2.1, toSpec_killB hx]
  have hS : ∀ (i : Fin p.piA.size) (j : Fin p.piB.size), value (split p.piB.size x i j) =
      f ((GenericWire.toSpec _ _ x).split i j) := fun i j => by
    rw [hv _ (hm i j).2.2.2.2.2.2, toSpec_split hx]
  unfold rhs Rhone.LinearAlgebra.Recursion.rhs
  simp only [lsum_eq, nsum_eq, term_eq, hA, hB, hC, hAB, hkA, hkB, hS]
  rfl

theorem closureCheck_eq (p : Params) (N : Nat) (value : Config → Rat)
    (f : Rhone.LinearAlgebra.Recursion.Config p.piA.size p.piB.size → Rat)
    (hv : ∀ y, Shaped p.piA.size p.piB.size y →
      value y = f (GenericWire.toSpec p.piA.size p.piB.size y)) :
    closureCheck p N value = GenericClosure.check p.thetaA p.thetaB p.rho
      (GenericWire.pi p.piA) (GenericWire.pi p.piB) N f := by
  unfold closureCheck GenericClosure.check
  rw [← configs_map, List.all_map]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true, Function.comp_apply]
  refine forall_congr' fun x => imp_congr_right fun hx => ?_
  have hs := shaped_of_mem_configs hx
  rw [nL_eq, hv x hs, boundary_eq, diag_eq, rhs_eq p value f hs hv]

theorem toSpec_inj {ka kb : Nat} {x y : Config} (hx : Shaped ka kb x) (hy : Shaped ka kb y)
    (h : GenericWire.toSpec ka kb x = GenericWire.toSpec ka kb y) : x = y := by
  rw [← GenericWire.fromSpec_toSpec ka kb x hx.1 hx.2.1 hx.2.2,
    ← GenericWire.fromSpec_toSpec ka kb y hy.1 hy.2.1 hy.2.2, h]

theorem keyOf_inj {x y : Config} (h : keyOf x = keyOf y) : x = y := by
  cases x; cases y
  simp only [keyOf, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  rfl

theorem insertRows_spec (rows : List (Config × Rat)) (m : Std.HashMap Key Rat) :
    (∃ t, insertRows rows m = some t) ↔
      ((rows.map (fun row => keyOf row.1)).Nodup ∧
        ∀ row ∈ rows, m.contains (keyOf row.1) = false) := by
  induction rows generalizing m with
  | nil => simp [insertRows]
  | cons row rows ih =>
    simp only [insertRows]
    by_cases hc : m.contains (keyOf row.1) = true
    · refine ⟨fun ⟨t, ht⟩ => by simp [hc] at ht, fun ⟨_, hall⟩ => ?_⟩
      have := hall row List.mem_cons_self
      rw [hc] at this; cases this
    · simp only [hc, Bool.false_eq_true, ↓reduceIte, ih, List.map_cons, List.nodup_cons,
        List.mem_map, List.mem_cons, forall_eq_or_imp, Std.HashMap.contains_insert,
        Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
      simp only [Bool.not_eq_true] at hc
      constructor
      · rintro ⟨hnd, hall⟩
        exact ⟨⟨fun ⟨r, hr, he⟩ => (hall r hr).1 he.symm, hnd⟩, trivial, fun r hr => (hall r hr).2⟩
      · rintro ⟨⟨hnot, hnd⟩, _, hall⟩
        exact ⟨hnd, fun r hr => ⟨fun he => hnot ⟨r, hr, he.symm⟩, hall r hr⟩⟩

theorem insertRows_get (rows : List (Config × Rat)) (m t : Std.HashMap Key Rat)
    (h : insertRows rows m = some t) (k : Key) :
    t.get? k = ((rows.find? (fun row => keyOf row.1 == k)).map Prod.snd).or (m.get? k) := by
  induction rows generalizing m with
  | nil => simp only [insertRows, Option.some.injEq] at h; subst h; simp
  | cons row rows ih =>
    simp only [insertRows] at h
    split at h
    · cases h
    · rename_i hc
      rw [ih _ h, Std.HashMap.get?_insert]
      by_cases hk : keyOf row.1 = k
      · subst hk
        have hspec := (insertRows_spec rows _).mp ⟨t, h⟩
        have hnone : rows.find? (fun r => keyOf r.1 == keyOf row.1) = none := by
          rw [List.find?_eq_none]
          intro r hr he
          have := hspec.2 r hr
          rw [beq_iff_eq.mp he, Std.HashMap.contains_insert] at this
          simp at this
        simp [hnone]
      · have : (keyOf row.1 == k) = false := by simpa using hk
        simp [this]

theorem find_key_of_nodup {rows : List (Config × Rat)}
    (hnd : (rows.map (fun row => keyOf row.1)).Nodup) {r : Config × Rat} (hr : r ∈ rows) :
    rows.find? (fun row => keyOf row.1 == keyOf r.1) = some r := by
  induction rows with
  | nil => simp at hr
  | cons h rows ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    rcases List.mem_cons.mp hr with rfl | hr
    · simp
    · by_cases hk : keyOf h.1 = keyOf r.1
      · exact absurd ⟨r, hr, hk.symm⟩ hnd.1
      · have : (keyOf h.1 == keyOf r.1) = false := by simpa using hk
        simp [this, ih hnd.2 hr]

theorem find_congr {α : Type} {p q : α → Bool} {l : List α} (h : ∀ x ∈ l, p x = q x) :
    l.find? p = l.find? q :=
  List.find?_congr h

def specRows (ka kb : Nat) (rows : List (Config × Rat)) :
    List (Rhone.LinearAlgebra.Recursion.Config ka kb × Rat) :=
  rows.map fun row => (GenericWire.toSpec ka kb row.1, row.2)

theorem same_toSpec {ka kb : Nat} {x y : Config} (hx : Shaped ka kb x) (hy : Shaped ka kb y) :
    GenericRows.same (GenericWire.toSpec ka kb x) (GenericWire.toSpec ka kb y) =
      (keyOf x == keyOf y) := by
  apply Bool.eq_iff_iff.mpr
  rw [GenericRows.same_true_iff, beq_iff_eq]
  constructor
  · intro h; rw [toSpec_inj hx hy h]
  · intro h; rw [keyOf_inj h]

theorem value_specRows {ka kb : Nat} {rows : List (Config × Rat)}
    (hs : ∀ row ∈ rows, Shaped ka kb row.1) {t : Std.HashMap Key Rat}
    (ht : insertRows rows {} = some t) {y : Config} (hy : Shaped ka kb y) :
    GenericRows.value (specRows ka kb rows) (GenericWire.toSpec ka kb y) =
      t.getD (keyOf y) 0 := by
  unfold GenericRows.value specRows
  rw [List.find?_map, Std.HashMap.getD_eq_getD_getElem?, ← Std.HashMap.get?_eq_getElem?,
    insertRows_get rows {} t ht]
  have hc : rows.find? ((fun row => GenericRows.same row.1 (GenericWire.toSpec ka kb y)) ∘
      (fun row => (GenericWire.toSpec ka kb row.1, row.2))) =
      rows.find? (fun row => keyOf row.1 == keyOf y) :=
    find_congr fun r hr => by simp only [Function.comp_apply, same_toSpec (hs r hr) hy]
  rw [hc]
  cases rows.find? (fun row => keyOf row.1 == keyOf y) <;> simp

theorem present_specRows {ka kb : Nat} {rows : List (Config × Rat)}
    (hs : ∀ row ∈ rows, Shaped ka kb row.1) {t : Std.HashMap Key Rat}
    (ht : insertRows rows {} = some t) {y : Config} (hy : Shaped ka kb y) :
    GenericRows.present (specRows ka kb rows) (GenericWire.toSpec ka kb y) =
      t.contains (keyOf y) := by
  unfold GenericRows.present specRows
  rw [Std.HashMap.contains_eq_isSome_getElem?, ← Std.HashMap.get?_eq_getElem?,
    insertRows_get rows {} t ht, List.any_map]
  have hc : rows.any ((fun row => GenericRows.same row.1 (GenericWire.toSpec ka kb y)) ∘
      (fun row => (GenericWire.toSpec ka kb row.1, row.2))) =
      rows.any (fun row => keyOf row.1 == keyOf y) := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, Function.comp_apply]
    exact exists_congr fun r => and_congr_right fun hr => by rw [same_toSpec (hs r hr) hy]
  rw [hc, ← List.isSome_find?]
  cases rows.find? (fun row => keyOf row.1 == keyOf y) <;> simp

theorem nodup_specRows {ka kb : Nat} {rows : List (Config × Rat)}
    (hs : ∀ row ∈ rows, Shaped ka kb row.1) :
    ((specRows ka kb rows).map Prod.fst).Nodup ↔
      (rows.map (fun row => keyOf row.1)).Nodup := by
  have e1 : (specRows ka kb rows).map Prod.fst =
      (rows.map Prod.fst).map (GenericWire.toSpec ka kb) := by
    simp [specRows, List.map_map, Function.comp_def]
  have e2 : rows.map (fun row => keyOf row.1) = (rows.map Prod.fst).map keyOf := by
    simp [List.map_map, Function.comp_def]
  rw [e1, e2]
  have hs' : ∀ x ∈ rows.map Prod.fst, Shaped ka kb x := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
    exact hs r hr
  constructor
  · intro h
    exact (h.of_map _).map (fun _ _ e => keyOf_inj e)
  · intro h
    exact (h.of_map _).map_on fun x hx y hy e => toSpec_inj (hs' x hx) (hs' y hy) e

theorem rowsCheck_eq (p : Params) (N : Nat) (rows : List (Config × Rat))
    (hs : ∀ row ∈ rows, Shaped p.piA.size p.piB.size row.1) :
    rowsCheck p N rows = GenericRows.check p.thetaA p.thetaB p.rho
      (GenericWire.pi p.piA) (GenericWire.pi p.piB) N (specRows p.piA.size p.piB.size rows) := by
  have hA : rows.all (fun row => inClosure p.piA.size p.piB.size N row.1) =
      (specRows p.piA.size p.piB.size rows).all
        (fun row => decide (CheckerSpec.InClosure N row.1)) := by
    simp only [specRows, List.all_map, Function.comp_def, inClosure, nA_eq, nB_eq,
      CheckerSpec.InClosure]
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    exact forall₂_congr fun _ _ => decide_eq_true_iff.symm
  unfold rowsCheck GenericRows.check
  rw [hA]
  cases ht : insertRows rows {} with
  | none =>
    have hnd : ¬ (rows.map (fun row => keyOf row.1)).Nodup := by
      intro hnd
      obtain ⟨t, ht'⟩ := (insertRows_spec rows {}).mpr ⟨hnd, fun _ _ => by simp⟩
      rw [ht] at ht'
      cases ht'
    have hu : GenericRows.uniqueKeys (specRows p.piA.size p.piB.size rows) = false := by
      simpa [GenericRows.uniqueKeys, nodup_specRows hs] using hnd
    simp [hu]
  | some t =>
    have hnd := ((insertRows_spec rows {}).mp ⟨t, ht⟩).1
    have hu : GenericRows.uniqueKeys (specRows p.piA.size p.piB.size rows) = true := by
      simpa [GenericRows.uniqueKeys, nodup_specRows hs] using hnd
    have hnc : GenericRows.noConflicts (specRows p.piA.size p.piB.size rows) = true := by
      simp only [GenericRows.noConflicts, List.all_eq_true, decide_eq_true_eq]
      intro row hrow
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hrow
      rw [value_specRows hs ht (hs r hr), Std.HashMap.getD_eq_getD_getElem?,
        ← Std.HashMap.get?_eq_getElem?, insertRows_get rows {} t ht, find_key_of_nodup hnd hr]
      simp
    have hP : (configs p.piA.size p.piB.size N).all (fun x => t.contains (keyOf x)) =
        (GenericClosure.configs p.piA.size p.piB.size N).all
          (GenericRows.present (specRows p.piA.size p.piB.size rows)) := by
      rw [← configs_map, List.all_map]
      apply Bool.eq_iff_iff.mpr
      simp only [List.all_eq_true, Function.comp_apply]
      exact forall_congr' fun x => imp_congr_right fun hx => by
        rw [present_specRows hs ht (shaped_of_mem_configs hx)]
    have hE : closureCheck p N (fun x => t.getD (keyOf x) 0) =
        GenericClosure.check p.thetaA p.thetaB p.rho (GenericWire.pi p.piA)
          (GenericWire.pi p.piB) N (GenericRows.value (specRows p.piA.size p.piB.size rows)) :=
      closureCheck_eq p N _ _ fun y hy => (value_specRows hs ht hy).symm
    simp only [hP, hE, hu, hnc, Bool.and_true, Bool.and_assoc]

theorem valid_eq (p : Params) : valid p = GenericWire.valid p := by
  apply Bool.eq_iff_iff.mpr
  simp only [valid, GenericWire.valid, asum, lsum_eq, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, List.mem_range, GenericWire.pi, Fin.forall_iff]
  tauto

def Request.toWire (r : Request) : GenericWire.Request := ⟨r.params, r.bound, r.rawRows⟩

theorem Request.accepted_eq (r : Request) : r.accepted = r.toWire.accepted := by
  unfold Request.accepted GenericWire.Request.accepted Request.toWire
  simp only [valid_eq]
  cases hs : r.rawRows.all (fun row =>
      row.1.a.size == r.params.piA.size && row.1.b.size == r.params.piB.size &&
        row.1.c.size == r.params.piA.size * r.params.piB.size)
  · simp
  · have hsh : ∀ row ∈ r.rawRows.toList, Shaped r.params.piA.size r.params.piB.size row.1 := by
      simp only [Array.all_eq_true', Bool.and_eq_true, beq_iff_eq] at hs
      intro row hr
      obtain ⟨⟨ha, hb⟩, hc⟩ := hs row (by simpa using hr)
      exact ⟨ha, hb, hc⟩
    rw [rowsCheck_eq _ _ _ hsh]
    rfl

theorem entry_eq : entry = GenericWire.entry := rfl

theorem fieldsAllowed_eq : fieldsAllowed = GenericWire.fieldsAllowed := rfl

theorem checkRequest_eq (doc : Json) : checkRequest doc = GenericWire.checkRequest doc := by
  have ite_bind' : ∀ {α β : Type} {c : Prop} [Decidable c] (A B : Except String α)
      (k : α → Except String β), ((if c then A else B) >>= k) = if c then A >>= k else B >>= k :=
    fun A B k => by split <;> rfl
  simp only [checkRequest, GenericWire.checkRequest, decode, GenericWire.decode, bind_assoc,
    pure_bind, valid_eq, fieldsAllowed_eq, entry_eq, Request.accepted_eq, Request.toWire,
    ite_bind']

theorem request_eq (line : String) : request line = GenericWire.request line := by
  simp only [request, GenericWire.request]
  rw [show checkRequest = GenericWire.checkRequest from funext checkRequest_eq]

theorem request_probability (line : String) (h : request line = .ok true) :
    ∃ doc : Json, Json.parse line = .ok doc ∧ ∃ r : GenericWire.Request,
      GenericWire.decode doc = .ok r ∧ ∀ row ∈ r.rawRows.toList, (row.2 : Real) =
        Rhone.Coalescent.TwoLocusGenealogy.qProb (r.params.thetaA : Real) (r.params.thetaB : Real)
          (r.params.rho : Real) (fun i => (GenericWire.pi r.params.piA i : Real))
          (fun j => (GenericWire.pi r.params.piB j : Real))
          (GenericWire.toSpec r.params.piA.size r.params.piB.size row.1) := by
  rw [request_eq] at h
  obtain ⟨doc, hd, r, hr, ha⟩ := GenericWire.request_accept line h
  exact ⟨doc, hd, r, hr, GenericWire.Request.accepted_probability r ha⟩

end Rhone.Computation.GenericKernel
