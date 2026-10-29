/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.CheckerWeightedLawProof
public import Rhone.Computation.CheckerSoundnessProof
public import Rhone.Computation.CheckerRestrictionProof
public import Rhone.Computation.RangeProductProof

/-! # Exact normalization fold and the fully typed sampling law -/

@[expose] public section
namespace Rhone.Computation

open CheckerEncoding CheckerSpec Finset

private def typedTest (s : Config) (size : Nat) : Bool :=
  s.a.all (· == 0) && s.b.all (· == 0) && s.block == (size, size)

private def typedWeight (s : Config) (size : Nat) : Rat :=
  (factorial size : Rat) / (s.c.foldl (fun z count => z * factorial count) 1 : Rat)

private theorem typedTest_encode (ξ : Rhone.LinearAlgebra.Recursion.Config 2 2) (size : Nat) :
    typedTest (encode ξ) size = true ↔ ξ ∈ fullyTyped size := by
  have ha : (encode ξ).a.all (· == 0) = true ↔ ξ.a = (fun _ => 0) := by
    simp [encode, funext_iff, Fin.forall_fin_two]
  have hb : (encode ξ).b.all (· == 0) = true ↔ ξ.b = (fun _ => 0) := by
    simp [encode, funext_iff, Fin.forall_fin_two]
  simp only [typedTest, Bool.and_eq_true_iff, beq_iff_eq, ha, hb, encode_block,
    mem_fullyTyped]
  constructor
  · rintro ⟨⟨ha, hb⟩, hblock⟩
    refine ⟨ha, hb, ?_⟩
    simpa [Rhone.LinearAlgebra.Recursion.Config.nA, Rhone.LinearAlgebra.Recursion.Config.sumA, ha]
      using congrArg Prod.fst hblock
  · rintro ⟨ha, hb, ht⟩
    refine ⟨⟨ha, hb⟩, ?_⟩
    simp [Rhone.LinearAlgebra.Recursion.Config.nA, Rhone.LinearAlgebra.Recursion.Config.nB,
      Rhone.LinearAlgebra.Recursion.Config.sumA, Rhone.LinearAlgebra.Recursion.Config.sumB, ha, hb,
          ht]

private theorem typedWeight_encode (ξ : Rhone.LinearAlgebra.Recursion.Config 2 2) (size : Nat) :
    typedWeight (encode ξ) size = (Nat.factorial size : Rat) /
      ((∏ i, ∏ j, Nat.factorial (ξ.c i j) : Nat) : Rat) := by
  simp [typedWeight, encode, factorial, rangeProduct_zero_eq_factorial,
    Fin.prod_univ_two, mul_assoc]

private theorem fold_typed_sum [DecidableEq Config] (l : List Config) (hn : l.Nodup)
    (p : Config → Bool) (f : Config → Rat) (initial : Rat) :
    l.foldl (fun mass s => if p s then mass + f s else mass) initial =
      initial + ∑ s ∈ l.toFinset.filter (fun s => p s), f s := by
  induction l generalizing initial with
  | nil => simp
  | cons s l ih =>
    obtain ⟨hs, hl⟩ := List.nodup_cons.mp hn
    simp only [List.foldl_cons]
    rw [ih hl]
    by_cases hp : p s = true <;> simp [Finset.filter_insert, hp, hs, add_assoc]

theorem checkerNormalization_eq_weighted (value : Config → Rat)
    (f : Rhone.LinearAlgebra.Recursion.Config 2 2 → Rat) {n size : Nat} (hsize : size ≤ n)
    (hv : ∀ s ∈ closure n, value s = f (decode s)) :
    checkerNormalization value (closure n) size =
      ∑ ξ ∈ fullyTyped size, (Nat.factorial size : Rat) /
        ((∏ i, ∏ j, Nat.factorial (ξ.c i j) : Nat) : Rat) * f ξ := by
  classical
  have hfold : checkerNormalization value (closure n) size =
      (closureList n).foldl (fun mass s =>
        if typedTest s size then mass + typedWeight s size * value s else mass) 0 := by
    simp [checkerNormalization, closure, typedTest, typedWeight]
  rw [hfold, fold_typed_sum _ (closureList_nodup n), zero_add]
  refine Finset.sum_bij (fun s _ => decode s) ?_ ?_ ?_ ?_
  · intro s hs
    obtain ⟨hs, ht⟩ := Finset.mem_filter.mp hs
    obtain ⟨ha, hb, hc⟩ := closureList_shape (List.mem_toFinset.mp hs)
    apply (typedTest_encode (decode s) size).mp
    simpa only [encode_decode s ha hb hc] using ht
  · intro s hs t ht he
    have hshape (x : Config)
        (hx : x ∈ (closureList n).toFinset.filter (fun s => typedTest s size)) :=
      closureList_shape (List.mem_toFinset.mp (Finset.mem_filter.mp hx).1)
    obtain ⟨sa, sb, sc⟩ := hshape s hs
    obtain ⟨ta, tb, tc⟩ := hshape t ht
    exact (encode_decode s sa sb sc).symm.trans
      ((congrArg encode he).trans (encode_decode t ta tb tc))
  · intro ξ hξ
    obtain ⟨ha, hb, ht⟩ := mem_fullyTyped.mp hξ
    have hin : InClosure n ξ := by
      simpa [InClosure, Rhone.LinearAlgebra.Recursion.Config.nA,
        Rhone.LinearAlgebra.Recursion.Config.nB, Rhone.LinearAlgebra.Recursion.Config.sumA,
        Rhone.LinearAlgebra.Recursion.Config.sumB, ha, hb, ht] using And.intro hsize hsize
    have hs : encode ξ ∈ closureList n := by
      simpa only [closure, List.mem_toArray] using (encode_mem_closure ξ).mpr hin
    refine ⟨encode ξ, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hs,
      (typedTest_encode ξ size).mpr hξ⟩, decode_encode ξ⟩
  · intro s hs
    have hmem : s ∈ closure n := by
      simpa only [closure, List.mem_toArray] using
        List.mem_toFinset.mp (Finset.mem_filter.mp hs).1
    obtain ⟨ha, hb, hc⟩ := closureList_shape
      (List.mem_toFinset.mp (Finset.mem_filter.mp hs).1)
    have hw := typedWeight_encode (decode s) size
    rw [encode_decode s ha hb hc] at hw
    rw [hw, hv s hmem]

end Rhone.Computation
