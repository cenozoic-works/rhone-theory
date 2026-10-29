/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Coalescent.SmcPrimeOneSplitEventTime
public import Mathlib.Data.List.OfFn
/-!
# The extracted event trace is a permutation of the events ordered by clock

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 1–7. -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess SmcSupport
/-- Source: marjoram_wall2006, Methods, steps 1–7. -/
theorem extractionRebuildEvent_time_strict (N : ℕ) (h : ARGPrefix (N + 1))
    (hs : OneSplitPrefixSupported N h) (i j : Fin (N + 1)) (hij : i < j) :
    rebuildEventTime (extractOneSplitSkeleton N h)
      (extractionRebuildEvent N (extractionRun N h i.val)
        (h ⟨i.val, Finset.mem_Iic.mpr (by have := i.isLt; omega)⟩)
        (h ⟨i.val + 1, Finset.mem_Iic.mpr (by have := i.isLt; omega)⟩)) <
    rebuildEventTime (extractOneSplitSkeleton N h)
      (extractionRebuildEvent N (extractionRun N h j.val)
        (h ⟨j.val, Finset.mem_Iic.mpr (by have := j.isLt; omega)⟩)
        (h ⟨j.val + 1, Finset.mem_Iic.mpr (by have := j.isLt; omega)⟩)) := by
  rw [extractionRebuildEvent_time N h hs i, extractionRebuildEvent_time N h hs j]
  exact (hs.clock_mono (i.val + 1) j.val (by exact hij) j.isLt.le).trans_lt
    (hs.clock_lt j)
/-- Source: marjoram_wall2006, Methods, steps 1–7. -/
theorem extractionRebuildEvent_injective (N : ℕ) (h : ARGPrefix (N + 1))
    (hs : OneSplitPrefixSupported N h) :
    Function.Injective (fun k : Fin (N + 1) =>
      extractionRebuildEvent N (extractionRun N h k.val)
        (h ⟨k.val, Finset.mem_Iic.mpr (by have := k.isLt; omega)⟩)
        (h ⟨k.val + 1, Finset.mem_Iic.mpr (by have := k.isLt; omega)⟩)) := by
  intro i j he
  dsimp only at he
  rcases lt_trichotomy i j with hij | hij | hij
  · have ht := extractionRebuildEvent_time_strict N h hs i j hij
    rw [he] at ht
    exact False.elim (lt_irrefl _ ht)
  · exact hij
  · have ht := extractionRebuildEvent_time_strict N h hs j i hij
    rw [he] at ht
    exact False.elim (lt_irrefl _ ht)
/-- Source: marjoram_wall2006, Methods, steps 1–7. -/
theorem extractionRebuildEvent_bijective (N : ℕ) (h : ARGPrefix (N + 1))
    (hs : OneSplitPrefixSupported N h) :
    Function.Bijective (fun k : Fin (N + 1) =>
      extractionRebuildEvent N (extractionRun N h k.val)
        (h ⟨k.val, Finset.mem_Iic.mpr (by have := k.isLt; omega)⟩)
        (h ⟨k.val + 1, Finset.mem_Iic.mpr (by have := k.isLt; omega)⟩)) := by
  classical
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨extractionRebuildEvent_injective N h hs, ?_⟩
  simp only [RebuildEvent, Fintype.card_fin, Fintype.card_sum, Fintype.card_bool]
  have := hs.sample_pos
  omega
/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 1–7. -/
theorem extractionRebuildTrace_perm (N : ℕ) (h : ARGPrefix (N + 1))
    (hs : OneSplitPrefixSupported N h) :
    (extractionRebuildTrace N h).Perm
      ((List.finRange (N - 1)).map Sum.inl ++
        ([.inr false, .inr true] : List (RebuildEvent N))) := by
  classical
  have hnodup : (extractionRebuildTrace N h).Nodup :=
    (List.nodup_finRange _).map (extractionRebuildEvent_injective N h hs)
  have hbase : (((List.finRange (N - 1)).map Sum.inl) ++
      ([.inr false, .inr true] : List (RebuildEvent N))).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨(List.nodup_finRange _).map Sum.inl_injective, by simp, ?_⟩
    intro a ha b hb hab
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    all_goals cases hab
  apply (List.perm_ext_iff_of_nodup hnodup hbase).mpr
  intro e
  constructor
  · intro _
    cases e with
    | inl k => simp
    | inr b => cases b <;> simp
  · intro _
    obtain ⟨k, hk⟩ := (extractionRebuildEvent_bijective N h hs).surjective e
    exact List.mem_map.mpr ⟨k, by simp, hk⟩
end Rhone.Coalescent.SmcPrime
