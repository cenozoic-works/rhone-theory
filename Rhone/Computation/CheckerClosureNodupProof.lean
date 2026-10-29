/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Computation.Closure
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.List.Range

/-! # Duplicate-free complete closure -/

@[expose] public section

namespace Rhone.Computation

private theorem tagged_flatMap_nodup {α : Type*} {l : List Nat} {f : Nat → List α}
    (tag : α → Nat) (hl : l.Nodup) (hn : ∀ i, (f i).Nodup)
    (ht : ∀ i, ∀ s ∈ f i, tag s = i) : (l.flatMap f).Nodup := by
  refine List.nodup_flatMap.mpr ⟨fun i _ => hn i, ?_⟩
  exact hl.imp fun {i j} hij s hi hj => hij ((ht i s hi).symm.trans (ht j s hj))

private theorem tagged_map_nodup {α : Type*} {l : List Nat} {f : Nat → α}
    (tag : α → Nat) (hl : l.Nodup) (ht : ∀ i, tag (f i) = i) : (l.map f).Nodup :=
  hl.map (Function.LeftInverse.injective ht)

theorem closureList_nodup (n : Nat) : (closureList n).Nodup := by
  unfold closureList
  refine tagged_flatMap_nodup (fun s : Config => s.c.getD 0 0) List.nodup_range ?_ ?_
  · intro c00
    refine tagged_flatMap_nodup (fun s : Config => s.c.getD 1 0) List.nodup_range ?_ ?_
    · intro c01
      refine tagged_flatMap_nodup (fun s : Config => s.c.getD 2 0) List.nodup_range ?_ ?_
      · intro c10
        refine tagged_flatMap_nodup (fun s : Config => s.c.getD 3 0) List.nodup_range ?_ ?_
        · intro c11
          refine tagged_flatMap_nodup (fun s : Config => s.a.getD 0 0) List.nodup_range ?_ ?_
          · intro a0
            refine tagged_flatMap_nodup (fun s : Config => s.a.getD 1 0) List.nodup_range ?_ ?_
            · intro a1
              refine tagged_flatMap_nodup (fun s : Config => s.b.getD 0 0)
                List.nodup_range ?_ ?_
              · intro b0
                exact tagged_map_nodup (fun s : Config => s.b.getD 1 0)
                  List.nodup_range (fun _ => rfl)
              · intro b0 s hs
                simp only [List.mem_map] at hs
                rcases hs with ⟨b1, _, rfl⟩
                rfl
            · intro a1 s hs
              simp only [List.mem_flatMap, List.mem_map] at hs
              rcases hs with ⟨b0, _, b1, _, rfl⟩
              rfl
          · intro a0 s hs
            simp only [List.mem_flatMap, List.mem_map] at hs
            rcases hs with ⟨a1, _, b0, _, b1, _, rfl⟩
            rfl
        · intro c11 s hs
          simp only [List.mem_flatMap, List.mem_map] at hs
          rcases hs with ⟨a0, _, a1, _, b0, _, b1, _, rfl⟩
          rfl
      · intro c10 s hs
        simp only [List.mem_flatMap, List.mem_map] at hs
        rcases hs with ⟨c11, _, a0, _, a1, _, b0, _, b1, _, rfl⟩
        rfl
    · intro c01 s hs
      simp only [List.mem_flatMap, List.mem_map] at hs
      rcases hs with ⟨c10, _, c11, _, a0, _, a1, _, b0, _, b1, _, rfl⟩
      rfl
  · intro c00 s hs
    simp only [List.mem_flatMap, List.mem_map] at hs
    rcases hs with ⟨c01, _, c10, _, c11, _, a0, _, a1, _, b0, _, b1, _, rfl⟩
    rfl

end Rhone.Computation
