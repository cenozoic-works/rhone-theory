/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib

/-! # Slot-wise linear functions of a family of test vectors -/

@[expose] public section

namespace Rhone.LinearAlgebra.Multilinear

open Finset

variable {F : Type*} [CommRing F] {ι κ : Type*} {K L : ℕ}

structure IsMulti (G : (ι → Fin K → F) → F) : Prop where
  add : ∀ [DecidableEq ι] (s : ι → Fin K → F) (u : ι) (x y : Fin K → F),
    G (Function.update s u (x + y)) = G (Function.update s u x) + G (Function.update s u y)
  smul : ∀ [DecidableEq ι] (s : ι → Fin K → F) (u : ι) (c : F) (x : Fin K → F),
    G (Function.update s u (c • x)) = c * G (Function.update s u x)

noncomputable def IsMulti.toML {G : (ι → Fin K → F) → F} (hG : IsMulti G) :
    MultilinearMap F (fun _ : ι => (Fin K → F)) F where
  toFun := G
  map_update_add' := fun s u x y => hG.add s u x y
  map_update_smul' := fun s u c x => by simpa [smul_eq_mul] using hG.smul s u c x

theorem update_inst_eq {β : ι → Sort*} (i1 i2 : DecidableEq ι) (f : ∀ a, β a) (a : ι)
    (v : β a) : @Function.update ι β i1 f a v = @Function.update ι β i2 f a v := by
  have h : i1 = i2 := Subsingleton.elim _ _
  rw [h]

theorem isMulti_of [dec : DecidableEq ι] {G : (ι → Fin K → F) → F}
    (hadd : ∀ (s : ι → Fin K → F) (u : ι) (x y : Fin K → F),
      G (Function.update s u (x + y)) = G (Function.update s u x) + G (Function.update s u y))
    (hsmul : ∀ (s : ι → Fin K → F) (u : ι) (c : F) (x : Fin K → F),
      G (Function.update s u (c • x)) = c * G (Function.update s u x)) :
    IsMulti G where
  add := by
    intro inst s u x y
    simp only [update_inst_eq inst dec]
    exact hadd s u x y
  smul := by
    intro inst s u c x
    simp only [update_inst_eq inst dec]
    exact hsmul s u c x

theorem IsMulti.eq_zero_of_slot [DecidableEq ι] {G : (ι → Fin K → F) → F} (hG : IsMulti G)
    (s : ι → Fin K → F) (u : ι) : G (Function.update s u 0) = 0 := by
  simpa using hG.smul s u 0 0

theorem IsMulti.sum {J : Type*} (t : Finset J) (G : J → (ι → Fin K → F) → F)
    (h : ∀ j ∈ t, IsMulti (G j)) : IsMulti (fun s => ∑ j ∈ t, G j s) where
  add := fun s u x y => by
    rw [Finset.sum_congr rfl fun j hj => (h j hj).add s u x y, Finset.sum_add_distrib]
  smul := fun s u c x => by
    rw [Finset.sum_congr rfl fun j hj => (h j hj).smul s u c x, ← Finset.mul_sum]

theorem IsMulti.const_mul (c : F) {G : (ι → Fin K → F) → F} (h : IsMulti G) :
    IsMulti (fun s => c * G s) where
  add := fun s u x y => by rw [h.add]; ring
  smul := fun s u a x => by rw [h.smul]; ring

theorem IsMulti.add' {G H : (ι → Fin K → F) → F} (hG : IsMulti G) (hH : IsMulti H) :
    IsMulti (fun s => G s + H s) where
  add := fun s u x y => by rw [hG.add, hH.add]; ring
  smul := fun s u c x => by rw [hG.smul, hH.smul]; ring

section Expand

variable [Fintype ι] [DecidableEq ι]

theorem sum_smul_single (x : Fin K → F) :
    (∑ i, (x i) • (Pi.single i (1 : F) : Fin K → F)) = x :=
  (pi_eq_sum_univ' x).symm

theorem IsMulti.expand {G : (ι → Fin K → F) → F} (hG : IsMulti G) (s : ι → Fin K → F) :
    G s = ∑ α : ι → Fin K, (∏ u, s u (α u)) * G (fun u => Pi.single (α u) 1) := by
  have h0 : hG.toML s = G s := rfl
  calc G s = hG.toML (fun u => ∑ i, (s u i) • (Pi.single i (1 : F) : Fin K → F)) := by
        rw [← h0]; congr 1; funext u; rw [sum_smul_single]
    _ = ∑ α : ι → Fin K,
          hG.toML (fun u => (s u (α u)) • (Pi.single (α u) (1 : F) : Fin K → F)) :=
        hG.toML.map_sum _
    _ = ∑ α : ι → Fin K, (∏ u, s u (α u)) * G (fun u => Pi.single (α u) 1) := by
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [hG.toML.map_smul_univ]
      rfl

variable [Fintype κ] [DecidableEq κ]

theorem expand₂ {G : (ι → Fin K → F) → (κ → Fin L → F) → F}
    (hA : ∀ w, IsMulti (fun s => G s w)) (hB : ∀ s, IsMulti (fun w => G s w))
    (s : ι → Fin K → F) (w : κ → Fin L → F) :
    G s w = ∑ α : ι → Fin K, ∑ β : κ → Fin L,
      (∏ u, s u (α u)) * (∏ v, w v (β v))
        * G (fun u => Pi.single (α u) 1) (fun v => Pi.single (β v) 1) := by
  rw [(hA w).expand s]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [(hB fun u => Pi.single (α u) 1).expand w, Finset.mul_sum]
  exact Finset.sum_congr rfl fun β _ => by ring

end Expand

section Agree

variable [Finite ι] [Finite κ]

theorem eq_of_basis {G H : (ι → Fin K → F) → (κ → Fin L → F) → F}
    (hGA : ∀ w, IsMulti (fun s => G s w)) (hGB : ∀ s, IsMulti (fun w => G s w))
    (hHA : ∀ w, IsMulti (fun s => H s w)) (hHB : ∀ s, IsMulti (fun w => H s w))
    (hbas : ∀ (α : ι → Fin K) (β : κ → Fin L),
      G (fun u => Pi.single (α u) 1) (fun v => Pi.single (β v) 1)
        = H (fun u => Pi.single (α u) 1) (fun v => Pi.single (β v) 1))
    (s : ι → Fin K → F) (w : κ → Fin L → F) : G s w = H s w := by
  classical
  cases nonempty_fintype ι
  cases nonempty_fintype κ
  rw [expand₂ hGA hGB s w, expand₂ hHA hHB s w]
  exact Finset.sum_congr rfl fun α _ =>
    Finset.sum_congr rfl fun β _ => by rw [hbas]

end Agree

section Basis

variable [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem prod_single_apply (α α' : ι → Fin K) :
    (∏ u, (Pi.single (α u) (1 : F) : Fin K → F) (α' u)) = if α' = α then 1 else 0 := by
  by_cases h : α' = α
  · subst h; simp
  · rw [ite_eq_right h]
    obtain ⟨u, hu⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ u) (Pi.single_eq_of_ne hu 1)

theorem single_mul_single (i i' : Fin K) :
    (Pi.single i (1 : F) : Fin K → F) * Pi.single i' 1
      = if i = i' then (Pi.single i 1 : Fin K → F) else 0 := by
  funext j
  by_cases h : i = i'
  · subst h; by_cases hj : j = i <;> simp [hj]
  · rw [ite_eq_right h]
    by_cases hj : j = i
    · subst hj; simp [Ne.symm h]
    · simp [hj]

end Basis

end Rhone.LinearAlgebra.Multilinear
