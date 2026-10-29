/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib

/-! # Aggregation over restriction fibres of set partitions, and singleton reductions -/

@[expose] public section

namespace Rhone.Algebra.Isotypic

open Finset

variable {α : Type*} [DecidableEq α] [Fintype α]

def IsPart (b : α → Finset α) : Prop :=
  (∀ a c, c ∈ b a → b c = b a) ∧ (∀ a, (b a).Nonempty → a ∈ b a)

instance : DecidablePred (IsPart (α := α)) := fun b => by
  unfold IsPart
  infer_instance

def SetPart (α : Type*) [DecidableEq α] [Fintype α] : Type _ := {b : α → Finset α // IsPart b}

namespace SetPart

instance : DecidableEq (SetPart α) :=
  inferInstanceAs (DecidableEq {b : α → Finset α // IsPart b})

instance : Fintype (SetPart α) :=
  inferInstanceAs (Fintype {b : α → Finset α // IsPart b})

def block (ξ : SetPart α) : α → Finset α := ξ.val

@[ext] theorem ext {ξ η : SetPart α} (h : ∀ a, ξ.block a = η.block a) : ξ = η :=
  Subtype.ext (funext h)

theorem block_congr (ξ : SetPart α) {a c : α} (h : c ∈ ξ.block a) : ξ.block c = ξ.block a :=
  ξ.2.1 a c h

theorem self_mem_block (ξ : SetPart α) {a : α} (h : (ξ.block a).Nonempty) : a ∈ ξ.block a :=
  ξ.2.2 a h

def carrier (ξ : SetPart α) : Finset α := Finset.univ.filter fun a => a ∈ ξ.block a

theorem mem_carrier {ξ : SetPart α} {a : α} : a ∈ carrier ξ ↔ a ∈ ξ.block a := by
  simp [carrier]

theorem mem_carrier_of_mem_block {ξ : SetPart α} {a c : α} (h : c ∈ ξ.block a) :
    c ∈ carrier ξ := by
  rw [mem_carrier, ξ.block_congr h]
  exact h

theorem block_subset_carrier (ξ : SetPart α) (a : α) : ξ.block a ⊆ carrier ξ :=
  fun _ hc => mem_carrier_of_mem_block hc

theorem block_eq_empty {ξ : SetPart α} {a : α} (h : a ∉ carrier ξ) : ξ.block a = ∅ := by
  by_contra hne
  exact h (mem_carrier.mpr (ξ.self_mem_block (Finset.nonempty_of_ne_empty hne)))

theorem block_eq_of_mem_both {ξ : SetPart α} {a b c : α} (ha : c ∈ ξ.block a)
    (hb : c ∈ ξ.block b) : ξ.block a = ξ.block b := by
  rw [← ξ.block_congr ha, ← ξ.block_congr hb]

def oneBlock (S : Finset α) : SetPart α :=
  ⟨fun a => if a ∈ S then S else ∅, by
    refine ⟨?_, ?_⟩
    · intro a c hc
      dsimp only at hc ⊢
      by_cases ha : a ∈ S
      · rw [ite_eq_left ha] at hc
        rw [ite_eq_left hc, ite_eq_left ha]
      · rw [ite_eq_right ha] at hc
        exact absurd hc (Finset.notMem_empty c)
    · intro a ha
      dsimp only at ha ⊢
      by_cases h : a ∈ S
      · rw [ite_eq_left h]
        exact h
      · rw [ite_eq_right h] at ha
        exact absurd ha (by simp)⟩

theorem oneBlock_block (S : Finset α) (a : α) :
    (oneBlock S).block a = if a ∈ S then S else ∅ := rfl

@[simp] theorem carrier_oneBlock (S : Finset α) : carrier (oneBlock S) = S := by
  ext a
  rw [mem_carrier, oneBlock_block]
  by_cases h : a ∈ S <;> simp [h]

def restrictTo (ξ : SetPart α) (T : Finset α) : SetPart α :=
  ⟨fun a => if a ∈ T then ξ.block a ∩ T else ∅, by
    refine ⟨?_, ?_⟩
    · intro a c hc
      dsimp only at hc ⊢
      by_cases ha : a ∈ T
      · rw [ite_eq_left ha] at hc
        rw [Finset.mem_inter] at hc
        rw [ite_eq_left hc.2, ite_eq_left ha, ξ.block_congr hc.1]
      · rw [ite_eq_right ha] at hc
        exact absurd hc (Finset.notMem_empty c)
    · intro a ha
      dsimp only at ha ⊢
      by_cases h : a ∈ T
      · rw [ite_eq_left h] at ha ⊢
        obtain ⟨c, hc⟩ := ha
        rw [Finset.mem_inter] at hc ⊢
        exact ⟨ξ.self_mem_block ⟨c, hc.1⟩, h⟩
      · rw [ite_eq_right h] at ha
        exact absurd ha (by simp)⟩

theorem restrictTo_block (ξ : SetPart α) (T : Finset α) (a : α) :
    (restrictTo ξ T).block a = if a ∈ T then ξ.block a ∩ T else ∅ := rfl

@[simp] theorem carrier_restrictTo (ξ : SetPart α) (T : Finset α) :
    carrier (restrictTo ξ T) = T ∩ carrier ξ := by
  ext a
  rw [mem_carrier, restrictTo_block, Finset.mem_inter, mem_carrier]
  by_cases h : a ∈ T <;> simp [h]

theorem carrier_restrictTo_of_subset {ξ : SetPart α} {T : Finset α} (h : T ⊆ carrier ξ) :
    carrier (restrictTo ξ T) = T := by
  rw [carrier_restrictTo, Finset.inter_eq_left.mpr h]

theorem restrictTo_restrictTo (ξ : SetPart α) {T T' : Finset α} (h : T' ⊆ T) :
    restrictTo (restrictTo ξ T) T' = restrictTo ξ T' := by
  refine SetPart.ext fun a => ?_
  rw [restrictTo_block, restrictTo_block, restrictTo_block]
  by_cases ha : a ∈ T'
  · rw [ite_eq_left ha, ite_eq_left ha, ite_eq_left (h ha), Finset.inter_assoc,
      Finset.inter_eq_right.mpr h]
  · rw [ite_eq_right ha, ite_eq_right ha]

@[simp] theorem restrictTo_carrier (ξ : SetPart α) : restrictTo ξ (carrier ξ) = ξ := by
  refine SetPart.ext fun a => ?_
  rw [restrictTo_block]
  by_cases ha : a ∈ carrier ξ
  · rw [ite_eq_left ha, Finset.inter_eq_left.mpr (block_subset_carrier ξ a)]
  · rw [ite_eq_right ha, block_eq_empty ha]

theorem restrictTo_oneBlock {T T' : Finset α} (h : T' ⊆ T) :
    restrictTo (oneBlock T) T' = oneBlock T' := by
  refine SetPart.ext fun a => ?_
  rw [restrictTo_block, oneBlock_block, oneBlock_block]
  by_cases ha : a ∈ T'
  · rw [ite_eq_left ha, ite_eq_left (h ha), ite_eq_left ha, Finset.inter_eq_right.mpr h]
  · rw [ite_eq_right ha, ite_eq_right ha]

theorem isPart_addSingleton {η : SetPart α} {k : α} (hk : k ∉ carrier η) :
    IsPart (fun a => if a = k then ({k} : Finset α) else η.block a) := by
  refine ⟨?_, ?_⟩
  · intro a c hc
    dsimp only at hc ⊢
    by_cases ha : a = k
    · rw [ite_eq_left ha] at hc
      rw [Finset.mem_singleton] at hc
      rw [ite_eq_left hc, ite_eq_left ha]
    · rw [ite_eq_right ha] at hc
      have hcT : c ∈ carrier η := mem_carrier_of_mem_block hc
      have hck : c ≠ k := fun h => hk (h ▸ hcT)
      rw [ite_eq_right hck, ite_eq_right ha, η.block_congr hc]
  · intro a ha
    dsimp only at ha ⊢
    by_cases h : a = k
    · rw [ite_eq_left h]
      simp [h]
    · rw [ite_eq_right h] at ha ⊢
      exact η.self_mem_block ha

def addSingleton (η : SetPart α) (k : α) : SetPart α :=
  if hk : k ∈ carrier η then η else ⟨_, isPart_addSingleton hk⟩

theorem addSingleton_block {η : SetPart α} {k : α} (hk : k ∉ carrier η) (a : α) :
    (addSingleton η k).block a = if a = k then {k} else η.block a := by
  have h : addSingleton η k = ⟨_, isPart_addSingleton hk⟩ := dite_eq_right hk
  rw [h]
  rfl

@[simp] theorem carrier_addSingleton {η : SetPart α} {k : α} (hk : k ∉ carrier η) :
    carrier (addSingleton η k) = insert k (carrier η) := by
  ext a
  rw [mem_carrier, addSingleton_block hk, Finset.mem_insert, mem_carrier]
  by_cases h : a = k <;> simp [h]

theorem isPart_addTo {η : SetPart α} {k : α} (hk : k ∉ carrier η) (c : α) :
    IsPart (fun a => if a = k ∨ (a ∈ carrier η ∧ η.block a = η.block c) then
      insert k (η.block c) else η.block a) := by
  refine ⟨?_, ?_⟩
  · intro a b hb
    dsimp only at hb ⊢
    by_cases ha : a = k ∨ (a ∈ carrier η ∧ η.block a = η.block c)
    · rw [ite_eq_left ha] at hb
      rw [Finset.mem_insert] at hb
      rcases hb with hb | hb
      · rw [ite_eq_left (Or.inl hb), ite_eq_left ha]
      · have hbc : η.block b = η.block c := η.block_congr hb
        have hbcar : b ∈ carrier η := mem_carrier_of_mem_block hb
        rw [ite_eq_left (Or.inr ⟨hbcar, hbc⟩), ite_eq_left ha]
    · rw [ite_eq_right ha] at hb
      have hbcar : b ∈ carrier η := mem_carrier_of_mem_block hb
      have hbk : b ≠ k := fun h => hk (h ▸ hbcar)
      have hacar : a ∈ carrier η := mem_carrier.mpr (η.self_mem_block ⟨b, hb⟩)
      have hab : η.block b = η.block a := η.block_congr hb
      have hbne : ¬(b = k ∨ (b ∈ carrier η ∧ η.block b = η.block c)) := by
        rintro (h | ⟨-, h⟩)
        · exact hbk h
        · exact ha (Or.inr ⟨hacar, hab ▸ h⟩)
      rw [ite_eq_right hbne, ite_eq_right ha, hab]
  · intro a ha
    dsimp only at ha ⊢
    by_cases h : a = k ∨ (a ∈ carrier η ∧ η.block a = η.block c)
    · rw [ite_eq_left h]
      rcases h with h | ⟨hcar, hb⟩
      · simp [h]
      · exact Finset.mem_insert_of_mem (hb ▸ mem_carrier.mp hcar)
    · rw [ite_eq_right h] at ha ⊢
      exact η.self_mem_block ha

def addTo (η : SetPart α) (k c : α) : SetPart α :=
  if hk : k ∈ carrier η then η else ⟨_, isPart_addTo hk c⟩

theorem addTo_block {η : SetPart α} {k : α} (hk : k ∉ carrier η) (c a : α) :
    (addTo η k c).block a =
      if a = k ∨ (a ∈ carrier η ∧ η.block a = η.block c) then insert k (η.block c)
      else η.block a := by
  have h : addTo η k c = ⟨_, isPart_addTo hk c⟩ := dite_eq_right hk
  rw [h]
  rfl

@[simp] theorem carrier_addTo {η : SetPart α} {k : α} (hk : k ∉ carrier η) (c : α) :
    carrier (addTo η k c) = insert k (carrier η) := by
  ext a
  rw [mem_carrier, addTo_block hk]
  by_cases h : a = k ∨ (a ∈ carrier η ∧ η.block a = η.block c)
  · rw [ite_eq_left h, Finset.mem_insert, Finset.mem_insert]
    rcases h with h | ⟨hcar, hb⟩
    · subst h
      simp
    · exact ⟨fun _ => Or.inr hcar, fun _ => Or.inr (hb ▸ mem_carrier.mp hcar)⟩
  · rw [ite_eq_right h, Finset.mem_insert, ← mem_carrier]
    constructor
    · exact fun hm => Or.inr hm
    · rintro (rfl | hm)
      · exact absurd (Or.inl rfl) h
      · exact hm

theorem restrictTo_addSingleton {η : SetPart α} {k : α} (hk : k ∉ carrier η) :
    restrictTo (addSingleton η k) (carrier η) = η := by
  refine SetPart.ext fun a => ?_
  rw [restrictTo_block, addSingleton_block hk]
  by_cases ha : a ∈ carrier η
  · have hak : a ≠ k := fun h => hk (h ▸ ha)
    rw [ite_eq_left ha, ite_eq_right hak, Finset.inter_eq_left.mpr (block_subset_carrier η a)]
  · rw [ite_eq_right ha, block_eq_empty ha]

theorem restrictTo_addTo {η : SetPart α} {k : α} (hk : k ∉ carrier η) (c : α) :
    restrictTo (addTo η k c) (carrier η) = η := by
  refine SetPart.ext fun a => ?_
  rw [restrictTo_block, addTo_block hk]
  by_cases ha : a ∈ carrier η
  · have hak : a ≠ k := fun h => hk (h ▸ ha)
    rw [ite_eq_left ha]
    by_cases hb : η.block a = η.block c
    · rw [ite_eq_left (Or.inr ⟨ha, hb⟩), ← hb]
      refine Finset.Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)
      · rw [Finset.mem_inter, Finset.mem_insert] at hx
        rcases hx.1 with rfl | hx'
        · exact absurd hx.2 hk
        · exact hx'
      · rw [Finset.mem_inter, Finset.mem_insert]
        exact ⟨Or.inr hx, block_subset_carrier η a hx⟩
    · have hcond : ¬(a = k ∨ (a ∈ carrier η ∧ η.block a = η.block c)) := by
        rintro (h | ⟨-, h⟩)
        · exact hak h
        · exact hb h
      rw [ite_eq_right hcond, Finset.inter_eq_left.mpr (block_subset_carrier η a)]
  · rw [ite_eq_right ha, block_eq_empty ha]

theorem addSingleton_ne_addTo {η : SetPart α} {k : α} (hk : k ∉ carrier η) {c : α}
    (hc : c ∈ carrier η) : addSingleton η k ≠ addTo η k c := by
  intro h
  have hb : (addSingleton η k).block k = (addTo η k c).block k := by rw [h]
  rw [addSingleton_block hk, addTo_block hk, ite_eq_left rfl, ite_eq_left (Or.inl rfl)] at hb
  have hcm : c ∈ ({k} : Finset α) := by
    rw [hb]
    exact Finset.mem_insert_of_mem (mem_carrier.mp hc)
  rw [Finset.mem_singleton] at hcm
  exact hk (hcm ▸ hc)

def fibOf (U S : Finset α) (η : SetPart α) : Finset (SetPart α) :=
  Finset.univ.filter fun ξ => carrier ξ = U ∧ restrictTo ξ S = η

theorem mem_fibOf {U S : Finset α} {η ξ : SetPart α} :
    ξ ∈ fibOf U S η ↔ carrier ξ = U ∧ restrictTo ξ S = η := by
  simp [fibOf]

theorem fibre_eq (η : SetPart α) {k : α} (hk : k ∉ carrier η) :
    fibOf (insert k (carrier η)) (carrier η) η
      = insert (addSingleton η k) ((carrier η).image fun c => addTo η k c) := by
  ext ζ
  rw [mem_fibOf, Finset.mem_insert, Finset.mem_image]
  constructor
  · rintro ⟨hcar, hres⟩
    have hkζ : k ∈ carrier ζ := by rw [hcar]; exact Finset.mem_insert_self _ _
    have hblock : ∀ a ∈ carrier η, η.block a = ζ.block a ∩ carrier η := by
      intro a ha
      have hb : (restrictTo ζ (carrier η)).block a = η.block a := by rw [hres]
      rw [restrictTo_block, ite_eq_left ha] at hb
      exact hb.symm
    have hsub : ∀ a, ζ.block a ⊆ insert k (carrier η) := by
      intro a
      rw [← hcar]
      exact block_subset_carrier ζ a
    have hmemζ : ∀ a ∈ carrier η, a ∈ ζ.block a := by
      intro a ha
      rw [← mem_carrier, hcar]
      exact Finset.mem_insert_of_mem ha
    have hout : ∀ a, a ≠ k → a ∉ carrier η → ζ.block a = ∅ := by
      intro a hak ha
      refine block_eq_empty ?_
      rw [hcar, Finset.mem_insert]
      rintro (rfl | h)
      · exact hak rfl
      · exact ha h
    by_cases hk1 : ζ.block k = {k}
    · left
      refine SetPart.ext fun a => ?_
      rw [addSingleton_block hk]
      by_cases hak : a = k
      · rw [ite_eq_left hak, hak, hk1]
      · rw [ite_eq_right hak]
        by_cases ha : a ∈ carrier η
        · have haζ : a ∈ ζ.block a := hmemζ a ha
          have hknot : k ∉ ζ.block a := by
            intro hkm
            have h1 : ζ.block k = ζ.block a := ζ.block_congr hkm
            rw [hk1] at h1
            rw [← h1] at haζ
            exact hak (Finset.mem_singleton.mp haζ)
          have hz : ζ.block a ⊆ carrier η := by
            intro x hx
            rcases Finset.mem_insert.mp (hsub a hx) with rfl | hx'
            · exact absurd hx hknot
            · exact hx'
          rw [hblock a ha, Finset.inter_eq_left.mpr hz]
        · rw [hout a hak ha, block_eq_empty ha]
    · right
      have hkk : k ∈ ζ.block k := mem_carrier.mp hkζ
      obtain ⟨c, hc, hck⟩ : ∃ c ∈ ζ.block k, c ≠ k := by
        by_contra hcon
        refine hk1 (Finset.Subset.antisymm (fun x hx => ?_) (by simpa using hkk))
        rw [Finset.mem_singleton]
        by_contra hxk
        exact hcon ⟨x, hx, hxk⟩
      have hcT : c ∈ carrier η := by
        rcases Finset.mem_insert.mp (hsub k hc) with rfl | h
        · exact absurd rfl hck
        · exact h
      refine ⟨c, hcT, ?_⟩
      have hzc : ζ.block c = ζ.block k := ζ.block_congr hc
      have hBc : η.block c = ζ.block k ∩ carrier η := by rw [hblock c hcT, hzc]
      have hkblock : ζ.block k = insert k (η.block c) := by
        rw [hBc]
        refine Finset.Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)
        · rw [Finset.mem_insert, Finset.mem_inter]
          rcases Finset.mem_insert.mp (hsub k hx) with rfl | hx'
          · exact Or.inl rfl
          · exact Or.inr ⟨hx, hx'⟩
        · rw [Finset.mem_insert, Finset.mem_inter] at hx
          rcases hx with rfl | ⟨hx, -⟩
          · exact hkk
          · exact hx
      refine SetPart.ext fun a => ?_
      rw [addTo_block hk]
      by_cases hak : a = k
      · rw [ite_eq_left (Or.inl hak), hak, hkblock]
      · by_cases ha : a ∈ carrier η
        · by_cases hb : η.block a = η.block c
          · rw [ite_eq_left (Or.inr ⟨ha, hb⟩), ← hkblock]
            have haa : a ∈ η.block c := by rw [← hb]; exact mem_carrier.mp ha
            have hmem : a ∈ ζ.block k := by
              rw [hkblock]
              exact Finset.mem_insert_of_mem haa
            exact (ζ.block_congr hmem).symm ▸ rfl
          · have hcond : ¬(a = k ∨ (a ∈ carrier η ∧ η.block a = η.block c)) := by
              rintro (h | ⟨-, h⟩)
              · exact hak h
              · exact hb h
            rw [ite_eq_right hcond]
            have hknot : k ∉ ζ.block a := by
              intro hkm
              exact hb (by rw [hblock a ha, ← ζ.block_congr hkm, hBc])
            have hz : ζ.block a ⊆ carrier η := by
              intro x hx
              rcases Finset.mem_insert.mp (hsub a hx) with rfl | hx'
              · exact absurd hx hknot
              · exact hx'
            rw [hblock a ha, Finset.inter_eq_left.mpr hz]
        · have hcond : ¬(a = k ∨ (a ∈ carrier η ∧ η.block a = η.block c)) := by
            rintro (h | ⟨h, -⟩)
            · exact hak h
            · exact ha h
          rw [ite_eq_right hcond, hout a hak ha, block_eq_empty ha]
  · rintro (rfl | ⟨c, -, rfl⟩)
    · exact ⟨carrier_addSingleton hk, restrictTo_addSingleton hk⟩
    · exact ⟨carrier_addTo hk c, restrictTo_addTo hk c⟩

theorem fibre_one_block_pair {T : Finset α} {k : α} (hk : k ∉ T) (hne : T.Nonempty) :
    fibOf (insert k T) T (oneBlock T)
      = {addSingleton (oneBlock T) k, oneBlock (insert k T)} := by
  have hk' : k ∉ carrier (oneBlock T) := by rwa [carrier_oneBlock]
  have key := fibre_eq (oneBlock T) hk'
  rw [carrier_oneBlock] at key
  rw [key]
  congr 1
  obtain ⟨c₀, hc₀⟩ := hne
  have himg : ∀ c ∈ T, addTo (oneBlock T) k c = oneBlock (insert k T) := by
    intro c hc
    have hbc : (oneBlock T).block c = T := by rw [oneBlock_block, ite_eq_left hc]
    refine SetPart.ext fun a => ?_
    rw [addTo_block hk', carrier_oneBlock, hbc, oneBlock_block (insert k T) a]
    by_cases hak : a = k
    · rw [ite_eq_left (Or.inl hak), hak, ite_eq_left (Finset.mem_insert_self k T)]
    · by_cases ha : a ∈ T
      · have hba : (oneBlock T).block a = T := by rw [oneBlock_block, ite_eq_left ha]
        rw [ite_eq_left (Or.inr ⟨ha, hba⟩), ite_eq_left (Finset.mem_insert_of_mem ha)]
      · have hba : (oneBlock T).block a = ∅ := by rw [oneBlock_block, ite_eq_right ha]
        have hcond : ¬(a = k ∨ (a ∈ T ∧ (oneBlock T).block a = T)) := by
          rintro (h | ⟨h, -⟩)
          · exact hak h
          · exact ha h
        rw [ite_eq_right hcond, hba, ite_eq_right (show a ∉ insert k T by simp [hak, ha])]
  ext ζ
  rw [Finset.mem_image, Finset.mem_singleton]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact himg c hc
  · rintro rfl
    exact ⟨c₀, hc₀, himg c₀ hc₀⟩

def singletons (ξ : SetPart α) : Finset α := (carrier ξ).filter fun a => ξ.block a = {a}

theorem mem_singletons {ξ : SetPart α} {a : α} :
    a ∈ singletons ξ ↔ a ∈ carrier ξ ∧ ξ.block a = {a} := by simp [singletons]

def SingletonFree (ξ : SetPart α) : Prop := singletons ξ = ∅

theorem singletonFree_iff {ξ : SetPart α} : SingletonFree ξ ↔ (singletons ξ).card = 0 := by
  rw [SingletonFree, Finset.card_eq_zero]

theorem singletons_addSingleton {η : SetPart α} {k : α} (hk : k ∉ carrier η) :
    singletons (addSingleton η k) = insert k (singletons η) := by
  ext a
  rw [mem_singletons, carrier_addSingleton hk, addSingleton_block hk, Finset.mem_insert,
    Finset.mem_insert, mem_singletons]
  by_cases hak : a = k
  · subst hak
    simp
  · rw [ite_eq_right hak]
    simp only [hak, false_or]

theorem card_singletons_addSingleton {η : SetPart α} {k : α} (hk : k ∉ carrier η) :
    (singletons (addSingleton η k)).card = (singletons η).card + 1 := by
  rw [singletons_addSingleton hk, Finset.card_insert_of_notMem]
  intro h
  exact hk (mem_singletons.mp h).1

theorem singletons_addTo_subset {η : SetPart α} {k : α} (hk : k ∉ carrier η) {c : α}
    (hc : c ∈ carrier η) : singletons (addTo η k c) ⊆ singletons η := by
  intro a ha
  rw [mem_singletons, carrier_addTo hk, addTo_block hk] at ha
  obtain ⟨hcar, hb⟩ := ha
  rw [mem_singletons]
  by_cases hak : a = k
  · subst hak
    rw [ite_eq_left (Or.inl rfl)] at hb
    have hcm : c ∈ ({a} : Finset α) := by
      rw [← hb]
      exact Finset.mem_insert_of_mem (mem_carrier.mp hc)
    rw [Finset.mem_singleton] at hcm
    exact absurd (hcm ▸ hc) hk
  · have ha' : a ∈ carrier η := by
      rcases Finset.mem_insert.mp hcar with h | h
      · exact absurd h hak
      · exact h
    by_cases hcond : η.block a = η.block c
    · rw [ite_eq_left (Or.inr ⟨ha', hcond⟩)] at hb
      have hkm : k ∈ ({a} : Finset α) := by
        rw [← hb]
        exact Finset.mem_insert_self _ _
      rw [Finset.mem_singleton] at hkm
      exact absurd hkm.symm hak
    · rw [ite_eq_right (by rintro (h | ⟨-, h⟩); exacts [hak h, hcond h])] at hb
      exact ⟨ha', hb⟩

theorem card_singletons_addTo_le {η : SetPart α} {k : α} (hk : k ∉ carrier η) {c : α}
    (hc : c ∈ carrier η) : (singletons (addTo η k c)).card ≤ (singletons η).card :=
  Finset.card_le_card (singletons_addTo_subset hk hc)

section Agg

variable {M : Type*} [AddCommGroup M]

def agg (P : SetPart α → SetPart α → M) (S T : Finset α) (ηA ηB : SetPart α) : M :=
  ∑ ξA ∈ fibOf Finset.univ S ηA, ∑ ξB ∈ fibOf Finset.univ T ηB, P ξA ξB

theorem sum_fibOf_tower {U S T : Finset α} (hTS : T ⊆ S) (hSU : S ⊆ U) (η : SetPart α)
    (f : SetPart α → M) :
    ∑ ξ ∈ fibOf U T η, f ξ = ∑ ζ ∈ fibOf S T η, ∑ ξ ∈ fibOf U S ζ, f ξ := by
  have hmaps : ∀ ξ ∈ fibOf U T η, restrictTo ξ S ∈ fibOf S T η := by
    intro ξ hξ
    rw [mem_fibOf] at hξ ⊢
    refine ⟨?_, ?_⟩
    · rw [carrier_restrictTo, hξ.1, Finset.inter_eq_left.mpr hSU]
    · rw [restrictTo_restrictTo ξ hTS, hξ.2]
  rw [← Finset.sum_fiberwise_of_maps_to hmaps f]
  refine Finset.sum_congr rfl fun ζ hζ => ?_
  rw [mem_fibOf] at hζ
  congr 1
  ext ξ
  rw [Finset.mem_filter, mem_fibOf, mem_fibOf]
  constructor
  · rintro ⟨⟨hc, -⟩, hr⟩
    exact ⟨hc, hr⟩
  · rintro ⟨hc, hr⟩
    exact ⟨⟨hc, by rw [← restrictTo_restrictTo ξ hTS, hr, hζ.2]⟩, hr⟩

theorem agg_tower_B (P : SetPart α → SetPart α → M) (S : Finset α) {T T' : Finset α}
    (hT : T' ⊆ T) (ηA η : SetPart α) :
    agg P S T' ηA η = ∑ ζ ∈ fibOf T T' η, agg P S T ηA ζ := by
  unfold agg
  rw [Finset.sum_comm, sum_fibOf_tower hT (Finset.subset_univ T) η
    (fun ξB => ∑ ξA ∈ fibOf Finset.univ S ηA, P ξA ξB)]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

theorem agg_tower_A (P : SetPart α → SetPart α → M) {S S' : Finset α} (hS : S' ⊆ S)
    (T : Finset α) (η ηB : SetPart α) :
    agg P S' T η ηB = ∑ ζ ∈ fibOf S S' η, agg P S T ζ ηB :=
  sum_fibOf_tower hS (Finset.subset_univ S) η _

theorem singletonReduce_B (P : SetPart α → SetPart α → M) (S : Finset α) (ηA η : SetPart α)
    {k : α} (hk : k ∉ carrier η) :
    agg P S (insert k (carrier η)) ηA (addSingleton η k)
      = agg P S (carrier η) ηA η
        - ∑ ζ ∈ (carrier η).image (fun c => addTo η k c),
            agg P S (insert k (carrier η)) ηA ζ := by
  have htower := agg_tower_B P S (Finset.subset_insert k (carrier η)) ηA η
  rw [fibre_eq η hk, Finset.sum_insert] at htower
  · rw [htower]
    abel
  · rw [Finset.mem_image]
    rintro ⟨c, hc, hEq⟩
    exact addSingleton_ne_addTo hk hc hEq.symm

theorem singletonReduce_A (P : SetPart α → SetPart α → M) (T : Finset α) (η ηB : SetPart α)
    {k : α} (hk : k ∉ carrier η) :
    agg P (insert k (carrier η)) T (addSingleton η k) ηB
      = agg P (carrier η) T η ηB
        - ∑ ζ ∈ (carrier η).image (fun c => addTo η k c),
            agg P (insert k (carrier η)) T ζ ηB := by
  have htower := agg_tower_A P (Finset.subset_insert k (carrier η)) T η ηB
  rw [fibre_eq η hk, Finset.sum_insert] at htower
  · rw [htower]
    abel
  · rw [Finset.mem_image]
    rintro ⟨c, hc, hEq⟩
    exact addSingleton_ne_addTo hk hc hEq.symm

end Agg

end SetPart

end Rhone.Algebra.Isotypic
