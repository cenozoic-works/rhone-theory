/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.Isotypic.Sector
public import Rhone.Algebra.Isotypic.Aggregate

/-! # Singleton induction and the row–row divisibility for the `(n−1,1)` component -/

@[expose] public section

namespace Rhone.Algebra.Isotypic

open Finset SetPart

variable {α : Type*} [DecidableEq α] [Fintype α]

namespace SetPart

theorem isPart_permAct (σ : Equiv.Perm α) (ξ : SetPart α) :
    IsPart (fun a => (ξ.block (σ.symm a)).image σ) := by
  refine ⟨?_, ?_⟩
  · intro a c hc
    dsimp only at hc ⊢
    rw [Finset.mem_image] at hc
    obtain ⟨x, hx, rfl⟩ := hc
    rw [Equiv.symm_apply_apply, ξ.block_congr hx]
  · intro a ha
    dsimp only at ha ⊢
    rw [Finset.image_nonempty] at ha
    rw [Finset.mem_image]
    exact ⟨σ.symm a, ξ.self_mem_block ha, σ.apply_symm_apply a⟩

def permAct (σ : Equiv.Perm α) (ξ : SetPart α) : SetPart α := ⟨_, isPart_permAct σ ξ⟩

theorem permAct_block (σ : Equiv.Perm α) (ξ : SetPart α) (a : α) :
    (permAct σ ξ).block a = (ξ.block (σ.symm a)).image σ := rfl

@[simp] theorem carrier_permAct (σ : Equiv.Perm α) (ξ : SetPart α) :
    carrier (permAct σ ξ) = (carrier ξ).image σ := by
  ext a
  constructor
  · intro ha
    rw [mem_carrier, permAct_block, Finset.mem_image] at ha
    obtain ⟨x, hx, hxa⟩ := ha
    have hxs : x = σ.symm a := by rw [← hxa, Equiv.symm_apply_apply]
    rw [hxs] at hx
    exact Finset.mem_image.mpr ⟨σ.symm a, mem_carrier.mpr hx, σ.apply_symm_apply a⟩
  · intro ha
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    rw [mem_carrier, permAct_block, Equiv.symm_apply_apply]
    exact Finset.mem_image.mpr ⟨x, mem_carrier.mp hx, rfl⟩

theorem permAct_injective (σ : Equiv.Perm α) : Function.Injective (permAct σ (α := α)) := by
  intro ξ η h
  refine SetPart.ext fun a => ?_
  have hb : (permAct σ ξ).block (σ a) = (permAct σ η).block (σ a) := by rw [h]
  rw [permAct_block, permAct_block, Equiv.symm_apply_apply] at hb
  exact Finset.image_injective σ.injective hb

theorem permAct_oneBlock (σ : Equiv.Perm α) (S : Finset α) :
    permAct σ (oneBlock S) = oneBlock (S.image σ) := by
  refine SetPart.ext fun a => ?_
  rw [permAct_block, oneBlock_block, oneBlock_block]
  by_cases h : σ.symm a ∈ S
  · rw [ite_eq_left h, ite_eq_left (Finset.mem_image.mpr ⟨σ.symm a, h, σ.apply_symm_apply a⟩)]
  · rw [ite_eq_right h, ite_eq_right, Finset.image_empty]
    rintro hmem
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hmem
    rw [Equiv.symm_apply_apply] at h
    exact h hx

theorem permAct_addSingleton {η : SetPart α} {k : α} (hk : k ∉ carrier η) (σ : Equiv.Perm α) :
    permAct σ (addSingleton η k) = addSingleton (permAct σ η) (σ k) := by
  have hk' : σ k ∉ carrier (permAct σ η) := by
    rw [carrier_permAct, Finset.mem_image]
    rintro ⟨x, hx, hxk⟩
    exact hk (σ.injective hxk ▸ hx)
  refine SetPart.ext fun a => ?_
  rw [permAct_block, addSingleton_block hk, addSingleton_block hk', permAct_block]
  by_cases h : σ.symm a = k
  · rw [ite_eq_left h, ite_eq_left (by rw [← h, Equiv.apply_symm_apply]), Finset.image_singleton]
  · rw [ite_eq_right h, ite_eq_right]
    intro hak
    exact h (by rw [hak, Equiv.symm_apply_apply])

theorem permAct_addTo {η : SetPart α} {k : α} (hk : k ∉ carrier η) (σ : Equiv.Perm α) (c : α) :
    permAct σ (addTo η k c) = addTo (permAct σ η) (σ k) (σ c) := by
  have hk' : σ k ∉ carrier (permAct σ η) := by
    rw [carrier_permAct, Finset.mem_image]
    rintro ⟨x, hx, hxk⟩
    exact hk (σ.injective hxk ▸ hx)
  refine SetPart.ext fun a => ?_
  rw [permAct_block, addTo_block hk, addTo_block hk', permAct_block, permAct_block,
    Equiv.symm_apply_apply, carrier_permAct]
  have hcond : (a = σ k ∨ (a ∈ (carrier η).image σ ∧
        (η.block (σ.symm a)).image σ = (η.block c).image σ))
      ↔ (σ.symm a = k ∨ (σ.symm a ∈ carrier η ∧ η.block (σ.symm a) = η.block c)) := by
    constructor
    · rintro (h | ⟨h1, h2⟩)
      · exact Or.inl (by rw [h, Equiv.symm_apply_apply])
      · refine Or.inr ⟨?_, Finset.image_injective σ.injective h2⟩
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp h1
        rwa [Equiv.symm_apply_apply]
    · rintro (h | ⟨h1, h2⟩)
      · exact Or.inl (by rw [← h, Equiv.apply_symm_apply])
      · exact Or.inr ⟨Finset.mem_image.mpr ⟨σ.symm a, h1, σ.apply_symm_apply a⟩, by rw [h2]⟩
  by_cases h : σ.symm a = k ∨ (σ.symm a ∈ carrier η ∧ η.block (σ.symm a) = η.block c)
  · rw [ite_eq_left h, ite_eq_left (hcond.mpr h), Finset.image_insert]
  · rw [ite_eq_right h, ite_eq_right (fun hc => h (hcond.mp hc))]

@[simp] theorem singletons_permAct (σ : Equiv.Perm α) (ξ : SetPart α) :
    singletons (permAct σ ξ) = (singletons ξ).image σ := by
  ext a
  rw [mem_singletons, carrier_permAct, permAct_block, Finset.mem_image, Finset.mem_image]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨σ.symm a, mem_singletons.mpr ⟨?_, ?_⟩, σ.apply_symm_apply a⟩
    · obtain ⟨x, hx, rfl⟩ := h1
      rwa [Equiv.symm_apply_apply]
    · refine Finset.image_injective σ.injective ?_
      rw [h2, Finset.image_singleton, Equiv.apply_symm_apply]
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨hx1, hx2⟩ := mem_singletons.mp hx
    refine ⟨⟨x, hx1, rfl⟩, ?_⟩
    rw [Equiv.symm_apply_apply, hx2, Finset.image_singleton]

theorem card_singletons_permAct (σ : Equiv.Perm α) (ξ : SetPart α) :
    (singletons (permAct σ ξ)).card = (singletons ξ).card := by
  rw [singletons_permAct, Finset.card_image_of_injective _ σ.injective]

theorem image_univ_perm (σ : Equiv.Perm α) : (Finset.univ : Finset α).image σ = Finset.univ :=
  Finset.image_univ_equiv σ

def del (ξ : SetPart α) (k : α) : SetPart α := restrictTo ξ ((carrier ξ).erase k)

@[simp] theorem carrier_del (ξ : SetPart α) (k : α) :
    carrier (del ξ k) = (carrier ξ).erase k :=
  carrier_restrictTo_of_subset (Finset.erase_subset _ _)

theorem notMem_carrier_del (ξ : SetPart α) (k : α) : k ∉ carrier (del ξ k) := by
  rw [carrier_del]
  exact Finset.notMem_erase k _

theorem eq_addSingleton_del {ξ : SetPart α} {k : α} (hk : k ∈ singletons ξ) :
    ξ = addSingleton (del ξ k) k := by
  obtain ⟨hkc, hkb⟩ := mem_singletons.mp hk
  refine SetPart.ext fun a => ?_
  rw [addSingleton_block (notMem_carrier_del ξ k), del, restrictTo_block]
  by_cases hak : a = k
  · rw [ite_eq_left hak, hak, hkb]
  · rw [ite_eq_right hak]
    by_cases ha : a ∈ carrier ξ
    · have hae : a ∈ (carrier ξ).erase k := Finset.mem_erase.mpr ⟨hak, ha⟩
      rw [ite_eq_left hae]
      refine (Finset.inter_eq_left.mpr fun x hx => ?_).symm
      refine Finset.mem_erase.mpr ⟨?_, block_subset_carrier ξ a hx⟩
      intro hxk
      apply hak
      have hbx : ξ.block x = {x} := by rw [hxk]; exact hkb
      have hcg : ξ.block a = {x} := (ξ.block_congr hx).symm.trans hbx
      have hax : a ∈ ({x} : Finset α) := by rw [← hcg]; exact mem_carrier.mp ha
      rw [Finset.mem_singleton] at hax
      rw [hax]
      exact hxk
    · rw [ite_eq_right (fun h => ha (Finset.mem_of_mem_erase h)), block_eq_empty ha]

theorem card_carrier_del {ξ : SetPart α} {k : α} (hk : k ∈ carrier ξ) :
    (carrier ξ).card = (carrier (del ξ k)).card + 1 := by
  rw [carrier_del, Finset.card_erase_of_mem hk]
  have hpos : 0 < (carrier ξ).card := Finset.card_pos.mpr ⟨k, hk⟩
  omega

theorem insert_carrier_del {ξ : SetPart α} {k : α} (hk : k ∈ carrier ξ) :
    insert k (carrier (del ξ k)) = carrier ξ := by
  rw [carrier_del, Finset.insert_erase hk]

theorem card_singletons_del {ξ : SetPart α} {k : α} (hk : k ∈ singletons ξ) :
    (singletons ξ).card = (singletons (del ξ k)).card + 1 := by
  conv_lhs => rw [eq_addSingleton_del hk]
  rw [card_singletons_addSingleton (notMem_carrier_del ξ k)]

end SetPart

section Induction

variable {R : Type*} [CommRing R] {V : Type*} [AddCommGroup V] [Module R V]

theorem dvd_of_singleton_induction (P : SetPart α → SetPart α → V) (L : Submodule R V)
    (D : ℕ → ℕ → R) (hDB : ∀ i j, D i j ∣ D i (j + 1)) (hDA : ∀ i j, D i j ∣ D (i + 1) j)
    (hbase : ∀ ηA ηB : SetPart α, SingletonFree ηA → SingletonFree ηB →
      HasDen L (D (carrier ηA).card (carrier ηB).card)
        (agg P (carrier ηA) (carrier ηB) ηA ηB))
    (ηA ηB : SetPart α) :
    HasDen L (D (carrier ηA).card (carrier ηB).card)
      (agg P (carrier ηA) (carrier ηB) ηA ηB) := by
  have key : ∀ m : ℕ, ∀ ηA ηB : SetPart α,
      (singletons ηA).card + (singletons ηB).card ≤ m →
      HasDen L (D (carrier ηA).card (carrier ηB).card)
        (agg P (carrier ηA) (carrier ηB) ηA ηB) := by
    intro m
    induction m with
    | zero =>
        intro ηA ηB hle
        refine hbase ηA ηB ?_ ?_ <;> rw [singletonFree_iff] <;> omega
    | succ m ih =>
        intro ηA ηB hle
        by_cases hB : (singletons ηB).Nonempty
        · obtain ⟨k, hk⟩ := hB
          have hkc : k ∈ carrier ηB := (mem_singletons.mp hk).1
          have hkη : k ∉ carrier (del ηB k) := notMem_carrier_del ηB k
          have hdec : ηB = addSingleton (del ηB k) k := eq_addSingleton_del hk
          have hins : insert k (carrier (del ηB k)) = carrier ηB := insert_carrier_del hkc
          have hcard : (carrier ηB).card = (carrier (del ηB k)).card + 1 := card_carrier_del hkc
          have hsing : (singletons ηB).card = (singletons (del ηB k)).card + 1 :=
            card_singletons_del hk
          have hred := singletonReduce_B P (carrier ηA) ηA (del ηB k) hkη
          rw [hins, ← hdec] at hred
          rw [hred]
          refine HasDen.sub ?_ (HasDen.sum fun ζ hζ => ?_)
          · refine (ih ηA (del ηB k) (by omega)).of_dvd ?_
            rw [hcard]
            exact hDB _ _
          · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hζ
            have hcarζ : carrier (addTo (del ηB k) k c) = carrier ηB := by
              rw [carrier_addTo hkη, hins]
            have hIH := ih ηA (addTo (del ηB k) k c)
              (by
                have := card_singletons_addTo_le hkη hc
                omega)
            rw [hcarζ] at hIH
            exact hIH
        · by_cases hA : (singletons ηA).Nonempty
          · obtain ⟨u, hu⟩ := hA
            have huc : u ∈ carrier ηA := (mem_singletons.mp hu).1
            have huη : u ∉ carrier (del ηA u) := notMem_carrier_del ηA u
            have hdec : ηA = addSingleton (del ηA u) u := eq_addSingleton_del hu
            have hins : insert u (carrier (del ηA u)) = carrier ηA := insert_carrier_del huc
            have hcard : (carrier ηA).card = (carrier (del ηA u)).card + 1 := card_carrier_del huc
            have hsing : (singletons ηA).card = (singletons (del ηA u)).card + 1 :=
              card_singletons_del hu
            have hred := singletonReduce_A P (carrier ηB) (del ηA u) ηB huη
            rw [hins, ← hdec] at hred
            rw [hred]
            refine HasDen.sub ?_ (HasDen.sum fun ζ hζ => ?_)
            · refine (ih (del ηA u) ηB (by omega)).of_dvd ?_
              rw [hcard]
              exact hDA _ _
            · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hζ
              have hcarζ : carrier (addTo (del ηA u) u c) = carrier ηA := by
                rw [carrier_addTo huη, hins]
              have hIH := ih (addTo (del ηA u) u c) ηB
                (by
                  have := card_singletons_addTo_le huη hc
                  omega)
              rw [hcarζ] at hIH
              exact hIH
          · rw [Finset.not_nonempty_iff_eq_empty] at hA hB
            exact hbase ηA ηB hA hB
  exact key _ ηA ηB le_rfl

theorem dvd_contrast_of_singleton_induction (P : SetPart α → SetPart α → V)
    (L : Submodule R V) (D Dp : ℕ → ℕ → R)
    (hDB : ∀ i j, D i j ∣ D i (j + 1)) (hDA : ∀ i j, D i j ∣ D (i + 1) j)
    (hbase : ∀ ηA ηB : SetPart α, SingletonFree ηA → SingletonFree ηB →
      HasDen L (D (carrier ηA).card (carrier ηB).card)
        (agg P (carrier ηA) (carrier ηB) ηA ηB))
    (hDpB : ∀ i j, Dp i j ∣ Dp i (j + 1)) (hDlow : ∀ i j, D i j ∣ Dp (i + 1) j)
    (hbaseContrast : ∀ (σ : Equiv.Perm α) (ηA ηB : SetPart α),
      SingletonFree ηA → SingletonFree ηB → (carrier ηA).image σ = carrier ηA →
      HasDen L (Dp (carrier ηA).card (carrier ηB).card)
        (agg P (carrier ηA) (carrier ηB) ηA ηB
          - agg P (carrier ηA) (carrier ηB) (permAct σ ηA) ηB))
    (σ : Equiv.Perm α) (ηA ηB : SetPart α) (hσ : (carrier ηA).image σ = carrier ηA) :
    HasDen L (Dp (carrier ηA).card (carrier ηB).card)
      (agg P (carrier ηA) (carrier ηB) ηA ηB
        - agg P (carrier ηA) (carrier ηB) (permAct σ ηA) ηB) := by
  have key : ∀ m : ℕ, ∀ ηA ηB : SetPart α,
      (singletons ηA).card + (singletons ηB).card ≤ m →
      (carrier ηA).image σ = carrier ηA →
      HasDen L (Dp (carrier ηA).card (carrier ηB).card)
        (agg P (carrier ηA) (carrier ηB) ηA ηB
          - agg P (carrier ηA) (carrier ηB) (permAct σ ηA) ηB) := by
    intro m
    induction m with
    | zero =>
        intro ηA ηB hle hs
        refine hbaseContrast σ ηA ηB ?_ ?_ hs <;> rw [singletonFree_iff] <;> omega
    | succ m ih =>
        intro ηA ηB hle hs
        by_cases hB : (singletons ηB).Nonempty
        · obtain ⟨k, hk⟩ := hB
          have hkc : k ∈ carrier ηB := (mem_singletons.mp hk).1
          have hkη : k ∉ carrier (del ηB k) := notMem_carrier_del ηB k
          have hdec : ηB = addSingleton (del ηB k) k := eq_addSingleton_del hk
          have hins : insert k (carrier (del ηB k)) = carrier ηB := insert_carrier_del hkc
          have hcard : (carrier ηB).card = (carrier (del ηB k)).card + 1 := card_carrier_del hkc
          have hsing : (singletons ηB).card = (singletons (del ηB k)).card + 1 :=
            card_singletons_del hk
          have hred1 := singletonReduce_B P (carrier ηA) ηA (del ηB k) hkη
          have hred2 := singletonReduce_B P (carrier ηA) (permAct σ ηA) (del ηB k) hkη
          rw [hins, ← hdec] at hred1 hred2
          rw [hred1, hred2, sub_sub_sub_comm, ← Finset.sum_sub_distrib]
          refine HasDen.sub ?_ (HasDen.sum fun ζ hζ => ?_)
          · refine (ih ηA (del ηB k) (by omega) hs).of_dvd ?_
            rw [hcard]
            exact hDpB _ _
          · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hζ
            have hcarζ : carrier (addTo (del ηB k) k c) = carrier ηB := by
              rw [carrier_addTo hkη, hins]
            have hIH := ih ηA (addTo (del ηB k) k c)
              (by
                have := card_singletons_addTo_le hkη hc
                omega) hs
            rw [hcarζ] at hIH
            exact hIH
        · by_cases hA : (singletons ηA).Nonempty
          · obtain ⟨u, hu⟩ := hA
            have huc : u ∈ carrier ηA := (mem_singletons.mp hu).1
            have huη : u ∉ carrier (del ηA u) := notMem_carrier_del ηA u
            have hdec : ηA = addSingleton (del ηA u) u := eq_addSingleton_del hu
            have hins : insert u (carrier (del ηA u)) = carrier ηA := insert_carrier_del huc
            have hcard : (carrier ηA).card = (carrier (del ηA u)).card + 1 := card_carrier_del huc
            have hsing : (singletons ηA).card = (singletons (del ηA u)).card + 1 :=
              card_singletons_del hu
            have hdecσ : permAct σ ηA = addSingleton (permAct σ (del ηA u)) (σ u) := by
              conv_lhs => rw [hdec]
              exact permAct_addSingleton huη σ
            have huησ : σ u ∉ carrier (permAct σ (del ηA u)) := by
              rw [carrier_permAct, Finset.mem_image]
              rintro ⟨x, hx, hxu⟩
              exact huη (σ.injective hxu ▸ hx)
            have hinsσ : insert (σ u) (carrier (permAct σ (del ηA u))) = carrier ηA := by
              rw [carrier_permAct, ← Finset.image_insert, hins, hs]
            have hred1 := singletonReduce_A P (carrier ηB) (del ηA u) ηB huη
            have hred2 := singletonReduce_A P (carrier ηB) (permAct σ (del ηA u)) ηB huησ
            rw [hins, ← hdec] at hred1
            rw [hinsσ, ← hdecσ] at hred2
            rw [hred1, hred2, sub_sub_sub_comm]
            refine HasDen.sub ?_ ?_
            · refine HasDen.sub ?_ ?_
              · refine (dvd_of_singleton_induction P L D hDB hDA hbase
                  (del ηA u) ηB).of_dvd ?_
                rw [hcard]
                exact hDlow _ _
              · refine (dvd_of_singleton_induction P L D hDB hDA hbase
                  (permAct σ (del ηA u)) ηB).of_dvd ?_
                have : (carrier (permAct σ (del ηA u))).card = (carrier (del ηA u)).card := by
                  rw [carrier_permAct, Finset.card_image_of_injective _ σ.injective]
                rw [this, hcard]
                exact hDlow _ _
            · have himg : (carrier (permAct σ (del ηA u))).image
                    (fun c => addTo (permAct σ (del ηA u)) (σ u) c)
                  = ((carrier (del ηA u)).image fun c => addTo (del ηA u) u c).image
                      (permAct σ) := by
                rw [Finset.image_image, carrier_permAct, Finset.image_image]
                refine Finset.image_congr fun c _ => ?_
                exact (permAct_addTo huη σ c).symm
              rw [himg, Finset.sum_image (fun x _ y _ h => permAct_injective σ h),
                ← Finset.sum_sub_distrib]
              refine HasDen.sum fun ζ hζ => ?_
              obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hζ
              have hcarζ : carrier (addTo (del ηA u) u c) = carrier ηA := by
                rw [carrier_addTo huη, hins]
              have hIH := ih (addTo (del ηA u) u c) ηB
                (by
                  have := card_singletons_addTo_le huη hc
                  omega) (by rw [hcarζ]; exact hs)
              rw [hcarζ] at hIH
              exact hIH
          · rw [Finset.not_nonempty_iff_eq_empty] at hA hB
            exact hbaseContrast σ ηA ηB hA hB hs
  exact key _ ηA ηB le_rfl hσ

end Induction

section BSide

variable {V : Type*} [AddCommGroup V]

def bPart (k : α) : SetPart α := addSingleton (oneBlock ((Finset.univ : Finset α).erase k)) k

theorem bPart_def (k : α) :
    bPart k = addSingleton (oneBlock ((Finset.univ : Finset α).erase k)) k := rfl

theorem notMem_carrier_oneBlock_erase (k : α) :
    k ∉ carrier (oneBlock ((Finset.univ : Finset α).erase k)) := by
  rw [carrier_oneBlock]
  exact Finset.notMem_erase k _

@[simp] theorem carrier_bPart (k : α) : carrier (bPart k) = (Finset.univ : Finset α) := by
  rw [bPart, carrier_addSingleton (notMem_carrier_oneBlock_erase k), carrier_oneBlock,
    Finset.insert_erase (Finset.mem_univ k)]

theorem permAct_bPart (σ : Equiv.Perm α) (k : α) : permAct σ (bPart k) = bPart (σ k) := by
  rw [bPart, permAct_addSingleton (notMem_carrier_oneBlock_erase k), permAct_oneBlock,
    Finset.image_erase σ.injective, image_univ_perm, bPart]

theorem permAct_oneBlock_univ (σ : Equiv.Perm α) :
    permAct σ (oneBlock (Finset.univ : Finset α)) = oneBlock (Finset.univ : Finset α) := by
  rw [permAct_oneBlock, image_univ_perm]

theorem bPart_ne_oneBlock_univ [Nontrivial α] (k : α) :
    bPart k ≠ oneBlock (Finset.univ : Finset α) := by
  intro h
  obtain ⟨l, hl⟩ := exists_ne k
  have hb : (bPart k).block k = (oneBlock (Finset.univ : Finset α)).block k := by rw [h]
  rw [bPart, addSingleton_block (notMem_carrier_oneBlock_erase k), ite_eq_left rfl, oneBlock_block,
    ite_eq_left (Finset.mem_univ k)] at hb
  have : l ∈ ({k} : Finset α) := by rw [hb]; exact Finset.mem_univ l
  exact hl (Finset.mem_singleton.mp this)

theorem fibOf_univ_univ (ξ : SetPart α) (h : carrier ξ = Finset.univ) :
    fibOf Finset.univ Finset.univ ξ = {ξ} := by
  ext ζ
  rw [mem_fibOf, Finset.mem_singleton]
  constructor
  · rintro ⟨hc, hr⟩
    rw [← hc] at hr
    rwa [restrictTo_carrier] at hr
  · rintro rfl
    exact ⟨h, by rw [← h, restrictTo_carrier]⟩

theorem agg_oneBlock_erase [Nontrivial α] (P : SetPart α → SetPart α → V) (ξ : SetPart α)
    (hξ : carrier ξ = Finset.univ) (k : α) :
    agg P Finset.univ ((Finset.univ : Finset α).erase k) ξ
        (oneBlock ((Finset.univ : Finset α).erase k))
      = P ξ (bPart k) + P ξ (oneBlock (Finset.univ : Finset α)) := by
  have hk : k ∉ (Finset.univ : Finset α).erase k := Finset.notMem_erase k _
  have hne : ((Finset.univ : Finset α).erase k).Nonempty := by
    obtain ⟨l, hl⟩ := exists_ne k
    exact ⟨l, Finset.mem_erase.mpr ⟨hl, Finset.mem_univ l⟩⟩
  have hfib := fibre_one_block_pair hk hne
  rw [Finset.insert_erase (Finset.mem_univ k)] at hfib
  unfold agg
  rw [fibOf_univ_univ ξ hξ, Finset.sum_singleton, hfib, ← bPart_def k,
    Finset.sum_pair (bPart_ne_oneBlock_univ k)]

theorem bSideReduction [Nontrivial α] (P : SetPart α → SetPart α → V)
    (hequiv : ∀ (σ : Equiv.Perm α) (ξA ξB : SetPart α),
      P (permAct σ ξA) (permAct σ ξB) = P ξA ξB)
    (ξ : SetPart α) (hξ : carrier ξ = Finset.univ) (k l : α) :
    P ξ (bPart k) - P ξ (bPart l)
      = agg P Finset.univ ((Finset.univ : Finset α).erase k) ξ
          (oneBlock ((Finset.univ : Finset α).erase k))
        - agg P Finset.univ ((Finset.univ : Finset α).erase k)
            (permAct (Equiv.swap k l) ξ) (oneBlock ((Finset.univ : Finset α).erase k)) := by
  have hcarσ : carrier (permAct (Equiv.swap k l) ξ) = Finset.univ := by
    rw [carrier_permAct, hξ, image_univ_perm]
  rw [agg_oneBlock_erase P ξ hξ k, agg_oneBlock_erase P _ hcarσ k]
  have h1 : P (permAct (Equiv.swap k l) ξ) (bPart k) = P ξ (bPart l) := by
    have := hequiv (Equiv.swap k l) ξ (bPart l)
    rw [permAct_bPart, Equiv.swap_apply_right] at this
    rw [this]
  have h2 : P (permAct (Equiv.swap k l) ξ) (oneBlock (Finset.univ : Finset α))
      = P ξ (oneBlock (Finset.univ : Finset α)) := by
    have := hequiv (Equiv.swap k l) ξ (oneBlock (Finset.univ : Finset α))
    rw [permAct_oneBlock_univ] at this
    rw [this]
  rw [h1, h2]
  abel

end BSide

section Main

variable {R : Type*} [CommRing R] {V : Type*} [AddCommGroup V] [Module R V]

theorem rowRow_dvd [Nontrivial α] (P : SetPart α → SetPart α → V) (L : Submodule R V)
    (D Dp : ℕ → ℕ → R)
    (hDB : ∀ i j, D i j ∣ D i (j + 1)) (hDA : ∀ i j, D i j ∣ D (i + 1) j)
    (hbase : ∀ ηA ηB : SetPart α, SingletonFree ηA → SingletonFree ηB →
      HasDen L (D (carrier ηA).card (carrier ηB).card)
        (agg P (carrier ηA) (carrier ηB) ηA ηB))
    (hDpB : ∀ i j, Dp i j ∣ Dp i (j + 1)) (hDlow : ∀ i j, D i j ∣ Dp (i + 1) j)
    (hbaseContrast : ∀ (σ : Equiv.Perm α) (ηA ηB : SetPart α),
      SingletonFree ηA → SingletonFree ηB → (carrier ηA).image σ = carrier ηA →
      HasDen L (Dp (carrier ηA).card (carrier ηB).card)
        (agg P (carrier ηA) (carrier ηB) ηA ηB
          - agg P (carrier ηA) (carrier ηB) (permAct σ ηA) ηB))
    (hequiv : ∀ (σ : Equiv.Perm α) (ξA ξB : SetPart α),
      P (permAct σ ξA) (permAct σ ξB) = P ξA ξB)
    (ξ : SetPart α) (hξ : carrier ξ = Finset.univ) (k l : α) :
    HasDen L (Dp (Fintype.card α) (Fintype.card α - 1)) (P ξ (bPart k) - P ξ (bPart l)) := by
  have hcarB : carrier (oneBlock ((Finset.univ : Finset α).erase k))
      = (Finset.univ : Finset α).erase k := carrier_oneBlock _
  have hcards : (carrier ξ).card = Fintype.card α := by rw [hξ, Finset.card_univ]
  have hcardB : (carrier (oneBlock ((Finset.univ : Finset α).erase k))).card
      = Fintype.card α - 1 := by
    rw [hcarB, Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ]
  have hσ : (carrier ξ).image (Equiv.swap k l) = carrier ξ := by
    rw [hξ, image_univ_perm]
  have hmain := dvd_contrast_of_singleton_induction P L D Dp hDB hDA hbase hDpB hDlow
    hbaseContrast (Equiv.swap k l) ξ (oneBlock ((Finset.univ : Finset α).erase k)) hσ
  rw [hcards, hcardB, hξ, hcarB] at hmain
  rw [bSideReduction P hequiv ξ hξ k l]
  exact hmain

end Main

section Marginal

omit [DecidableEq α] in
theorem card_filter_comp_perm {δ : Type*} [DecidableEq δ] (e : Equiv.Perm α) (u : α → δ)
    (c : δ) : (Finset.univ.filter fun a => u (e a) = c).card
      = (Finset.univ.filter fun a => u a = c).card := by
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  exact Fintype.card_congr (Equiv.subtypeEquiv e fun _ => Iff.rfl)

omit [DecidableEq α] in
theorem exists_perm_comp_eq {β : Type*} [DecidableEq β] (f g : α → β)
    (h : ∀ b : β, (Finset.univ.filter fun a => f a = b).card
        = (Finset.univ.filter fun a => g a = b).card) :
    ∃ σ : Equiv.Perm α, ∀ a, f (σ a) = g a := by
  have hcard : ∀ b : β, Fintype.card {a // g a = b} = Fintype.card {a // f a = b} := by
    intro b
    rw [Fintype.card_subtype, Fintype.card_subtype]
    exact (h b).symm
  let m : (Σ b : β, {a // g a = b}) ≃ (Σ b : β, {a // f a = b}) :=
    Equiv.sigmaCongrRight fun b => Fintype.equivOfCardEq (hcard b)
  refine ⟨(Equiv.sigmaFiberEquiv g).symm.trans (m.trans (Equiv.sigmaFiberEquiv f)), fun a => ?_⟩
  exact (m ((Equiv.sigmaFiberEquiv g).symm a)).2.2

omit [DecidableEq α] in
theorem exists_perm_pair {β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (f f' : α → β) (g g' : α → γ)
    (hA : ∀ b : β, (Finset.univ.filter fun a => f a = b).card
        = (Finset.univ.filter fun a => f' a = b).card)
    (hB : ∀ c : γ, (Finset.univ.filter fun a => g a = c).card
        = (Finset.univ.filter fun a => g' a = c).card) :
    ∃ ρ σ : Equiv.Perm α, (∀ a, f' a = f (ρ a)) ∧ ∀ a, g' a = g (σ (ρ a)) := by
  obtain ⟨ρ, hρ⟩ := exists_perm_comp_eq f f' hA
  have hB' : ∀ c : γ, (Finset.univ.filter fun a => g a = c).card
      = (Finset.univ.filter fun a => g' (ρ.symm a) = c).card := by
    intro c
    rw [card_filter_comp_perm ρ.symm g' c]
    exact hB c
  obtain ⟨σ, hσ⟩ := exists_perm_comp_eq g (fun a => g' (ρ.symm a)) hB'
  refine ⟨ρ, σ, fun a => (hρ a).symm, fun a => ?_⟩
  have := hσ (ρ a)
  rw [Equiv.symm_apply_apply] at this
  exact this.symm

omit [DecidableEq α] in
theorem qDiff_marginal_pair {β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (f f' : α → β) (g g' : α → γ)
    (hA : ∀ b : β, (Finset.univ.filter fun a => f a = b).card
        = (Finset.univ.filter fun a => f' a = b).card)
    (hB : ∀ c : γ, (Finset.univ.filter fun a => g a = c).card
        = (Finset.univ.filter fun a => g' a = c).card) :
    (∃ ρ σ : Equiv.Perm α, (∀ a, f' a = f (ρ a)) ∧ ∀ a, g' a = g (σ (ρ a)))
      ∧ (∃ ρ τ : Equiv.Perm α, (∀ a, g' a = g (ρ a)) ∧ ∀ a, f' a = f (τ (ρ a))) :=
  ⟨exists_perm_pair f f' g g' hA hB, exists_perm_pair g g' f f' hB hA⟩

end Marginal

end Rhone.Algebra.Isotypic
