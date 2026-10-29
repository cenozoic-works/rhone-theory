/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.PartitionCarryingChain.Sw

/-! # The star configuration of a backward state -/

@[expose] public section

namespace Rhone.Coalescent.PartitionCarryingChain

open Finset TwoLocusGenealogy TypedAncestralChain EsfPair
open LinearAlgebra.Recursion

variable {n K : ℕ} {θA θB : ℝ} {σ : Fin n → Fin K} {π : Fin K → ℝ} {L : Finset (Lin n)}
variable {p q : Lin n}

def uStar (σ : Fin n → Fin K) (p : Lin n) (i : Fin K) : ℕ :=
  if (p.1 ∩ p.2).Nonempty ∧ ∀ k ∈ p.1 ∩ p.2, σ k = i then 1 else 0

def scount (σ : Fin n → Fin K) (L : Finset (Lin n)) (i : Fin K) : ℕ := ∑ p ∈ L, uStar σ p i

noncomputable def stI (p : Lin n) : ℝ := if p.1 ∩ p.2 = ∅ then 0 else 1

def MonoStars (σ : Fin n → Fin K) (L : Finset (Lin n)) : Prop :=
  ∀ p ∈ L, ∀ k ∈ p.1 ∩ p.2, ∀ l ∈ p.1 ∩ p.2, σ k = σ l

instance decidableMonoStars (σ : Fin n → Fin K) (L : Finset (Lin n)) :
    Decidable (MonoStars σ L) := by
  unfold MonoStars
  infer_instance

noncomputable def Vst (σ : Fin n → Fin K) (π : Fin K → ℝ) (θA θB : ℝ) (L : Finset (Lin n)) : ℝ :=
  if MonoStars σ L then qOne (θA + θB) π (scount σ L) else 0

theorem Vst_of_mono (h : MonoStars σ L) :
    Vst σ π θA θB L = qOne (θA + θB) π (scount σ L) := by rw [Vst, ite_eq_left h]

theorem Vst_of_not_mono (h : ¬ MonoStars σ L) : Vst σ π θA θB L = 0 := by rw [Vst, ite_eq_right h]

theorem MonoStars.subset (h : MonoStars σ L) {M : Finset (Lin n)} (hML : M ⊆ L) :
    MonoStars σ M := fun p hp => h p (hML hp)

theorem monoStars_empty : MonoStars σ (∅ : Finset (Lin n)) :=
  fun p hp => absurd hp (Finset.notMem_empty p)

theorem uStar_congr {r : Lin n} (h : p.1 ∩ p.2 = r.1 ∩ r.2) (i : Fin K) :
    uStar σ p i = uStar σ r i := by rw [uStar, uStar, h]

theorem uStar_eq_zero_of_empty (h : p.1 ∩ p.2 = ∅) (i : Fin K) : uStar σ p i = 0 := by
  rw [uStar, ite_eq_right]
  rintro ⟨hne, -⟩
  rw [h] at hne
  exact absurd hne (by simp)

theorem stI_of_empty (h : p.1 ∩ p.2 = ∅) : stI p = 0 := by rw [stI, ite_eq_left h]

theorem stI_of_ne (h : p.1 ∩ p.2 ≠ ∅) : stI p = 1 := by rw [stI, ite_eq_right h]

theorem exists_colour (hmono : ∀ k ∈ p.1 ∩ p.2, ∀ l ∈ p.1 ∩ p.2, σ k = σ l)
    (hne : (p.1 ∩ p.2).Nonempty) : ∃ i, ∀ j, uStar σ p j = if j = i then 1 else 0 := by
  obtain ⟨k₀, hk₀⟩ := hne
  refine ⟨σ k₀, fun j => ?_⟩
  by_cases hj : j = σ k₀
  · subst hj
    rw [uStar, ite_eq_left ⟨⟨k₀, hk₀⟩, fun k hk => hmono k hk k₀ hk₀⟩, ite_eq_left rfl]
  · rw [uStar, ite_eq_right, ite_eq_right hj]
    rintro ⟨-, hall⟩
    exact hj (hall k₀ hk₀).symm

theorem sum_uStar (hmono : ∀ k ∈ p.1 ∩ p.2, ∀ l ∈ p.1 ∩ p.2, σ k = σ l) :
    (∑ i, ((uStar σ p i : ℕ) : ℝ)) = stI p := by
  by_cases hne : p.1 ∩ p.2 = ∅
  · rw [stI_of_empty hne, Finset.sum_eq_zero fun i _ => by
      rw [uStar_eq_zero_of_empty hne i]; norm_num]
  · obtain ⟨i, hi⟩ := exists_colour hmono (Finset.nonempty_iff_ne_empty.2 hne)
    rw [stI_of_ne hne, Finset.sum_eq_single i]
    · rw [hi i, ite_eq_left rfl]
      norm_num
    · intro j _ hj
      rw [hi j, ite_eq_right hj]
      norm_num
    · intro hc
      exact absurd (Finset.mem_univ i) hc

theorem mstar_eq (hne : p.1 ∩ p.2 ≠ ∅) :
    mstar σ π p = ∑ i, ((uStar σ p i : ℕ) : ℝ) * π i := by
  rw [mstar, ite_eq_right hne, matchA]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [uStar]
  by_cases hc : ∀ k ∈ p.1 ∩ p.2, σ k = i
  · rw [ite_eq_left hc, ite_eq_left ⟨Finset.nonempty_iff_ne_empty.2 hne, hc⟩]
    norm_num
  · rw [ite_eq_right hc, ite_eq_right (fun h => hc h.2)]
    norm_num

theorem scount_mutAL (hw : WF L) (hp : p ∈ L) (i : Fin K) :
    scount σ (mutAL L p) i + uStar σ p i = scount σ L i := by
  have hbase : scount σ (mutAL L p) i = ∑ r ∈ L.erase p, uStar σ r i := by
    rw [scount, mutAL]
    split_ifs with h2
    · rfl
    · rw [Finset.sum_insert (mutA_not_mem hw hp (Finset.nonempty_iff_ne_empty.2 h2)),
        uStar_eq_zero_of_empty (by simp) i, zero_add]
  rw [hbase, scount]
  exact Finset.sum_erase_add L _ hp

theorem scount_mutBL (hw : WF L) (hp : p ∈ L) (i : Fin K) :
    scount σ (mutBL L p) i + uStar σ p i = scount σ L i := by
  have hbase : scount σ (mutBL L p) i = ∑ r ∈ L.erase p, uStar σ r i := by
    rw [scount, mutBL]
    split_ifs with h1
    · rfl
    · rw [Finset.sum_insert (mutB_not_mem hw hp (Finset.nonempty_iff_ne_empty.2 h1)),
        uStar_eq_zero_of_empty (by simp) i, zero_add]
  rw [hbase, scount]
  exact Finset.sum_erase_add L _ hp

theorem scount_coalL (hw : WF L) (hp : p ∈ L) (hq : q ∈ L.erase p) (i : Fin K) :
    scount σ (coalL L p q) i + uStar σ p i + uStar σ q i
      = uStar σ (p.1 ∪ q.1, p.2 ∪ q.2) i + scount σ L i := by
  have hqL : q ∈ L := Finset.mem_of_mem_erase hq
  have hm : ((p.1 ∪ q.1, p.2 ∪ q.2) : Lin n) ∉ (L.erase p).erase q := coal_not_mem hw hp hqL
  have h1 : scount σ (coalL L p q) i
      = uStar σ (p.1 ∪ q.1, p.2 ∪ q.2) i + ∑ r ∈ (L.erase p).erase q, uStar σ r i := by
    rw [scount, coalL, Finset.sum_insert hm]
  have h2 : (∑ r ∈ (L.erase p).erase q, uStar σ r i) + uStar σ q i
      = ∑ r ∈ L.erase p, uStar σ r i := Finset.sum_erase_add _ _ hq
  have h3 : (∑ r ∈ L.erase p, uStar σ r i) + uStar σ p i = scount σ L i :=
    Finset.sum_erase_add _ _ hp
  rw [h1, scount] at *
  omega

theorem monoStars_mutAL (h : MonoStars σ L) (p : Lin n) : MonoStars σ (mutAL L p) := by
  intro r hr
  rcases mem_mutAL.1 hr with ⟨-, hre⟩ | hre
  · subst hre
    intro k hk
    exact absurd hk (by simp)
  · exact h r (Finset.mem_of_mem_erase hre)

theorem monoStars_mutBL (h : MonoStars σ L) (p : Lin n) : MonoStars σ (mutBL L p) := by
  intro r hr
  rcases mem_mutBL.1 hr with ⟨-, hre⟩ | hre
  · subst hre
    intro k hk
    exact absurd hk (by simp)
  · exact h r (Finset.mem_of_mem_erase hre)

theorem star_coal (hal : Aligned L) (hp : p ∈ L) (hq : q ∈ L) (hpq : p ≠ q) :
    ((p.1 ∪ q.1, p.2 ∪ q.2) : Lin n).1 ∩ ((p.1 ∪ q.1, p.2 ∪ q.2) : Lin n).2
      = (p.1 ∩ p.2) ∪ (q.1 ∩ q.2) := inter_union_union hal hp hq hpq

theorem monoStars_coalL (h : MonoStars σ L) (hal : Aligned L) (hp : p ∈ L) (hq : q ∈ L)
    (hpq : p ≠ q) (hcol : ∀ k ∈ p.1 ∩ p.2, ∀ l ∈ q.1 ∩ q.2, σ k = σ l) :
    MonoStars σ (coalL L p q) := by
  have hst := star_coal hal hp hq hpq
  intro r hr
  rcases Finset.mem_insert.1 hr with rfl | hre
  · rw [hst]
    intro k hk l hl
    rcases Finset.mem_union.1 hk with hk' | hk' <;> rcases Finset.mem_union.1 hl with hl' | hl'
    · exact h p hp k hk' l hl'
    · exact hcol k hk' l hl'
    · exact (hcol l hl' k hk').symm
    · exact h q hq k hk' l hl'
  · exact h r (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hre))

theorem not_monoStars_coalL (h : ¬ MonoStars σ L) (p q : Lin n) :
    ¬ MonoStars σ (coalL L p q) := by
  intro hc
  refine h fun r hr k hk l hl => ?_
  by_cases hrp : r = p
  · have hk' : k ∈ (p.1 ∪ q.1, p.2 ∪ q.2).1 ∩ (p.1 ∪ q.1, p.2 ∪ q.2).2 := by
      rw [hrp] at hk
      exact Finset.mem_inter.2 ⟨Finset.mem_union_left _ (Finset.mem_inter.1 hk).1,
        Finset.mem_union_left _ (Finset.mem_inter.1 hk).2⟩
    have hl' : l ∈ (p.1 ∪ q.1, p.2 ∪ q.2).1 ∩ (p.1 ∪ q.1, p.2 ∪ q.2).2 := by
      rw [hrp] at hl
      exact Finset.mem_inter.2 ⟨Finset.mem_union_left _ (Finset.mem_inter.1 hl).1,
        Finset.mem_union_left _ (Finset.mem_inter.1 hl).2⟩
    exact hc _ (Finset.mem_insert_self _ _) k hk' l hl'
  · by_cases hrq : r = q
    · have hk' : k ∈ (p.1 ∪ q.1, p.2 ∪ q.2).1 ∩ (p.1 ∪ q.1, p.2 ∪ q.2).2 := by
        rw [hrq] at hk
        exact Finset.mem_inter.2 ⟨Finset.mem_union_right _ (Finset.mem_inter.1 hk).1,
          Finset.mem_union_right _ (Finset.mem_inter.1 hk).2⟩
      have hl' : l ∈ (p.1 ∪ q.1, p.2 ∪ q.2).1 ∩ (p.1 ∪ q.1, p.2 ∪ q.2).2 := by
        rw [hrq] at hl
        exact Finset.mem_inter.2 ⟨Finset.mem_union_right _ (Finset.mem_inter.1 hl).1,
          Finset.mem_union_right _ (Finset.mem_inter.1 hl).2⟩
      exact hc _ (Finset.mem_insert_self _ _) k hk' l hl'
    · exact hc r (Finset.mem_insert_of_mem
        (Finset.mem_erase.2 ⟨hrq, Finset.mem_erase.2 ⟨hrp, hr⟩⟩)) k hk l hl

theorem not_monoStars_erase (h : ¬ MonoStars σ L)
    (hp : ∀ k ∈ p.1 ∩ p.2, ∀ l ∈ p.1 ∩ p.2, σ k = σ l) : ¬ MonoStars σ (L.erase p) := by
  intro hc
  refine h fun r hr k hk l hl => ?_
  by_cases hrp : r = p
  · subst hrp
    exact hp k hk l hl
  · exact hc r (Finset.mem_erase.2 ⟨hrp, hr⟩) k hk l hl

end Rhone.Coalescent.PartitionCarryingChain
