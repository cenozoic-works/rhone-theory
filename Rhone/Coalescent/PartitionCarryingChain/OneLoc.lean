/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.PartitionCarryingChain.Count

/-! # The star-weighted chain is the one-locus chain at rate `θ_A + θ_B` -/

@[expose] public section

namespace Rhone.Coalescent.PartitionCarryingChain

open Finset TwoLocusGenealogy TypedAncestralChain EsfPair
open LinearAlgebra.Recursion

variable {n K : ℕ} {θA θB : ℝ} {σ : Fin n → Fin K} {π : Fin K → ℝ} {L : Finset (Lin n)}
variable {p q : Lin n}

theorem stI_idem (p : Lin n) : stI p * stI p = stI p := by
  rw [stI]
  split_ifs <;> norm_num

theorem uStar_idem (σ : Fin n → Fin K) (p : Lin n) (i : Fin K) :
    ((uStar σ p i : ℕ) : ℝ) * ((uStar σ p i : ℕ) : ℝ) = ((uStar σ p i : ℕ) : ℝ) := by
  rw [uStar]
  split_ifs <;> norm_num

theorem colour_spec {i : Fin K} (h : uStar σ p i = 1) :
    (p.1 ∩ p.2).Nonempty ∧ ∀ k ∈ p.1 ∩ p.2, σ k = i := by
  rw [uStar] at h
  split_ifs at h with hc
  exact hc

theorem sum_pair_offdiag (L : Finset (Lin n)) (u : Lin n → ℝ) (hu : ∀ p, u p * u p = u p) :
    (∑ p ∈ L, ∑ q ∈ L.erase p, u p * u q)
      = (∑ p ∈ L, u p) * (∑ p ∈ L, u p) - ∑ p ∈ L, u p := by
  have h1 : ∀ p ∈ L, (∑ q ∈ L.erase p, u q) = (∑ q ∈ L, u q) - u p := by
    intro p hp
    have h := Finset.sum_erase_add L u hp
    linarith
  calc (∑ p ∈ L, ∑ q ∈ L.erase p, u p * u q)
      = ∑ p ∈ L, (u p * (∑ q ∈ L, u q) - u p * u p) := by
        refine Finset.sum_congr rfl fun p hp => ?_
        rw [← Finset.mul_sum, h1 p hp, mul_sub]
    _ = (∑ p ∈ L, u p * (∑ q ∈ L, u q)) - ∑ p ∈ L, u p * u p := by
        rw [Finset.sum_sub_distrib]
    _ = (∑ p ∈ L, u p) * (∑ p ∈ L, u p) - ∑ p ∈ L, u p := by
        rw [← Finset.sum_mul]
        congr 1
        exact Finset.sum_congr rfl fun p _ => hu p

theorem sum_pair_card (L : Finset (Lin n)) :
    (∑ p ∈ L, ∑ _q ∈ L.erase p, (1 : ℝ)) = (L.card : ℝ) * ((L.card : ℝ) - 1) := by
  have h1 : ∀ p ∈ L, (∑ _q ∈ L.erase p, (1 : ℝ)) = (L.card : ℝ) - 1 := by
    intro p hp
    have hc : 1 ≤ L.card := Finset.card_pos.2 ⟨p, hp⟩
    rw [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.card_erase_of_mem hp,
      Nat.cast_sub hc, Nat.cast_one]
  rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul]

theorem Vst_mutAL (hw : WF L) (hmono : MonoStars σ L) (hp : p ∈ L) :
    mstar σ π p * Vst σ π θA θB (mutAL L p)
      = (1 - stI p) * Vst σ π θA θB L
        + ∑ i, ((uStar σ p i : ℕ) : ℝ)
            * (π i * qOne (θA + θB) π (decf (scount σ L) i)) := by
  have hmono' : MonoStars σ (mutAL L p) := monoStars_mutAL hmono p
  by_cases hne : p.1 ∩ p.2 = ∅
  · have hu : ∀ i, uStar σ p i = 0 := fun i => uStar_eq_zero_of_empty hne i
    have hsc : scount σ (mutAL L p) = scount σ L := by
      funext i
      have h := scount_mutAL (σ := σ) hw hp i
      rw [hu i, add_zero] at h
      exact h
    rw [mstar, ite_eq_left hne, one_mul, Vst_of_mono hmono', Vst_of_mono hmono, hsc,
      stI_of_empty hne, Finset.sum_eq_zero fun i _ => by rw [hu i]; norm_num]
    ring
  · obtain ⟨i₀, hi₀⟩ := exists_colour (hmono p hp) (Finset.nonempty_iff_ne_empty.2 hne)
    have hsc : scount σ (mutAL L p) = decf (scount σ L) i₀ := by
      funext j
      have h := scount_mutAL (σ := σ) hw hp j
      by_cases hj : j = i₀
      · rw [hi₀ j, ite_eq_left hj] at h
        rw [hj] at h
        rw [hj, decf_self]
        omega
      · rw [hi₀ j, ite_eq_right hj] at h
        rw [decf_of_ne _ hj]
        omega
    have hL : (∑ i, ((uStar σ p i : ℕ) : ℝ) * π i) = π i₀ := by
      rw [Finset.sum_eq_single i₀]
      · rw [hi₀ i₀, ite_eq_left rfl]
        norm_num
      · intro j _ hj
        rw [hi₀ j, ite_eq_right hj]
        norm_num
      · intro hc
        exact absurd (Finset.mem_univ i₀) hc
    have hR : (∑ i, ((uStar σ p i : ℕ) : ℝ)
          * (π i * qOne (θA + θB) π (decf (scount σ L) i)))
        = π i₀ * qOne (θA + θB) π (decf (scount σ L) i₀) := by
      rw [Finset.sum_eq_single i₀]
      · rw [hi₀ i₀, ite_eq_left rfl]
        norm_num
      · intro j _ hj
        rw [hi₀ j, ite_eq_right hj]
        norm_num
      · intro hc
        exact absurd (Finset.mem_univ i₀) hc
    rw [mstar_eq hne, Vst_of_mono hmono', hsc, stI_of_ne hne, hL, hR]
    ring

theorem Vst_mutBL (hw : WF L) (hmono : MonoStars σ L) (hp : p ∈ L) :
    mstar σ π p * Vst σ π θA θB (mutBL L p)
      = (1 - stI p) * Vst σ π θA θB L
        + ∑ i, ((uStar σ p i : ℕ) : ℝ)
            * (π i * qOne (θA + θB) π (decf (scount σ L) i)) := by
  have hmono' : MonoStars σ (mutBL L p) := monoStars_mutBL hmono p
  by_cases hne : p.1 ∩ p.2 = ∅
  · have hu : ∀ i, uStar σ p i = 0 := fun i => uStar_eq_zero_of_empty hne i
    have hsc : scount σ (mutBL L p) = scount σ L := by
      funext i
      have h := scount_mutBL (σ := σ) hw hp i
      rw [hu i, add_zero] at h
      exact h
    rw [mstar, ite_eq_left hne, one_mul, Vst_of_mono hmono', Vst_of_mono hmono, hsc,
      stI_of_empty hne, Finset.sum_eq_zero fun i _ => by rw [hu i]; norm_num]
    ring
  · obtain ⟨i₀, hi₀⟩ := exists_colour (hmono p hp) (Finset.nonempty_iff_ne_empty.2 hne)
    have hsc : scount σ (mutBL L p) = decf (scount σ L) i₀ := by
      funext j
      have h := scount_mutBL (σ := σ) hw hp j
      by_cases hj : j = i₀
      · rw [hi₀ j, ite_eq_left hj] at h
        rw [hj] at h
        rw [hj, decf_self]
        omega
      · rw [hi₀ j, ite_eq_right hj] at h
        rw [decf_of_ne _ hj]
        omega
    have hL : (∑ i, ((uStar σ p i : ℕ) : ℝ) * π i) = π i₀ := by
      rw [Finset.sum_eq_single i₀]
      · rw [hi₀ i₀, ite_eq_left rfl]
        norm_num
      · intro j _ hj
        rw [hi₀ j, ite_eq_right hj]
        norm_num
      · intro hc
        exact absurd (Finset.mem_univ i₀) hc
    have hR : (∑ i, ((uStar σ p i : ℕ) : ℝ)
          * (π i * qOne (θA + θB) π (decf (scount σ L) i)))
        = π i₀ * qOne (θA + θB) π (decf (scount σ L) i₀) := by
      rw [Finset.sum_eq_single i₀]
      · rw [hi₀ i₀, ite_eq_left rfl]
        norm_num
      · intro j _ hj
        rw [hi₀ j, ite_eq_right hj]
        norm_num
      · intro hc
        exact absurd (Finset.mem_univ i₀) hc
    rw [mstar_eq hne, Vst_of_mono hmono', hsc, stI_of_ne hne, hL, hR]
    ring

theorem Vst_coalL (hw : WF L) (hal : Aligned L) (hmono : MonoStars σ L) (hp : p ∈ L)
    (hq : q ∈ L.erase p) :
    Vst σ π θA θB (coalL L p q)
      = (1 - stI p * stI q) * Vst σ π θA θB L
        + ∑ i, (((uStar σ p i : ℕ) : ℝ) * ((uStar σ q i : ℕ) : ℝ))
            * qOne (θA + θB) π (decf (scount σ L) i) := by
  have hqL : q ∈ L := Finset.mem_of_mem_erase hq
  have hqp : q ≠ p := Finset.ne_of_mem_erase hq
  have hpq : p ≠ q := fun hc => hqp hc.symm
  have hst : ((p.1 ∪ q.1, p.2 ∪ q.2) : Lin n).1 ∩ ((p.1 ∪ q.1, p.2 ∪ q.2) : Lin n).2
      = (p.1 ∩ p.2) ∪ (q.1 ∩ q.2) := star_coal hal hp hqL hpq
  by_cases hnep : p.1 ∩ p.2 = ∅
  · have hum : ∀ i, uStar σ (p.1 ∪ q.1, p.2 ∪ q.2) i = uStar σ q i := by
      intro i
      refine uStar_congr ?_ i
      rw [hst, hnep, Finset.empty_union]
    have hup : ∀ i, uStar σ p i = 0 := fun i => uStar_eq_zero_of_empty hnep i
    have hsc : scount σ (coalL L p q) = scount σ L := by
      funext i
      have h := scount_coalL (σ := σ) hw hp hq i
      rw [hup i, hum i] at h
      omega
    have hmono' : MonoStars σ (coalL L p q) :=
      monoStars_coalL hmono hal hp hqL hpq fun k hk => by
        rw [hnep] at hk
        exact absurd hk (Finset.notMem_empty k)
    have hVeq : Vst σ π θA θB (coalL L p q) = Vst σ π θA θB L := by
      rw [Vst_of_mono hmono', Vst_of_mono hmono, hsc]
    rw [hVeq, stI_of_empty hnep,
      Finset.sum_eq_zero fun i _ => by rw [hup i]; norm_num]
    ring
  · by_cases hneq : q.1 ∩ q.2 = ∅
    · have hum : ∀ i, uStar σ (p.1 ∪ q.1, p.2 ∪ q.2) i = uStar σ p i := by
        intro i
        refine uStar_congr ?_ i
        rw [hst, hneq, Finset.union_empty]
      have huq : ∀ i, uStar σ q i = 0 := fun i => uStar_eq_zero_of_empty hneq i
      have hsc : scount σ (coalL L p q) = scount σ L := by
        funext i
        have h := scount_coalL (σ := σ) hw hp hq i
        rw [huq i, hum i] at h
        omega
      have hmono' : MonoStars σ (coalL L p q) :=
        monoStars_coalL hmono hal hp hqL hpq fun k _ l hl => by
          rw [hneq] at hl
          exact absurd hl (Finset.notMem_empty l)
      have hVeq : Vst σ π θA θB (coalL L p q) = Vst σ π θA θB L := by
        rw [Vst_of_mono hmono', Vst_of_mono hmono, hsc]
      rw [hVeq, stI_of_empty hneq,
        Finset.sum_eq_zero fun i _ => by rw [huq i]; norm_num]
      ring
    · obtain ⟨ip, hip⟩ := exists_colour (hmono p hp) (Finset.nonempty_iff_ne_empty.2 hnep)
      obtain ⟨iq, hiq⟩ := exists_colour (hmono q hqL) (Finset.nonempty_iff_ne_empty.2 hneq)
      have hcp : (p.1 ∩ p.2).Nonempty ∧ ∀ k ∈ p.1 ∩ p.2, σ k = ip :=
        colour_spec (by rw [hip ip, ite_eq_left rfl])
      have hcq : (q.1 ∩ q.2).Nonempty ∧ ∀ k ∈ q.1 ∩ q.2, σ k = iq :=
        colour_spec (by rw [hiq iq, ite_eq_left rfl])
      by_cases hcol : ip = iq
      · have hcolq : ∀ k ∈ q.1 ∩ q.2, σ k = ip := by
          intro k hk
          rw [hcol]
          exact hcq.2 k hk
        have hallm : ∀ k ∈ (p.1 ∪ q.1, p.2 ∪ q.2).1 ∩ (p.1 ∪ q.1, p.2 ∪ q.2).2, σ k = ip := by
          intro k hk
          rw [hst] at hk
          rcases Finset.mem_union.1 hk with hk' | hk'
          · exact hcp.2 k hk'
          · exact hcolq k hk'
        have hmne : ((p.1 ∪ q.1, p.2 ∪ q.2) : Lin n).1
            ∩ ((p.1 ∪ q.1, p.2 ∪ q.2) : Lin n).2 |>.Nonempty := by
          obtain ⟨k, hk⟩ := hcp.1
          exact ⟨k, by rw [hst]; exact Finset.mem_union_left _ hk⟩
        have hum : ∀ j, uStar σ (p.1 ∪ q.1, p.2 ∪ q.2) j = if j = ip then 1 else 0 := by
          intro j
          by_cases hj : j = ip
          · rw [uStar, ite_eq_left ⟨hmne, by rw [hj]; exact hallm⟩, ite_eq_left hj]
          · rw [uStar, ite_eq_right, ite_eq_right hj]
            rintro ⟨-, hall⟩
            obtain ⟨k, hk⟩ := hmne
            exact hj ((hall k hk).symm.trans (hallm k hk))
        have hsc : scount σ (coalL L p q) = decf (scount σ L) ip := by
          funext j
          have h := scount_coalL (σ := σ) hw hp hq j
          by_cases hj : j = ip
          · rw [hip j, ite_eq_left hj, hiq j, ite_eq_left (hj.trans hcol), hum j,
              ite_eq_left hj] at h
            rw [hj] at h
            rw [hj, decf_self]
            omega
          · rw [hip j, ite_eq_right hj, hiq j, ite_eq_right (fun hc => hj (hc.trans hcol.symm)),
              hum j, ite_eq_right hj] at h
            rw [decf_of_ne _ hj]
            omega
        have hmono' : MonoStars σ (coalL L p q) :=
          monoStars_coalL hmono hal hp hqL hpq fun k hk l hl => by
            rw [hcp.2 k hk, hcolq l hl]
        have hR : (∑ i, (((uStar σ p i : ℕ) : ℝ) * ((uStar σ q i : ℕ) : ℝ))
              * qOne (θA + θB) π (decf (scount σ L) i))
            = qOne (θA + θB) π (decf (scount σ L) ip) := by
          rw [Finset.sum_eq_single ip]
          · rw [hip ip, ite_eq_left rfl, hiq ip, ite_eq_left hcol]
            norm_num
          · intro j _ hj
            rw [hip j, ite_eq_right hj]
            norm_num
          · intro hc
            exact absurd (Finset.mem_univ ip) hc
        rw [Vst_of_mono hmono', hsc, stI_of_ne hnep, stI_of_ne hneq, hR]
        ring
      · have hbad : ¬ MonoStars σ (coalL L p q) := by
          intro hc
          obtain ⟨k, hk⟩ := hcp.1
          obtain ⟨l, hl⟩ := hcq.1
          have hk' : k ∈ (p.1 ∪ q.1, p.2 ∪ q.2).1 ∩ (p.1 ∪ q.1, p.2 ∪ q.2).2 := by
            rw [hst]; exact Finset.mem_union_left _ hk
          have hl' : l ∈ (p.1 ∪ q.1, p.2 ∪ q.2).1 ∩ (p.1 ∪ q.1, p.2 ∪ q.2).2 := by
            rw [hst]; exact Finset.mem_union_right _ hl
          have := hc _ (Finset.mem_insert_self _ _) k hk' l hl'
          rw [hcp.2 k hk, hcq.2 l hl] at this
          exact hcol this
        have hR : (∑ i, (((uStar σ p i : ℕ) : ℝ) * ((uStar σ q i : ℕ) : ℝ))
              * qOne (θA + θB) π (decf (scount σ L) i)) = 0 := by
          refine Finset.sum_eq_zero fun j _ => ?_
          by_cases hj : j = ip
          · rw [hiq j, ite_eq_right (fun hc => hcol (hj.symm.trans hc))]
            norm_num
          · rw [hip j, ite_eq_right hj]
            norm_num
        rw [Vst_of_not_mono hbad, stI_of_ne hnep, stI_of_ne hneq, hR]
        ring

end Rhone.Coalescent.PartitionCarryingChain
