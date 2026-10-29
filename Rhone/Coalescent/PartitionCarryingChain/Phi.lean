/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.EsfPair.Aligned

/-! # At `ρ = 0` the partition-carrying chain is a finite DAG -/

@[expose] public section

namespace Rhone.Coalescent.PartitionCarryingChain

open Finset TwoLocusGenealogy TypedAncestralChain EsfPair

variable {n : ℕ} {θA θB : ℝ} {ζA ζB : Blocks n}

def Phi (L : Finset (Lin n)) : ℕ := L.card + (coverA L).card + (coverB L).card

theorem card_coalL_lt {L : Finset (Lin n)} {p q : Lin n} (hp : p ∈ L) (hq : q ∈ L.erase p) :
    (coalL L p q).card < L.card := by
  have h1 : (L.erase p).card = L.card - 1 := Finset.card_erase_of_mem hp
  have h2 : ((L.erase p).erase q).card = (L.erase p).card - 1 := Finset.card_erase_of_mem hq
  have h3 : 1 ≤ L.card := Finset.card_pos.2 ⟨p, hp⟩
  have h4 : 1 ≤ (L.erase p).card := Finset.card_pos.2 ⟨q, hq⟩
  have h5 : (coalL L p q).card ≤ ((L.erase p).erase q).card + 1 := Finset.card_insert_le _ _
  omega

theorem card_mutAL_le {L : Finset (Lin n)} {p : Lin n} (hp : p ∈ L) :
    (mutAL L p).card ≤ L.card := by
  have h1 : (L.erase p).card = L.card - 1 := Finset.card_erase_of_mem hp
  have h3 : 1 ≤ L.card := Finset.card_pos.2 ⟨p, hp⟩
  rw [mutAL]
  split_ifs with h
  · omega
  · have h5 : (insert ((∅ : Finset (Fin n)), p.2) (L.erase p)).card ≤ (L.erase p).card + 1 :=
      Finset.card_insert_le _ _
    omega

theorem card_mutBL_le {L : Finset (Lin n)} {p : Lin n} (hp : p ∈ L) :
    (mutBL L p).card ≤ L.card := by
  have h1 : (L.erase p).card = L.card - 1 := Finset.card_erase_of_mem hp
  have h3 : 1 ≤ L.card := Finset.card_pos.2 ⟨p, hp⟩
  rw [mutBL]
  split_ifs with h
  · omega
  · have h5 : (insert (p.1, (∅ : Finset (Fin n))) (L.erase p)).card ≤ (L.erase p).card + 1 :=
      Finset.card_insert_le _ _
    omega

theorem card_sdiff_lt {S T : Finset (Fin n)} (hsub : T ⊆ S) (hne : T.Nonempty) :
    (S \ T).card < S.card := by
  obtain ⟨k, hk⟩ := hne
  refine Finset.card_lt_card ⟨Finset.sdiff_subset, fun hc => ?_⟩
  exact (Finset.mem_sdiff.1 (hc (hsub hk))).2 hk

theorem Phi_coal_lt {L : Finset (Lin n)} {p q : Lin n} (hp : p ∈ L) (hq : q ∈ L.erase p) :
    Phi (coalL L p q) < Phi L := by
  rw [Phi, Phi, coverA_coal hp hq, coverB_coal hp hq]
  have := card_coalL_lt hp hq
  omega

theorem Phi_mutA_lt {L : Finset (Lin n)} (hw : WF L) {p : Lin n} (hp : p ∈ carA L) :
    Phi (mutAL L p) < Phi L := by
  obtain ⟨hpL, hne⟩ := mem_carA.1 hp
  rw [Phi, Phi, coverA_mutA hw hpL, coverB_mutA hw hpL]
  have h1 := card_mutAL_le hpL
  have h2 := card_sdiff_lt (subset_coverA hpL) hne
  omega

theorem Phi_mutB_lt {L : Finset (Lin n)} (hw : WF L) {p : Lin n} (hp : p ∈ carB L) :
    Phi (mutBL L p) < Phi L := by
  obtain ⟨hpL, hne⟩ := mem_carB.1 hp
  rw [Phi, Phi, coverA_mutB hw hpL, coverB_mutB hw hpL]
  have h1 := card_mutBL_le hpL
  have h2 := card_sdiff_lt (subset_coverB hpL) hne
  omega

theorem eq_empty_of_Phi_zero {L : Finset (Lin n)} (h : Phi L = 0) : L = ∅ := by
  have : L.card = 0 := by rw [Phi] at h; omega
  exact Finset.card_eq_zero.1 this

theorem stepP_congr_rho_zero {g₁ g₂ : PSt n → ℝ} {s : PSt n}
    (hcoal : ∀ p ∈ s.1, ∀ q ∈ s.1.erase p, g₁ (coalP s p q) = g₂ (coalP s p q))
    (hmutA : ∀ p ∈ carA s.1, g₁ (mutAP s p) = g₂ (mutAP s p))
    (hmutB : ∀ p ∈ carB s.1, g₁ (mutBP s p) = g₂ (mutBP s p)) :
    stepP θA θB 0 g₁ s = stepP θA θB 0 g₂ s := by
  rw [stepP, stepP, zero_mul, zero_mul]
  congr 1
  congr 1
  · congr 1
    · exact Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun q hq => hcoal p hp q hq
    · exact congrArg _ (Finset.sum_congr rfl hmutA)
  · exact congrArg _ (Finset.sum_congr rfl hmutB)

theorem hitNP_stab :
    ∀ (N : ℕ) (s : PSt n), WFP s → Phi s.1 ≤ N →
      hitNP ζA ζB θA θB 0 (N + 1) s = hitNP ζA ζB θA θB 0 N s := by
  intro N
  induction N with
  | zero =>
    intro s _ hN
    have h : s.1 = ∅ := eq_empty_of_Phi_zero (Nat.le_zero.1 hN)
    rw [hitNP_of_empty _ h, hitNP_of_empty _ h]
  | succ N ih =>
    intro s hs hN
    by_cases h : s.1 = ∅
    · rw [hitNP_of_empty _ h, hitNP_of_empty _ h]
    · rw [hitNP_succ_of_ne (N + 1) h, hitNP_succ_of_ne N h]
      congr 1
      refine stepP_congr_rho_zero ?_ ?_ ?_
      · intro p hp q hq
        refine ih (coalP s p q) (hs.coal hp hq) ?_
        have := Phi_coal_lt hp hq
        change Phi (coalL s.1 p q) ≤ N
        omega
      · intro p hp
        refine ih (mutAP s p) (hs.mutA hp) ?_
        have := Phi_mutA_lt hs.wf hp
        change Phi (mutAL s.1 p) ≤ N
        omega
      · intro p hp
        refine ih (mutBP s p) (hs.mutB hp) ?_
        have := Phi_mutB_lt hs.wf hp
        change Phi (mutBL s.1 p) ≤ N
        omega

theorem hitNP_eq_of_le {s : PSt n} (hs : WFP s) {N M : ℕ}
    (hN : Phi s.1 ≤ N) (hNM : N ≤ M) :
    hitNP ζA ζB θA θB 0 M s = hitNP ζA ζB θA θB 0 N s := by
  induction M, hNM using Nat.le_induction with
  | base => rfl
  | succ M hM ih => rw [hitNP_stab M s hs (hN.trans hM), ih]

theorem hitNP_monotone (hθA : 0 < θA) (hθB : 0 < θB) {s : PSt n} (hw : WF s.1) :
    Monotone fun N => hitNP ζA ζB θA θB 0 N s :=
  monotone_nat_of_le_succ fun N => hitNP_mono hθA hθB le_rfl N hw

theorem PPst_eq_hitNP (hθA : 0 < θA) (hθB : 0 < θB) {s : PSt n} (hs : WFP s) {N : ℕ}
    (hN : Phi s.1 ≤ N) : PPst θA θB 0 ζA ζB s = hitNP ζA ζB θA θB 0 N s := by
  have hbdd : BddAbove (Set.range fun M => hitNP ζA ζB θA θB 0 M s) :=
    ⟨1, by rintro x ⟨M, rfl⟩; exact hitNP_le_one hθA hθB le_rfl M hs⟩
  refine le_antisymm (ciSup_le fun M => ?_) (le_ciSup hbdd N)
  rcases le_total M N with hMN | hNM
  · exact hitNP_monotone hθA hθB hs.wf hMN
  · exact le_of_eq (hitNP_eq_of_le hs hN hNM)

theorem esfKernel_eq_hitNP (hθA : 0 < θA) (hθB : 0 < θB) {N : ℕ}
    (hN : Phi (fullState n) ≤ N) :
    esfKernel θA θB 0 ζA ζB = hitNP ζA ζB θA θB 0 N (initP n) :=
  PPst_eq_hitNP hθA hθB wfp_initP hN

end Rhone.Coalescent.PartitionCarryingChain
