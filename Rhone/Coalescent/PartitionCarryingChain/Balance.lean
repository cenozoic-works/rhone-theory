/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.PartitionCarryingChain.OneLoc

/-! # The balance equation, and the identification of the star-weighted chain -/

@[expose] public section

namespace Rhone.Coalescent.PartitionCarryingChain

open Finset TwoLocusGenealogy TypedAncestralChain EsfPair
open LinearAlgebra.Recursion

variable {n K : ℕ} {θA θB : ℝ} {σ : Fin n → Fin K} {π : Fin K → ℝ} {L : Finset (Lin n)}

theorem sum_uStar_L (σ : Fin n → Fin K) (L : Finset (Lin n)) (i : Fin K) :
    (∑ p ∈ L, ((uStar σ p i : ℕ) : ℝ)) = ((scount σ L i : ℕ) : ℝ) := by
  rw [scount, Nat.cast_sum]

theorem sum_scount_eq_sum_stI (hmono : MonoStars σ L) :
    (∑ i, ((scount σ L i : ℕ) : ℝ)) = ∑ p ∈ L, stI p := by
  have h1 : ∀ i : Fin K, ((scount σ L i : ℕ) : ℝ) = ∑ p ∈ L, ((uStar σ p i : ℕ) : ℝ) :=
    fun i => (sum_uStar_L σ L i).symm
  rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_comm]
  exact Finset.sum_congr rfl fun p hp => sum_uStar (hmono p hp)

theorem empty_star_of_notMem_carA {p : Lin n} (hpL : p ∈ L) (hpn : p ∉ carA L) :
    p.1 ∩ p.2 = ∅ := by
  have h1 : p.1 = ∅ := by
    by_contra hc
    exact hpn (mem_carA.2 ⟨hpL, Finset.nonempty_iff_ne_empty.2 hc⟩)
  rw [h1, Finset.empty_inter]

theorem empty_star_of_notMem_carB {p : Lin n} (hpL : p ∈ L) (hpn : p ∉ carB L) :
    p.1 ∩ p.2 = ∅ := by
  have h1 : p.2 = ∅ := by
    by_contra hc
    exact hpn (mem_carB.2 ⟨hpL, Finset.nonempty_iff_ne_empty.2 hc⟩)
  rw [h1, Finset.inter_empty]

theorem sum_stI_carA : (∑ p ∈ carA L, stI p) = ∑ p ∈ L, stI p :=
  Finset.sum_subset (carA_subset L) fun _p hpL hpn =>
    stI_of_empty (empty_star_of_notMem_carA hpL hpn)

theorem sum_stI_carB : (∑ p ∈ carB L, stI p) = ∑ p ∈ L, stI p :=
  Finset.sum_subset (carB_subset L) fun _p hpL hpn =>
    stI_of_empty (empty_star_of_notMem_carB hpL hpn)

theorem sum_uStar_carA (i : Fin K) :
    (∑ p ∈ carA L, ((uStar σ p i : ℕ) : ℝ)) = ((scount σ L i : ℕ) : ℝ) := by
  rw [← sum_uStar_L σ L i]
  refine Finset.sum_subset (carA_subset L) fun p hpL hpn => ?_
  rw [uStar_eq_zero_of_empty (empty_star_of_notMem_carA hpL hpn) i]
  norm_num

theorem sum_uStar_carB (i : Fin K) :
    (∑ p ∈ carB L, ((uStar σ p i : ℕ) : ℝ)) = ((scount σ L i : ℕ) : ℝ) := by
  rw [← sum_uStar_L σ L i]
  refine Finset.sum_subset (carB_subset L) fun p hpL hpn => ?_
  rw [uStar_eq_zero_of_empty (empty_star_of_notMem_carB hpL hpn) i]
  norm_num

theorem scount_empty (σ : Fin n → Fin K) : scount σ (∅ : Finset (Lin n)) = fun _ => 0 := by
  funext i
  rw [scount, Finset.sum_empty]

theorem sw_identity (hθ : 0 < θA + θB) (hw : WF L) (hal : Aligned L) :
    (∑ p ∈ L, ∑ q ∈ L.erase p, Vst σ π θA θB (coalL L p q))
      + θA * (∑ p ∈ carA L, mstar σ π p * Vst σ π θA θB (mutAL L p))
      + θB * (∑ p ∈ carB L, mstar σ π p * Vst σ π θA θB (mutBL L p))
      = dtot θA θB 0 L * Vst σ π θA θB L := by
  have hdtot : dtot θA θB 0 L
      = (L.card : ℝ) * ((L.card : ℝ) - 1) + θA * ((na L : ℕ) : ℝ) + θB * ((nb L : ℕ) : ℝ) := by
    rw [dtot, natCast_mul_pred]
    ring
  by_cases hmono : MonoStars σ L
  · have hV : Vst σ π θA θB L = qOne (θA + θB) π (scount σ L) := Vst_of_mono hmono
    have hS : (∑ i, ((scount σ L i : ℕ) : ℝ)) = ∑ p ∈ L, stI p := sum_scount_eq_sum_stI hmono
    have hC : (∑ p ∈ L, ∑ q ∈ L.erase p, Vst σ π θA θB (coalL L p q))
        = ((L.card : ℝ) * ((L.card : ℝ) - 1)
            - ((∑ i, ((scount σ L i : ℕ) : ℝ)) * (∑ i, ((scount σ L i : ℕ) : ℝ))
                - ∑ i, ((scount σ L i : ℕ) : ℝ))) * Vst σ π θA θB L
          + ∑ i, (((scount σ L i : ℕ) : ℝ) * ((scount σ L i : ℕ) : ℝ)
              - ((scount σ L i : ℕ) : ℝ)) * qOne (θA + θB) π (decf (scount σ L) i) := by
      have hterm : ∀ p ∈ L, ∀ q ∈ L.erase p, Vst σ π θA θB (coalL L p q)
          = (1 - stI p * stI q) * Vst σ π θA θB L
            + ∑ i, (((uStar σ p i : ℕ) : ℝ) * ((uStar σ q i : ℕ) : ℝ))
                * qOne (θA + θB) π (decf (scount σ L) i) :=
        fun p hp q hq => Vst_coalL hw hal hmono hp hq
      rw [Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun q hq => hterm p hp q hq,
        Finset.sum_congr rfl fun p _ => Finset.sum_add_distrib, Finset.sum_add_distrib]
      congr 1
      · have h1 : ∀ p ∈ L, (∑ q ∈ L.erase p, (1 - stI p * stI q) * Vst σ π θA θB L)
            = ((∑ _q ∈ L.erase p, (1 : ℝ)) - ∑ q ∈ L.erase p, stI p * stI q)
              * Vst σ π θA θB L := by
          intro p _
          rw [← Finset.sum_mul, Finset.sum_sub_distrib]
        rw [Finset.sum_congr rfl h1, ← Finset.sum_mul, Finset.sum_sub_distrib,
          sum_pair_card, sum_pair_offdiag L stI stI_idem, ← hS]
      · rw [Finset.sum_congr rfl fun p _ => Finset.sum_comm, Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        have h2 : ∀ p ∈ L, (∑ q ∈ L.erase p, (((uStar σ p i : ℕ) : ℝ)
              * ((uStar σ q i : ℕ) : ℝ)) * qOne (θA + θB) π (decf (scount σ L) i))
            = (∑ q ∈ L.erase p, ((uStar σ p i : ℕ) : ℝ) * ((uStar σ q i : ℕ) : ℝ))
                * qOne (θA + θB) π (decf (scount σ L) i) :=
          fun p _ => (Finset.sum_mul _ _ _).symm
        rw [Finset.sum_congr rfl h2, ← Finset.sum_mul,
          sum_pair_offdiag L (fun p => ((uStar σ p i : ℕ) : ℝ)) (fun p => uStar_idem σ p i),
          sum_uStar_L σ L i]
    have hA : (∑ p ∈ carA L, mstar σ π p * Vst σ π θA θB (mutAL L p))
        = (((na L : ℕ) : ℝ) - ∑ i, ((scount σ L i : ℕ) : ℝ)) * Vst σ π θA θB L
          + ∑ i, ((scount σ L i : ℕ) : ℝ)
              * (π i * qOne (θA + θB) π (decf (scount σ L) i)) := by
      have hterm : ∀ p ∈ carA L, mstar σ π p * Vst σ π θA θB (mutAL L p)
          = (1 - stI p) * Vst σ π θA θB L
            + ∑ i, ((uStar σ p i : ℕ) : ℝ)
                * (π i * qOne (θA + θB) π (decf (scount σ L) i)) :=
        fun p hp => Vst_mutAL hw hmono (carA_subset L hp)
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
      congr 1
      · have hc1 : (∑ _p ∈ carA L, (1 : ℝ)) = ((na L : ℕ) : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
          rfl
        rw [← Finset.sum_mul, Finset.sum_sub_distrib, hc1, sum_stI_carA, ← hS]
      · rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_mul, sum_uStar_carA i]
    have hB : (∑ p ∈ carB L, mstar σ π p * Vst σ π θA θB (mutBL L p))
        = (((nb L : ℕ) : ℝ) - ∑ i, ((scount σ L i : ℕ) : ℝ)) * Vst σ π θA θB L
          + ∑ i, ((scount σ L i : ℕ) : ℝ)
              * (π i * qOne (θA + θB) π (decf (scount σ L) i)) := by
      have hterm : ∀ p ∈ carB L, mstar σ π p * Vst σ π θA θB (mutBL L p)
          = (1 - stI p) * Vst σ π θA θB L
            + ∑ i, ((uStar σ p i : ℕ) : ℝ)
                * (π i * qOne (θA + θB) π (decf (scount σ L) i)) :=
        fun p hp => Vst_mutBL hw hmono (carB_subset L hp)
      rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
      congr 1
      · have hc1 : (∑ _p ∈ carB L, (1 : ℝ)) = ((nb L : ℕ) : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one]
          rfl
        rw [← Finset.sum_mul, Finset.sum_sub_distrib, hc1, sum_stI_carB, ← hS]
      · rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_mul, sum_uStar_carB i]
    have hkey : ((∑ i, ((scount σ L i : ℕ) : ℝ)) * ((∑ i, ((scount σ L i : ℕ) : ℝ)) - 1)
          + (θA + θB) * ∑ i, ((scount σ L i : ℕ) : ℝ)) * Vst σ π θA θB L
        = (∑ i, (((scount σ L i : ℕ) : ℝ) * ((scount σ L i : ℕ) : ℝ)
              - ((scount σ L i : ℕ) : ℝ)) * qOne (θA + θB) π (decf (scount σ L) i))
          + (θA + θB) * ∑ i, ((scount σ L i : ℕ) : ℝ)
              * (π i * qOne (θA + θB) π (decf (scount σ L) i)) := by
      have hrec := qOne_recursion (θ := θA + θB) (π := π) hθ (scount σ L)
      rw [natCast_mul_pred, Nat.cast_sum] at hrec
      rw [hV, hrec, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [natCast_mul_pred]
      ring
    rw [hC, hA, hB, hdtot]
    linear_combination (-1 : ℝ) * hkey
  · have h0 : Vst σ π θA θB L = 0 := Vst_of_not_mono hmono
    have hc0 : ∀ p ∈ L, ∀ q ∈ L.erase p, Vst σ π θA θB (coalL L p q) = 0 :=
      fun p _ q _ => Vst_of_not_mono (not_monoStars_coalL hmono p q)
    have ha0 : ∀ p ∈ carA L, mstar σ π p * Vst σ π θA θB (mutAL L p) = 0 := by
      intro p _
      by_cases hpm : ∀ k ∈ p.1 ∩ p.2, ∀ l ∈ p.1 ∩ p.2, σ k = σ l
      · have h1 : ¬ MonoStars σ (mutAL L p) := fun hc =>
          not_monoStars_erase hmono hpm (hc.subset erase_subset_mutAL)
        rw [Vst_of_not_mono h1, mul_zero]
      · have hne : p.1 ∩ p.2 ≠ ∅ := by
          intro hc
          refine hpm fun k hk => ?_
          rw [hc] at hk
          exact absurd hk (Finset.notMem_empty k)
        rw [mstar, ite_eq_right hne, matchA_eq_zero hpm, zero_mul]
    have hb0 : ∀ p ∈ carB L, mstar σ π p * Vst σ π θA θB (mutBL L p) = 0 := by
      intro p _
      by_cases hpm : ∀ k ∈ p.1 ∩ p.2, ∀ l ∈ p.1 ∩ p.2, σ k = σ l
      · have h1 : ¬ MonoStars σ (mutBL L p) := fun hc =>
          not_monoStars_erase hmono hpm (hc.subset erase_subset_mutBL)
        rw [Vst_of_not_mono h1, mul_zero]
      · have hne : p.1 ∩ p.2 ≠ ∅ := by
          intro hc
          refine hpm fun k hk => ?_
          rw [hc] at hk
          exact absurd hk (Finset.notMem_empty k)
        rw [mstar, ite_eq_right hne, matchA_eq_zero hpm, zero_mul]
    rw [Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun q hq => hc0 p hp q hq,
      Finset.sum_congr rfl ha0, Finset.sum_congr rfl hb0, h0]
    simp

theorem swN_eq_Vst (hθA : 0 < θA) (hθB : 0 < θB) (σ : Fin n → Fin K) (π : Fin K → ℝ) :
    ∀ (N : ℕ) (L : Finset (Lin n)), WF L → Aligned L → Phi L ≤ N →
      swN σ π θA θB N L = Vst σ π θA θB L := by
  intro N
  induction N with
  | zero =>
    intro L _ _ hN
    have h : L = ∅ := eq_empty_of_Phi_zero (Nat.le_zero.1 hN)
    subst h
    rw [swN_empty, Vst_of_mono monoStars_empty, scount_empty, qOne_zero]
  | succ N ih =>
    intro L hw hal hN
    by_cases h : L = ∅
    · subst h
      rw [swN_empty, Vst_of_mono monoStars_empty, scount_empty, qOne_zero]
    · have hd : 0 < dtot θA θB 0 L :=
        dtot_pos hθA hθB le_rfl hw (Finset.nonempty_iff_ne_empty.2 h)
      have e1 : ∀ p ∈ L, ∀ q ∈ L.erase p,
          swN σ π θA θB N (coalL L p q) = Vst σ π θA θB (coalL L p q) := by
        intro p hp q hq
        refine ih _ (hw.coal hp (Finset.mem_of_mem_erase hq))
          (hal.coal hp (Finset.mem_of_mem_erase hq)) ?_
        have hlt := Phi_coal_lt hp hq
        omega
      have e2 : ∀ p ∈ carA L,
          mstar σ π p * swN σ π θA θB N (mutAL L p)
            = mstar σ π p * Vst σ π θA θB (mutAL L p) := by
        intro p hp
        have hpL := (mem_carA.1 hp).1
        have hlt := Phi_mutA_lt hw hp
        rw [ih _ (hw.mutA hpL) (hal.mutA hpL) (by omega)]
      have e3 : ∀ p ∈ carB L,
          mstar σ π p * swN σ π θA θB N (mutBL L p)
            = mstar σ π p * Vst σ π θA θB (mutBL L p) := by
        intro p hp
        have hpL := (mem_carB.1 hp).1
        have hlt := Phi_mutB_lt hw hp
        rw [ih _ (hw.mutB hpL) (hal.mutB hpL) (by omega)]
      rw [swN_succ_of_ne N h,
        Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun q hq => e1 p hp q hq,
        Finset.sum_congr rfl e2, Finset.sum_congr rfl e3,
        sw_identity (by linarith) hw hal, mul_comm, mul_div_assoc, div_self hd.ne', mul_one]

end Rhone.Coalescent.PartitionCarryingChain
