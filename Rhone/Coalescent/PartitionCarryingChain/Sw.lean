/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.PartitionCarryingChain.Emit

/-! # The star-weighted chain, and the meet-weighted decomposition -/

@[expose] public section

namespace Rhone.Coalescent.PartitionCarryingChain

open Finset TwoLocusGenealogy TypedAncestralChain EsfPair

variable {n K : ℕ} {θA θB : ℝ} {σ : Fin n → Fin K} {π : Fin K → ℝ}

noncomputable def mstar (σ : Fin n → Fin K) (π : Fin K → ℝ) (p : Lin n) : ℝ :=
  if p.1 ∩ p.2 = ∅ then 1 else matchA σ π (p.1 ∩ p.2)

noncomputable def swN (σ : Fin n → Fin K) (π : Fin K → ℝ) (θA θB : ℝ) :
    ℕ → Finset (Lin n) → ℝ
  | 0, L => if L = ∅ then 1 else 0
  | N + 1, L =>
      if L = ∅ then 1
      else ((∑ p ∈ L, ∑ q ∈ L.erase p, swN σ π θA θB N (coalL L p q))
          + θA * (∑ p ∈ carA L, mstar σ π p * swN σ π θA θB N (mutAL L p))
          + θB * (∑ p ∈ carB L, mstar σ π p * swN σ π θA θB N (mutBL L p)))
        / dtot θA θB 0 L

@[simp] theorem swN_empty (N : ℕ) : swN σ π θA θB N (∅ : Finset (Lin n)) = 1 := by
  cases N <;> simp [swN]

theorem swN_zero_of_ne {L : Finset (Lin n)} (h : L ≠ ∅) : swN σ π θA θB 0 L = 0 := by
  rw [swN, ite_eq_right h]

theorem swN_succ_of_ne (N : ℕ) {L : Finset (Lin n)} (h : L ≠ ∅) :
    swN σ π θA θB (N + 1) L
      = ((∑ p ∈ L, ∑ q ∈ L.erase p, swN σ π θA θB N (coalL L p q))
          + θA * (∑ p ∈ carA L, mstar σ π p * swN σ π θA θB N (mutAL L p))
          + θB * (∑ p ∈ carB L, mstar σ π p * swN σ π θA θB N (mutBL L p)))
        / dtot θA θB 0 L := by
  rw [swN, ite_eq_right h]

theorem coalP_fst (s : PSt n) (p q : Lin n) : (coalP s p q).1 = coalL s.1 p q := rfl

theorem mutAP_fst (s : PSt n) (p : Lin n) : (mutAP s p).1 = mutAL s.1 p := rfl

theorem mutBP_fst (s : PSt n) (p : Lin n) : (mutBP s p).1 = mutBL s.1 p := rfl

theorem sum_mul_hitAt (f : Blocks n → Blocks n → ℝ) (s : PSt n) :
    (∑ x : Blocks n × Blocks n, f x.1 x.2 * hitAt x.1 x.2 s) = f s.2.1 s.2.2 := by
  have h : ∀ x : Blocks n × Blocks n, f x.1 x.2 * hitAt x.1 x.2 s
      = if x = (s.2.1, s.2.2) then f s.2.1 s.2.2 else 0 := by
    rintro ⟨a, b⟩
    by_cases hc : s.2.1 = a ∧ s.2.2 = b
    · rw [hitAt, ite_eq_left hc, mul_one, ite_eq_left (by rw [hc.1, hc.2]), hc.1, hc.2]
    · rw [hitAt, ite_eq_right hc, mul_zero, ite_eq_right]
      intro hd
      exact hc ⟨(congrArg Prod.fst hd).symm, (congrArg Prod.snd hd).symm⟩
  rw [Finset.sum_congr rfl fun x _ => h x,
    Finset.sum_ite_eq' Finset.univ (s.2.1, s.2.2) (fun _ => f s.2.1 s.2.2),
    ite_eq_left (Finset.mem_univ _)]

theorem meet_hitNP_weighted (σ : Fin n → Fin K) (π : Fin K → ℝ) (θA θB : ℝ) (N : ℕ)
    {s : PSt n} (hs : Inv s) :
    (∑ x : Blocks n × Blocks n, wA σ π (meet x.1 x.2) * hitNP x.1 x.2 θA θB 0 N s)
      = wA σ π (emitStar s) * swN σ π θA θB N s.1 := by
  induction N generalizing s with
  | zero =>
    by_cases h : s.1 = ∅
    · rw [Finset.sum_congr rfl fun x _ => by rw [hitNP_of_empty 0 h],
        sum_mul_hitAt (fun a b => wA σ π (meet a b)) s, emitStar_of_absorbed hs h,
        show swN σ π θA θB 0 s.1 = 1 by rw [h, swN_empty], mul_one]
    · rw [Finset.sum_congr rfl fun x _ => by rw [hitNP_zero, ite_eq_right h, mul_zero],
        Finset.sum_const_zero, swN_zero_of_ne h, mul_zero]
  | succ N ih =>
    by_cases h : s.1 = ∅
    · rw [Finset.sum_congr rfl fun x _ => by rw [hitNP_of_empty (N + 1) h],
        sum_mul_hitAt (fun a b => wA σ π (meet a b)) s, emitStar_of_absorbed hs h,
        show swN σ π θA θB (N + 1) s.1 = 1 by rw [h, swN_empty], mul_one]
    · set G : PSt n → ℝ := fun t =>
        ∑ x : Blocks n × Blocks n, wA σ π (meet x.1 x.2) * hitNP x.1 x.2 θA θB 0 N t
        with hGdef
      have hG : ∀ t : PSt n, Inv t → G t = wA σ π (emitStar t) * swN σ π θA θB N t.1 :=
        fun t ht => ih ht
      have hcoal : ∀ p ∈ s.1, ∀ q ∈ s.1.erase p,
          G (coalP s p q) = wA σ π (emitStar s) * swN σ π θA θB N (coalL s.1 p q) := by
        intro p hp q hq
        rw [hG _ (hs.coal hp hq), emitStar_coal hs hp hq, coalP_fst]
      have hmutA : ∀ p ∈ carA s.1,
          G (mutAP s p)
            = wA σ π (emitStar s) * (mstar σ π p * swN σ π θA θB N (mutAL s.1 p)) := by
        intro p hp
        rw [hG _ (hs.mutA hp), emitStar_mutA hs hp, mutAP_fst, mstar]
        split_ifs with hz
        · rw [one_mul]
        · rw [wA_insert (star_notMem_emitStar hs (mem_carA.1 hp).1)]
          ring
      have hmutB : ∀ p ∈ carB s.1,
          G (mutBP s p)
            = wA σ π (emitStar s) * (mstar σ π p * swN σ π θA θB N (mutBL s.1 p)) := by
        intro p hp
        rw [hG _ (hs.mutB hp), emitStar_mutB hs hp, mutBP_fst, mstar]
        split_ifs with hz
        · rw [one_mul]
        · rw [wA_insert (star_notMem_emitStar hs (mem_carB.1 hp).1)]
          ring
      have e1 : (∑ p ∈ s.1, ∑ q ∈ s.1.erase p, G (coalP s p q))
          = wA σ π (emitStar s)
            * ∑ p ∈ s.1, ∑ q ∈ s.1.erase p, swN σ π θA θB N (coalL s.1 p q) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun p hp => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun q hq => hcoal p hp q hq
      have e2 : (∑ p ∈ carA s.1, G (mutAP s p))
          = wA σ π (emitStar s)
            * ∑ p ∈ carA s.1, mstar σ π p * swN σ π θA θB N (mutAL s.1 p) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl hmutA
      have e3 : (∑ p ∈ carB s.1, G (mutBP s p))
          = wA σ π (emitStar s)
            * ∑ p ∈ carB s.1, mstar σ π p * swN σ π θA θB N (mutBL s.1 p) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl hmutB
      have hstep : stepP θA θB 0 G s
          = wA σ π (emitStar s)
            * ((∑ p ∈ s.1, ∑ q ∈ s.1.erase p, swN σ π θA θB N (coalL s.1 p q))
              + θA * (∑ p ∈ carA s.1, mstar σ π p * swN σ π θA θB N (mutAL s.1 p))
              + θB * (∑ p ∈ carB s.1, mstar σ π p * swN σ π θA θB N (mutBL s.1 p))) := by
        rw [stepP, e1, e2, e3]
        ring
      calc (∑ x : Blocks n × Blocks n,
              wA σ π (meet x.1 x.2) * hitNP x.1 x.2 θA θB 0 (N + 1) s)
          = (∑ x : Blocks n × Blocks n, wA σ π (meet x.1 x.2)
              * stepP θA θB 0 (hitNP x.1 x.2 θA θB 0 N) s) / dtot θA θB 0 s.1 := by
            rw [Finset.sum_div]
            exact Finset.sum_congr rfl fun x _ => by
              rw [hitNP_succ_of_ne N h, mul_div_assoc]
        _ = stepP θA θB 0 G s / dtot θA θB 0 s.1 := by
            rw [stepP_sum (fun x : Blocks n × Blocks n => wA σ π (meet x.1 x.2))
              (fun x => hitNP x.1 x.2 θA θB 0 N) s, hGdef]
        _ = wA σ π (emitStar s) * swN σ π θA θB (N + 1) s.1 := by
            rw [hstep, swN_succ_of_ne N h, mul_div_assoc]

end Rhone.Coalescent.PartitionCarryingChain
