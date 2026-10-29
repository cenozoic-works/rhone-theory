/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.EsfPair.Chain

/-! # The block weights, and the finite-horizon ESF-pair decomposition -/

@[expose] public section

namespace Rhone.Coalescent.EsfPair

open Finset TwoLocusGenealogy TypedAncestralChain

variable {n KA KB : ℕ} {θA θB ρ : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ}
variable {σA : Fin n → Fin KA} {σB : Fin n → Fin KB}

noncomputable def wA (σA : Fin n → Fin KA) (πA : Fin KA → ℝ) (ζ : Blocks n) : ℝ :=
  ∏ β ∈ ζ, matchA σA πA β

noncomputable def wB (σB : Fin n → Fin KB) (πB : Fin KB → ℝ) (ζ : Blocks n) : ℝ :=
  ∏ γ ∈ ζ, matchB σB πB γ

@[simp] theorem wA_empty : wA σA πA (∅ : Blocks n) = 1 := by simp [wA]

@[simp] theorem wB_empty : wB σB πB (∅ : Blocks n) = 1 := by simp [wB]

theorem wA_insert {ζ : Blocks n} {β : Finset (Fin n)} (h : β ∉ ζ) :
    wA σA πA (insert β ζ) = matchA σA πA β * wA σA πA ζ := by
  rw [wA, wA, Finset.prod_insert h]

theorem wB_insert {ζ : Blocks n} {γ : Finset (Fin n)} (h : γ ∉ ζ) :
    wB σB πB (insert γ ζ) = matchB σB πB γ * wB σB πB ζ := by
  rw [wB, wB, Finset.prod_insert h]

theorem wA_one_allele (ζ : Blocks n) :
    wA (fun _ => (0 : Fin 1)) (fun _ => (1 : ℝ)) ζ = 1 :=
  Finset.prod_eq_one fun β _ => matchA_one_allele β

theorem wB_one_allele (ζ : Blocks n) :
    wB (fun _ => (0 : Fin 1)) (fun _ => (1 : ℝ)) ζ = 1 :=
  Finset.prod_eq_one fun γ _ => matchB_one_allele γ

theorem hitAt_mul {s : PSt n} (x : Blocks n × Blocks n) :
    (wA σA πA x.1 * wB σB πB x.2) * hitAt x.1 x.2 s
      = if x = (s.2.1, s.2.2) then wA σA πA s.2.1 * wB σB πB s.2.2 else 0 := by
  obtain ⟨a, b⟩ := x
  by_cases h : s.2.1 = a ∧ s.2.2 = b
  · rw [hitAt, ite_eq_left h, mul_one, ite_eq_left (by rw [h.1, h.2]), h.1, h.2]
  · rw [hitAt, ite_eq_right h, mul_zero, ite_eq_right]
    intro hc
    exact h ⟨(congrArg Prod.fst hc).symm, (congrArg Prod.snd hc).symm⟩

theorem sum_hitAt (s : PSt n) :
    (∑ x : Blocks n × Blocks n, (wA σA πA x.1 * wB σB πB x.2) * hitAt x.1 x.2 s)
      = wA σA πA s.2.1 * wB σB πB s.2.2 := by
  rw [Finset.sum_congr rfl fun x _ => hitAt_mul (σA := σA) (σB := σB) (πA := πA) (πB := πB) x,
    Finset.sum_ite_eq' Finset.univ (s.2.1, s.2.2)
      (fun _ => wA σA πA s.2.1 * wB σB πB s.2.2), ite_eq_left (Finset.mem_univ _)]

theorem hitNP_weighted (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (N : ℕ) {s : PSt n}
    (hs : WFP s) :
    (∑ x : Blocks n × Blocks n,
        (wA σA πA x.1 * wB σB πB x.2) * hitNP x.1 x.2 θA θB ρ N s)
      = wA σA πA s.2.1 * wB σB πB s.2.2 * hitN σA σB θA θB ρ πA πB N s.1 := by
  induction N generalizing s with
  | zero =>
    by_cases h : s.1 = ∅
    · rw [Finset.sum_congr rfl fun x _ => by rw [hitNP_of_empty 0 h], sum_hitAt,
        h, hitN_empty, mul_one]
    · rw [Finset.sum_congr rfl fun x _ => by rw [hitNP_zero, ite_eq_right h, mul_zero],
        Finset.sum_const_zero, hitN, ite_eq_right h, mul_zero]
  | succ N ih =>
    by_cases h : s.1 = ∅
    · rw [Finset.sum_congr rfl fun x _ => by rw [hitNP_of_empty (N + 1) h], sum_hitAt,
        h, hitN_empty, mul_one]
    · have hd : 0 < dtot θA θB ρ s.1 :=
        dtot_pos hθA hθB hρ hs.wf (Finset.nonempty_iff_ne_empty.2 h)
      set W : ℝ := wA σA πA s.2.1 * wB σB πB s.2.2 with hW
      set G : PSt n → ℝ := fun t =>
        ∑ x : Blocks n × Blocks n, (wA σA πA x.1 * wB σB πB x.2) * hitNP x.1 x.2 θA θB ρ N t
        with hGdef
      have hG : ∀ t : PSt n, WFP t →
          G t = wA σA πA t.2.1 * wB σB πB t.2.2 * hitN σA σB θA θB ρ πA πB N t.1 :=
        fun t ht => ih ht
      have hcoal : ∀ p ∈ s.1, ∀ q ∈ s.1.erase p,
          G (coalP s p q) = W * hitN σA σB θA θB ρ πA πB N (coalL s.1 p q) :=
        fun p hp q hq => hG (coalP s p q) (hs.coal hp hq)
      have hrec : ∀ p ∈ carC s.1,
          G (recP s p) = W * hitN σA σB θA θB ρ πA πB N (recL s.1 p) := by
        intro p hp
        obtain ⟨hpL, h1, h2⟩ := mem_carC.1 hp
        exact hG (recP s p) (hs.recomb hpL h1 h2)
      have hmutA : ∀ p ∈ carA s.1,
          G (mutAP s p)
            = W * (matchA σA πA p.1 * hitN σA σB θA θB ρ πA πB N (mutAL s.1 p)) := by
        intro p hp
        have h1 : G (mutAP s p) = wA σA πA (insert p.1 s.2.1) * wB σB πB s.2.2
            * hitN σA σB θA θB ρ πA πB N (mutAL s.1 p) := hG (mutAP s p) (hs.mutA hp)
        rw [h1, wA_insert (notMem_emittedA hs hp), hW]
        ring
      have hmutB : ∀ p ∈ carB s.1,
          G (mutBP s p)
            = W * (matchB σB πB p.2 * hitN σA σB θA θB ρ πA πB N (mutBL s.1 p)) := by
        intro p hp
        have h1 : G (mutBP s p) = wA σA πA s.2.1 * wB σB πB (insert p.2 s.2.2)
            * hitN σA σB θA θB ρ πA πB N (mutBL s.1 p) := hG (mutBP s p) (hs.mutB hp)
        rw [h1, wB_insert (notMem_emittedB hs hp), hW]
        ring
      have e1 : (∑ p ∈ s.1, ∑ q ∈ s.1.erase p, G (coalP s p q))
          = W * ∑ p ∈ s.1, ∑ q ∈ s.1.erase p,
              hitN σA σB θA θB ρ πA πB N (coalL s.1 p q) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun p hp => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun q hq => hcoal p hp q hq
      have e2 : (∑ p ∈ carA s.1, G (mutAP s p))
          = W * ∑ p ∈ carA s.1,
              matchA σA πA p.1 * hitN σA σB θA θB ρ πA πB N (mutAL s.1 p) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl hmutA
      have e3 : (∑ p ∈ carB s.1, G (mutBP s p))
          = W * ∑ p ∈ carB s.1,
              matchB σB πB p.2 * hitN σA σB θA θB ρ πA πB N (mutBL s.1 p) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl hmutB
      have e4 : (∑ p ∈ carC s.1, G (recP s p))
          = W * ∑ p ∈ carC s.1, hitN σA σB θA θB ρ πA πB N (recL s.1 p) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl hrec
      have hstep : stepP θA θB ρ G s
          = W * step σA σB θA θB ρ πA πB (hitN σA σB θA θB ρ πA πB N) s.1 := by
        rw [stepP, step, e1, e2, e3, e4]
        ring
      calc (∑ x : Blocks n × Blocks n,
              (wA σA πA x.1 * wB σB πB x.2) * hitNP x.1 x.2 θA θB ρ (N + 1) s)
          = (∑ x : Blocks n × Blocks n, (wA σA πA x.1 * wB σB πB x.2)
              * stepP θA θB ρ (hitNP x.1 x.2 θA θB ρ N) s) / dtot θA θB ρ s.1 := by
            rw [Finset.sum_div]
            exact Finset.sum_congr rfl fun x _ => by
              rw [hitNP_succ_of_ne N h, mul_div_assoc]
        _ = stepP θA θB ρ G s / dtot θA θB ρ s.1 := by
            rw [stepP_sum (fun x : Blocks n × Blocks n => wA σA πA x.1 * wB σB πB x.2)
              (fun x => hitNP x.1 x.2 θA θB ρ N) s, hGdef]
        _ = W * hitN σA σB θA θB ρ πA πB (N + 1) s.1 := by
            rw [hstep, hitN_succ_of_ne N h, mul_div_assoc]

theorem sum_hitNP_eq_absN (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (N : ℕ) {s : PSt n}
    (hs : WFP s) :
    (∑ x : Blocks n × Blocks n, hitNP x.1 x.2 θA θB ρ N s) = absN θA θB ρ N s.1 := by
  have h := hitNP_weighted (σA := fun _ => (0 : Fin 1)) (σB := fun _ => (0 : Fin 1))
    (πA := fun _ => (1 : ℝ)) (πB := fun _ => (1 : ℝ)) hθA hθB hρ N hs
  rw [wA_one_allele, wB_one_allele, one_mul, one_mul, ← absN_eq_hitN] at h
  rw [← h]
  exact Finset.sum_congr rfl fun x _ => by
    rw [wA_one_allele, wB_one_allele, one_mul, one_mul]

end Rhone.Coalescent.EsfPair
