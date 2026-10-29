/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.InfiniteAllelesLimit.Colour
public import Rhone.Probability.InfiniteAllelesLimit.Interp

/-! # Steps 1 and 2: `P` is a fixed, `ρ`-free linear functional of finitely many `q`-values -/

@[expose] public section

namespace Rhone.Coalescent.InfiniteAllelesLimit

open Finset Polynomial TwoLocusGenealogy EsfPair LinearAlgebra.Recursion

variable {n : ℕ} {θA θB ρ x y : ℝ} {ζA ζB ηA ηB : Blocks n}

def refSet (ζ : Blocks n) : Finset (Blocks n) :=
  (partsOf (Finset.univ : Finset (Fin n))).filter fun η => Refines η ζ

theorem mem_refSet : ηA ∈ refSet ζA ↔
    IsPartOf (Finset.univ : Finset (Fin n)) ηA ∧ Refines ηA ζA := by
  simp [refSet]

theorem self_mem_refSet (h : IsPartOf (Finset.univ : Finset (Fin n)) ζA) : ζA ∈ refSet ζA :=
  mem_refSet.2 ⟨h, fun β hβ => ⟨β, hβ, subset_rfl⟩⟩

theorem card_le_of_mem_refSet (h : ηA ∈ refSet ζA) : ηA.card ≤ n :=
  card_le_of_isPartOf (mem_refSet.1 h).1

noncomputable def wSample (ζA ζB : Blocks n) : Config (numCols n) (numCols n) :=
  cSample (colourOf ζA) (colourOf ζB)

noncomputable def qWin (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (ζA ζB : Blocks n)
    (x y : ℝ) : ℝ :=
  LinearAlgebra.Recursion.q (πA := piWin ζA x) (πB := piWin ζB y) hθA hθB hρ (wSample ζA ζB)

theorem qWin_eq_sum (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hA : IsPartOf (Finset.univ : Finset (Fin n)) ζA)
    (hB : IsPartOf (Finset.univ : Finset (Fin n)) ζB)
    (hx : 0 ≤ x) (hxm : (ζA.card : ℝ) * x ≤ 1)
    (hy : 0 ≤ y) (hym : (ζB.card : ℝ) * y ≤ 1) :
    qWin hθA hθB hρ ζA ζB x y
      = ∑ ηA ∈ refSet ζA, ∑ ηB ∈ refSet ζB,
          esfKernel θA θB ρ ηA ηB * x ^ ηA.card * y ^ ηB.card := by
  have hzA : ∀ ηA : Blocks n, ηA ∉ refSet ζA → ∀ ηB : Blocks n,
      esfKernel θA θB ρ ηA ηB * wA (colourOf ζA) (piWin ζA x) ηA
        * wB (colourOf ζB) (piWin ζB y) ηB = 0 := by
    intro ηA hηA ηB
    by_cases hp : IsPartOf (Finset.univ : Finset (Fin n)) ηA
    · have hnr : ¬ Refines ηA ζA := fun hc => hηA (mem_refSet.2 ⟨hp, hc⟩)
      rw [wA_piWin hA hp, ite_eq_right hnr, mul_zero, zero_mul]
    · rw [esfKernel_eq_zero_of_not_part fun hc => hp hc.1, zero_mul, zero_mul]
  have hzB : ∀ ηA : Blocks n, ∀ ηB : Blocks n, ηB ∉ refSet ζB →
      esfKernel θA θB ρ ηA ηB * wA (colourOf ζA) (piWin ζA x) ηA
        * wB (colourOf ζB) (piWin ζB y) ηB = 0 := by
    intro ηA ηB hηB
    by_cases hp : IsPartOf (Finset.univ : Finset (Fin n)) ηB
    · have hnr : ¬ Refines ηB ζB := fun hc => hηB (mem_refSet.2 ⟨hp, hc⟩)
      rw [show wB (colourOf ζB) (piWin ζB y) ηB = wA (colourOf ζB) (piWin ζB y) ηB from rfl,
        wA_piWin hB hp, ite_eq_right hnr, mul_zero]
    · rw [esfKernel_eq_zero_of_not_part fun hc => hp hc.2, zero_mul, zero_mul]
  have hval : ∀ ηA ∈ refSet ζA, ∀ ηB ∈ refSet ζB,
      esfKernel θA θB ρ ηA ηB * wA (colourOf ζA) (piWin ζA x) ηA
        * wB (colourOf ζB) (piWin ζB y) ηB
        = esfKernel θA θB ρ ηA ηB * x ^ ηA.card * y ^ ηB.card := by
    intro ηA hηA ηB hηB
    obtain ⟨hpA, hrA⟩ := mem_refSet.1 hηA
    obtain ⟨hpB, hrB⟩ := mem_refSet.1 hηB
    rw [wA_piWin hA hpA, ite_eq_left hrA,
      show wB (colourOf ζB) (piWin ζB y) ηB = wA (colourOf ζB) (piWin ζB y) ηB from rfl,
      wA_piWin hB hpB, ite_eq_left hrB]
  rw [qWin, wSample, esf_pair_decomposition hθA hθB hρ (piWin_nonneg hx hxm) (piWin_sum_one hA)
      (piWin_nonneg hy hym) (piWin_sum_one hB),
    ← Finset.sum_subset (Finset.subset_univ (refSet ζA))
      (fun ηA _ h => Finset.sum_eq_zero fun ηB _ => hzA ηA h ηB)]
  refine Finset.sum_congr rfl fun ηA hηA => ?_
  rw [← Finset.sum_subset (Finset.subset_univ (refSet ζB))
    (fun ηB _ h => hzB ηA ηB h)]
  exact Finset.sum_congr rfl fun ηB hηB => hval ηA hηA ηB hηB

noncomputable def polY (θA θB ρ x : ℝ) (ζA ζB : Blocks n) : Polynomial ℝ :=
  ∑ ηB ∈ refSet ζB,
    Polynomial.C (∑ ηA ∈ refSet ζA, esfKernel θA θB ρ ηA ηB * x ^ ηA.card)
      * Polynomial.X ^ ηB.card

theorem polY_degree_le : (polY θA θB ρ x ζA ζB).degree ≤ (n : WithBot ℕ) :=
  Probability.InfiniteAllelesLimit.degree_sum_monomial_le _ _ _ _ fun _ h => card_le_of_mem_refSet h

theorem polY_eval (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hA : IsPartOf (Finset.univ : Finset (Fin n)) ζA)
    (hB : IsPartOf (Finset.univ : Finset (Fin n)) ζB)
    (hx : 0 ≤ x) (hxm : (ζA.card : ℝ) * x ≤ 1)
    (hy : 0 ≤ y) (hym : (ζB.card : ℝ) * y ≤ 1) :
    (polY θA θB ρ x ζA ζB).eval y = qWin hθA hθB hρ ζA ζB x y := by
  rw [qWin_eq_sum hθA hθB hρ hA hB hx hxm hy hym, polY, Polynomial.eval_finsetSum,
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun ηB _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    Finset.sum_mul]

theorem polY_coeff (hB : IsPartOf (Finset.univ : Finset (Fin n)) ζB) :
    (polY θA θB ρ x ζA ζB).coeff ζB.card
      = ∑ ηA ∈ refSet ζA, esfKernel θA θB ρ ηA ζB * x ^ ηA.card := by
  have hsingle : ∀ ηB ∈ refSet ζB, ηB ≠ ζB →
      (if ζB.card = ηB.card then
        (∑ ηA ∈ refSet ζA, esfKernel θA θB ρ ηA ηB * x ^ ηA.card) else 0) = 0 := by
    intro ηB hηB hne
    obtain ⟨hp, hr⟩ := mem_refSet.1 hηB
    exact ite_eq_right fun hc => hne (eq_of_refines_of_card_eq hp hB hr hc.symm)
  rw [polY, Probability.InfiniteAllelesLimit.sum_monomial_coeff,
    Finset.sum_eq_single ζB hsingle (fun h => absurd (self_mem_refSet hB) h), ite_eq_left rfl]

noncomputable def polX (θA θB ρ : ℝ) (ζA ζB : Blocks n) : Polynomial ℝ :=
  ∑ ηA ∈ refSet ζA, Polynomial.C (esfKernel θA θB ρ ηA ζB) * Polynomial.X ^ ηA.card

theorem polX_degree_le : (polX θA θB ρ ζA ζB).degree ≤ (n : WithBot ℕ) :=
  Probability.InfiniteAllelesLimit.degree_sum_monomial_le _ _ _ _ fun _ h => card_le_of_mem_refSet h

theorem polX_eval (hB : IsPartOf (Finset.univ : Finset (Fin n)) ζB) :
    (polX θA θB ρ ζA ζB).eval x = (polY θA θB ρ x ζA ζB).coeff ζB.card := by
  rw [polY_coeff hB, polX, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun ηA _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

theorem polX_coeff (hA : IsPartOf (Finset.univ : Finset (Fin n)) ζA) :
    (polX θA θB ρ ζA ζB).coeff ζA.card = esfKernel θA θB ρ ζA ζB := by
  have hsingle : ∀ ηA ∈ refSet ζA, ηA ≠ ζA →
      (if ζA.card = ηA.card then esfKernel θA θB ρ ηA ζB else 0) = 0 := by
    intro ηA hηA hne
    obtain ⟨hp, hr⟩ := mem_refSet.1 hηA
    exact ite_eq_right fun hc => hne (eq_of_refines_of_card_eq hp hA hr hc.symm)
  rw [polX, Probability.InfiniteAllelesLimit.sum_monomial_coeff,
    Finset.sum_eq_single ζA hsingle (fun h => absurd (self_mem_refSet hA) h), ite_eq_left rfl]

noncomputable def wgtA (ζA : Blocks n) (k : Fin (n + 1)) : ℝ :=
  Probability.InfiniteAllelesLimit.exWeight Finset.univ
      (Probability.InfiniteAllelesLimit.xnode ζA.card n) ζA.card k

theorem esfKernel_eq_sum_q (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hA : IsPartOf (Finset.univ : Finset (Fin n)) ζA)
    (hB : IsPartOf (Finset.univ : Finset (Fin n)) ζB) :
    esfKernel θA θB ρ ζA ζB
      = ∑ k : Fin (n + 1), ∑ l : Fin (n + 1),
          wgtA ζA k * wgtA ζB l
            * qWin hθA hθB hρ ζA ζB (Probability.InfiniteAllelesLimit.xnode ζA.card n k)
                (Probability.InfiniteAllelesLimit.xnode ζB.card n l) := by
  have hxstep : ∀ k : Fin (n + 1),
      (polX θA θB ρ ζA ζB).eval (Probability.InfiniteAllelesLimit.xnode ζA.card n k)
        = ∑ l : Fin (n + 1), wgtA ζB l
            * qWin hθA hθB hρ ζA ζB (Probability.InfiniteAllelesLimit.xnode ζA.card n k)
                (Probability.InfiniteAllelesLimit.xnode ζB.card n l) := by
    intro k
    rw [polX_eval hB, ← Probability.InfiniteAllelesLimit.sum_exWeight_xnode ζB.card ζB.card
        (polY θA θB ρ
      (Probability.InfiniteAllelesLimit.xnode ζA.card n k) ζA ζB) polY_degree_le]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [wgtA, polY_eval hθA hθB hρ hA hB Probability.InfiniteAllelesLimit.xnode_nonneg
        Probability.InfiniteAllelesLimit.mul_xnode_le_one
        Probability.InfiniteAllelesLimit.xnode_nonneg
      Probability.InfiniteAllelesLimit.mul_xnode_le_one]
  rw [← polX_coeff (θA := θA) (θB := θB) (ρ := ρ) (ζB := ζB) hA,
    ← Probability.InfiniteAllelesLimit.sum_exWeight_xnode ζA.card ζA.card (polX θA θB ρ ζA ζB)
        polX_degree_le]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hxstep k, wgtA, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

end Rhone.Coalescent.InfiniteAllelesLimit
