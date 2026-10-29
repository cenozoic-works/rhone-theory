/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.EsfPair.Marginal
public import Rhone.Statistics.AllelicPartitionEwens

/-!
# Ewens sampling formula for the allelic partition of the marked Kingman coalescent

Source: ewens1972, eq. (23), (29)–(30), eq. (A3), pp. 95, 100–102, 107; berestycki2009, Thm 2.9, eq.
(40); kingman1982, sec. 1, eq. (1.1)–(1.4), (1.7). -/

@[expose] public section
namespace Rhone.Statistics
open MeasureTheory Finset Rhone.LinearAlgebra MarkovChain Coalescent Rhone.Combinatorics Probability
open EsfPair Recursion
open scoped NNReal ENNReal

variable {n : ℕ}

local notation "wz(" θ ", " n ", " z ")" =>
  FinChain.pathProduct (RateChain.jumpChain (partitionChain (Fin n))) (n - 1)
    (fun k π => killLevelFactor θ π (z k)) ⊥

theorem rising_eq_ascPochhammer_eval (θ : ℝ) (k : ℕ) :
    rising θ k = (ascPochhammer ℝ k).eval θ := by
  induction k with
  | zero => simp
  | succ k ih => rw [rising_succ, ascPochhammer_succ_eval, ih]

theorem isPartOf_parts (P : Finpartition (univ : Finset (Fin n))) :
    IsPartOf (univ : Finset (Fin n)) P.parts where
  ne := fun _ hβ => P.nonempty_of_mem_parts hβ
  pd := fun _ hβ _ hβ' hne => P.disjoint hβ hβ' hne
  cover := P.biUnion_parts

theorem exists_finpartition_of_isPartOf {ζ : Blocks n}
    (h : IsPartOf (univ : Finset (Fin n)) ζ) :
    ∃ P : Finpartition (univ : Finset (Fin n)), P.parts = ζ := by
  refine ⟨{ parts := ζ, supIndep := ?_, sup_parts := ?_, bot_notMem := ?_ }, rfl⟩
  · rw [Finset.supIndep_iff_pairwiseDisjoint]
    intro β hβ β' hβ' hne
    exact h.pd β hβ β' hβ' hne
  · rw [Finset.sup_eq_biUnion]
    exact h.cover
  · exact h.empty_notMem

theorem esfPart_parts (n : ℕ) (θ : ℝ) (P : Finpartition (univ : Finset (Fin n))) :
    esfPart n θ P.parts =
      θ ^ P.parts.card * (∏ B ∈ P.parts, ((B.card - 1).factorial : ℝ)) /
        (ascPochhammer ℝ n).eval θ := by
  rw [esfPart, ite_eq_left (isPartOf_parts P), rising_eq_ascPochhammer_eval]

theorem esf_mul_eq_factorial_mul_esfPart (n : ℕ) (θ : ℝ)
    (P : Finpartition (univ : Finset (Fin n))) (p : Nat.Partition n)
    (hp : P.parts.val.map Finset.card = p.parts) :
    ((∏ B ∈ P.parts, (B.card.factorial : ℝ)) *
        ∏ j ∈ p.parts.toFinset, ((p.parts.count j).factorial : ℝ)) * esf θ p =
      (n.factorial : ℝ) * esfPart n θ P.parts := by
  have hcard : p.parts.card = P.parts.card := by
    rw [← hp, Multiset.card_map]
    rfl
  have hprod : ((p.parts.prod : ℕ) : ℝ) = ∏ B ∈ P.parts, (B.card : ℝ) := by
    rw [← hp, ← Nat.cast_prod]
    rfl
  have hfac : (∏ B ∈ P.parts, (B.card.factorial : ℝ)) =
      (∏ B ∈ P.parts, (B.card : ℝ)) * ∏ B ∈ P.parts, ((B.card - 1).factorial : ℝ) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun B hB => ?_
    have hpos : B.card ≠ 0 := (Finset.card_pos.2 (P.nonempty_of_mem_parts hB)).ne'
    rw [← Nat.cast_mul, Nat.mul_factorial_pred hpos]
  have ha : (∏ B ∈ P.parts, (B.card : ℝ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun B hB =>
      Nat.cast_ne_zero.2 (Finset.card_pos.2 (P.nonempty_of_mem_parts hB)).ne'
  have hC : (∏ j ∈ p.parts.toFinset, ((p.parts.count j).factorial : ℝ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun j _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  rw [esfPart_parts, esf, partWeight, hcard, hprod, hfac]
  generalize (∏ B ∈ P.parts, (B.card : ℝ)) = a at ha ⊢
  generalize (∏ j ∈ p.parts.toFinset, ((p.parts.count j).factorial : ℝ)) = C at hC ⊢
  have hcancel : ∀ b : ℝ, a * b * C * (a * C)⁻¹ = b := fun b => by field_simp
  calc a * (∏ B ∈ P.parts, ((B.card - 1).factorial : ℝ)) * C *
        ((n.factorial : ℝ) * θ ^ P.parts.card * (a * C)⁻¹ / (ascPochhammer ℝ n).eval θ)
      = (a * (∏ B ∈ P.parts, ((B.card - 1).factorial : ℝ)) * C * (a * C)⁻¹) *
          ((n.factorial : ℝ) * θ ^ P.parts.card) / (ascPochhammer ℝ n).eval θ := by ring
    _ = (n.factorial : ℝ) * (θ ^ P.parts.card *
          (∏ B ∈ P.parts, ((B.card - 1).factorial : ℝ)) / (ascPochhammer ℝ n).eval θ) := by
        rw [hcancel]
        ring

theorem labelWeight_of_labelsMatch {κ : Type*} [DecidableEq κ] (θ : ℝ)
    {P : Finpartition (univ : Finset (Fin n))} {c : Fin n → κ} (h : labelsMatch P c) :
    labelWeight θ ((univ : Finset (Fin n)).val.map c) = esfPart n θ P.parts := by
  have hT := labelType_of_labelsMatch h
  have h1 : ((univ : Finset (Fin n)).val.map c).toFinset.card = P.parts.card := by
    have := congrArg Multiset.card hT
    rw [labelType, Multiset.card_map, Multiset.card_map] at this
    exact this
  have h2 : (∏ t ∈ ((univ : Finset (Fin n)).val.map c).toFinset,
        ((((univ : Finset (Fin n)).val.map c).count t - 1).factorial : ℝ)) =
      ∏ B ∈ P.parts, ((B.card - 1).factorial : ℝ) := by
    have := congrArg (fun s : Multiset ℕ => (s.map fun m => ((m - 1).factorial : ℝ)).prod) hT
    simp only [labelType, Multiset.map_map] at this
    exact this
  have h3 : ((univ : Finset (Fin n)).val.map c).card = n := by
    rw [Multiset.card_map]
    exact (Finset.card_univ).trans (Fintype.card_fin n)
  rw [esfPart, ite_eq_left (isPartOf_parts P), labelWeight, h1, h2, h3]
  rfl

theorem sum_pathProduct_parts_eq {θ : ℝ} (hθ : 0 < θ) (ζ : Blocks n) :
    (∑ z : Fin (n - 1) → Finset (Finset (Fin n)),
      if (patternFinpartition z).parts = ζ then wz(θ, n, z) else 0) = esfPart n θ ζ := by
  by_cases hζ : IsPartOf (univ : Finset (Fin n)) ζ
  · obtain ⟨P, rfl⟩ := exists_finpartition_of_isPartOf hζ
    have hc : labelsMatch P (fun a => P.part a) := fun a b =>
      (P.mem_part_iff_part_eq_part (mem_univ b) (mem_univ a)).trans eq_comm
    have hiff : ∀ z : Fin (n - 1) → Finset (Finset (Fin n)),
        (patternFinpartition z).parts = P.parts ↔
          patternMatches univ z (fun a => P.part a) := by
      intro z
      rw [patternMatches_univ_iff]
      constructor
      · intro h
        rw [Finpartition.ext h]
        exact hc
      · intro h
        have : patternFinpartition z = P := eq_of_part_eq fun a => by
          ext b
          rw [h a b, hc a b]
        rw [this]
    rw [← labelWeight_of_labelsMatch θ hc, ← killingWeight_bot,
      ← patternSum_eq hθ (n - 1) ⊥ (by
        rw [Finpartition.card_bot, Finset.card_univ, Fintype.card_fin]
        omega) univ (fun a => P.part a)]
    exact Finset.sum_congr rfl fun z _ => if_congr (hiff z) rfl rfl
  · rw [esfPart_eq_zero hζ]
    refine Finset.sum_eq_zero fun z _ => ite_eq_right fun h => hζ ?_
    rw [← h]
    exact isPartOf_parts _

theorem sum_esfPart_blockType {θ : ℝ} (hθ : 0 < θ) (p : Nat.Partition n) :
    (∑ ζ : Blocks n, if ζ.val.map Finset.card = p.parts then esfPart n θ ζ else 0) =
      esf θ p := by
  rw [← sum_pathProduct_patternFinpartition hθ p]
  have hz : ∀ z : Fin (n - 1) → Finset (Finset (Fin n)),
      (if (patternFinpartition z).parts.val.map Finset.card = p.parts then wz(θ, n, z)
        else 0) =
      ∑ ζ : Blocks n, if ζ.val.map Finset.card = p.parts then
        (if (patternFinpartition z).parts = ζ then wz(θ, n, z) else 0) else 0 := by
    intro z
    rw [Finset.sum_eq_single (patternFinpartition z).parts]
    · rw [ite_eq_left (rfl : (patternFinpartition z).parts = (patternFinpartition z).parts)]
    · intro ζ _ hne
      rw [ite_eq_right (fun h : (patternFinpartition z).parts = ζ => hne h.symm), ite_self]
    · intro h
      exact absurd (mem_univ _) h
  rw [Finset.sum_congr rfl fun z _ => hz z, Finset.sum_comm]
  refine Finset.sum_congr rfl fun ζ _ => ?_
  by_cases hp : ζ.val.map Finset.card = p.parts
  · simp only [ite_eq_left hp]
    exact (sum_pathProduct_parts_eq hθ ζ).symm
  · simp only [ite_eq_right hp]
    exact Finset.sum_const_zero.symm

/--
Source: ewens1972, eq. (23), (29)–(30), eq. (A3), pp. 95, 100–102, 107; berestycki2009, Thm 2.9, eq.
(40). -/
theorem markedKingman_allelicFinpartition_real (n : ℕ) (θ : ℝ≥0) (hθ : 0 < (θ : ℝ))
    (ζ : Blocks n) :
    (markedKingmanLaw n θ).real {x | (allelicFinpartition n x).parts = ζ} =
      esfPart n (θ : ℝ) ζ := by
  have hset : {x : KingmanMutationHistory n × (KingmanMutationBranch n → ℕ) |
      (allelicFinpartition n x).parts = ζ} =
      {x | (patternFinpartition (mutatedBlocks n x.2)).parts = ζ} := by
    ext x
    change (allelicFinpartition n x).parts = ζ ↔
      (patternFinpartition (mutatedBlocks n x.2)).parts = ζ
    rw [allelicFinpartition_eq_patternFinpartition]
  rw [hset]
  exact (markedKingmanLaw_real_mutatedBlocks_prop θ
    (fun z => (patternFinpartition z).parts = ζ)).trans (sum_pathProduct_parts_eq hθ ζ)

theorem sum_esfKernel_eq_markedKingman (θA : ℝ≥0) {θB ρ : ℝ} (hθA : 0 < (θA : ℝ))
    (hθB : 0 < θB) (hρ : 0 ≤ ρ) (ζA : Blocks n) :
    (∑ ζB : Blocks n, esfKernel (θA : ℝ) θB ρ ζA ζB) =
      (markedKingmanLaw n θA).real {x | (allelicFinpartition n x).parts = ζA} := by
  rw [margA_eq_esfPart hθA hθB hρ, markedKingman_allelicFinpartition_real n θA hθA]

theorem margB_eq_markedKingman {θA : ℝ} (θB : ℝ≥0) {ρ : ℝ} (hθA : 0 < θA)
    (hθB : 0 < (θB : ℝ)) (hρ : 0 ≤ ρ) (ζB : Blocks n) :
    margB θA (θB : ℝ) ρ ζB =
      (markedKingmanLaw n θB).real {x | (allelicFinpartition n x).parts = ζB} := by
  rw [margB_eq_esfPart hθA hθB hρ, markedKingman_allelicFinpartition_real n θB hθB]

theorem sum_esfKernel_blockType_eq_esf {θA θB ρ : ℝ} (hθA : 0 < θA) (hθB : 0 < θB)
    (hρ : 0 ≤ ρ) (p : Nat.Partition n) :
    (∑ ζA : Blocks n, if ζA.val.map Finset.card = p.parts then
        ∑ ζB : Blocks n, esfKernel θA θB ρ ζA ζB else 0) = esf θA p := by
  rw [← sum_esfPart_blockType hθA p]
  exact Finset.sum_congr rfl fun ζA _ => by rw [margA_eq_esfPart hθA hθB hρ]

theorem sum_margB_blockType_eq_esf {θA θB ρ : ℝ} (hθA : 0 < θA) (hθB : 0 < θB)
    (hρ : 0 ≤ ρ) (p : Nat.Partition n) :
    (∑ ζB : Blocks n, if ζB.val.map Finset.card = p.parts then margB θA θB ρ ζB else 0) =
      esf θB p := by
  rw [← sum_esfPart_blockType hθB p]
  exact Finset.sum_congr rfl fun ζB _ => by rw [margB_eq_esfPart hθA hθB hρ]

theorem ewensUrnLaw_eq_sum_esfKernel {θA θB ρ : ℝ} (hθA : 0 < θA) (hθB : 0 < θB)
    (hρ : 0 ≤ ρ) (p : Nat.Partition n) :
    ewensUrnLaw θA hθA n p =
      ENNReal.ofReal (∑ ζA : Blocks n, if ζA.val.map Finset.card = p.parts then
        ∑ ζB : Blocks n, esfKernel θA θB ρ ζA ζB else 0) := by
  rw [sum_esfKernel_blockType_eq_esf hθA hθB hρ p, ewensUrnLaw_apply]

end Rhone.Statistics
