/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.TajimaVarianceModel
public import Rhone.Statistics.EwensUrn

/-!
# The allelic partition of a sample under the marked Kingman law

Source: ewens1972, eq. (29)–(30), eq. (A3), pp. 100, 102, 107; berestycki2009, Thm 2.9, eq. (40);
kingman1982, sec. 1, eq. (1.1)–(1.4), (1.7). -/

@[expose] public section
namespace Rhone.Statistics
open MeasureTheory ProbabilityTheory Finset
open scoped NNReal

instance instMeasurableSpaceNatPartition (n : ℕ) : MeasurableSpace (Nat.Partition n) := ⊤

instance instDiscreteMeasurableSpaceNatPartition (n : ℕ) :
    DiscreteMeasurableSpace (Nat.Partition n) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

def sameAllele (n : ℕ)
    (x : Coalescent.KingmanMutationHistory n × (Coalescent.KingmanMutationBranch n → ℕ))
    (a b : Fin n) : Prop :=
  ∀ br : Coalescent.KingmanMutationBranch n, (a ∈ br.2 ↔ ¬ b ∈ br.2) → x.2 br = 0

instance instDecidableRelSameAllele (n : ℕ)
    (x : Coalescent.KingmanMutationHistory n × (Coalescent.KingmanMutationBranch n → ℕ)) :
    DecidableRel (sameAllele n x) := fun a b =>
  inferInstanceAs (Decidable
    (∀ br : Coalescent.KingmanMutationBranch n, (a ∈ br.2 ↔ ¬ b ∈ br.2) → x.2 br = 0))

theorem sameAllele_refl (n : ℕ)
    (x : Coalescent.KingmanMutationHistory n × (Coalescent.KingmanMutationBranch n → ℕ))
    (a : Fin n) : sameAllele n x a a := fun _ h => absurd h (by tauto)

theorem sameAllele_symm {n : ℕ}
    {x : Coalescent.KingmanMutationHistory n × (Coalescent.KingmanMutationBranch n → ℕ)}
    {a b : Fin n} (h : sameAllele n x a b) : sameAllele n x b a :=
  fun br hbr => h br (by tauto)

theorem sameAllele_trans {n : ℕ}
    {x : Coalescent.KingmanMutationHistory n × (Coalescent.KingmanMutationBranch n → ℕ)}
    {a b c : Fin n} (hab : sameAllele n x a b) (hbc : sameAllele n x b c) :
    sameAllele n x a c := by
  intro br hbr
  by_cases h : (a ∈ br.2 ↔ ¬ b ∈ br.2)
  · exact hab br h
  · exact hbc br (by tauto)

theorem sameAllele_congr {n : ℕ}
    {x y : Coalescent.KingmanMutationHistory n × (Coalescent.KingmanMutationBranch n → ℕ)}
        (h : x.2 = y.2)
    (a b : Fin n) : sameAllele n x a b ↔ sameAllele n y a b := by
  unfold sameAllele
  rw [h]

def allelicSetoid (n : ℕ)
    (x : Coalescent.KingmanMutationHistory n × (Coalescent.KingmanMutationBranch n → ℕ)) :
    Setoid (Fin n) where
  r := sameAllele n x
  iseqv := ⟨sameAllele_refl n x, sameAllele_symm, sameAllele_trans⟩

instance instDecidableRelAllelicSetoid (n : ℕ)
    (x : Coalescent.KingmanMutationHistory n × (Coalescent.KingmanMutationBranch n → ℕ)) :
    DecidableRel (allelicSetoid n x).r :=
  instDecidableRelSameAllele n x

def allelicFinpartition (n : ℕ)
    (x : Coalescent.KingmanMutationHistory n × (Coalescent.KingmanMutationBranch n → ℕ)) :
    Finpartition (univ : Finset (Fin n)) :=
  Finpartition.ofSetoid (allelicSetoid n x)

theorem mem_part_allelicFinpartition {n : ℕ}
    {x : Coalescent.KingmanMutationHistory n × (Coalescent.KingmanMutationBranch n → ℕ)}
        {a b : Fin n} :
    b ∈ (allelicFinpartition n x).part a ↔ sameAllele n x a b :=
  Finpartition.mem_part_ofSetoid_iff_rel

noncomputable def allelicPartition (n : ℕ)
    (x : Coalescent.KingmanMutationHistory n × (Coalescent.KingmanMutationBranch n → ℕ)) :
        Nat.Partition n
        where
  parts := (allelicFinpartition n x).parts.val.map Finset.card
  parts_pos := by
    intro i hi
    obtain ⟨B, hB, rfl⟩ := Multiset.mem_map.1 hi
    exact Finset.card_pos.2 ((allelicFinpartition n x).nonempty_of_mem_parts hB)
  parts_sum := by
    have h := (allelicFinpartition n x).sum_card_parts
    rw [Finset.card_univ, Fintype.card_fin] at h
    exact h

theorem allelicPartition_parts (n : ℕ)
    (x : Coalescent.KingmanMutationHistory n × (Coalescent.KingmanMutationBranch n → ℕ)) :
    (allelicPartition n x).parts = (allelicFinpartition n x).parts.val.map Finset.card := rfl

theorem allelicPartition_congr {n : ℕ}
    {x y : Coalescent.KingmanMutationHistory n × (Coalescent.KingmanMutationBranch n → ℕ)}
        (h : x.2 = y.2) :
    allelicPartition n x = allelicPartition n y := by
  obtain ⟨x1, x2⟩ := x
  obtain ⟨y1, y2⟩ := y
  obtain rfl : x2 = y2 := h
  rfl

theorem measurable_allelicPartition (n : ℕ) : Measurable (allelicPartition n) := by
  have hg : Measurable (fun m : Coalescent.KingmanMutationBranch n → ℕ =>
      allelicPartition n ((fun _ => ⊥, fun _ => 0), m)) := Measurable.of_discrete
  have he : allelicPartition n = (fun m : Coalescent.KingmanMutationBranch n → ℕ =>
      allelicPartition n ((fun _ => ⊥, fun _ => 0), m)) ∘ Prod.snd := by
    funext x
    exact allelicPartition_congr rfl
  rw [he]
  exact hg.comp measurable_snd

end Rhone.Statistics
