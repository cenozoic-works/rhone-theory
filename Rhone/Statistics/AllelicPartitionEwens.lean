/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Statistics.AllelicPatternSum
public import Rhone.Statistics.EwensLabellingSum
public import Rhone.Statistics.AllelicPartition
public import Rhone.Coalescent.KingmanSamplingConsistency
public import Mathlib.Data.Fintype.CardEmbedding

/-!
# The Ewens sampling formula under the marked Kingman law

Source: ewens1972, eq. (23), (29)–(30), eq. (A3), pp. 95, 100–102, 107; berestycki2009, Thm 2.9, eq.
(40); kingman1982, sec. 1, eq. (1.1)–(1.4), (1.7). -/

@[expose] public section
namespace Rhone.Statistics
open MeasureTheory ProbabilityTheory Finset MarkovChain Coalescent Rhone.Combinatorics
open scoped NNReal ENNReal

section matching

variable {α κ : Type*} [Fintype α] [DecidableEq α] [DecidableEq κ]
  {P : Finpartition (univ : Finset α)} {c : α → κ}

def labelsMatch (P : Finpartition (univ : Finset α)) (c : α → κ) : Prop :=
  ∀ a b, (b ∈ P.part a ↔ c a = c b)

instance instDecidableLabelsMatch (P : Finpartition (univ : Finset α)) (c : α → κ) :
    Decidable (labelsMatch P c) := by
  unfold labelsMatch
  infer_instance

theorem labelType_of_labelsMatch (h : labelsMatch P c) :
    labelType (univ.val.map c) = P.parts.val.map Finset.card := by
  have hfib : ∀ a, (univ.filter fun b => c a = c b) = P.part a := fun a => by
    ext b
    rw [mem_filter, h a b]
    exact and_iff_right (mem_univ b)
  have hex : ∀ t, t ∈ (Multiset.map c univ.val).toFinset.val → ∃ a, c a = t := fun t ht => by
    obtain ⟨a, -, ha⟩ := Multiset.mem_map.1 (Multiset.mem_toFinset.1 (Finset.mem_def.2 ht))
    exact ⟨a, ha⟩
  unfold labelType
  refine Multiset.map_eq_map_of_bij_of_nodup _ _ (Finset.nodup _) P.parts.nodup
    (fun t _ => univ.filter fun b => t = c b) ?_ ?_ ?_ ?_
  · intro t ht
    obtain ⟨a, rfl⟩ := hex t ht
    rw [hfib]
    exact P.part_mem.2 (mem_univ a)
  · intro t1 ht1 t2 _ h12
    obtain ⟨a, rfl⟩ := hex t1 ht1
    have ha : a ∈ univ.filter fun b => c a = c b := mem_filter.2 ⟨mem_univ a, rfl⟩
    have h12' : (univ.filter fun b => c a = c b) = univ.filter fun b => t2 = c b := h12
    rw [h12'] at ha
    exact ((mem_filter.1 ha).2).symm
  · intro B hB
    obtain ⟨a, ha⟩ := P.nonempty_of_mem_parts hB
    refine ⟨c a, Finset.mem_def.1 (Multiset.mem_toFinset.2
      (Multiset.mem_map.2 ⟨a, Finset.mem_def.1 (mem_univ a), rfl⟩)), ?_⟩
    exact (hfib a).trans (P.part_eq_of_mem hB ha)
  · intro t _
    exact Multiset.count_map _ _ _

theorem card_filter_labelsMatch [Fintype κ] (P : Finpartition (univ : Finset α)) :
    (univ.filter fun c : α → κ => labelsMatch P c).card =
      (Fintype.card κ).descFactorial P.parts.card := by
  let e : {c : α → κ // labelsMatch P c} ≃ ({B // B ∈ P.parts} ↪ κ) :=
    { toFun := fun cc => ⟨fun B => cc.1 (P.nonempty_of_mem_parts B.2).choose,
        fun B B' hBB' => by
          have hb := (P.nonempty_of_mem_parts B.2).choose_spec
          have hb' := (P.nonempty_of_mem_parts B'.2).choose_spec
          have h1 := (cc.2 _ _).2 hBB'
          rw [P.part_eq_of_mem B.2 hb] at h1
          exact Subtype.ext (P.eq_of_mem_parts B.2 B'.2 h1 hb')⟩
      invFun := fun f => ⟨fun a => f ⟨P.part a, P.part_mem.2 (mem_univ a)⟩, fun a b => by
        rw [P.mem_part_iff_part_eq_part (mem_univ b) (mem_univ a)]
        exact ⟨fun h => congrArg f (Subtype.ext h.symm),
          fun h => (congrArg Subtype.val (f.injective h)).symm⟩⟩
      left_inv := fun cc => Subtype.ext (funext fun a =>
        ((cc.2 a _).1 (P.nonempty_of_mem_parts (P.part_mem.2 (mem_univ a))).choose_spec).symm)
      right_inv := fun f => DFunLike.ext _ _ fun B => congrArg f
        (Subtype.ext (P.part_eq_of_mem B.2 (P.nonempty_of_mem_parts B.2).choose_spec)) }
  rw [← Fintype.card_subtype, Fintype.card_congr e, Fintype.card_embedding_eq,
    Fintype.card_coe]

theorem killingWeight_bot (θ : ℝ) (c : α → κ) :
    killingWeight θ (⊥ : Finpartition (univ : Finset α)) univ c =
      labelWeight θ (univ.val.map c) := by
  have hl : ∀ a : α, blockLabels univ c {a} = {c a} := fun a => by
    unfold blockLabels
    rw [Finset.inter_univ, Finset.image_singleton]
  have hv : ∀ B ∈ (⊥ : Finpartition (univ : Finset α)).parts,
      (blockLabels univ c B).card ≤ 1 := by
    intro B hB
    obtain ⟨a, -, rfl⟩ := Finpartition.mem_bot_iff.1 hB
    rw [hl, Finset.card_singleton]
  unfold killingWeight
  rw [cfgWeight_of_valid θ hv, Finpartition.parts_bot, Finset.sum_map]
  congr 1
  calc ∑ a ∈ (univ : Finset α),
        (blockLabels univ c ((⟨singleton, singleton_injective⟩ : α ↪ Finset α) a)).val
      = ∑ a ∈ (univ : Finset α), ({c a} : Multiset κ) :=
        Finset.sum_congr rfl fun a _ => by
          change (blockLabels univ c {a}).val = _
          rw [hl, Finset.singleton_val]
    _ = ((univ.val.map c).map fun t => ({t} : Multiset κ)).sum := by
        rw [Multiset.map_map]
        rfl
    _ = univ.val.map c := Multiset.sum_map_singleton _

end matching

variable {n : ℕ}

local notation "wz(" θ ", " n ", " z ")" =>
  FinChain.pathProduct (RateChain.jumpChain (partitionChain (Fin n))) (n - 1)
    (fun k π => killLevelFactor θ π (z k)) ⊥

def patternSetoid {N : ℕ} (z : Fin N → Finset (Finset (Fin n))) : Setoid (Fin n) where
  r := patternRel z
  iseqv := ⟨fun _ _ _ _ => Iff.rfl, patternRel_symm,
    fun h1 h2 k B hB => (h1 k B hB).trans (h2 k B hB)⟩

instance instDecidableRelPatternSetoid {N : ℕ} (z : Fin N → Finset (Finset (Fin n))) :
    DecidableRel (patternSetoid z).r := fun a b => instDecidablePatternRel z a b

def patternFinpartition {N : ℕ} (z : Fin N → Finset (Finset (Fin n))) :
    Finpartition (univ : Finset (Fin n)) :=
  Finpartition.ofSetoid (patternSetoid z)

theorem mem_part_patternFinpartition {N : ℕ} {z : Fin N → Finset (Finset (Fin n))}
    {a b : Fin n} : b ∈ (patternFinpartition z).part a ↔ patternRel z a b :=
  Finpartition.mem_part_ofSetoid_iff_rel

theorem patternMatches_univ_iff {κ : Type*} {N : ℕ}
    (z : Fin N → Finset (Finset (Fin n))) (c : Fin n → κ) :
    patternMatches univ z c ↔ labelsMatch (patternFinpartition z) c := by
  constructor
  · intro h a b
    rw [mem_part_patternFinpartition]
    exact h a (mem_univ a) b (mem_univ b)
  · intro h a _ b _
    rw [← mem_part_patternFinpartition]
    exact h a b

theorem sameAllele_iff_patternRel
    (x : KingmanMutationHistory n × (KingmanMutationBranch n → ℕ)) (a b : Fin n) :
    sameAllele n x a b ↔ patternRel (mutatedBlocks n x.2) a b := by
  constructor
  · intro h k B hB
    by_contra hne
    exact (mem_mutatedBlocks.1 hB) (h (k, B) (by tauto))
  · rintro h ⟨k, B⟩ hsep
    by_contra hne
    have h2 : a ∈ B ↔ b ∈ B := h k B (mem_mutatedBlocks.2 hne)
    have h3 : a ∈ B ↔ ¬ b ∈ B := hsep
    tauto

theorem allelicFinpartition_eq_patternFinpartition
    (x : KingmanMutationHistory n × (KingmanMutationBranch n → ℕ)) :
    allelicFinpartition n x = patternFinpartition (mutatedBlocks n x.2) :=
  eq_of_part_eq fun a => by
    ext b
    rw [mem_part_allelicFinpartition, mem_part_patternFinpartition, sameAllele_iff_patternRel]

theorem sum_pathProduct_patternFinpartition {θ : ℝ} (hθ : 0 < θ) (p : Nat.Partition n) :
    (∑ z : Fin (n - 1) → Finset (Finset (Fin n)),
      if (patternFinpartition z).parts.val.map Finset.card = p.parts then wz(θ, n, z)
      else 0) = Probability.esf θ p := by
  have hD : ((n.descFactorial p.parts.card : ℕ) : ℝ) ≠ 0 := by
    have hle : p.parts.card ≤ n := by
      have h := Multiset.card_nsmul_le_sum (s := p.parts) (a := 1) fun x hx => p.parts_pos hx
      rw [p.parts_sum, smul_eq_mul, mul_one] at h
      exact h
    exact_mod_cast fun h0 => absurd (Nat.descFactorial_eq_zero_iff_lt.1 h0) (not_lt.2 hle)
  have hcount : ∀ z : Fin (n - 1) → Finset (Finset (Fin n)),
      ∑ c : Fin n → Fin n,
        (if labelType (univ.val.map c) = p.parts ∧ patternMatches univ z c then (1 : ℝ)
          else 0) =
      if (patternFinpartition z).parts.val.map Finset.card = p.parts then
        ((n.descFactorial p.parts.card : ℕ) : ℝ) else 0 := by
    intro z
    by_cases hQ : (patternFinpartition z).parts.val.map Finset.card = p.parts
    · have hcond : ∀ c : Fin n → Fin n,
          (labelType (univ.val.map c) = p.parts ∧ patternMatches univ z c) ↔
            labelsMatch (patternFinpartition z) c := fun c => by
        rw [patternMatches_univ_iff]
        exact ⟨fun h => h.2, fun h => ⟨(labelType_of_labelsMatch h).trans hQ, h⟩⟩
      have hk : (patternFinpartition z).parts.card = p.parts.card :=
        (Multiset.card_map Finset.card _).symm.trans (congrArg Multiset.card hQ)
      rw [ite_eq_left hQ, Finset.sum_boole, Finset.filter_congr (fun c _ => hcond c),
        card_filter_labelsMatch, Fintype.card_fin, hk]
    · rw [ite_eq_right hQ]
      refine Finset.sum_eq_zero fun c _ => ite_eq_right fun h => hQ ?_
      rw [← labelType_of_labelsMatch ((patternMatches_univ_iff z c).1 h.2)]
      exact h.1
  have hc : ∀ c : Fin n → Fin n, labelWeight θ (univ.val.map c) =
      ∑ z : Fin (n - 1) → Finset (Finset (Fin n)),
        if patternMatches univ z c then wz(θ, n, z) else 0 := by
    intro c
    rw [← killingWeight_bot, ← patternSum_eq hθ (n - 1) ⊥ (by
      rw [Finpartition.card_bot, Finset.card_univ, Fintype.card_fin]
      omega) univ c]
    rfl
  have hlab := labellingSum_eq (Fin n) hθ n p
  rw [Fintype.card_fin] at hlab
  refine mul_left_cancel₀ hD ?_
  rw [← hlab]
  unfold labellingSum
  calc ((n.descFactorial p.parts.card : ℕ) : ℝ) *
        ∑ z : Fin (n - 1) → Finset (Finset (Fin n)),
          (if (patternFinpartition z).parts.val.map Finset.card = p.parts then wz(θ, n, z)
            else 0)
      = ∑ z : Fin (n - 1) → Finset (Finset (Fin n)), wz(θ, n, z) *
          (if (patternFinpartition z).parts.val.map Finset.card = p.parts then
            ((n.descFactorial p.parts.card : ℕ) : ℝ) else 0) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun z _ => ?_
        by_cases hQ : (patternFinpartition z).parts.val.map Finset.card = p.parts
        · rw [ite_eq_left hQ, ite_eq_left hQ, mul_comm]
        · rw [ite_eq_right hQ, ite_eq_right hQ, mul_zero, mul_zero]
    _ = ∑ z : Fin (n - 1) → Finset (Finset (Fin n)), wz(θ, n, z) *
          ∑ c : Fin n → Fin n,
            (if labelType (univ.val.map c) = p.parts ∧ patternMatches univ z c then (1 : ℝ)
              else 0) :=
        Finset.sum_congr rfl fun z _ => by rw [hcount z]
    _ = ∑ c : Fin n → Fin n, ∑ z : Fin (n - 1) → Finset (Finset (Fin n)), wz(θ, n, z) *
          (if labelType (univ.val.map c) = p.parts ∧ patternMatches univ z c then (1 : ℝ)
            else 0) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun z _ => Finset.mul_sum _ _ _
    _ = ∑ c : Fin n → Fin n,
          if labelType (univ.val.map c) = p.parts then labelWeight θ (univ.val.map c)
          else 0 := by
        refine Finset.sum_congr rfl fun c _ => ?_
        by_cases ht : labelType (univ.val.map c) = p.parts
        · rw [ite_eq_left ht, hc c]
          refine Finset.sum_congr rfl fun z _ => ?_
          by_cases hm : patternMatches univ z c
          · rw [ite_eq_left (And.intro ht hm), ite_eq_left hm, mul_one]
          · rw [ite_eq_right (fun h => hm h.2), ite_eq_right hm, mul_zero]
        · rw [ite_eq_right ht]
          exact Finset.sum_eq_zero fun z _ => by
            rw [ite_eq_right (fun h => ht h.1), mul_zero]

/--
Source: ewens1972, eq. (23), (29)–(30), eq. (A3), pp. 95, 100–102, 107; berestycki2009, Thm 2.9, eq.
(40). -/
theorem markedKingman_allelicPartition_real (n : ℕ) (θ : ℝ≥0) (hθ : 0 < (θ : ℝ))
    (p : Nat.Partition n) :
    (markedKingmanLaw n θ).real {x | allelicPartition n x = p} = Probability.esf (θ : ℝ) p := by
  have hset : {x : KingmanMutationHistory n × (KingmanMutationBranch n → ℕ) |
      allelicPartition n x = p} =
      {x | (patternFinpartition (mutatedBlocks n x.2)).parts.val.map Finset.card =
        p.parts} := by
    ext x
    change allelicPartition n x = p ↔
      (patternFinpartition (mutatedBlocks n x.2)).parts.val.map Finset.card = p.parts
    rw [← allelicFinpartition_eq_patternFinpartition, ← allelicPartition_parts]
    exact Nat.Partition.ext_iff
  rw [hset]
  exact (markedKingmanLaw_real_mutatedBlocks_prop θ
    (fun z => (patternFinpartition z).parts.val.map Finset.card = p.parts)).trans
    (sum_pathProduct_patternFinpartition hθ p)

/--
Source: ewens1972, eq. (23), (29)–(30), eq. (A3), pp. 95, 100–102, 107; berestycki2009, Thm 2.9, eq.
(40). -/
theorem markedKingman_allelicPartition_ewens (n : ℕ) (θ : ℝ≥0) (hθ : 0 < (θ : ℝ)) :
    (markedKingmanLaw n θ).map (allelicPartition n) = (ewensUrnLaw (θ : ℝ) hθ n).toMeasure := by
  apply Measure.ext_of_singleton
  intro p
  rw [Measure.map_apply (measurable_allelicPartition n) (measurableSet_singleton p),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton p), ewensUrnLaw_apply,
    ← markedKingman_allelicPartition_real n θ hθ p]
  exact (ofReal_measureReal (measure_ne_top _ _)).symm

end Rhone.Statistics
