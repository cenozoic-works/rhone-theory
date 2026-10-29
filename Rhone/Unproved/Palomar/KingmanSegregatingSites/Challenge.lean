module

public import Mathlib

set_option maxSynthPendingDepth 3

@[expose] public section

elab "clear_aux_proof_cache" : command => do
  Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}
  let ext ← unsafe Lean.Elab.Command.liftCoreM
    (Lean.evalConst (Lean.EnvExtension (Lean.PersistentHashMap Nat Nat))
      (Lean.Name.mkNum `_private.Lean.Meta.Match.Match 0 ++ `Lean.Meta.Match.matcherExt))
  Lean.modifyEnv fun env => ext.setState env {}

elab "set_main_module " m:ident : command =>
  Lean.modifyEnv fun env => env.setMainModule m.getId

clear_aux_proof_cache
set_main_module Rhone.MarkovChain.FinChain

namespace Rhone.MarkovChain

open Finset Matrix

structure FinChain (S : Type*) [Fintype S] where

  P : Matrix S S ℝ

  nonneg : ∀ x y, 0 ≤ P x y

  row_sum : ∀ x, ∑ y, P x y = 1

end Rhone.MarkovChain

clear_aux_proof_cache
set_main_module Rhone.MarkovChain.Process

namespace Rhone.MarkovChain

open MeasureTheory ProbabilityTheory Finset Preorder

structure DiscreteProcess (S : Type*) [MeasurableSpace S] where

  step : Kernel S S

  [isMarkov : IsMarkovKernel step]

namespace DiscreteProcess

variable {S : Type*} [MeasurableSpace S] (P : DiscreteProcess S)

instance : IsMarkovKernel P.step := P.isMarkov

noncomputable def stepSeq (m : ℕ) : Kernel ((_ : Iic m) → S) S :=
  P.step.comap (fun x => x ⟨m, mem_Iic.2 le_rfl⟩) (measurable_pi_apply _)

instance (m : ℕ) : IsMarkovKernel (P.stepSeq m) := by
  rw [stepSeq]
  infer_instance

noncomputable def traj : Kernel S (ℕ → S) :=
  (Kernel.traj (X := fun _ => S) P.stepSeq 0).comap (fun x _ => x)
    (measurable_pi_iff.2 fun _ => measurable_id)

instance : IsMarkovKernel P.traj := by
  rw [traj]
  infer_instance

noncomputable def pathLaw (x : S) : Measure (ℕ → S) := P.traj x

end DiscreteProcess

end Rhone.MarkovChain

clear_aux_proof_cache
set_main_module Rhone.MarkovChain.Trajectory

namespace Rhone.MarkovChain.FinChain

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

variable {S : Type*} [Fintype S] [DecidableEq S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  (C : FinChain S)

omit [DecidableEq S] [MeasurableSpace S] [DiscreteMeasurableSpace S] in

theorem sum_ofReal_P (x : S) : ∑ y, ENNReal.ofReal (C.P x y) = 1 := by
  rw [← ENNReal.ofReal_sum_of_nonneg fun y _ => C.nonneg x y, C.row_sum, ENNReal.ofReal_one]

noncomputable def stepPMF (x : S) : PMF S :=
  PMF.ofFintype (fun y => ENNReal.ofReal (C.P x y)) (C.sum_ofReal_P x)

noncomputable def kernel : Kernel S S where
  toFun x := (C.stepPMF x).toMeasure
  measurable' := Measurable.of_discrete

instance : IsMarkovKernel C.kernel :=
  ⟨fun x => by change IsProbabilityMeasure (C.stepPMF x).toMeasure; infer_instance⟩

noncomputable def toProcess : DiscreteProcess S := ⟨C.kernel⟩

noncomputable def pathLaw (x : S) : Measure (ℕ → S) := C.toProcess.pathLaw x

end Rhone.MarkovChain.FinChain

clear_aux_proof_cache
set_main_module Rhone.MarkovChain.RateChain

namespace Rhone.MarkovChain

open Finset

structure RateChain (S : Type*) [Fintype S] where

  Q : Matrix S S ℝ

  off_diag_nonneg : ∀ x y, x ≠ y → 0 ≤ Q x y

  row_sum : ∀ x, ∑ y, Q x y = 0

namespace RateChain

variable {S : Type*} [Fintype S] [DecidableEq S] (R : RateChain S)

omit [DecidableEq S] in

def rate (x : S) : ℝ := -R.Q x x

theorem rate_eq_sum (x : S) : R.rate x = ∑ y ∈ univ.erase x, R.Q x y := by
  have h := R.row_sum x
  rw [← Finset.add_sum_erase univ _ (mem_univ x)] at h
  rw [rate]
  linarith

omit [DecidableEq S] in

theorem rate_nonneg (x : S) : 0 ≤ R.rate x := by
  classical
  rw [rate_eq_sum]
  exact Finset.sum_nonneg fun y hy => R.off_diag_nonneg x y (Finset.ne_of_mem_erase hy).symm

noncomputable def jumpMatrix : Matrix S S ℝ := fun x y =>
  if R.rate x = 0 then (if x = y then 1 else 0) else (if x = y then 0 else R.Q x y / R.rate x)

theorem sum_jumpMatrix_mul {x : S} (hx : R.rate x ≠ 0) (u : S → ℝ) :
    ∑ y, R.jumpMatrix x y * u y = u x + (∑ y, R.Q x y * u y) / R.rate x := by
  have hterm : ∀ y, R.jumpMatrix x y * u y =
      (if x = y then u y else 0) + R.Q x y * u y / R.rate x := by
    intro y
    by_cases hxy : x = y
    · subst hxy
      have hq : R.Q x x = -R.rate x := by simp [rate]
      simp only [jumpMatrix, hx, ↓reduceIte, zero_mul, hq]
      field_simp
      ring
    · simp only [jumpMatrix, hx, hxy, ↓reduceIte]
      ring
  simp only [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq, ← Finset.sum_div]
  simp

noncomputable def jumpChain : FinChain S where
  P := R.jumpMatrix
  nonneg x y := by
    unfold jumpMatrix
    split_ifs with h1 h2 h2
    · exact zero_le_one
    · exact le_rfl
    · exact le_rfl
    · exact div_nonneg (R.off_diag_nonneg x y h2) (R.rate_nonneg x)
  row_sum x := by
    by_cases hx : R.rate x = 0
    · simp [jumpMatrix, hx]
    · have h := R.sum_jumpMatrix_mul hx (fun _ => 1)
      simp only [mul_one, R.row_sum x, zero_div, add_zero] at h
      exact h

end RateChain

end Rhone.MarkovChain

clear_aux_proof_cache
set_main_module Rhone.MarkovChain.JumpHold

namespace Rhone.MarkovChain

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

noncomputable def clockLaw : Measure (ℕ → ℝ) := Measure.infinitePi fun _ : ℕ => expMeasure 1

namespace RateChain

variable {S : Type*} [Fintype S] [DecidableEq S] (R : RateChain S)

omit [DecidableEq S] in

noncomputable def holdTime (p : (ℕ → S) × (ℕ → ℝ)) (k : ℕ) : ℝ := p.2 k / R.rate (p.1 k)

variable [MeasurableSpace S] [DiscreteMeasurableSpace S]

noncomputable def jumpHoldLaw (x : S) : Measure ((ℕ → S) × (ℕ → ℝ)) :=
  (R.jumpChain.pathLaw x).prod clockLaw

end RateChain

end Rhone.MarkovChain

clear_aux_proof_cache
set_main_module Rhone.MarkovChain.Ancestral

namespace Rhone.MarkovChain

open Finset MeasureTheory

instance instMeasurableSpaceFinpartition {β : Type*} [Lattice β] [OrderBot β] (a : β) :
    MeasurableSpace (Finpartition a) := ⊤

instance instDiscreteMeasurableSpaceFinpartition {β : Type*} [Lattice β] [OrderBot β] (a : β) :
    DiscreteMeasurableSpace (Finpartition a) := ⟨fun _ => MeasurableSpace.measurableSet_top⟩

end Rhone.MarkovChain

clear_aux_proof_cache
set_main_module Rhone.Coalescent.Kingman

namespace Rhone.Coalescent

open Finset

def coalRate (k : ℕ) : ℚ := k * (k - 1) / 2

end Rhone.Coalescent

clear_aux_proof_cache
set_main_module Rhone.Coalescent.KingmanPartition

namespace Rhone.Coalescent

open Finset MeasureTheory MarkovChain
open scoped ENNReal

variable {α : Type*} [Fintype α] [DecidableEq α]

def mergeBlocksOf (π : Finpartition (univ : Finset α)) (s : Finset (Finset α))
    (hs : s ⊆ π.parts) (hne : s.Nonempty) : Finpartition (univ : Finset α) :=
  (π.ofSubset (sdiff_subset : π.parts \ s ⊆ π.parts) rfl).extend (b := s.sup id)
    (by
      obtain ⟨a, ha⟩ := hne
      exact fun h => π.ne_bot (hs ha) (le_bot_iff.1 (h ▸ Finset.le_sup (f := id) ha)))
    (Finset.disjoint_sup_left.2 fun i hi =>
      π.supIndep hs (mem_sdiff.1 hi).1 (mem_sdiff.1 hi).2)
    (by
      rw [← Finset.sup_union, sdiff_union_of_subset hs]
      exact π.sup_parts)

def mergeBlocks (π : Finpartition (univ : Finset α)) (s : Finset (Finset α)) :
    Finpartition (univ : Finset α) :=
  if h : s ⊆ π.parts ∧ s.Nonempty then mergeBlocksOf π s h.1 h.2 else π

variable {π σ : Finpartition (univ : Finset α)} {s : Finset (Finset α)}

theorem parts_mergeBlocks (hs : s ⊆ π.parts) (hne : s.Nonempty) :
    (mergeBlocks π s).parts = insert (s.sup id) (π.parts \ s) := by
  rw [mergeBlocks, dite_eq_left ⟨hs, hne⟩]
  rfl

theorem le_mergeBlocks (π : Finpartition (univ : Finset α)) (s : Finset (Finset α)) :
    π ≤ mergeBlocks π s := by
  by_cases h : s ⊆ π.parts ∧ s.Nonempty
  · intro b hb
    rw [parts_mergeBlocks h.1 h.2]
    by_cases hbs : b ∈ s
    · exact ⟨s.sup id, mem_insert_self _ _, Finset.le_sup (f := id) hbs⟩
    · exact ⟨b, mem_insert_of_mem (mem_sdiff.2 ⟨hb, hbs⟩), le_rfl⟩
  · rw [mergeBlocks, dite_eq_right h]

theorem sup_notMem_parts (hs : s ⊆ π.parts) (hc : s.card = 2) : s.sup id ∉ π.parts := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 hc
  have ha : a ∈ π.parts := hs (by simp)
  have hb : b ∈ π.parts := hs (by simp)
  have hsup : ({a, b} : Finset (Finset α)).sup id = a ∪ b := by simp
  rw [hsup]
  intro hmem
  have h1 : a ∪ b = a := by
    by_contra hne
    have hd : Disjoint (a ∪ b) a := π.disjoint hmem ha hne
    exact π.ne_bot ha (hd.eq_bot_of_ge subset_union_left)
  have h2 : a ∪ b = b := by
    by_contra hne
    have hd : Disjoint (a ∪ b) b := π.disjoint hmem hb hne
    exact π.ne_bot hb (hd.eq_bot_of_ge subset_union_right)
  exact hab (h1.symm.trans h2)

theorem card_parts_mergeBlocks (hs : s ⊆ π.parts) (hc : s.card = 2) :
    (mergeBlocks π s).parts.card + 1 = π.parts.card := by
  have hne : s.Nonempty := card_pos.1 (by omega)
  have hx : s.sup id ∉ π.parts \ s := fun h => sup_notMem_parts hs hc (mem_sdiff.1 h).1
  have hle : s.card ≤ π.parts.card := card_le_card hs
  rw [parts_mergeBlocks hs hne, card_insert_of_notMem hx, card_sdiff_of_subset hs]
  omega

theorem parts_sdiff_parts_mergeBlocks (hs : s ⊆ π.parts) (hc : s.card = 2) :
    π.parts \ (mergeBlocks π s).parts = s := by
  have hne : s.Nonempty := card_pos.1 (by omega)
  have hx := sup_notMem_parts hs hc
  rw [parts_mergeBlocks hs hne]
  ext c
  simp only [mem_sdiff, mem_insert, not_or, not_and, not_not]
  constructor
  · rintro ⟨hcπ, -, h⟩
    exact h hcπ
  · intro hcs
    exact ⟨hs hcs, fun h => hx (h ▸ hs hcs), fun _ => hcs⟩

def merges (π : Finpartition (univ : Finset α)) : Finset (Finpartition (univ : Finset α)) :=
  (powersetCard 2 π.parts).image (mergeBlocks π)

theorem le_of_mem_merges (h : σ ∈ merges π) : π ≤ σ := by
  obtain ⟨s, -, rfl⟩ := mem_image.1 h
  exact le_mergeBlocks π s

theorem card_parts_of_mem_merges (h : σ ∈ merges π) : σ.parts.card + 1 = π.parts.card := by
  obtain ⟨s, hs, rfl⟩ := mem_image.1 h
  rw [mem_powersetCard] at hs
  exact card_parts_mergeBlocks hs.1 hs.2

theorem self_notMem_merges (π : Finpartition (univ : Finset α)) : π ∉ merges π := fun h => by
  have := card_parts_of_mem_merges h
  omega

theorem card_merges (π : Finpartition (univ : Finset α)) :
    (merges π).card = (π.parts.card).choose 2 := by
  rw [merges, card_image_of_injOn, card_powersetCard]
  intro s hs t ht hst
  rw [mem_coe, mem_powersetCard] at hs ht
  rw [← parts_sdiff_parts_mergeBlocks hs.1 hs.2, ← parts_sdiff_parts_mergeBlocks ht.1 ht.2]
  exact congrArg (fun ρ : Finpartition (univ : Finset α) => π.parts \ ρ.parts) hst

noncomputable def partitionQ :
    Matrix (Finpartition (univ : Finset α)) (Finpartition (univ : Finset α)) ℝ := fun π σ =>
  (if σ ∈ merges π then 1 else 0) - if σ = π then (coalRate π.parts.card : ℝ) else 0

attribute [-instance] CharZero.NeZero.two in

theorem coalRate_cast_eq_choose (k : ℕ) : (coalRate k : ℝ) = (k.choose 2 : ℕ) := by
  rw [Nat.cast_choose_two, coalRate]
  push_cast
  ring

variable (α) in

noncomputable def partitionChain : RateChain (Finpartition (univ : Finset α)) where
  Q := partitionQ
  off_diag_nonneg π σ h := by
    simp only [partitionQ, h.symm, ↓reduceIte, sub_zero]
    split_ifs <;> norm_num
  row_sum π := by
    simp only [partitionQ]
    rw [Finset.sum_sub_distrib, Finset.sum_boole, Finset.sum_ite_eq', ite_eq_left (mem_univ π),
      coalRate_cast_eq_choose, ← card_merges, sub_eq_zero]
    exact congrArg (fun t : Finset (Finpartition (univ : Finset α)) => (t.card : ℝ))
      (by ext σ; simp)

end Rhone.Coalescent

clear_aux_proof_cache
set_main_module Rhone.Coalescent.TajimaVarianceModel

namespace Rhone.Coalescent
open MeasureTheory ProbabilityTheory Finset
open scoped NNReal

attribute [-instance] T35Space.toT0Space UniformSpace.toCompletelyRegularSpace
  CompletelyRegularSpace.instRegularSpace

abbrev KingmanMutationHistory (n : ℕ) :=
  (ℕ → Finpartition (Finset.univ : Finset (Fin n))) × (ℕ → ℝ)

abbrev KingmanMutationBranch (n : ℕ) := Fin (n - 1) × Finset (Fin n)

noncomputable def kingmanBranchPairWeight (n : ℕ) (B : Finset (Fin n)) : ℝ :=
  2 * (B.card : ℝ) * (n - B.card) / ((n : ℝ) * (n - 1))

noncomputable def kingmanBranchMutationRate (n : ℕ) (θ : ℝ≥0)
    (h : KingmanMutationHistory n) (b : KingmanMutationBranch n) : ℝ≥0 :=
  ⟨if b.2 ∈ (h.1 b.1.val).parts ∧ 1 < (h.1 b.1.val).parts.card then
      max 0 ((θ : ℝ) / 2 *
        (Rhone.Coalescent.partitionChain (Fin n)).holdTime h b.1.val)
    else 0, by split_ifs <;> positivity⟩

theorem measurable_kingmanBranchMutationRate (n : ℕ) (θ : ℝ≥0)
    (b : KingmanMutationBranch n) :
    Measurable (fun h : KingmanMutationHistory n => kingmanBranchMutationRate n θ h b) := by
  apply Measurable.subtype_mk
  unfold Rhone.MarkovChain.RateChain.holdTime
  apply Measurable.ite
  · have hm : Measurable (fun h : KingmanMutationHistory n => h.1 b.1.val) :=
      (measurable_pi_apply b.1.val).comp measurable_fst
    exact hm (MeasurableSet.of_discrete (s :=
      {π : Finpartition (Finset.univ : Finset (Fin n)) |
        b.2 ∈ π.parts ∧ 1 < π.parts.card}))
  · have hr : Measurable (Rhone.Coalescent.partitionChain (Fin n)).rate :=
      Measurable.of_discrete
    fun_prop
  · fun_prop

noncomputable def kingmanBranchMutationKernel (n : ℕ) (θ : ℝ≥0) :
    Kernel (KingmanMutationHistory n) (KingmanMutationBranch n → ℕ) where
  toFun h := Measure.pi (fun b : KingmanMutationBranch n =>
    poissonMeasure (kingmanBranchMutationRate n θ h b))
  measurable' := by
    classical
    apply Measure.measurable_of_measurable_coe
    intro s hs
    have he : (fun h : KingmanMutationHistory n =>
        Measure.pi (fun b : KingmanMutationBranch n =>
          poissonMeasure (kingmanBranchMutationRate n θ h b)) s) =
        fun h => ∑' x : KingmanMutationBranch n → ℕ,
          s.indicator (fun x =>
            Measure.pi (fun b : KingmanMutationBranch n =>
              poissonMeasure (kingmanBranchMutationRate n θ h b)) {x}) x := by
      funext h
      exact (Measure.tsum_indicator_apply_singleton _ s hs).symm
    rw [he]
    apply Measurable.tsum
    intro x
    by_cases hx : x ∈ s
    · simp only [Set.indicator_of_mem hx, Measure.pi_singleton, poissonMeasure_singleton]
      apply Finset.measurable_prod
      intro b _
      have hb := measurable_kingmanBranchMutationRate n θ b
      fun_prop
    · simp only [Set.indicator_of_notMem hx]
      exact measurable_const

instance kingmanBranchMutationKernel_markov (n : ℕ) (θ : ℝ≥0) :
    IsMarkovKernel (kingmanBranchMutationKernel n θ) where
  isProbabilityMeasure h := by
    change IsProbabilityMeasure (Measure.pi (fun b : KingmanMutationBranch n =>
      poissonMeasure (kingmanBranchMutationRate n θ h b)))
    infer_instance

noncomputable def markedKingmanLaw (n : ℕ) (θ : ℝ≥0) :
    Measure (KingmanMutationHistory n × (Coalescent.KingmanMutationBranch n → ℕ)) :=
  ((Rhone.Coalescent.partitionChain (Fin n)).jumpHoldLaw ⊥).compProd
    (kingmanBranchMutationKernel n θ)

noncomputable def markedKingmanPi (n : ℕ)
    (x : KingmanMutationHistory n × (Coalescent.KingmanMutationBranch n → ℕ)) : ℝ :=
  ∑ b : KingmanMutationBranch n, kingmanBranchPairWeight n b.2 * (x.2 b : ℝ)

end Rhone.Coalescent

clear_aux_proof_cache
set_main_module Rhone.Statistics.Watterson

namespace Rhone.Statistics

open Finset Coalescent MarkovChain

def tajimaA1 (n : ℕ) : ℚ := harmonic (n - 1)

def tajimaA2 (n : ℕ) : ℚ := ∑ i ∈ Icc 1 (n - 1), (1 : ℚ) / (i : ℚ) ^ 2

def tajimaB1 (n : ℕ) : ℚ := ((n : ℚ) + 1) / (3 * ((n : ℚ) - 1))

def tajimaB2 (n : ℕ) : ℚ := 2 * ((n : ℚ) ^ 2 + n + 3) / (9 * n * ((n : ℚ) - 1))

end Rhone.Statistics

clear_aux_proof_cache
set_main_module Rhone.Statistics.SegregatingModel

namespace Rhone.Statistics
open MeasureTheory Finset

noncomputable def markedKingmanSegregating (n : ℕ)
    (x : Coalescent.KingmanMutationHistory n × (Coalescent.KingmanMutationBranch n → ℕ)) : ℝ :=
  ∑ b : Coalescent.KingmanMutationBranch n, (x.2 b : ℝ)

noncomputable def markedKingmanWatterson (n : ℕ)
    (x : Coalescent.KingmanMutationHistory n × (Coalescent.KingmanMutationBranch n → ℕ)) : ℝ :=
  markedKingmanSegregating n x / (tajimaA1 n : ℝ)

end Rhone.Statistics

clear_aux_proof_cache
set_main_module Palomar.KingmanSegregatingSites.Challenge

namespace Rhone.Palomar.KingmanSegregatingSites

open Coalescent Statistics MeasureTheory ProbabilityTheory
open scoped NNReal

theorem markedKingmanSegregating_mean {n : ℕ} (hn : 2 ≤ n) (θ : ℝ≥0) :
    (∫ x, markedKingmanSegregating n x ∂markedKingmanLaw n θ) =
      (θ : ℝ) * (tajimaA1 n : ℝ) := by
  sorry

theorem markedKingmanSegregating_variance {n : ℕ} (hn : 2 ≤ n) (θ : ℝ≥0) :
    ProbabilityTheory.variance (markedKingmanSegregating n) (markedKingmanLaw n θ) =
      (θ : ℝ) * (tajimaA1 n : ℝ) + (θ : ℝ) ^ 2 * (tajimaA2 n : ℝ) := by
  sorry

theorem markedKingmanWatterson_mean {n : ℕ} (hn : 2 ≤ n) (θ : ℝ≥0) :
    (∫ x, markedKingmanWatterson n x ∂markedKingmanLaw n θ) = (θ : ℝ) := by
  sorry

theorem markedKingmanWatterson_variance {n : ℕ} (hn : 2 ≤ n) (θ : ℝ≥0) :
    ProbabilityTheory.variance (markedKingmanWatterson n) (markedKingmanLaw n θ) =
      (θ : ℝ) / (tajimaA1 n : ℝ) +
        (θ : ℝ) ^ 2 * (tajimaA2 n : ℝ) / (tajimaA1 n : ℝ) ^ 2 := by
  sorry

theorem markedKingmanPi_mean {n : ℕ} (hn : 2 ≤ n) (θ : ℝ≥0) :
    ∫ x, markedKingmanPi n x ∂markedKingmanLaw n θ = θ := by
  sorry

theorem markedKingmanPi_variance {n : ℕ} (hn : 2 ≤ n) (θ : ℝ≥0) :
    ∫ x, (markedKingmanPi n x - θ) ^ 2 ∂markedKingmanLaw n θ =
      (Rhone.Statistics.tajimaB1 n : ℝ) * θ +
        (Rhone.Statistics.tajimaB2 n : ℝ) * (θ : ℝ) ^ 2 := by
  sorry

end Rhone.Palomar.KingmanSegregatingSites
