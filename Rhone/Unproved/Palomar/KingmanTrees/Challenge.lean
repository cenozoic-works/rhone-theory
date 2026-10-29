module

public import Mathlib

set_option maxSynthPendingDepth 3

@[expose] public section

elab "clear_aux_proof_cache" : command =>
  Lean.modifyEnv fun env => Lean.Meta.auxLemmasExt.setState env {}

elab "set_main_module " m:ident : command =>
  Lean.modifyEnv fun env => env.setMainModule m.getId

namespace ADR11

open Finset

section Kingman

variable {L : Type*} [Fintype L] [DecidableEq L]

def roots (F : Finset (Finset L)) : Finset (Finset L) :=
  F.filter fun A => ∀ B ∈ F, A ⊆ B → B = A

end Kingman

def singletonForest (n : ℕ) : Finset (Finset (Fin n)) :=
  univ.image fun l => {l}

variable {L : Type*} [Fintype L] [DecidableEq L]

def IsForest (F : Finset (Finset L)) : Prop :=
  (∀ A ∈ F, A.Nonempty) ∧ ∀ A ∈ F, ∀ B ∈ F, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B

def merges (F : Finset (Finset L)) : Finset (Finset (Finset L)) :=
  ((roots F ×ˢ roots F).filter fun p => p.1 ≠ p.2).image fun p => insert (p.1 ∪ p.2) F

noncomputable def jumpMatrix : Matrix (Finset (Finset L)) (Finset (Finset L)) ℝ :=
  fun F G =>
    if #(roots F) ≤ 1 then (if G = F then 1 else 0)
    else if G ∈ merges F then (((#(roots F)).choose 2 : ℕ) : ℝ)⁻¹ else 0

end ADR11

namespace ADR11

open Finset

variable {X : Type*} [Fintype X] [DecidableEq X]

def IsHierarchy (H : Finset (Finset X)) : Prop :=
  univ ∈ H ∧ (∀ x : X, {x} ∈ H) ∧ (∀ A ∈ H, A.Nonempty) ∧
    ∀ A ∈ H, ∀ B ∈ H, A ⊆ B ∨ B ⊆ A ∨ Disjoint A B

end ADR11

namespace ADR11

open Finset

def IsBinaryHierarchy {L : Type*} [Fintype L] [DecidableEq L] (G : Finset (Finset L)) : Prop :=
  IsHierarchy G ∧ ∀ A ∈ G, 2 ≤ #A → ∃ B ∈ G, ∃ C ∈ G, Disjoint B C ∧ B ∪ C = A

end ADR11

clear_aux_proof_cache

namespace Rhone.Combinatorics

open Finset

universe u

def RankedForestHistory {L : Type u} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) : ℕ → Type u
  | 0 => PUnit
  | t + 1 => Σ G : {G : Finset (Finset L) // G ∈ ADR11.merges F},
      RankedForestHistory G.1 t

noncomputable instance {L : Type*} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) (t : ℕ) : Fintype (RankedForestHistory F t) := by
  induction t generalizing F with
  | zero => change Fintype PUnit; infer_instance
  | succ t ih =>
    change Fintype (Σ G : {G : Finset (Finset L) // G ∈ ADR11.merges F},
      RankedForestHistory G.1 t)
    letI : ∀ G : {G : Finset (Finset L) // G ∈ ADR11.merges F},
      Fintype (RankedForestHistory G.1 t) := fun G => ih G.1
    infer_instance

abbrev RankedLabelledHistory (n : ℕ) :=
  RankedForestHistory (ADR11.singletonForest n) (n - 1)

def historyEnd {L : Type*} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) : (t : ℕ) → RankedForestHistory F t → Finset (Finset L)
  | 0, _ => F
  | t + 1, h => historyEnd h.1.1 t h.2

noncomputable def historyMass {L : Type*} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) : (t : ℕ) → RankedForestHistory F t → ℝ
  | 0, _ => 1
  | t + 1, h => ADR11.jumpMatrix F h.1.1 * historyMass h.1.1 t h.2

end Rhone.Combinatorics

clear_aux_proof_cache

namespace Rhone.Combinatorics

open Finset

universe u

def forestRelabel {L : Type u} [DecidableEq L] (e : L ≃ L)
    (F : Finset (Finset L)) : Finset (Finset L) :=
  F.image (fun C => C.map e.toEmbedding)

def historyAt {L : Type u} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) : (t : ℕ) → RankedForestHistory F t → ℕ → Finset (Finset L)
  | 0, _, _ => F
  | _t + 1, _, 0 => F
  | t + 1, h, k + 1 => historyAt h.1.1 t h.2 k

def RankedShapeRel (n : ℕ) (h h' : RankedLabelledHistory n) : Prop :=
  ∃ e : Equiv.Perm (Fin n), ∀ k ≤ n - 1,
    forestRelabel e (historyAt (ADR11.singletonForest n) (n - 1) h k) =
      historyAt (ADR11.singletonForest n) (n - 1) h' k

def UnrankedShapeRel (n : ℕ) (h h' : RankedLabelledHistory n) : Prop :=
  ∃ e : Equiv.Perm (Fin n),
    forestRelabel e (historyEnd (ADR11.singletonForest n) (n - 1) h) =
      historyEnd (ADR11.singletonForest n) (n - 1) h'

set_main_module Rhone.Combinatorics.KingmanShapes

private theorem forestRelabel_refl {L : Type*} [DecidableEq L]
    (F : Finset (Finset L)) : forestRelabel (Equiv.refl L) F = F := by
  simp [forestRelabel]

private theorem forestRelabel_trans {L : Type*} [DecidableEq L]
    (e f : L ≃ L) (F : Finset (Finset L)) :
    forestRelabel f (forestRelabel e F) = forestRelabel (e.trans f) F := by
  simp only [forestRelabel, image_image]
  congr 1
  funext C
  simp only [Function.comp_apply, map_map]
  rfl

theorem rankedShapeRel_equivalence (n : ℕ) : Equivalence (RankedShapeRel n) := by
  constructor
  · intro h
    exact ⟨Equiv.refl _, fun k hk => forestRelabel_refl _⟩
  · intro h h' hh
    obtain ⟨e, he⟩ := hh
    refine ⟨e.symm, fun k hk => ?_⟩
    rw [← he k hk, forestRelabel_trans]
    simpa using forestRelabel_refl
      (historyAt (ADR11.singletonForest n) (n - 1) h k)
  · intro h h' h'' hh hh'
    obtain ⟨e, he⟩ := hh
    obtain ⟨f, hf⟩ := hh'
    refine ⟨e.trans f, fun k hk => ?_⟩
    rw [← forestRelabel_trans, he k hk, hf k hk]

theorem unrankedShapeRel_equivalence (n : ℕ) : Equivalence (UnrankedShapeRel n) := by
  constructor
  · intro h
    exact ⟨Equiv.refl _, forestRelabel_refl _⟩
  · intro h h' hh
    obtain ⟨e, he⟩ := hh
    refine ⟨e.symm, ?_⟩
    rw [← he, forestRelabel_trans]
    simpa using forestRelabel_refl (historyEnd (ADR11.singletonForest n) (n - 1) h)
  · intro h h' h'' hh hh'
    obtain ⟨e, he⟩ := hh
    obtain ⟨f, hf⟩ := hh'
    refine ⟨e.trans f, ?_⟩
    rw [← forestRelabel_trans, he, hf]

set_main_module Palomar.KingmanTrees.Challenge

def rankedShapeSetoid (n : ℕ) : Setoid (RankedLabelledHistory n) :=
  ⟨RankedShapeRel n, rankedShapeRel_equivalence n⟩

def unrankedShapeSetoid (n : ℕ) : Setoid (RankedLabelledHistory n) :=
  ⟨UnrankedShapeRel n, unrankedShapeRel_equivalence n⟩

def RankedShape (n : ℕ) := Quotient (rankedShapeSetoid n)

def UnrankedShape (n : ℕ) := Quotient (unrankedShapeSetoid n)

noncomputable instance (n : ℕ) : Fintype (RankedShape n) := by
  unfold RankedShape
  exact Fintype.ofFinite _

noncomputable instance (n : ℕ) : Fintype (UnrankedShape n) := by
  unfold UnrankedShape
  exact Fintype.ofFinite _

end Rhone.Combinatorics

clear_aux_proof_cache

namespace Rhone

open Finset

noncomputable def Combinatorics.historyPayoff {L : Type*} [Fintype L] [DecidableEq L]
    (F : Finset (Finset L)) (t : ℕ) (f : Finset (Finset L) → ℝ) : ℝ :=
  ∑ h : Combinatorics.RankedForestHistory F t, Combinatorics.historyMass F t h * f
      (Combinatorics.historyEnd F t h)

abbrev Coalescent.LabelledTopology (n : ℕ) :=
  {G : Finset (Finset (Fin n)) // ADR11.IsBinaryHierarchy G}

noncomputable def Coalescent.topologyWeight (n : ℕ) (T : Coalescent.LabelledTopology n) : ℝ :=
  Combinatorics.historyPayoff (ADR11.singletonForest n) (n - 1) (fun G => if G = T.1 then 1 else 0)

def Coalescent.coalescentTopologyCladeProduct {n : ℕ} (T : Coalescent.LabelledTopology n) : ℕ :=
  ∏ C ∈ T.1.filter (fun C => 2 ≤ C.card), (C.card - 1)

noncomputable def Coalescent.rootSplitMass (n : ℕ) (A : Finset (Fin n)) : ℝ :=
  ∑ h : Combinatorics.RankedLabelledHistory n,
    if ADR11.roots ((Combinatorics.historyEnd (ADR11.singletonForest n) (n - 1) h).erase univ) =
      {A, univ \ A} then Combinatorics.historyMass (ADR11.singletonForest n) (n - 1) h else 0

noncomputable def Coalescent.samplePopulationRootMass (N : ℕ) (S : Finset (Fin N)) : ℝ :=
  ∑ h : Combinatorics.RankedLabelledHistory N,
    if ((ADR11.roots
        ((Combinatorics.historyEnd (ADR11.singletonForest N) (N - 1) h).erase univ)).filter
      (fun R => ¬Disjoint R S)).card = 2 then
      Combinatorics.historyMass (ADR11.singletonForest N) (N - 1) h else 0

noncomputable def Coalescent.treeColless {L : Type*} [Fintype L] [DecidableEq L]
    (G : Finset (Finset L)) : ℕ :=
  ∑ C ∈ G.filter (fun C => 2 ≤ C.card),
    let m := (ADR11.roots ((G.filter (fun D => D ⊆ C)).erase C)).sup Finset.card
    m - (C.card - m)

noncomputable def Coalescent.leafCladeDepth {L : Type*} [DecidableEq L]
    (G : Finset (Finset L)) (x : L) : ℕ :=
  (G.filter (fun C => x ∈ C)).card - 1

noncomputable def Coalescent.treeSackin {L : Type*} [Fintype L] [DecidableEq L]
    (G : Finset (Finset L)) : ℕ := ∑ x, Coalescent.leafCladeDepth G x

end Rhone

clear_aux_proof_cache

namespace Rhone.MarkovChain

open Finset Matrix

structure FinChain (S : Type*) [Fintype S] where

  P : Matrix S S ℝ

  nonneg : ∀ x y, 0 ≤ P x y

  row_sum : ∀ x, ∑ y, P x y = 1

namespace FinChain

variable {S : Type*} [Fintype S] [DecidableEq S] (C : FinChain S)

def stepN (n : ℕ) : Matrix S S ℝ := C.P ^ n

end FinChain

end Rhone.MarkovChain

clear_aux_proof_cache

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

namespace Rhone.Coalescent

open Finset

def coalRate (k : ℕ) : ℚ := k * (k - 1) / 2

end Rhone.Coalescent

clear_aux_proof_cache

namespace Rhone.Coalescent

open Finset MarkovChain

set_main_module Rhone.Coalescent.KingmanPartition

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

set_main_module Palomar.KingmanTrees.Challenge

end Rhone.Coalescent

namespace Rhone.Palomar.KingmanTrees

open Finset Coalescent Rhone.Combinatorics MarkovChain

theorem card_ranked_labelled_history (n : ℕ) (hn : 1 ≤ n) :
    Fintype.card (RankedLabelledHistory n) =
      n.factorial * (n - 1).factorial / 2 ^ (n - 1) := by
  sorry

theorem ranked_labelled_history_mass (n : ℕ) (hn : 1 ≤ n)
    (h : RankedLabelledHistory n) :
    historyMass (ADR11.singletonForest n) (n - 1) h =
      (2 : ℝ) ^ (n - 1) / ((n.factorial : ℝ) * ((n - 1).factorial : ℝ)) := by
  sorry

theorem card_ranked_shape_one : Fintype.card (RankedShape 1) = 1 := by
  sorry

theorem card_ranked_shape_two : Fintype.card (RankedShape 2) = 1 := by
  sorry

theorem card_unranked_shape_one : Fintype.card (UnrankedShape 1) = 1 := by
  sorry

theorem card_unranked_shape_two : Fintype.card (UnrankedShape 2) = 1 := by
  sorry

theorem card_ranked_shape_recurrence (n : ℕ) (hn : 3 ≤ n) :
    2 * Fintype.card (RankedShape n) =
      ∑ k ∈ Ico 1 n, (n - 2).choose (k - 1) *
        Fintype.card (RankedShape k) * Fintype.card (RankedShape (n - k)) := by
  sorry

theorem card_unranked_shape_recurrence (n : ℕ) (hn : 2 ≤ n) :
  Fintype.card (UnrankedShape n) =
    (∑ k ∈ Finset.Ico 1 ((n - 1) / 2 + 1),
      Fintype.card (UnrankedShape k) * Fintype.card (UnrankedShape (n - k))) +
    if Even n then
      Fintype.card (UnrankedShape (n / 2)) *
        (Fintype.card (UnrankedShape (n / 2)) + 1) / 2
    else 0 := by
  sorry

theorem kingman_topology_probability_of_clade_factors (n : ℕ) (hn : 1 ≤ n)
    (T : LabelledTopology n) :
    topologyWeight n T =
      (2 : ℝ) ^ (n - 1) / ((n.factorial : ℝ) * (coalescentTopologyCladeProduct T : ℝ)) := by
  sorry

theorem root_split_mass (n : ℕ) (hn : 2 ≤ n) (A : Finset (Fin n))
    (hA0 : 0 < A.card) (hAn : A.card < n) :
    rootSplitMass n A = (2 : ℝ) / ((n - 1 : ℕ) * (n.choose A.card : ℝ)) := by
  sorry

theorem sample_population_root_probability (N : ℕ) (hN : 2 ≤ N)
    (S : Finset (Fin N)) (hS : 1 ≤ S.card) :
    samplePopulationRootMass N S =
      ((S.card - 1 : ℕ) : ℝ) * (N + 1 : ℕ) /
        (((S.card + 1 : ℕ) : ℝ) * (N - 1 : ℕ)) := by
  sorry

theorem tendsto_sample_population_root_probability (n : ℕ) (hn : 1 ≤ n) :
    Filter.Tendsto
      (fun N => samplePopulationRootMass N
        (Finset.univ.filter (fun x : Fin N => x.val < n)))
      Filter.atTop (nhds (((n - 1 : ℕ) : ℝ) / (n + 1 : ℕ))) := by
  sorry

theorem kingman_colless_expectation (n : ℕ) (hn : 1 ≤ n) :
    historyPayoff (ADR11.singletonForest n) (n - 1) (fun G => (treeColless G : ℝ)) =
      (n : ℝ) * (((harmonic (n / 2) : ℚ) : ℝ)) - 2 * (n / 2 : ℕ) := by
  sorry

theorem kingman_sackin_expectation (n : ℕ) (hn : 1 ≤ n) :
    historyPayoff (ADR11.singletonForest n) (n - 1) (fun G => (treeSackin G : ℝ)) =
      2 * (n : ℝ) * (((harmonic n : ℚ) : ℝ) - 1) := by
  sorry

theorem historyPayoff_roots_eq_partition_stepN {L : Type*} [Fintype L] [DecidableEq L]
    {F : Finset (Finset L)} (hF : ADR11.IsForest F) (π : Finpartition (univ : Finset L))
    (hπ : π.parts = ADR11.roots F) (t : ℕ) (ht : t ≤ (ADR11.roots F).card - 1)
    (f : Finset (Finset L) → ℝ) :
    historyPayoff F t (fun G => f (ADR11.roots G)) =
      ∑ σ : Finpartition (univ : Finset L),
        (partitionChain L).jumpChain.stepN t π σ * f σ.parts := by
  sorry

theorem sum_jumpMatrix_roots_eq_partitionJump {L : Type*} [Fintype L] [DecidableEq L]
    {F : Finset (Finset L)} (hF : ADR11.IsForest F)
    (π σ : Finpartition (univ : Finset L)) (hπ : π.parts = ADR11.roots F) :
    (∑ G ∈ univ.filter (fun G : Finset (Finset L) => ADR11.roots G = σ.parts),
        ADR11.jumpMatrix F G) =
      (partitionChain L).jumpChain.P π σ := by
  sorry

end Rhone.Palomar.KingmanTrees
