/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.CanningsAncestral

/-!
# One-step expansion of the ancestral chain of a Cannings model

Source: mohle_sagitov2001, p. 1548, eq. (3). -/

@[expose] public section

namespace Rhone.Coalescent

open Finset

theorem vec2_injective {X : Type*} {x y : X} (h : x ≠ y) : Function.Injective ![x, y] :=
  Matrix.injective_pair_iff_ne.2 h

theorem vec3_injective {X : Type*} {x y z : X} (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    Function.Injective ![x, y, z] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> first
    | rfl
    | exact absurd hij hxy | exact absurd hij.symm hxy
    | exact absurd hij hyz | exact absurd hij.symm hyz
    | exact absurd hij hxz | exact absurd hij.symm hxz

theorem vec4_injective {X : Type*} {a b c d : X} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) : Function.Injective ![a, b, c, d] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> first
    | rfl
    | exact absurd hij hab | exact absurd hij.symm hab
    | exact absurd hij hac | exact absurd hij.symm hac
    | exact absurd hij had | exact absurd hij.symm had
    | exact absurd hij hbc | exact absurd hij.symm hbc
    | exact absurd hij hbd | exact absurd hij.symm hbd
    | exact absurd hij hcd | exact absurd hij.symm hcd

theorem card_filter_doublePair_le {ι : Type*} [Fintype ι] [DecidableEq ι] (ν : ι → ℕ) :
    (univ.filter fun u : Fin 4 ↪ Σ p, Fin (ν p) =>
      (u 0).1 = (u 1).1 ∧ (u 2).1 = (u 3).1).card ≤ (∑ p, (ν p).descFactorial 2) ^ 2 := by
  classical
  have h2 : (univ.filter fun u : Fin 2 ↪ Σ p, Fin (ν p) => ∀ y, (u y).1 = (u 0).1).card =
      ∑ p, (ν p).descFactorial 2 := by
    convert card_filter_embedding_fst_const (Y := Fin 2) ν 0
    exact (Fintype.card_fin 2).symm
  rw [sq, ← h2, ← card_product]
  refine card_le_card_of_injOn
    (fun u => ((⟨![0, 1], by decide⟩ : Fin 2 ↪ Fin 4).trans u,
      (⟨![2, 3], by decide⟩ : Fin 2 ↪ Fin 4).trans u)) ?_ ?_
  · intro u hu
    have hu' := (mem_filter.1 (mem_coe.1 hu)).2
    rw [mem_coe, mem_product, mem_filter, mem_filter]
    refine ⟨⟨mem_univ _, fun i => ?_⟩, mem_univ _, fun i => ?_⟩
    · fin_cases i
      · rfl
      · exact hu'.1.symm
    · fin_cases i
      · rfl
      · exact hu'.2.symm
  · intro u _ u' _ h
    have h1 := (Prod.ext_iff.1 h).1
    have h2' := (Prod.ext_iff.1 h).2
    ext i : 1
    fin_cases i
    · exact DFunLike.congr_fun h1 0
    · exact DFunLike.congr_fun h1 1
    · exact DFunLike.congr_fun h2' 0
    · exact DFunLike.congr_fun h2' 1

theorem mul_sub_one_le_add_div (a L : ℝ) (ha : 0 ≤ a) (hL : 1 ≤ L) :
    a * (a - 1) ≤ L * a + a * (a - 1) * (a - 2) / L := by
  have hL0 : 0 < L := by linarith
  have key : 0 ≤ (a - 1) ^ 2 - (L + 1) * (a - 1) + L ^ 2 := by
    nlinarith [sq_nonneg (2 * (a - 1) - L - 1),
      mul_nonneg (sub_nonneg.2 hL) (by linarith : (0 : ℝ) ≤ 3 * L + 1)]
  have e : L * a + a * (a - 1) * (a - 2) / L - a * (a - 1) =
      a * ((a - 1) ^ 2 - (L + 1) * (a - 1) + L ^ 2) / L := by
    field_simp
    ring
  have h := div_nonneg (mul_nonneg ha key) hL0.le
  linarith

end Rhone.Coalescent

namespace Rhone.MarkovChain.CanningsModel

open Finset Coalescent Rhone.Combinatorics

variable {N : ℕ} {Ω : Type*} [Fintype Ω] (M : CanningsModel N Ω) (ω : Ω)
variable {α : Type*} [Fintype α] [DecidableEq α] (π : Finpartition (univ : Finset α))

noncomputable def sameParentSet {k : ℕ} (x : Fin (k + 1) ↪ {B // B ∈ π.parts}) :
    Finset ({B // B ∈ π.parts} ↪ M.Child ω) :=
  univ.filter fun e => ∀ i, (e (x i)).1 = (e (x 0)).1

noncomputable def doublePairSet (x : Fin 4 ↪ {B // B ∈ π.parts}) :
    Finset ({B // B ∈ π.parts} ↪ M.Child ω) :=
  univ.filter fun e => (e (x 0)).1 = (e (x 1)).1 ∧ (e (x 2)).1 = (e (x 3)).1

open Classical in
noncomputable def badSet : Finset ({B // B ∈ π.parts} ↪ M.Child ω) :=
  (univ.biUnion fun x : Fin 3 ↪ {B // B ∈ π.parts} => M.sameParentSet ω π x) ∪
    univ.biUnion fun x : Fin 4 ↪ {B // B ∈ π.parts} => M.doublePairSet ω π x

noncomputable def stepCount (σ : Finpartition (univ : Finset α)) : ℕ :=
  (univ.filter fun e : {B // B ∈ π.parts} ↪ M.Child ω => M.parentPartition ω π e = σ).card

noncomputable def badBound (b : ℕ) : ℝ :=
  (b : ℝ) ^ 3 * ((M.tripleCount ω : ℝ) / (N.descFactorial 3 : ℝ)) +
    (b : ℝ) ^ 4 * ((M.pairCount ω : ℝ) ^ 2 / (N.descFactorial 4 : ℝ))

variable {ω π}

theorem card_sameParentSet_div (hb : π.parts.card ≤ N) {k : ℕ}
    (x : Fin (k + 1) ↪ {B // B ∈ π.parts}) :
    ((M.sameParentSet ω π x).card : ℝ) / (N.descFactorial π.parts.card : ℝ) =
      ((∑ p, (M.ν ω p).descFactorial (k + 1) : ℕ) : ℝ) / (N.descFactorial (k + 1) : ℝ) := by
  have hk : k + 1 ≤ π.parts.card := by
    have h := Fintype.card_le_of_embedding x
    rwa [Fintype.card_fin, Fintype.card_coe] at h
  have hcard : (M.sameParentSet ω π x).card =
      (∑ p, (M.ν ω p).descFactorial (Fintype.card (Fin (k + 1)))) *
        (∑ p, M.ν ω p - Fintype.card (Fin (k + 1))).descFactorial
          (Fintype.card {B // B ∈ π.parts} - Fintype.card (Fin (k + 1))) := by
    rw [sameParentSet]
    convert card_filter_sameParent (M.ν ω) x 0
  rw [M.sum_ν ω, Fintype.card_fin, Fintype.card_coe] at hcard
  have hdf := Nat.descFactorial_mul_descFactorial (n := N) hk
  have hA : ((N - (k + 1)).descFactorial (π.parts.card - (k + 1)) : ℝ) ≠ 0 :=
    cast_descFactorial_ne_zero (Nat.sub_le_sub_right hb _)
  rw [hcard, ← hdf, Nat.cast_mul, Nat.cast_mul,
    mul_comm ((N - (k + 1)).descFactorial (π.parts.card - (k + 1)) : ℝ),
    mul_div_mul_right _ _ hA]

theorem card_doublePairSet_div_le (hb : π.parts.card ≤ N)
    (x : Fin 4 ↪ {B // B ∈ π.parts}) :
    ((M.doublePairSet ω π x).card : ℝ) / (N.descFactorial π.parts.card : ℝ) ≤
      (M.pairCount ω : ℝ) ^ 2 / (N.descFactorial 4 : ℝ) := by
  have hk : 4 ≤ π.parts.card := by
    have h := Fintype.card_le_of_embedding x
    rwa [Fintype.card_fin, Fintype.card_coe] at h
  have hcard : (M.doublePairSet ω π x).card = _ :=
    card_filter_trans_embedding (C := M.Child ω) x
      (fun u => (u 0).1 = (u 1).1 ∧ (u 2).1 = (u 3).1)
  rw [M.card_child, Fintype.card_fin, Fintype.card_coe] at hcard
  have hle : ((univ.filter fun u : Fin 4 ↪ M.Child ω =>
      (u 0).1 = (u 1).1 ∧ (u 2).1 = (u 3).1).card : ℝ) ≤ (M.pairCount ω : ℝ) ^ 2 := by
    exact_mod_cast card_filter_doublePair_le (M.ν ω)
  have hdf := Nat.descFactorial_mul_descFactorial (n := N) hk
  have hA : ((N - 4).descFactorial (π.parts.card - 4) : ℝ) ≠ 0 :=
    cast_descFactorial_ne_zero (Nat.sub_le_sub_right hb _)
  rw [hcard, ← hdf, Nat.cast_mul, Nat.cast_mul,
    mul_comm ((N - 4).descFactorial (π.parts.card - 4) : ℝ), mul_div_mul_right _ _ hA]
  exact div_le_div_of_nonneg_right hle (Nat.cast_nonneg _)

theorem card_badSet_div_le (hb : π.parts.card ≤ N) :
    ((M.badSet ω π).card : ℝ) / (N.descFactorial π.parts.card : ℝ) ≤
      M.badBound ω π.parts.card := by
  classical
  have h1n : (M.badSet ω π).card ≤
      ∑ x : Fin 3 ↪ {B // B ∈ π.parts}, (M.sameParentSet ω π x).card +
        ∑ x : Fin 4 ↪ {B // B ∈ π.parts}, (M.doublePairSet ω π x).card :=
    (card_union_le _ _).trans (add_le_add card_biUnion_le card_biUnion_le)
  have h1 : ((M.badSet ω π).card : ℝ) ≤
      ∑ x : Fin 3 ↪ {B // B ∈ π.parts}, ((M.sameParentSet ω π x).card : ℝ) +
        ∑ x : Fin 4 ↪ {B // B ∈ π.parts}, ((M.doublePairSet ω π x).card : ℝ) := by
    exact_mod_cast h1n
  have hc3 : (Fintype.card (Fin 3 ↪ {B // B ∈ π.parts}) : ℝ) ≤ (π.parts.card : ℝ) ^ 3 := by
    rw [Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_coe]
    exact_mod_cast Nat.descFactorial_le_pow _ _
  have hc4 : (Fintype.card (Fin 4 ↪ {B // B ∈ π.parts}) : ℝ) ≤ (π.parts.card : ℝ) ^ 4 := by
    rw [Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_coe]
    exact_mod_cast Nat.descFactorial_le_pow _ _
  have hT : (0 : ℝ) ≤ (M.tripleCount ω : ℝ) / (N.descFactorial 3 : ℝ) := by positivity
  have hQ : (0 : ℝ) ≤ (M.pairCount ω : ℝ) ^ 2 / (N.descFactorial 4 : ℝ) := by positivity
  calc ((M.badSet ω π).card : ℝ) / (N.descFactorial π.parts.card : ℝ)
      ≤ (∑ x : Fin 3 ↪ {B // B ∈ π.parts}, ((M.sameParentSet ω π x).card : ℝ) +
          ∑ x : Fin 4 ↪ {B // B ∈ π.parts}, ((M.doublePairSet ω π x).card : ℝ)) /
            (N.descFactorial π.parts.card : ℝ) :=
        div_le_div_of_nonneg_right h1 (Nat.cast_nonneg _)
    _ = ∑ x : Fin 3 ↪ {B // B ∈ π.parts},
          ((M.sameParentSet ω π x).card : ℝ) / (N.descFactorial π.parts.card : ℝ) +
        ∑ x : Fin 4 ↪ {B // B ∈ π.parts},
          ((M.doublePairSet ω π x).card : ℝ) / (N.descFactorial π.parts.card : ℝ) := by
        rw [add_div, Finset.sum_div, Finset.sum_div]
    _ ≤ ∑ _x : Fin 3 ↪ {B // B ∈ π.parts},
          (M.tripleCount ω : ℝ) / (N.descFactorial 3 : ℝ) +
        ∑ _x : Fin 4 ↪ {B // B ∈ π.parts},
          (M.pairCount ω : ℝ) ^ 2 / (N.descFactorial 4 : ℝ) :=
        add_le_add (sum_le_sum fun x _ => (M.card_sameParentSet_div hb x).le)
          (sum_le_sum fun x _ => M.card_doublePairSet_div_le hb x)
    _ = (Fintype.card (Fin 3 ↪ {B // B ∈ π.parts}) : ℝ) *
          ((M.tripleCount ω : ℝ) / (N.descFactorial 3 : ℝ)) +
        (Fintype.card (Fin 4 ↪ {B // B ∈ π.parts}) : ℝ) *
          ((M.pairCount ω : ℝ) ^ 2 / (N.descFactorial 4 : ℝ)) := by
        rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Finset.card_univ,
          nsmul_eq_mul, nsmul_eq_mul]
    _ ≤ M.badBound ω π.parts.card :=
        add_le_add (mul_le_mul_of_nonneg_right hc3 hT) (mul_le_mul_of_nonneg_right hc4 hQ)

theorem eq_or_eq_of_notMem_badSet {e : {B // B ∈ π.parts} ↪ M.Child ω}
    (he : e ∉ M.badSet ω π) {u v u' v' : {B // B ∈ π.parts}} (huv : u ≠ v) (hu'v' : u' ≠ v')
    (h : (e u).1 = (e v).1) (h' : (e u').1 = (e v').1) :
    (u = u' ∧ v = v') ∨ (u = v' ∧ v = u') := by
  classical
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨h1, h2⟩ := hcon
  apply he
  rw [badSet, mem_union, mem_biUnion, mem_biUnion]
  by_cases a : u = u'
  · subst a
    have hvv' : v ≠ v' := fun hv => h1 ⟨rfl, hv⟩
    refine Or.inl ⟨⟨![u, v, v'], vec3_injective huv hvv' hu'v'⟩, mem_univ _, ?_⟩
    rw [sameParentSet, mem_filter]
    refine ⟨mem_univ _, fun i => ?_⟩
    fin_cases i
    · rfl
    · exact h.symm
    · exact h'.symm
  by_cases b : u = v'
  · subst b
    have hvu' : v ≠ u' := fun hv => h2 ⟨rfl, hv⟩
    refine Or.inl ⟨⟨![u, v, u'], vec3_injective huv hvu' a⟩, mem_univ _, ?_⟩
    rw [sameParentSet, mem_filter]
    refine ⟨mem_univ _, fun i => ?_⟩
    fin_cases i
    · rfl
    · exact h.symm
    · exact h'
  by_cases c : v = u'
  · subst c
    refine Or.inl ⟨⟨![u, v, v'], vec3_injective huv hu'v' b⟩, mem_univ _, ?_⟩
    rw [sameParentSet, mem_filter]
    refine ⟨mem_univ _, fun i => ?_⟩
    fin_cases i
    · rfl
    · exact h.symm
    · exact (h.trans h').symm
  by_cases d : v = v'
  · subst d
    refine Or.inl ⟨⟨![u, v, u'], vec3_injective huv hu'v'.symm a⟩, mem_univ _, ?_⟩
    rw [sameParentSet, mem_filter]
    refine ⟨mem_univ _, fun i => ?_⟩
    fin_cases i
    · rfl
    · exact h.symm
    · exact h'.trans h.symm
  · refine Or.inr ⟨⟨![u, v, u', v'], vec4_injective huv a b c d hu'v'⟩, mem_univ _, ?_⟩
    rw [doublePairSet, mem_filter]
    exact ⟨mem_univ _, h, h'⟩

theorem parentPartition_eq_mergeBlocks {e : {B // B ∈ π.parts} ↪ M.Child ω}
    (he : e ∉ M.badSet ω π) {x y : {B // B ∈ π.parts}} (hxy : x ≠ y)
    (hg : (e x).1 = (e y).1) : M.parentPartition ω π e = mergeBlocks π {x.1, y.1} :=
  kerPartition_blockOf_of_pair (fun z => (e z).1) hg fun u v huv h => by
    rcases M.eq_or_eq_of_notMem_badSet he hxy huv hg h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1.symm, h2.symm⟩
    · exact Or.inr ⟨h2.symm, h1.symm⟩

theorem parentPartition_eq_or_mem_merges {e : {B // B ∈ π.parts} ↪ M.Child ω}
    (he : e ∉ M.badSet ω π) :
    M.parentPartition ω π e = π ∨ M.parentPartition ω π e ∈ merges π := by
  by_cases hinj : Function.Injective fun x => (e x).1
  · exact Or.inl (kerPartition_blockOf_of_injective _ hinj)
  · rw [Function.Injective] at hinj
    push Not at hinj
    obtain ⟨u, v, hg, huv⟩ := hinj
    rw [M.parentPartition_eq_mergeBlocks he huv hg]
    exact Or.inr (mergeBlocks_pair_mem_merges huv)

theorem fst_eq_of_parentPartition_eq {e : {B // B ∈ π.parts} ↪ M.Child ω}
    {x y : {B // B ∈ π.parts}} (h : M.parentPartition ω π e = mergeBlocks π {x.1, y.1}) :
    (e x).1 = (e y).1 :=
  apply_eq_of_kerPartition_blockOf_eq (fun z => (e z).1) h

theorem stepCount_div_le_badBound (hb : π.parts.card ≤ N)
    {σ : Finpartition (univ : Finset α)} (hσ : σ ≠ π) (hσ' : σ ∉ merges π) :
    (M.stepCount ω π σ : ℝ) / (N.descFactorial π.parts.card : ℝ) ≤
      M.badBound ω π.parts.card := by
  have hsub : (univ.filter fun e : {B // B ∈ π.parts} ↪ M.Child ω =>
      M.parentPartition ω π e = σ) ⊆ M.badSet ω π := by
    intro e he
    by_contra hbad
    rcases M.parentPartition_eq_or_mem_merges hbad with h | h
    · exact hσ ((mem_filter.1 he).2.symm.trans h)
    · exact hσ' ((mem_filter.1 he).2 ▸ h)
  exact (div_le_div_of_nonneg_right (Nat.cast_le.2 (card_le_card hsub))
    (Nat.cast_nonneg _)).trans (M.card_badSet_div_le hb)

theorem stepCount_mergeBlocks_div_le (hb : π.parts.card ≤ N) {x y : {B // B ∈ π.parts}}
    (hxy : x ≠ y) :
    (M.stepCount ω π (mergeBlocks π {x.1, y.1}) : ℝ) / (N.descFactorial π.parts.card : ℝ) ≤
      (M.pairCount ω : ℝ) / (N.descFactorial 2 : ℝ) := by
  have hsub : (univ.filter fun e : {B // B ∈ π.parts} ↪ M.Child ω =>
      M.parentPartition ω π e = mergeBlocks π {x.1, y.1}) ⊆
      M.sameParentSet ω π ⟨![x, y], vec2_injective hxy⟩ := by
    intro e he
    rw [sameParentSet, mem_filter]
    refine ⟨mem_univ _, fun i => ?_⟩
    fin_cases i
    · rfl
    · exact (M.fst_eq_of_parentPartition_eq (mem_filter.1 he).2).symm
  exact (div_le_div_of_nonneg_right (Nat.cast_le.2 (card_le_card hsub))
    (Nat.cast_nonneg _)).trans (M.card_sameParentSet_div hb _).le

theorem pairCount_div_le_stepCount_add (hb : π.parts.card ≤ N) {x y : {B // B ∈ π.parts}}
    (hxy : x ≠ y) :
    (M.pairCount ω : ℝ) / (N.descFactorial 2 : ℝ) ≤
      (M.stepCount ω π (mergeBlocks π {x.1, y.1}) : ℝ) / (N.descFactorial π.parts.card : ℝ) +
        M.badBound ω π.parts.card := by
  classical
  have hsub : M.sameParentSet ω π ⟨![x, y], vec2_injective hxy⟩ ⊆
      (univ.filter fun e : {B // B ∈ π.parts} ↪ M.Child ω =>
        M.parentPartition ω π e = mergeBlocks π {x.1, y.1}) ∪ M.badSet ω π := by
    intro e he
    rw [sameParentSet, mem_filter] at he
    have h : (e y).1 = (e x).1 := he.2 1
    by_cases hbad : e ∈ M.badSet ω π
    · exact mem_union_right _ hbad
    · exact mem_union_left _
        (mem_filter.2 ⟨mem_univ _, M.parentPartition_eq_mergeBlocks hbad hxy h.symm⟩)
  have hn : (M.sameParentSet ω π ⟨![x, y], vec2_injective hxy⟩).card ≤
      M.stepCount ω π (mergeBlocks π {x.1, y.1}) + (M.badSet ω π).card :=
    (card_le_card hsub).trans (card_union_le _ _)
  have hr : ((M.sameParentSet ω π ⟨![x, y], vec2_injective hxy⟩).card : ℝ) ≤
      (M.stepCount ω π (mergeBlocks π {x.1, y.1}) : ℝ) + ((M.badSet ω π).card : ℝ) := by
    exact_mod_cast hn
  have h1 := div_le_div_of_nonneg_right hr
    (Nat.cast_nonneg (N.descFactorial π.parts.card) : (0 : ℝ) ≤ _)
  have h2 : ((M.sameParentSet ω π ⟨![x, y], vec2_injective hxy⟩).card : ℝ) /
      (N.descFactorial π.parts.card : ℝ) = (M.pairCount ω : ℝ) / (N.descFactorial 2 : ℝ) :=
    M.card_sameParentSet_div hb _
  rw [h2, add_div] at h1
  linarith [M.card_badSet_div_le (ω := ω) hb]

noncomputable def doublePairProb : ℝ :=
  ∑ ω, M.w ω * ((M.pairCount ω : ℝ) ^ 2 / (N.descFactorial 4 : ℝ))

noncomputable def expansionRemainder (b : ℕ) : ℝ :=
  (b : ℝ) ^ 3 * M.tripleCoalProb + (b : ℝ) ^ 4 * M.doublePairProb

theorem doublePairProb_nonneg : 0 ≤ M.doublePairProb :=
  sum_nonneg fun ω _ => mul_nonneg (M.w_nonneg ω) (by positivity)

theorem expansionRemainder_nonneg (b : ℕ) : 0 ≤ M.expansionRemainder b :=
  add_nonneg (mul_nonneg (by positivity) M.tripleCoalProb_nonneg)
    (mul_nonneg (by positivity) M.doublePairProb_nonneg)

theorem expansionRemainder_mono {b b' : ℕ} (h : b ≤ b') :
    M.expansionRemainder b ≤ M.expansionRemainder b' := by
  have hr : (b : ℝ) ≤ b' := Nat.cast_le.2 h
  exact add_le_add
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hr 3)
      M.tripleCoalProb_nonneg)
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hr 4)
      M.doublePairProb_nonneg)

theorem sum_w_mul_badBound (b : ℕ) :
    ∑ ω, M.w ω * M.badBound ω b = M.expansionRemainder b := by
  simp only [badBound, mul_add, Finset.sum_add_distrib]
  rw [expansionRemainder, tripleCoalProb_eq_sum, doublePairProb, Finset.mul_sum, Finset.mul_sum]
  congr 1 <;> exact sum_congr rfl fun ω _ => by ring

theorem ancestralMatrix_eq_sum (π σ : Finpartition (univ : Finset α)) :
    M.ancestralMatrix α π σ =
      ∑ ω, M.w ω * ((M.stepCount ω π σ : ℝ) / (N.descFactorial π.parts.card : ℝ)) :=
  sum_congr rfl fun _ _ => mul_div_assoc _ _ _

theorem ancestralMatrix_le_expansionRemainder (hb : π.parts.card ≤ N)
    {σ : Finpartition (univ : Finset α)} (hσ : σ ≠ π) (hσ' : σ ∉ merges π) :
    M.ancestralMatrix α π σ ≤ M.expansionRemainder π.parts.card := by
  rw [ancestralMatrix_eq_sum, ← M.sum_w_mul_badBound]
  exact sum_le_sum fun ω _ =>
    mul_le_mul_of_nonneg_left (M.stepCount_div_le_badBound hb hσ hσ') (M.w_nonneg ω)

theorem ancestralMatrix_mergeBlocks_le (hb : π.parts.card ≤ N) {x y : {B // B ∈ π.parts}}
    (hxy : x ≠ y) : M.ancestralMatrix α π (mergeBlocks π {x.1, y.1}) ≤ M.pairCoalProb := by
  rw [ancestralMatrix_eq_sum, pairCoalProb_eq_sum]
  exact sum_le_sum fun ω _ =>
    mul_le_mul_of_nonneg_left (M.stepCount_mergeBlocks_div_le hb hxy) (M.w_nonneg ω)

theorem pairCoalProb_le_ancestralMatrix_add (hb : π.parts.card ≤ N)
    {x y : {B // B ∈ π.parts}} (hxy : x ≠ y) :
    M.pairCoalProb ≤ M.ancestralMatrix α π (mergeBlocks π {x.1, y.1}) +
      M.expansionRemainder π.parts.card := by
  rw [ancestralMatrix_eq_sum, pairCoalProb_eq_sum, ← M.sum_w_mul_badBound,
    ← Finset.sum_add_distrib]
  refine sum_le_sum fun ω _ => ?_
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (M.pairCount_div_le_stepCount_add hb hxy) (M.w_nonneg ω)

theorem abs_ancestralMatrix_sub_le (h : Fintype.card α ≤ N)
    (π σ : Finpartition (univ : Finset α)) :
    |M.ancestralMatrix α π σ - (1 : Matrix _ _ ℝ) π σ - M.pairCoalProb * partitionQ π σ| ≤
      (Fintype.card (Finpartition (univ : Finset α)) : ℝ) *
        M.expansionRemainder π.parts.card := by
  have hb := card_parts_le_of_card_le h π
  have hr := M.expansionRemainder_nonneg π.parts.card
  have hK1 : (1 : ℝ) ≤ (Fintype.card (Finpartition (univ : Finset α)) : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.2 ⟨π⟩
  have hP0 := M.ancestralMatrix_nonneg π σ
  by_cases hσ : σ = π
  · subst hσ
    have hsub : merges σ ⊆ univ.erase σ := fun τ hτ =>
      mem_erase.2 ⟨fun hτσ => self_notMem_merges σ (hτσ ▸ hτ), mem_univ _⟩
    have hrow := M.ancestralMatrix_row_sum h σ
    rw [← Finset.add_sum_erase univ _ (mem_univ σ), ← Finset.sum_sdiff hsub] at hrow
    have hm_up : ∑ τ ∈ merges σ, M.ancestralMatrix α σ τ ≤
        (merges σ).card * M.pairCoalProb := by
      rw [← nsmul_eq_mul]
      refine sum_le_card_nsmul _ _ _ fun τ hτ => ?_
      obtain ⟨x, y, hxy, rfl⟩ := exists_pair_of_mem_merges hτ
      exact M.ancestralMatrix_mergeBlocks_le hb hxy
    have hm_lo : (merges σ).card * (M.pairCoalProb - M.expansionRemainder σ.parts.card) ≤
        ∑ τ ∈ merges σ, M.ancestralMatrix α σ τ := by
      rw [← nsmul_eq_mul]
      refine card_nsmul_le_sum _ _ _ fun τ hτ => ?_
      obtain ⟨x, y, hxy, rfl⟩ := exists_pair_of_mem_merges hτ
      linarith [M.pairCoalProb_le_ancestralMatrix_add hb hxy]
    have hrest0 : 0 ≤ ∑ τ ∈ univ.erase σ \ merges σ, M.ancestralMatrix α σ τ :=
      sum_nonneg fun τ _ => M.ancestralMatrix_nonneg σ τ
    have hrest : ∑ τ ∈ univ.erase σ \ merges σ, M.ancestralMatrix α σ τ ≤
        (Fintype.card (Finpartition (univ : Finset α)) : ℝ) *
          M.expansionRemainder σ.parts.card := by
      have h1 : ∑ τ ∈ univ.erase σ \ merges σ, M.ancestralMatrix α σ τ ≤
          (univ.erase σ \ merges σ).card * M.expansionRemainder σ.parts.card := by
        rw [← nsmul_eq_mul]
        refine sum_le_card_nsmul _ _ _ fun τ hτ => ?_
        rw [mem_sdiff, mem_erase] at hτ
        exact M.ancestralMatrix_le_expansionRemainder hb hτ.1.1 hτ.2
      refine h1.trans (mul_le_mul_of_nonneg_right ?_ hr)
      exact_mod_cast card_le_univ _
    have hmK : ((merges σ).card : ℝ) * M.expansionRemainder σ.parts.card ≤
        (Fintype.card (Finpartition (univ : Finset α)) : ℝ) *
          M.expansionRemainder σ.parts.card :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast card_le_univ _) hr
    have hQ : partitionQ σ σ = -((merges σ).card : ℝ) := by
      rw [partitionQ, ite_eq_right (self_notMem_merges σ), ite_eq_left rfl, coalRate_cast_eq_choose,
        card_merges]
      ring
    rw [hQ, Matrix.one_apply_eq, abs_le]
    constructor <;> nlinarith
  · have h1 : (1 : Matrix (Finpartition (univ : Finset α)) _ ℝ) π σ = 0 :=
      Matrix.one_apply_ne (Ne.symm hσ)
    by_cases hσ' : σ ∈ merges π
    · obtain ⟨x, y, hxy, rfl⟩ := exists_pair_of_mem_merges hσ'
      have hQ : partitionQ π (mergeBlocks π {x.1, y.1}) = 1 := by
        rw [partitionQ, ite_eq_left hσ', ite_eq_right hσ]
        ring
      have hup := M.ancestralMatrix_mergeBlocks_le hb hxy
      have hlo := M.pairCoalProb_le_ancestralMatrix_add hb hxy
      rw [hQ, h1, abs_le]
      constructor <;> nlinarith
    · have hQ : partitionQ π σ = 0 := by
        rw [partitionQ, ite_eq_right hσ', ite_eq_right hσ]
        ring
      have hup := M.ancestralMatrix_le_expansionRemainder hb hσ hσ'
      rw [hQ, h1, abs_le]
      constructor <;> nlinarith

theorem abs_ancestralMatrix_sub_le_card (h : Fintype.card α ≤ N)
    (π σ : Finpartition (univ : Finset α)) :
    |M.ancestralMatrix α π σ - (1 : Matrix _ _ ℝ) π σ - M.pairCoalProb * partitionQ π σ| ≤
      (Fintype.card (Finpartition (univ : Finset α)) : ℝ) *
        M.expansionRemainder (Fintype.card α) :=
  (M.abs_ancestralMatrix_sub_le h π σ).trans (mul_le_mul_of_nonneg_left
    (M.expansionRemainder_mono (π.card_parts_le_card.trans_eq Finset.card_univ))
    (Nat.cast_nonneg _))

theorem ν_le (ω : Ω) (p : Fin N) : M.ν ω p ≤ N :=
  (single_le_sum (f := M.ν ω) (fun _ _ => Nat.zero_le _) (mem_univ p)).trans_eq (M.sum_ν ω)

theorem sum_ν_cast (ω : Ω) : ∑ p, (M.ν ω p : ℝ) = N := by
  exact_mod_cast M.sum_ν ω

theorem pairCount_cast (ω : Ω) :
    (M.pairCount ω : ℝ) = ∑ p, (M.ν ω p : ℝ) * ((M.ν ω p : ℝ) - 1) := by
  rw [pairCount, Nat.cast_sum]
  exact sum_congr rfl fun p _ => Nat.cast_descFactorial_two ℝ _

theorem tripleCount_cast (ω : Ω) :
    (M.tripleCount ω : ℝ) =
      ∑ p, (M.ν ω p : ℝ) * ((M.ν ω p : ℝ) - 1) * ((M.ν ω p : ℝ) - 2) := by
  rw [tripleCount, Nat.cast_sum]
  exact sum_congr rfl fun p _ => cast_descFactorial_three _

theorem pairCount_le (ω : Ω) : (M.pairCount ω : ℝ) ≤ N * ((N : ℝ) - 1) := by
  rw [pairCount_cast, ← M.sum_ν_cast ω, Finset.sum_mul]
  refine sum_le_sum fun p _ => mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  have h : (M.ν ω p : ℝ) ≤ N := Nat.cast_le.2 (M.ν_le ω p)
  rw [M.sum_ν_cast ω]
  linarith

theorem pairCount_le_add (ω : Ω) {L : ℝ} (hL : 1 ≤ L) :
    (M.pairCount ω : ℝ) ≤ L * N + (M.tripleCount ω : ℝ) / L := by
  rw [pairCount_cast, tripleCount_cast, ← M.sum_ν_cast ω, Finset.mul_sum, Finset.sum_div,
    ← Finset.sum_add_distrib]
  exact sum_le_sum fun p _ => mul_sub_one_le_add_div _ _ (Nat.cast_nonneg _) hL

theorem tripleCount_le (ω : Ω) : M.tripleCount ω ≤ (N - 2) * M.pairCount ω := by
  rw [tripleCount, pairCount, Finset.mul_sum]
  refine sum_le_sum fun p _ => ?_
  rw [Nat.descFactorial_succ]
  exact Nat.mul_le_mul_right _ (Nat.sub_le_sub_right (M.ν_le ω p) 2)

theorem tripleCoalProb_le_pairCoalProb : M.tripleCoalProb ≤ M.pairCoalProb := by
  rw [tripleCoalProb_eq_sum, pairCoalProb_eq_sum]
  refine sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left ?_ (M.w_nonneg ω)
  by_cases hN : N < 3
  · rw [Nat.descFactorial_eq_zero_iff_lt.2 hN, Nat.cast_zero, div_zero]
    positivity
  · have h3 : N.descFactorial 3 = (N - 2) * N.descFactorial 2 := Nat.descFactorial_succ N 2
    have h2pos : (0 : ℝ) < (N.descFactorial 2 : ℝ) :=
      Nat.cast_pos.2 (Nat.descFactorial_pos.2 (by omega))
    have h3pos : (0 : ℝ) < (N.descFactorial 3 : ℝ) :=
      Nat.cast_pos.2 (Nat.descFactorial_pos.2 (by omega))
    rw [div_le_div_iff₀ h3pos h2pos, h3]
    have hn : M.tripleCount ω * N.descFactorial 2 ≤
        M.pairCount ω * ((N - 2) * N.descFactorial 2) := by
      calc M.tripleCount ω * N.descFactorial 2
          ≤ (N - 2) * M.pairCount ω * N.descFactorial 2 :=
            Nat.mul_le_mul_right _ (M.tripleCount_le ω)
        _ = M.pairCount ω * ((N - 2) * N.descFactorial 2) := by ring
    exact_mod_cast hn

theorem sum_w_mul_pairCount (hN : 2 ≤ N) :
    ∑ ω, M.w ω * (M.pairCount ω : ℝ) = M.pairCoalProb * ((N : ℝ) * ((N : ℝ) - 1)) := by
  have hpos : (N.descFactorial 2 : ℝ) ≠ 0 := cast_descFactorial_ne_zero hN
  rw [pairCoalProb_eq_sum, Finset.sum_mul, ← Nat.cast_descFactorial_two ℝ N]
  refine sum_congr rfl fun ω _ => ?_
  field_simp

theorem sum_w_mul_tripleCount (hN : 3 ≤ N) :
    ∑ ω, M.w ω * (M.tripleCount ω : ℝ) =
      M.tripleCoalProb * ((N : ℝ) * ((N : ℝ) - 1) * ((N : ℝ) - 2)) := by
  have hpos : (N.descFactorial 3 : ℝ) ≠ 0 := cast_descFactorial_ne_zero hN
  rw [tripleCoalProb_eq_sum, Finset.sum_mul, ← cast_descFactorial_three N]
  refine sum_congr rfl fun ω _ => ?_
  field_simp

theorem cast_descFactorial_four (hN : 3 ≤ N) :
    (N.descFactorial 4 : ℝ) = (N : ℝ) * ((N : ℝ) - 1) * ((N : ℝ) - 2) * ((N : ℝ) - 3) := by
  rw [Nat.descFactorial_succ, Nat.cast_mul, cast_descFactorial_three, Nat.cast_sub hN]
  push_cast
  ring

theorem sum_w_mul_pairCount_sq (hN : 4 ≤ N) :
    ∑ ω, M.w ω * (M.pairCount ω : ℝ) ^ 2 =
      M.doublePairProb * ((N : ℝ) * ((N : ℝ) - 1) * ((N : ℝ) - 2) * ((N : ℝ) - 3)) := by
  have hpos : (N.descFactorial 4 : ℝ) ≠ 0 := cast_descFactorial_ne_zero hN
  rw [doublePairProb, Finset.sum_mul, ← cast_descFactorial_four (by omega)]
  refine sum_congr rfl fun ω _ => ?_
  field_simp

theorem doublePairProb_le (hN : 6 ≤ N) {ε : ℝ} (hε : 0 < ε) (hεN : 1 ≤ ε * N) :
    M.doublePairProb ≤ 4 * ε * M.pairCoalProb + 2 * M.tripleCoalProb / ε := by
  have hn : (6 : ℝ) ≤ N := by exact_mod_cast hN
  have hc := M.pairCoalProb_nonneg
  have hd := M.tripleCoalProb_nonneg
  obtain ⟨n, hnN⟩ : ∃ n : ℝ, n = N := ⟨_, rfl⟩
  rw [← hnN] at hn hεN
  have hpt : ∀ ω, (M.pairCount ω : ℝ) ^ 2 ≤
      ε * n ^ 2 * (M.pairCount ω : ℝ) + (n - 1) / ε * (M.tripleCount ω : ℝ) := by
    intro ω
    have hP0 : (0 : ℝ) ≤ M.pairCount ω := Nat.cast_nonneg _
    have hT0 : (0 : ℝ) ≤ M.tripleCount ω := Nat.cast_nonneg _
    have hP1 := M.pairCount_le ω
    have hP2 := M.pairCount_le_add ω hεN
    rw [← hnN] at hP1 hP2
    have hL0 : 0 < ε * n := by linarith
    have h1 : (M.pairCount ω : ℝ) ^ 2 ≤
        (M.pairCount ω : ℝ) * (ε * n * n + (M.tripleCount ω : ℝ) / (ε * n)) := by
      rw [sq]
      exact mul_le_mul_of_nonneg_left hP2 hP0
    have h2 : (M.pairCount ω : ℝ) * ((M.tripleCount ω : ℝ) / (ε * n)) ≤
        n * (n - 1) * ((M.tripleCount ω : ℝ) / (ε * n)) :=
      mul_le_mul_of_nonneg_right hP1 (div_nonneg hT0 hL0.le)
    have h3 : n * (n - 1) * ((M.tripleCount ω : ℝ) / (ε * n)) =
        (n - 1) / ε * (M.tripleCount ω : ℝ) := by
      have hn0 : n ≠ 0 := by linarith
      field_simp
    calc (M.pairCount ω : ℝ) ^ 2
        ≤ (M.pairCount ω : ℝ) * (ε * n * n + (M.tripleCount ω : ℝ) / (ε * n)) := h1
      _ = ε * n ^ 2 * (M.pairCount ω : ℝ) +
            (M.pairCount ω : ℝ) * ((M.tripleCount ω : ℝ) / (ε * n)) := by ring
      _ ≤ ε * n ^ 2 * (M.pairCount ω : ℝ) + (n - 1) / ε * (M.tripleCount ω : ℝ) := by
          linarith
  have hmean : ∑ ω, M.w ω * (M.pairCount ω : ℝ) ^ 2 ≤
      ε * n ^ 2 * ∑ ω, M.w ω * (M.pairCount ω : ℝ) +
        (n - 1) / ε * ∑ ω, M.w ω * (M.tripleCount ω : ℝ) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine sum_le_sum fun ω _ => ?_
    have := mul_le_mul_of_nonneg_left (hpt ω) (M.w_nonneg ω)
    linarith
  rw [M.sum_w_mul_pairCount_sq (by omega), M.sum_w_mul_pairCount (by omega),
    M.sum_w_mul_tripleCount (by omega), ← hnN] at hmean
  have hD4 : 0 < n * (n - 1) * (n - 2) * (n - 3) := by
    have h1 : 0 < n := by linarith
    have h2 : 0 < n - 1 := by linarith
    have h3 : 0 < n - 2 := by linarith
    have h4 : 0 < n - 3 := by linarith
    positivity
  have hA : ε * n ^ 2 * (M.pairCoalProb * (n * (n - 1))) ≤
      4 * ε * M.pairCoalProb * (n * (n - 1) * (n - 2) * (n - 3)) := by
    have h0 : 0 ≤ ε * M.pairCoalProb * (n * (n - 1)) :=
      mul_nonneg (mul_nonneg hε.le hc) (mul_nonneg (by linarith) (by linarith))
    have h' : n ^ 2 ≤ 4 * ((n - 2) * (n - 3)) := by nlinarith
    calc ε * n ^ 2 * (M.pairCoalProb * (n * (n - 1)))
        = ε * M.pairCoalProb * (n * (n - 1)) * n ^ 2 := by ring
      _ ≤ ε * M.pairCoalProb * (n * (n - 1)) * (4 * ((n - 2) * (n - 3))) :=
          mul_le_mul_of_nonneg_left h' h0
      _ = 4 * ε * M.pairCoalProb * (n * (n - 1) * (n - 2) * (n - 3)) := by ring
  have hB : (n - 1) / ε * (M.tripleCoalProb * (n * (n - 1) * (n - 2))) ≤
      2 * M.tripleCoalProb / ε * (n * (n - 1) * (n - 2) * (n - 3)) := by
    have h0 : 0 ≤ M.tripleCoalProb / ε * (n * (n - 1) * (n - 2)) :=
      mul_nonneg (div_nonneg hd hε.le)
        (mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith))
    calc (n - 1) / ε * (M.tripleCoalProb * (n * (n - 1) * (n - 2)))
        = M.tripleCoalProb / ε * (n * (n - 1) * (n - 2)) * (n - 1) := by ring
      _ ≤ M.tripleCoalProb / ε * (n * (n - 1) * (n - 2)) * (2 * (n - 3)) :=
          mul_le_mul_of_nonneg_left (by linarith) h0
      _ = 2 * M.tripleCoalProb / ε * (n * (n - 1) * (n - 2) * (n - 3)) := by ring
  refine le_of_mul_le_mul_right ?_ hD4
  rw [add_mul]
  linarith

theorem pairCoalProb_le (hN : 3 ≤ N) {ε : ℝ} (hε : 0 < ε) (hεN : 1 ≤ ε * N) :
    M.pairCoalProb ≤ 2 * ε + M.tripleCoalProb / ε := by
  have hn : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hd := M.tripleCoalProb_nonneg
  obtain ⟨n, hnN⟩ : ∃ n : ℝ, n = N := ⟨_, rfl⟩
  rw [← hnN] at hn hεN
  have hL0 : 0 < ε * n := by linarith
  have hn0 : n ≠ 0 := by linarith
  have hmean : ∑ ω, M.w ω * (M.pairCount ω : ℝ) ≤
      ε * n * n + (∑ ω, M.w ω * (M.tripleCount ω : ℝ)) / (ε * n) := by
    have h1 : ∑ ω, M.w ω * (M.pairCount ω : ℝ) ≤
        ∑ ω, (M.w ω * (ε * n * n) + M.w ω * (M.tripleCount ω : ℝ) / (ε * n)) := by
      refine sum_le_sum fun ω _ => ?_
      have h := M.pairCount_le_add ω (L := ε * N) (by rw [← hnN]; exact hεN)
      rw [← hnN] at h
      have := mul_le_mul_of_nonneg_left h (M.w_nonneg ω)
      rw [mul_add, ← mul_div_assoc] at this
      exact this
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, M.sum_w, one_mul, ← Finset.sum_div] at h1
    exact h1
  rw [M.sum_w_mul_pairCount (by omega), M.sum_w_mul_tripleCount hN, ← hnN] at hmean
  have hD2 : 0 < n * (n - 1) := mul_pos (by linarith) (by linarith)
  have hA : ε * n * n ≤ 2 * ε * (n * (n - 1)) := by
    have : n ≤ 2 * (n - 1) := by linarith
    calc ε * n * n ≤ ε * n * (2 * (n - 1)) := mul_le_mul_of_nonneg_left this hL0.le
      _ = 2 * ε * (n * (n - 1)) := by ring
  have hB : M.tripleCoalProb * (n * (n - 1) * (n - 2)) / (ε * n) ≤
      M.tripleCoalProb / ε * (n * (n - 1)) := by
    have e : M.tripleCoalProb * (n * (n - 1) * (n - 2)) / (ε * n) =
        M.tripleCoalProb / ε * (n - 1) * (n - 2) := by
      field_simp
    have h0 : 0 ≤ M.tripleCoalProb / ε * (n - 1) :=
      mul_nonneg (div_nonneg hd hε.le) (by linarith)
    rw [e]
    calc M.tripleCoalProb / ε * (n - 1) * (n - 2)
        ≤ M.tripleCoalProb / ε * (n - 1) * n := mul_le_mul_of_nonneg_left (by linarith) h0
      _ = M.tripleCoalProb / ε * (n * (n - 1)) := by ring
  refine le_of_mul_le_mul_right ?_ hD2
  rw [add_mul]
  linarith

end Rhone.MarkovChain.CanningsModel
