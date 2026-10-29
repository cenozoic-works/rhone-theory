/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.InfiniteAlleles.Blocks

/-! # The seven moves, read on labelled typed samples -/

@[expose] public section

namespace Rhone.Probability.InfiniteAlleles

open Finset LinearAlgebra.Recursion LinearAlgebra.Recursion.Config

variable {n KA KB : ℕ}

section Update

theorem decf_eq_of {ι : Type*} [DecidableEq ι] {g g' : ι → ℕ} {i : ι} (h1 : g' i + 1 = g i)
    (h2 : ∀ i', i' ≠ i → g' i' = g i') : g' = decf g i := by
  funext i'
  by_cases h : i' = i
  · subst h; rw [decf_self]; omega
  · rw [decf_of_ne _ h]; exact h2 i' h

theorem incf_eq_of {ι : Type*} [DecidableEq ι] {g g' : ι → ℕ} {i : ι} (h1 : g' i = g i + 1)
    (h2 : ∀ i', i' ≠ i → g' i' = g i') : g' = incf g i := by
  funext i'
  by_cases h : i' = i
  · subst h; rw [incf_self]; exact h1
  · rw [incf_of_ne _ h]; exact h2 i' h

theorem decC_eq_of {m m' : Fin KA → Fin KB → ℕ} {i : Fin KA} {j : Fin KB}
    (h1 : m' i j + 1 = m i j) (h2 : ∀ j', j' ≠ j → m' i j' = m i j')
    (h3 : ∀ i', i' ≠ i → m' i' = m i') : m' = Config.decC m i j := by
  funext i'
  by_cases h : i' = i
  · subst h
    rw [Config.decC, Function.update_self]
    exact decf_eq_of h1 h2
  · rw [Config.decC, Function.update_of_ne h]
    exact h3 i' h

theorem incC_eq_of {m m' : Fin KA → Fin KB → ℕ} {i : Fin KA} {j : Fin KB}
    (h1 : m' i j = m i j + 1) (h2 : ∀ j', j' ≠ j → m' i j' = m i j')
    (h3 : ∀ i', i' ≠ i → m' i' = m i') : m' = Config.incC m i j := by
  funext i'
  by_cases h : i' = i
  · subst h
    rw [Config.incC, Function.update_self]
    exact incf_eq_of h1 h2
  · rw [Config.incC, Function.update_of_ne h]
    exact h3 i' h

end Update

section Card

variable {T : Finset (Fin n)} {k : Fin n} {p : Fin n → Prop} [DecidablePred p]

theorem filter_erase_comm (T : Finset (Fin n)) (k : Fin n) (p : Fin n → Prop)
    [DecidablePred p] : (T.erase k).filter p = (T.filter p).erase k :=
  Finset.filter_erase (p := p) k T

theorem card_filter_erase (hk : k ∈ T) (hp : p k) :
    ((T.erase k).filter p).card + 1 = (T.filter p).card := by
  rw [filter_erase_comm, Finset.card_erase_add_one (Finset.mem_filter.mpr ⟨hk, hp⟩)]

theorem card_filter_erase_of_not (hp : ¬ p k) :
    ((T.erase k).filter p).card = (T.filter p).card := by
  rw [filter_erase_comm, Finset.erase_eq_of_notMem fun hc => hp (Finset.mem_filter.mp hc).2]

theorem card_filter_insert (hk : k ∉ T) (hp : p k) :
    ((insert k T).filter p).card = (T.filter p).card + 1 := by
  rw [Finset.filter_insert, ite_eq_left hp,
    Finset.card_insert_of_notMem fun hc => hk (Finset.mem_filter.mp hc).1]

theorem card_filter_insert_of_not (hp : ¬ p k) :
    ((insert k T).filter p).card = (T.filter p).card := by
  rw [Finset.filter_insert, ite_eq_right hp]

end Card

def eraseA (S : Sample n) (k : Fin n) : Sample n := ⟨S.LA.erase k, S.LB⟩

def eraseB (S : Sample n) (k : Fin n) : Sample n := ⟨S.LA, S.LB.erase k⟩

def eraseAB (S : Sample n) (k : Fin n) : Sample n := ⟨S.LA.erase k, S.LB.erase k⟩

def swapB (S : Sample n) (k k' : Fin n) : Sample n := ⟨S.LA, insert k (S.LB.erase k')⟩

section Regions

variable {S : Sample n} {k k' : Fin n}

theorem regions_eraseA_onlyA (hk : k ∈ S.onlyA) :
    (eraseA S k).onlyA = S.onlyA.erase k ∧ (eraseA S k).onlyB = S.onlyB
      ∧ (eraseA S k).both = S.both := by
  have hkB : k ∉ S.LB := (Finset.mem_sdiff.mp hk).2
  refine ⟨?_, ?_, ?_⟩ <;> ext m <;>
    simp only [eraseA, Sample.onlyA, Sample.onlyB, Sample.both, Finset.mem_sdiff,
      Finset.mem_inter, Finset.mem_erase] <;>
    by_cases hm : m = k <;> subst_vars <;> simp_all

theorem regions_eraseA_both (hk : k ∈ S.both) :
    (eraseA S k).onlyA = S.onlyA ∧ (eraseA S k).onlyB = insert k S.onlyB
      ∧ (eraseA S k).both = S.both.erase k := by
  have hkA : k ∈ S.LA := (Finset.mem_inter.mp hk).1
  have hkB : k ∈ S.LB := (Finset.mem_inter.mp hk).2
  refine ⟨?_, ?_, ?_⟩ <;> ext m <;>
    simp only [eraseA, Sample.onlyA, Sample.onlyB, Sample.both, Finset.mem_sdiff,
      Finset.mem_inter, Finset.mem_erase, Finset.mem_insert] <;>
    by_cases hm : m = k <;> subst_vars <;> simp_all

theorem regions_eraseB_onlyB (hk : k ∈ S.onlyB) :
    (eraseB S k).onlyA = S.onlyA ∧ (eraseB S k).onlyB = S.onlyB.erase k
      ∧ (eraseB S k).both = S.both := by
  have hkA : k ∉ S.LA := (Finset.mem_sdiff.mp hk).2
  refine ⟨?_, ?_, ?_⟩ <;> ext m <;>
    simp only [eraseB, Sample.onlyA, Sample.onlyB, Sample.both, Finset.mem_sdiff,
      Finset.mem_inter, Finset.mem_erase] <;>
    by_cases hm : m = k <;> subst_vars <;> simp_all

theorem regions_eraseB_both (hk : k ∈ S.both) :
    (eraseB S k).onlyA = insert k S.onlyA ∧ (eraseB S k).onlyB = S.onlyB
      ∧ (eraseB S k).both = S.both.erase k := by
  have hkA : k ∈ S.LA := (Finset.mem_inter.mp hk).1
  have hkB : k ∈ S.LB := (Finset.mem_inter.mp hk).2
  refine ⟨?_, ?_, ?_⟩ <;> ext m <;>
    simp only [eraseB, Sample.onlyA, Sample.onlyB, Sample.both, Finset.mem_sdiff,
      Finset.mem_inter, Finset.mem_erase, Finset.mem_insert] <;>
    by_cases hm : m = k <;> subst_vars <;> simp_all

theorem regions_eraseAB (hk : k ∈ S.both) :
    (eraseAB S k).onlyA = S.onlyA ∧ (eraseAB S k).onlyB = S.onlyB
      ∧ (eraseAB S k).both = S.both.erase k := by
  have hkA : k ∈ S.LA := (Finset.mem_inter.mp hk).1
  have hkB : k ∈ S.LB := (Finset.mem_inter.mp hk).2
  refine ⟨?_, ?_, ?_⟩ <;> ext m <;>
    simp only [eraseAB, Sample.onlyA, Sample.onlyB, Sample.both, Finset.mem_sdiff,
      Finset.mem_inter, Finset.mem_erase] <;>
    by_cases hm : m = k <;> subst_vars <;> simp_all

theorem regions_swapB_merge (hk : k ∈ S.onlyA) (hk' : k' ∈ S.onlyB) :
    (swapB S k k').onlyA = S.onlyA.erase k ∧ (swapB S k k').onlyB = S.onlyB.erase k'
      ∧ (swapB S k k').both = insert k S.both := by
  have hkA : k ∈ S.LA := (Finset.mem_sdiff.mp hk).1
  have hkB : k ∉ S.LB := (Finset.mem_sdiff.mp hk).2
  have hk'A : k' ∉ S.LA := (Finset.mem_sdiff.mp hk').2
  have hk'B : k' ∈ S.LB := (Finset.mem_sdiff.mp hk').1
  have hne : k ≠ k' := fun hc => hk'A (hc ▸ hkA)
  refine ⟨?_, ?_, ?_⟩ <;> ext m <;>
    simp only [swapB, Sample.onlyA, Sample.onlyB, Sample.both, Finset.mem_sdiff,
      Finset.mem_inter, Finset.mem_erase, Finset.mem_insert] <;>
    by_cases hm : m = k <;> by_cases hm2 : m = k' <;> subst_vars <;> simp_all

theorem regions_swapB_split (hk : k ∈ S.both) (hk'A : k' ∉ S.LA) (hk'B : k' ∉ S.LB) :
    (swapB S k' k).onlyA = insert k S.onlyA ∧ (swapB S k' k).onlyB = insert k' S.onlyB
      ∧ (swapB S k' k).both = S.both.erase k := by
  have hkA : k ∈ S.LA := (Finset.mem_inter.mp hk).1
  have hkB : k ∈ S.LB := (Finset.mem_inter.mp hk).2
  have hne : k ≠ k' := fun hc => hk'A (hc ▸ hkA)
  refine ⟨?_, ?_, ?_⟩ <;> ext m <;>
    simp only [swapB, Sample.onlyA, Sample.onlyB, Sample.both, Finset.mem_sdiff,
      Finset.mem_inter, Finset.mem_erase, Finset.mem_insert] <;>
    by_cases hm : m = k <;> by_cases hm2 : m = k' <;> subst_vars <;> simp_all

end Regions

section Dictionary

variable (S : Sample n) (α : Fin n → Fin KA) (β : Fin n → Fin KB) {k k' : Fin n}

theorem cfgOf_eraseA_onlyA (hk : k ∈ S.onlyA) :
    cfgOf (eraseA S k) α β = (cfgOf S α β).dropA (α k) := by
  obtain ⟨r1, r2, r3⟩ := regions_eraseA_onlyA hk
  refine Config.ext (decf_eq_of ?_ ?_) (funext fun j => ?_) (funext fun i => funext fun j => ?_)
  · simp only [cfgOf_a, r1]
    exact card_filter_erase hk rfl
  · intro i' hi'
    simp only [cfgOf_a, r1]
    exact card_filter_erase_of_not fun hc => hi' hc.symm
  · simp only [cfgOf_b, Config.dropA, r2]
  · simp only [cfgOf_c, Config.dropA, r3]

theorem cfgOf_eraseB_onlyB (hk : k ∈ S.onlyB) :
    cfgOf (eraseB S k) α β = (cfgOf S α β).dropB (β k) := by
  obtain ⟨r1, r2, r3⟩ := regions_eraseB_onlyB hk
  refine Config.ext (funext fun i => ?_) (decf_eq_of ?_ ?_) (funext fun i => funext fun j => ?_)
  · simp only [cfgOf_a, Config.dropB, r1]
  · simp only [cfgOf_b, r2]
    exact card_filter_erase hk rfl
  · intro j' hj'
    simp only [cfgOf_b, r2]
    exact card_filter_erase_of_not fun hc => hj' hc.symm
  · simp only [cfgOf_c, Config.dropB, r3]

theorem cfgOf_eraseAB (hk : k ∈ S.both) :
    cfgOf (eraseAB S k) α β = (cfgOf S α β).dropC (α k) (β k) := by
  obtain ⟨r1, r2, r3⟩ := regions_eraseAB hk
  refine Config.ext (funext fun i => ?_) (funext fun j => ?_) (decC_eq_of ?_ ?_ ?_)
  · simp only [cfgOf_a, Config.dropC, r1]
  · simp only [cfgOf_b, Config.dropC, r2]
  · simp only [cfgOf_c, r3]
    exact card_filter_erase hk ⟨rfl, rfl⟩
  · intro j' hj'
    simp only [cfgOf_c, r3]
    exact card_filter_erase_of_not fun hc => hj' hc.2.symm
  · intro i' hi'
    funext j'
    simp only [cfgOf_c, r3]
    exact card_filter_erase_of_not fun hc => hi' hc.1.symm

theorem cfgOf_eraseA_both (hk : k ∈ S.both) :
    cfgOf (eraseA S k) α β = (cfgOf S α β).killA (α k) (β k) := by
  obtain ⟨r1, r2, r3⟩ := regions_eraseA_both hk
  have hkB : k ∉ S.onlyB := fun hc => (Finset.mem_sdiff.mp hc).2 (Finset.mem_inter.mp hk).1
  refine Config.ext (funext fun i => ?_) (incf_eq_of ?_ ?_) (decC_eq_of ?_ ?_ ?_)
  · simp only [cfgOf_a, Config.killA, r1]
  · simp only [cfgOf_b, r2]
    exact card_filter_insert hkB rfl
  · intro j' hj'
    simp only [cfgOf_b, r2]
    exact card_filter_insert_of_not fun hc => hj' hc.symm
  · simp only [cfgOf_c, r3]
    exact card_filter_erase hk ⟨rfl, rfl⟩
  · intro j' hj'
    simp only [cfgOf_c, r3]
    exact card_filter_erase_of_not fun hc => hj' hc.2.symm
  · intro i' hi'
    funext j'
    simp only [cfgOf_c, r3]
    exact card_filter_erase_of_not fun hc => hi' hc.1.symm

theorem cfgOf_eraseB_both (hk : k ∈ S.both) :
    cfgOf (eraseB S k) α β = (cfgOf S α β).killB (α k) (β k) := by
  obtain ⟨r1, r2, r3⟩ := regions_eraseB_both hk
  have hkA : k ∉ S.onlyA := fun hc => (Finset.mem_sdiff.mp hc).2 (Finset.mem_inter.mp hk).2
  refine Config.ext (incf_eq_of ?_ ?_) (funext fun j => ?_) (decC_eq_of ?_ ?_ ?_)
  · simp only [cfgOf_a, r1]
    exact card_filter_insert hkA rfl
  · intro i' hi'
    simp only [cfgOf_a, r1]
    exact card_filter_insert_of_not fun hc => hi' hc.symm
  · simp only [cfgOf_b, Config.killB, r2]
  · simp only [cfgOf_c, r3]
    exact card_filter_erase hk ⟨rfl, rfl⟩
  · intro j' hj'
    simp only [cfgOf_c, r3]
    exact card_filter_erase_of_not fun hc => hj' hc.2.symm
  · intro i' hi'
    funext j'
    simp only [cfgOf_c, r3]
    exact card_filter_erase_of_not fun hc => hi' hc.1.symm

theorem cfgOf_swapB_merge (hk : k ∈ S.onlyA) (hk' : k' ∈ S.onlyB) :
    cfgOf (swapB S k k') α (Function.update β k (β k'))
      = (cfgOf S α β).mergeAB (α k) (β k') := by
  obtain ⟨r1, r2, r3⟩ := regions_swapB_merge hk hk'
  have hkLB : k ∉ S.LB := (Finset.mem_sdiff.mp hk).2
  have hupd : ∀ m ∈ S.LB, Function.update β k (β k') m = β m := by
    intro m hm
    refine Function.update_of_ne ?_ _ _
    rintro rfl
    exact hkLB hm
  have hfB : ∀ {T : Finset (Fin n)}, T ⊆ S.LB → ∀ j' : Fin KB,
      (T.filter fun m => Function.update β k (β k') m = j') = T.filter fun m => β m = j' :=
    fun {_} hT j' => Finset.filter_congr fun m hm => by rw [hupd m (hT hm)]
  have hfC : ∀ {T : Finset (Fin n)}, T ⊆ S.LB → ∀ (i' : Fin KA) (j' : Fin KB),
      (T.filter fun m => α m = i' ∧ Function.update β k (β k') m = j')
        = T.filter fun m => α m = i' ∧ β m = j' :=
    fun {_} hT i' j' => Finset.filter_congr fun m hm => by rw [hupd m (hT hm)]
  have hsubB : S.onlyB.erase k' ⊆ S.LB := (Finset.erase_subset _ _).trans S.onlyB_subset
  have hkboth : k ∉ S.both := fun hc => hkLB (Finset.mem_inter.mp hc).2
  refine Config.ext (decf_eq_of ?_ ?_) (decf_eq_of ?_ ?_) (incC_eq_of ?_ ?_ ?_)
  · simp only [cfgOf_a, r1]
    exact card_filter_erase hk rfl
  · intro i' hi'
    simp only [cfgOf_a, r1]
    exact card_filter_erase_of_not fun hc => hi' hc.symm
  · simp only [cfgOf_b, r2, hfB hsubB]
    exact card_filter_erase hk' rfl
  · intro j' hj'
    simp only [cfgOf_b, r2, hfB hsubB]
    exact card_filter_erase_of_not fun hc => hj' hc.symm
  · simp only [cfgOf_c, r3,
      card_filter_insert (p := fun m => α m = α k ∧ Function.update β k (β k') m = β k')
        hkboth ⟨rfl, Function.update_self k (β k') β⟩,
      hfC S.both_subset_LB]
  · intro j' hj'
    simp only [cfgOf_c, r3,
      card_filter_insert_of_not (p := fun m => α m = α k ∧ Function.update β k (β k') m = j')
        (fun hc => hj' (((Function.update_self k (β k') β).symm.trans hc.2).symm)),
      hfC S.both_subset_LB]
  · intro i' hi'
    funext j'
    simp only [cfgOf_c, r3,
      card_filter_insert_of_not (p := fun m => α m = i' ∧ Function.update β k (β k') m = j')
        (fun hc => hi' hc.1.symm),
      hfC S.both_subset_LB]

theorem cfgOf_swapB_split (hk : k ∈ S.both) (hk'A : k' ∉ S.LA) (hk'B : k' ∉ S.LB) :
    cfgOf (swapB S k' k) α (Function.update β k' (β k))
      = (cfgOf S α β).split (α k) (β k) := by
  obtain ⟨r1, r2, r3⟩ := regions_swapB_split hk hk'A hk'B
  have hupd : ∀ m ∈ S.LB, Function.update β k' (β k) m = β m := by
    intro m hm
    refine Function.update_of_ne ?_ _ _
    rintro rfl
    exact hk'B hm
  have hfB : ∀ {T : Finset (Fin n)}, T ⊆ S.LB → ∀ j' : Fin KB,
      (T.filter fun m => Function.update β k' (β k) m = j') = T.filter fun m => β m = j' :=
    fun {_} hT j' => Finset.filter_congr fun m hm => by rw [hupd m (hT hm)]
  have hfC : ∀ {T : Finset (Fin n)}, T ⊆ S.LB → ∀ (i' : Fin KA) (j' : Fin KB),
      (T.filter fun m => α m = i' ∧ Function.update β k' (β k) m = j')
        = T.filter fun m => α m = i' ∧ β m = j' :=
    fun {_} hT i' j' => Finset.filter_congr fun m hm => by rw [hupd m (hT hm)]
  have hsubC : S.both.erase k ⊆ S.LB := (Finset.erase_subset _ _).trans S.both_subset_LB
  have hkA : k ∉ S.onlyA := fun hc => (Finset.mem_sdiff.mp hc).2 (Finset.mem_inter.mp hk).2
  have hk'onlyB : k' ∉ S.onlyB := fun hc => hk'B (Finset.mem_sdiff.mp hc).1
  refine Config.ext (incf_eq_of ?_ ?_) (incf_eq_of ?_ ?_) (decC_eq_of ?_ ?_ ?_)
  · simp only [cfgOf_a, r1]
    exact card_filter_insert hkA rfl
  · intro i' hi'
    simp only [cfgOf_a, r1]
    exact card_filter_insert_of_not fun hc => hi' hc.symm
  · simp only [cfgOf_b, r2,
      card_filter_insert (p := fun m => Function.update β k' (β k) m = β k) hk'onlyB
        (Function.update_self k' (β k) β),
      hfB S.onlyB_subset]
  · intro j' hj'
    simp only [cfgOf_b, r2,
      card_filter_insert_of_not (p := fun m => Function.update β k' (β k) m = j')
        (fun hc => hj' (((Function.update_self k' (β k) β).symm.trans hc).symm)),
      hfB S.onlyB_subset]
  · simp only [cfgOf_c, r3, hfC hsubC]
    exact card_filter_erase hk ⟨rfl, rfl⟩
  · intro j' hj'
    simp only [cfgOf_c, r3, hfC hsubC]
    exact card_filter_erase_of_not fun hc => hj' hc.2.symm
  · intro i' hi'
    funext j'
    simp only [cfgOf_c, r3, hfC hsubC]
    exact card_filter_erase_of_not fun hc => hi' hc.1.symm

end Dictionary

section Recursion

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F] {θA θB ρ : F}
variable (S : Sample n) (α : Fin n → Fin KA) (β : Fin n → Fin KB)

theorem Plab_recursion (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hS : 2 ≤ S.LA.card + S.LB.card) :
    diag θA θB ρ (cfgOf S α β) * Plab hθA hθB hρ S α β
      = rhsIA θA θB ρ (PIA hθA hθB hρ) (cfgOf S α β) :=
  (PIA_isSolutionIA hθA hθB hρ).recursion _ (by rw [nA_cfgOf, nB_cfgOf]; exact hS)

theorem Plab_boundary (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hS : S.LA.card + S.LB.card ≤ 1) : Plab hθA hθB hρ S α β = 1 := by
  have hlev : (cfgOf S α β).nA + (cfgOf S α β).nB ≤ 1 := by
    rw [nA_cfgOf, nB_cfgOf]; exact hS
  rcases level_le_one_cases _ hlev with h | ⟨i, h⟩ | ⟨j, h⟩
  · rw [Plab, h]; exact (PIA_isSolutionIA hθA hθB hρ).empty
  · rw [Plab, h]; exact (PIA_isSolutionIA hθA hθB hρ).bdryA i
  · rw [Plab, h]; exact (PIA_isSolutionIA hθA hθB hρ).bdryB j

theorem Plab_unique (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) {q : Config KA KB → F}
    (hq : IsSolutionIA θA θB ρ q) : q (cfgOf S α β) = Plab hθA hθB hρ S α β :=
  congrFun (PIA_unique hθA hθB hρ hq) _

variable {S α β} {k k' : Fin n}

theorem Plab_dropA (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (hk : k ∈ S.onlyA) :
    Plab hθA hθB hρ (eraseA S k) α β = PIA hθA hθB hρ ((cfgOf S α β).dropA (α k)) :=
  congrArg _ (cfgOf_eraseA_onlyA S α β hk)

theorem Plab_dropB (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (hk : k ∈ S.onlyB) :
    Plab hθA hθB hρ (eraseB S k) α β = PIA hθA hθB hρ ((cfgOf S α β).dropB (β k)) :=
  congrArg _ (cfgOf_eraseB_onlyB S α β hk)

theorem Plab_dropC (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (hk : k ∈ S.both) :
    Plab hθA hθB hρ (eraseAB S k) α β = PIA hθA hθB hρ ((cfgOf S α β).dropC (α k) (β k)) :=
  congrArg _ (cfgOf_eraseAB S α β hk)

theorem Plab_killA (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (hk : k ∈ S.both) :
    Plab hθA hθB hρ (eraseA S k) α β = PIA hθA hθB hρ ((cfgOf S α β).killA (α k) (β k)) :=
  congrArg _ (cfgOf_eraseA_both S α β hk)

theorem Plab_killB (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (hk : k ∈ S.both) :
    Plab hθA hθB hρ (eraseB S k) α β = PIA hθA hθB hρ ((cfgOf S α β).killB (α k) (β k)) :=
  congrArg _ (cfgOf_eraseB_both S α β hk)

theorem Plab_mergeAB (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (hk : k ∈ S.onlyA)
    (hk' : k' ∈ S.onlyB) :
    Plab hθA hθB hρ (swapB S k k') α (Function.update β k (β k'))
      = PIA hθA hθB hρ ((cfgOf S α β).mergeAB (α k) (β k')) :=
  congrArg _ (cfgOf_swapB_merge S α β hk hk')

theorem Plab_split (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (hk : k ∈ S.both)
    (hk'A : k' ∉ S.LA) (hk'B : k' ∉ S.LB) :
    Plab hθA hθB hρ (swapB S k' k) α (Function.update β k' (β k))
      = PIA hθA hθB hρ ((cfgOf S α β).split (α k) (β k)) :=
  congrArg _ (cfgOf_swapB_split S α β hk hk'A hk'B)

end Recursion

end Rhone.Probability.InfiniteAlleles
