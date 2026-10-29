/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.Multilinear.State

/-! # `Ξ` and the elementary moves -/

@[expose] public section

namespace Rhone.Probability.Multilinear

open Finset LinearAlgebra.Recursion Denominator

variable {KA KB : ℕ} {SA SB : Type*}

theorem ite_one_comm {ι : Type*} [DecidableEq ι] (x y : ι) :
    (if x = y then (1 : ℕ) else 0) = if y = x then 1 else 0 := by
  by_cases h : x = y
  · simp [h]
  · simp [h, Ne.symm h]

theorem ite_pair_comm {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] (x y : ι) (z t : κ) :
    (if x = y then (if z = t then (1 : ℕ) else 0) else 0) = if y = x ∧ t = z then 1 else 0 := by
  by_cases h1 : x = y
  · subst h1
    by_cases h2 : z = t
    · simp [h2]
    · simp [h2, Ne.symm h2]
  · simp [h1, Ne.symm h1]

theorem card_filter_swap_at {ι : Type*} [DecidableEq ι] {s : Finset ι} {k : ι} (hk : k ∈ s)
    (P Q : ι → Prop) [DecidablePred P] [DecidablePred Q]
    (hPQ : ∀ u ∈ s.erase k, (P u ↔ Q u)) :
    (s.filter P).card + (if Q k then 1 else 0)
      = (s.filter Q).card + (if P k then 1 else 0) := by
  have e1 := card_filter_erase_add hk P
  have e2 := card_filter_erase_add hk Q
  rw [Finset.filter_congr hPQ] at e1
  omega

section Moves

variable [Fintype SA] [DecidableEq SA] [Fintype SB] [DecidableEq SB]
variable {M : Finset (SA × SB)} (α : SA → Fin KA) (β : SB → Fin KB)

omit [Fintype SB] [DecidableEq SB] in
theorem fst_ne_of_mem_freeA {k : SA} (hk : k ∈ freeA M) {p : SA × SB} (hp : p ∈ M) :
    p.1 ≠ k := fun hc => (mem_freeA.mp hk p.2) (by rwa [← hc])

omit [Fintype SA] [DecidableEq SA] in
theorem snd_ne_of_mem_freeB {l : SB} (hl : l ∈ freeB M) {p : SA × SB} (hp : p ∈ M) :
    p.2 ≠ l := fun hc => (mem_freeB.mp hl p.1) (by rwa [← hc])

theorem xi_update_freeA {k : SA} (hk : k ∈ freeA M) (i : Fin KA) :
    xi M (Function.update α k i) β = addA ((xi M α β).dropA (α k)) i := by
  refine Config.ext (funext fun i' => ?_) rfl (funext fun i' => funext fun j' => ?_)
  · have hs := card_filter_swap_at hk (fun u => Function.update α k i u = i')
      (fun u => α u = i') fun u hu => by
        rw [Function.update_of_ne (Finset.mem_erase.mp hu).1]
    have e2 := card_filter_erase_add hk (fun u => α u = i')
    simp only [Function.update_self] at hs
    have h2 : (addA ((xi M α β).dropA (α k)) i).a i'
        = (((freeA M).filter fun u => α u = i').card - (if α k = i' then 1 else 0))
          + (if i = i' then 1 else 0) := by
      simp only [addA, Config.dropA, incf_apply, decf_apply, xi_a, ite_one_comm i' (α k),
        ite_one_comm i' i]
    rw [xi_a, h2]
    split_ifs at hs e2 ⊢ <;> omega
  · simp only [addA, Config.dropA, xi_c]
    exact congrArg Finset.card (Finset.filter_congr fun p hp => by
      rw [Function.update_of_ne (fst_ne_of_mem_freeA hk hp)])

theorem xi_update_freeB {l : SB} (hl : l ∈ freeB M) (j : Fin KB) :
    xi M α (Function.update β l j) = addB ((xi M α β).dropB (β l)) j := by
  refine Config.ext rfl (funext fun j' => ?_) (funext fun i' => funext fun j' => ?_)
  · have hs := card_filter_swap_at hl (fun v => Function.update β l j v = j')
      (fun v => β v = j') fun v hv => by
        rw [Function.update_of_ne (Finset.mem_erase.mp hv).1]
    have e2 := card_filter_erase_add hl (fun v => β v = j')
    simp only [Function.update_self] at hs
    have h2 : (addB ((xi M α β).dropB (β l)) j).b j'
        = (((freeB M).filter fun v => β v = j').card - (if β l = j' then 1 else 0))
          + (if j = j' then 1 else 0) := by
      simp only [addB, Config.dropB, incf_apply, decf_apply, xi_b, ite_one_comm j' (β l),
        ite_one_comm j' j]
    rw [xi_b, h2]
    split_ifs at hs e2 ⊢ <;> omega
  · simp only [addB, Config.dropB, xi_c]
    exact congrArg Finset.card (Finset.filter_congr fun p hp => by
      rw [Function.update_of_ne (snd_ne_of_mem_freeB hl hp)])

theorem xi_update_domA (h : IsMatching M) {p : SA × SB} (hp : p ∈ M) (i : Fin KA) :
    xi M (Function.update α p.1 i) β
      = addC ((xi M α β).dropC (α p.1) (β p.2)) i (β p.2) := by
  have hnf : p.1 ∉ freeA M := notMem_freeA_of_mem hp
  refine Config.ext (funext fun i' => ?_) rfl (funext fun i' => funext fun j' => ?_)
  · simp only [addC, Config.dropC, xi_a]
    exact congrArg Finset.card (Finset.filter_congr fun u hu => by
      rw [Function.update_of_ne fun hc => hnf (by rw [← hc]; exact hu)])
  · have hs := card_filter_swap_at hp
      (fun r => Function.update α p.1 i r.1 = i' ∧ β r.2 = j')
      (fun r => α r.1 = i' ∧ β r.2 = j') fun r hr => by
        rw [Function.update_of_ne
          fun hc => (Finset.mem_erase.mp hr).1 (h.fst _ (Finset.mem_erase.mp hr).2 _ hp hc)]
    have e2 := card_filter_erase_add hp (fun r => α r.1 = i' ∧ β r.2 = j')
    simp only [Function.update_self] at hs
    have h2 : (addC ((xi M α β).dropC (α p.1) (β p.2)) i (β p.2)).c i' j'
        = ((M.filter fun r => α r.1 = i' ∧ β r.2 = j').card
            - (if α p.1 = i' ∧ β p.2 = j' then 1 else 0))
          + (if i = i' ∧ β p.2 = j' then 1 else 0) := by
      simp only [addC, Config.dropC, incC_apply, decC_apply, xi_c,
        ite_pair_comm i' (α p.1) j' (β p.2), ite_pair_comm i' i j' (β p.2)]
    rw [xi_c, h2]
    split_ifs at hs e2 ⊢ <;> omega

theorem xi_update_domB (h : IsMatching M) {p : SA × SB} (hp : p ∈ M) (j : Fin KB) :
    xi M α (Function.update β p.2 j)
      = addC ((xi M α β).dropC (α p.1) (β p.2)) (α p.1) j := by
  have hnf : p.2 ∉ freeB M := notMem_freeB_of_mem hp
  refine Config.ext rfl (funext fun j' => ?_) (funext fun i' => funext fun j' => ?_)
  · simp only [addC, Config.dropC, xi_b]
    exact congrArg Finset.card (Finset.filter_congr fun v hv => by
      rw [Function.update_of_ne fun hc => hnf (by rw [← hc]; exact hv)])
  · have hs := card_filter_swap_at hp
      (fun r => α r.1 = i' ∧ Function.update β p.2 j r.2 = j')
      (fun r => α r.1 = i' ∧ β r.2 = j') fun r hr => by
        rw [Function.update_of_ne
          fun hc => (Finset.mem_erase.mp hr).1 (h.snd _ (Finset.mem_erase.mp hr).2 _ hp hc)]
    have e2 := card_filter_erase_add hp (fun r => α r.1 = i' ∧ β r.2 = j')
    simp only [Function.update_self] at hs
    have h2 : (addC ((xi M α β).dropC (α p.1) (β p.2)) (α p.1) j).c i' j'
        = ((M.filter fun r => α r.1 = i' ∧ β r.2 = j').card
            - (if α p.1 = i' ∧ β p.2 = j' then 1 else 0))
          + (if α p.1 = i' ∧ j = j' then 1 else 0) := by
      simp only [addC, Config.dropC, incC_apply, decC_apply, xi_c,
        ite_pair_comm i' (α p.1) j' (β p.2), ite_pair_comm i' (α p.1) j' j]
    rw [xi_c, h2]
    split_ifs at hs e2 ⊢ <;> omega

theorem xi_update_pair (h : IsMatching M) {p : SA × SB} (hp : p ∈ M)
    (i : Fin KA) (j : Fin KB) :
    xi M (Function.update α p.1 i) (Function.update β p.2 j)
      = addC ((xi M α β).dropC (α p.1) (β p.2)) i j := by
  have hnfA : p.1 ∉ freeA M := notMem_freeA_of_mem hp
  have hnfB : p.2 ∉ freeB M := notMem_freeB_of_mem hp
  refine Config.ext (funext fun i' => ?_) (funext fun j' => ?_)
    (funext fun i' => funext fun j' => ?_)
  · simp only [addC, Config.dropC, xi_a]
    exact congrArg Finset.card (Finset.filter_congr fun u hu => by
      rw [Function.update_of_ne fun hc => hnfA (by rw [← hc]; exact hu)])
  · simp only [addC, Config.dropC, xi_b]
    exact congrArg Finset.card (Finset.filter_congr fun v hv => by
      rw [Function.update_of_ne fun hc => hnfB (by rw [← hc]; exact hv)])
  · have hs := card_filter_swap_at hp
      (fun r => Function.update α p.1 i r.1 = i' ∧ Function.update β p.2 j r.2 = j')
      (fun r => α r.1 = i' ∧ β r.2 = j') fun r hr => by
        rw [Function.update_of_ne
            fun hc => (Finset.mem_erase.mp hr).1 (h.fst _ (Finset.mem_erase.mp hr).2 _ hp hc),
          Function.update_of_ne
            fun hc => (Finset.mem_erase.mp hr).1 (h.snd _ (Finset.mem_erase.mp hr).2 _ hp hc)]
    have e2 := card_filter_erase_add hp (fun r => α r.1 = i' ∧ β r.2 = j')
    simp only [Function.update_self] at hs
    have h2 : (addC ((xi M α β).dropC (α p.1) (β p.2)) i j).c i' j'
        = ((M.filter fun r => α r.1 = i' ∧ β r.2 = j').card
            - (if α p.1 = i' ∧ β p.2 = j' then 1 else 0))
          + (if i = i' ∧ j = j' then 1 else 0) := by
      simp only [addC, Config.dropC, incC_apply, decC_apply, xi_c,
        ite_pair_comm i' (α p.1) j' (β p.2), ite_pair_comm i' i j' j]
    rw [xi_c, h2]
    split_ifs at hs e2 ⊢ <;> omega

theorem xi_insert {k : SA} {l : SB} (hk : k ∈ freeA M) (hl : l ∈ freeB M) :
    xi (insert (k, l) M) α β = (xi M α β).mergeAB (α k) (β l) := by
  have hkl : (k, l) ∉ M := mem_freeA.mp hk l
  refine Config.ext (funext fun i' => ?_) (funext fun j' => ?_)
    (funext fun i' => funext fun j' => ?_)
  · have e := card_filter_erase_add hk (fun u => α u = i')
    simp only [Config.mergeAB, xi_a, freeA_insert, decf_apply, ite_one_comm i' (α k)]
    split_ifs at e ⊢ <;> omega
  · have e := card_filter_erase_add hl (fun v => β v = j')
    simp only [Config.mergeAB, xi_b, freeB_insert, decf_apply, ite_one_comm j' (β l)]
    split_ifs at e ⊢ <;> omega
  · have e := card_filter_insert hkl (fun r => α r.1 = i' ∧ β r.2 = j')
    simp only [Config.mergeAB, xi_c, incC_apply, ite_pair_comm i' (α k) j' (β l)]
    split_ifs at e ⊢ <;> omega

theorem xi_erase (h : IsMatching M) {p : SA × SB} (hp : p ∈ M) :
    xi (M.erase p) α β = (xi M α β).split (α p.1) (β p.2) := by
  refine Config.ext (funext fun i' => ?_) (funext fun j' => ?_)
    (funext fun i' => funext fun j' => ?_)
  · have e := card_filter_insert (notMem_freeA_of_mem hp) (fun u => α u = i')
    simp only [Config.split, xi_a, freeA_erase h hp, incf_apply, ite_one_comm i' (α p.1)]
    split_ifs at e ⊢ <;> omega
  · have e := card_filter_insert (notMem_freeB_of_mem hp) (fun v => β v = j')
    simp only [Config.split, xi_b, freeB_erase h hp, incf_apply, ite_one_comm j' (β p.2)]
    split_ifs at e ⊢ <;> omega
  · have e := card_filter_erase_add hp (fun r => α r.1 = i' ∧ β r.2 = j')
    simp only [Config.split, xi_c, decC_apply, ite_pair_comm i' (α p.1) j' (β p.2)]
    split_ifs at e ⊢ <;> omega

end Moves

end Rhone.Probability.Multilinear
