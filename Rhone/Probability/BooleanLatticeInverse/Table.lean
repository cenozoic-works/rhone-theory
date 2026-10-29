/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.BooleanLatticeInverse.Merge

/-! # The centred moments are the explicit table -/

@[expose] public section

universe u

namespace Rhone.Probability.BooleanLatticeInverse

open Finset LinearAlgebra.Recursion LinearAlgebra.Multilinear Multilinear SlotDeletion
open LinearAlgebra.Tridiag

theorem Q_empty_block {KA : ℕ} {F : Type*} [Field F] {SB : Type u} [Fintype SB] [DecidableEq SB]
    {q : Config KA 2 → F} (hq0 : q 0 = 1) {n : ℕ} (hn : n = 0)
    (hSB : Fintype.card SB = 0) (M : Finset (Fin n × SB)) (s : Fin n → Fin KA → F)
    (w : SB → Fin 2 → F) : Q q M s w = 1 := by
  subst hn
  have : IsEmpty SB := Fintype.card_eq_zero_iff.mp hSB
  have hM : M = ∅ := Finset.eq_empty_of_isEmpty M
  subst hM
  have hx : ∀ (α : Fin 0 → Fin KA) (β : SB → Fin 2), xi (∅ : Finset (Fin 0 × SB)) α β = 0 := by
    intro α β
    refine Config.ext ?_ ?_ ?_
    · funext i; simp [xi, freeA, domA]
    · funext i; simp [xi, freeB, domB]
    · funext i j; simp [xi]
  simp [Q, hx, hq0]

theorem sum_pairs_fst {SA SB : Type*} [DecidableEq SA] {F : Type*} [AddCommMonoid F]
    {M : Finset (SA × SB)} (hM : IsMatching M) (f : SA → F) :
    ∑ p ∈ M, f p.1 = ∑ x ∈ domA M, f x := by
  rw [domA, Finset.sum_image fun p hp p' hp' h => hM.fst p hp p' hp' h]

theorem sum_erase_swap {α F : Type*} [DecidableEq α] [AddCommMonoid F] (M : Finset α)
    (H : α → α → F) :
    ∑ p ∈ M, ∑ p' ∈ M.erase p, H p p' = ∑ p' ∈ M, ∑ p ∈ M.erase p', H p p' :=
  Finset.sum_comm' fun x y => by
    simp only [Finset.mem_erase]
    exact ⟨fun ⟨hx, hy, hyM⟩ => ⟨⟨Ne.symm hy, hx⟩, hyM⟩,
      fun ⟨⟨hxy, hx⟩, hy⟩ => ⟨hx, Ne.symm hxy, hy⟩⟩

theorem sum_succAbove_mem {F : Type*} [AddCommMonoid F] {n : ℕ} (x : Fin (n + 1))
    (T : Finset (Fin (n + 1))) (hx : x ∉ T) (g : Fin (n + 1) → F) :
    ∑ k ∈ T, g k = ∑ z : Fin n, if x.succAbove z ∈ T then g (x.succAbove z) else 0 := by
  have h := Fin.sum_univ_succAbove (fun k => if k ∈ T then g k else 0) x
  rw [ite_eq_right hx, zero_add] at h
  rw [← h, Finset.sum_ite_mem, Finset.univ_inter]

theorem sum_erase_eq_pull {SB : Type*} [DecidableEq SB] {F : Type*} [AddCommMonoid F] {n : ℕ}
    {M : Finset (Fin (n + 1) × SB)} (hM : IsMatching M) {p' : Fin (n + 1) × SB} (hp' : p' ∈ M)
    (f : Fin (n + 1) × SB → F) (g : Fin n → F)
    (h : ∀ p ∈ M.erase p', ∀ z, p.1 = p'.1.succAbove z → f p = g z) :
    ∑ p ∈ M.erase p', f p = ∑ z ∈ LinearAlgebra.BooleanLatticeInverse.pull p'.1 (domA M), g z := by
  have hne : ∀ p ∈ M.erase p', p.1 ≠ p'.1 := fun p hp he =>
    (Finset.mem_erase.mp hp).1 (hM.fst p (Finset.mem_erase.mp hp).2 p' hp' he)
  refine Finset.sum_bij (fun p hp => (Fin.exists_succAbove_eq (hne p hp)).choose)
    ?_ ?_ ?_ ?_
  · intro p hp
    rw [mem_pull, (Fin.exists_succAbove_eq (hne p hp)).choose_spec]
    exact mem_domA_of_mem (Finset.mem_erase.mp hp).2
  · intro p hp p'' hp'' he
    have h1 := (Fin.exists_succAbove_eq (hne p hp)).choose_spec
    have h2 := (Fin.exists_succAbove_eq (hne p'' hp'')).choose_spec
    rw [he] at h1
    exact hM.fst p (Finset.mem_erase.mp hp).2 p'' (Finset.mem_erase.mp hp'').2 (h1.symm.trans h2)
  · intro z hz
    rw [mem_pull, mem_domA] at hz
    obtain ⟨v, hv⟩ := hz
    have hp : (p'.1.succAbove z, v) ∈ M.erase p' :=
      Finset.mem_erase.mpr ⟨fun hc => Fin.succAbove_ne p'.1 z (congrArg Prod.fst hc), hv⟩
    refine ⟨_, hp, ?_⟩
    exact Fin.succAbove_right_injective (Fin.exists_succAbove_eq (hne _ hp)).choose_spec
  · intro p hp
    exact h p hp _ (Fin.exists_succAbove_eq (hne p hp)).choose_spec.symm

variable {KA : ℕ} {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {SB : Type u} [Fintype SB] [DecidableEq SB]
variable {θA θB ρ : F} {πA : Fin KA → F} {πB : Fin 2 → F}
variable (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
variable {q : Config KA 2 → F} (hq : IsSolution θA θB ρ πA πB q)
variable (hπA : ∑ i, πA i = 1) (hπB : πB 0 + πB 1 = 1)
    {P : LinearAlgebra.BooleanLatticeInverse.Tab KA F}
include hθA hθB hρ hq hπA hπB

theorem pairSum_eq {n : ℕ} {M : Finset (Fin n × SB)} (hM : IsMatching M)
    (hP : TrueBelow.{u} q πA πB P (n + Fintype.card SB)) (lab : Fin n → Fin KA) :
    (∑ k ∈ freeA M, ∑ x ∈ (freeA M).erase k,
        Q q M (hadA k x fun x => fA πA (lab x)) (fun _ => gB πB))
      + 2 * (∑ k ∈ freeA M, ∑ p ∈ M,
        Q q M (hadA p.1 k fun x => fA πA (lab x)) (fun _ => gB πB))
      + (∑ p ∈ M, ∑ p' ∈ M.erase p,
        Q q M (hadA p.1 p'.1 fun x => fA πA (lab x)) (hadB p.2 p'.2 fun _ => gB πB))
      = LinearAlgebra.BooleanLatticeInverse.pairSrc πA πB P n lab (Fintype.card SB) (domA M) := by
  by_cases hn : 2 ≤ n
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have hQA : ∀ (x' : Fin (m + 2)) (z : Fin (m + 1)),
        Q q M (hadA (x'.succAbove z) x' fun x => fA πA (lab x)) (fun _ => gB πB)
          = LinearAlgebra.BooleanLatticeInverse.aTerm πA P (m + 1) (lab ∘ x'.succAbove) (lab x')
              (Fintype.card SB)
              (LinearAlgebra.BooleanLatticeInverse.pull x' (domA M)) z :=
      fun x' z => Q_hadA_centred hθA hθB hρ hq hπA hM hP lab x' z
    have hfree : ∀ x' ∈ freeA M,
        (∑ k ∈ (freeA M).erase x',
            Q q M (hadA k x' fun x => fA πA (lab x)) (fun _ => gB πB))
          + 2 * (∑ p ∈ M, Q q M (hadA p.1 x' fun x => fA πA (lab x)) (fun _ => gB πB))
        = ∑ z : Fin (m + 1),
            (if z ∈ LinearAlgebra.BooleanLatticeInverse.pull x' (domA M) then (2 : F) else 1)
            * LinearAlgebra.BooleanLatticeInverse.aTerm πA P (m + 1) (lab ∘ x'.succAbove) (lab x')
                (Fintype.card SB)
              (LinearAlgebra.BooleanLatticeInverse.pull x' (domA M)) z := by
      intro x' hx'
      have hx'S : x' ∉ domA M := (Finset.mem_sdiff.mp hx').2
      have e : (∑ p ∈ M, Q q M (hadA p.1 x' fun x => fA πA (lab x)) (fun _ => gB πB))
          = ∑ k ∈ domA M, Q q M (hadA k x' fun x => fA πA (lab x)) (fun _ => gB πB) :=
        sum_pairs_fst hM (fun k => Q q M (hadA k x' fun x => fA πA (lab x)) (fun _ => gB πB))
      rw [e, sum_succAbove_mem x' ((freeA M).erase x') (by simp),
        sum_succAbove_mem x' (domA M) hx'S, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun z _ => ?_
      by_cases hz : z ∈ LinearAlgebra.BooleanLatticeInverse.pull x' (domA M)
      · have h2 : x'.succAbove z ∈ domA M := mem_pull.mp hz
        have h1 : x'.succAbove z ∉ (freeA M).erase x' := by simp [freeA, h2]
        rw [ite_eq_right h1, ite_eq_left h2, ite_eq_left hz, hQA]
        ring
      · have h2 : x'.succAbove z ∉ domA M := fun h => hz (mem_pull.mpr h)
        have h1 : x'.succAbove z ∈ (freeA M).erase x' :=
          Finset.mem_erase.mpr ⟨Fin.succAbove_ne x' z, by simp [freeA, h2]⟩
        rw [ite_eq_left h1, ite_eq_right h2, ite_eq_right hz, hQA]
        ring
    have hpair : (∑ p ∈ M, ∑ p' ∈ M.erase p,
          Q q M (hadA p.1 p'.1 fun x => fA πA (lab x)) (hadB p.2 p'.2 fun _ => gB πB))
        = ∑ x' ∈ domA M, ∑ z ∈ LinearAlgebra.BooleanLatticeInverse.pull x' (domA M),
            (LinearAlgebra.BooleanLatticeInverse.kapB πB * LinearAlgebra.BooleanLatticeInverse.aTerm
                πA P (m + 1) (lab ∘ x'.succAbove) (lab x') (Fintype.card SB - 2)
                ((LinearAlgebra.BooleanLatticeInverse.pull x' (domA M)).erase z) z
              + LinearAlgebra.BooleanLatticeInverse.gamB πB *
                  LinearAlgebra.BooleanLatticeInverse.aTerm πA P (m + 1) (lab ∘ x'.succAbove)
                  (lab x')
                (Fintype.card SB - 1) (LinearAlgebra.BooleanLatticeInverse.pull x' (domA M)) z) :=
                    by
      rw [sum_erase_swap M]
      have e : ∀ p' ∈ M, (∑ p ∈ M.erase p',
          Q q M (hadA p.1 p'.1 fun x => fA πA (lab x)) (hadB p.2 p'.2 fun _ => gB πB))
          = ∑ z ∈ LinearAlgebra.BooleanLatticeInverse.pull p'.1 (domA M),
            (LinearAlgebra.BooleanLatticeInverse.kapB πB * LinearAlgebra.BooleanLatticeInverse.aTerm
                πA P (m + 1) (lab ∘ p'.1.succAbove) (lab p'.1)
                (Fintype.card SB - 2)
                    ((LinearAlgebra.BooleanLatticeInverse.pull p'.1 (domA M)).erase z) z
              + LinearAlgebra.BooleanLatticeInverse.gamB πB *
                  LinearAlgebra.BooleanLatticeInverse.aTerm πA P (m + 1) (lab ∘ p'.1.succAbove)
                  (lab p'.1)
                (Fintype.card SB - 1) (LinearAlgebra.BooleanLatticeInverse.pull p'.1 (domA M)) z) :=
        fun p' hp' => sum_erase_eq_pull hM hp' _ _ fun p hp z hz =>
          Q_hadAB_centred hθA hθB hρ hq hπA hπB hM hP lab (Finset.mem_erase.mp hp).2 hp' z hz
      rw [Finset.sum_congr rfl e]
      exact sum_pairs_fst hM (fun x' => ∑ z ∈ LinearAlgebra.BooleanLatticeInverse.pull x' (domA M),
        (LinearAlgebra.BooleanLatticeInverse.kapB πB * LinearAlgebra.BooleanLatticeInverse.aTerm πA
            P (m + 1) (lab ∘ x'.succAbove) (lab x') (Fintype.card SB - 2)
            ((LinearAlgebra.BooleanLatticeInverse.pull x' (domA M)).erase z) z
          + LinearAlgebra.BooleanLatticeInverse.gamB πB * LinearAlgebra.BooleanLatticeInverse.aTerm
              πA P (m + 1) (lab ∘ x'.succAbove) (lab x')
            (Fintype.card SB - 1) (LinearAlgebra.BooleanLatticeInverse.pull x' (domA M)) z))
    have hsplit : ∀ Gf : Fin (m + 2) → F,
        ∑ x', Gf x' = ∑ x' ∈ domA M, Gf x' + ∑ x' ∈ freeA M, Gf x' := by
      intro Gf
      rw [← Finset.sum_add_sum_compl (domA M) Gf, Finset.compl_eq_univ_sdiff]
      rfl
    rw [sum_erase_swap (freeA M), hpair, Finset.mul_sum,
      ← Finset.sum_add_distrib, Finset.sum_congr rfl hfree]
    simp only [LinearAlgebra.BooleanLatticeInverse.pairSrc]
    rw [hsplit, add_comm]
    refine congrArg₂ _ ?_ ?_
    · refine Finset.sum_congr rfl fun x' hx' => ?_
      simp only [ite_eq_left hx']
      rw [Finset.sum_ite_mem, Finset.univ_inter]
    · refine Finset.sum_congr rfl fun x' hx' => ?_
      have hx'S : x' ∉ domA M := (Finset.mem_sdiff.mp hx').2
      simp only [ite_eq_right hx'S]
  · have hn' : n = 0 ∨ n = 1 := by omega
    rcases hn' with rfl | rfl
    · have hM0 : M = ∅ := Finset.eq_empty_of_isEmpty M
      subst hM0
      simp [LinearAlgebra.BooleanLatticeInverse.pairSrc, freeA, domA]
    · have hR : LinearAlgebra.BooleanLatticeInverse.pairSrc πA πB P 1 lab (Fintype.card SB)
        (domA M) = 0 := by simp [LinearAlgebra.BooleanLatticeInverse.pairSrc]
      have hall : ∀ k ∈ freeA M, ∀ p ∈ M, False := fun k hk p hp =>
        notMem_freeA_of_mem hp ((Subsingleton.elim p.1 k) ▸ hk)
      have e1 : (∑ k ∈ freeA M, ∑ x ∈ (freeA M).erase k,
          Q q M (hadA k x fun x => fA πA (lab x)) (fun _ => gB πB)) = 0 :=
        Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun x hx =>
          absurd (Subsingleton.elim x k) (Finset.mem_erase.mp hx).1
      have e2 : (∑ k ∈ freeA M, ∑ p ∈ M,
          Q q M (hadA p.1 k fun x => fA πA (lab x)) (fun _ => gB πB)) = 0 :=
        Finset.sum_eq_zero fun k hk => Finset.sum_eq_zero fun p hp => (hall k hk p hp).elim
      have e3 : (∑ p ∈ M, ∑ p' ∈ M.erase p,
          Q q M (hadA p.1 p'.1 fun x => fA πA (lab x)) (hadB p.2 p'.2 fun _ => gB πB)) = 0 :=
        Finset.sum_eq_zero fun p hp => Finset.sum_eq_zero fun p' hp' =>
          absurd (hM.fst p' (Finset.mem_erase.mp hp').2 p hp (Subsingleton.elim _ _))
            (Finset.mem_erase.mp hp').1
      rw [hR, e1, e2, e3]
      ring

omit hπA in
theorem bSum_eq {n : ℕ} {M : Finset (Fin n × SB)} (hM : IsMatching M)
    (hP : TrueBelow.{u} q πA πB P (n + Fintype.card SB)) (lab : Fin n → Fin KA) :
    (∑ l ∈ freeB M, ∑ l' ∈ (freeB M).erase l,
        Q q M (fun x => fA πA (lab x)) (hadB l l' fun _ => gB πB))
      + 2 * (∑ l ∈ freeB M, ∑ p ∈ M,
        Q q M (fun x => fA πA (lab x)) (hadB p.2 l fun _ => gB πB))
      = (((Fintype.card SB - (domA M).card) * (Fintype.card SB - (domA M).card - 1) : ℕ) : F)
          * (LinearAlgebra.BooleanLatticeInverse.kapB πB * P n lab (Fintype.card SB - 2) (domA M)
            + LinearAlgebra.BooleanLatticeInverse.gamB πB * P n lab (Fintype.card SB - 1) (domA M))
        + 2 * ((Fintype.card SB - (domA M).card : ℕ) : F)
          * ∑ x ∈ domA M,
              (LinearAlgebra.BooleanLatticeInverse.kapB πB * P n lab (Fintype.card SB - 2)
              ((domA M).erase x)
            + LinearAlgebra.BooleanLatticeInverse.gamB πB * P n lab (Fintype.card SB - 1)
                (domA M)) := by
  have hcard : (freeB M).card = Fintype.card SB - (domA M).card := by
    have h1 := card_freeB hM
    have h2 := card_domA hM
    omega
  set C : F := LinearAlgebra.BooleanLatticeInverse.kapB πB * P n lab (Fintype.card SB - 2) (domA M)
    + LinearAlgebra.BooleanLatticeInverse.gamB πB * P n lab (Fintype.card SB - 1) (domA M) with hC
  have h1 : (∑ l ∈ freeB M, ∑ l' ∈ (freeB M).erase l,
        Q q M (fun x => fA πA (lab x)) (hadB l l' fun _ => gB πB))
      = ((((freeB M).card * ((freeB M).card - 1) : ℕ)) : F) * C := by
    have : ∀ l ∈ freeB M, (∑ l' ∈ (freeB M).erase l,
        Q q M (fun x => fA πA (lab x)) (hadB l l' fun _ => gB πB))
        = (((freeB M).card - 1 : ℕ) : F) * C := by
      intro l hl
      rw [Finset.sum_congr rfl (g := fun _ => C) fun l' hl' =>
        Q_hadB_free hθA hθB hρ hq hπB hM hP lab hl (Finset.mem_erase.mp hl').2
          (Finset.mem_erase.mp hl').1.symm,
        Finset.sum_const, Finset.card_erase_of_mem hl, nsmul_eq_mul]
    rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, ← mul_assoc, ← Nat.cast_mul]
  set D' : Fin n → F := fun x => LinearAlgebra.BooleanLatticeInverse.kapB πB * P n lab
      (Fintype.card SB - 2) ((domA M).erase x)
    + LinearAlgebra.BooleanLatticeInverse.gamB πB * P n lab (Fintype.card SB - 1) (domA M) with hD'
  have h2 : (∑ l ∈ freeB M, ∑ p ∈ M,
        Q q M (fun x => fA πA (lab x)) (hadB p.2 l fun _ => gB πB))
      = ((freeB M).card : F) * ∑ x ∈ domA M, D' x := by
    rw [← sum_pairs_fst hM D']
    have : ∀ l ∈ freeB M, (∑ p ∈ M,
        Q q M (fun x => fA πA (lab x)) (hadB p.2 l fun _ => gB πB)) = ∑ p ∈ M, D' p.1 :=
      fun l hl => Finset.sum_congr rfl fun p hp =>
        Q_hadB_pair hθA hθB hρ hq hπB hM hP lab hl hp
    rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]
  rw [h1, h2, hcard]
  ring

theorem centred_block_eq {n : ℕ} {M : Finset (Fin n × SB)} (hM : IsMatching M)
    (hP : TrueBelow.{u} q πA πB P (n + Fintype.card SB)) (lab : Fin n → Fin KA)
    (Φ : Finset (Fin n) → F)
    (hΦ : ∀ M' : Finset (Fin n × SB), IsMatching M' →
      Q q M' (fun x => fA πA (lab x)) (fun _ => gB πB) = Φ (domA M')) :
    dcoef F n (Fintype.card SB) θA θB ρ (domA M).card * Φ (domA M) - ρ *
        LinearAlgebra.BooleanLatticeInverse.D Φ (domA M)
        - 2 * ((Fintype.card SB - (domA M).card : ℕ) : F) * LinearAlgebra.BooleanLatticeInverse.U Φ
            (domA M)
      = LinearAlgebra.BooleanLatticeInverse.srcKB2 πA πB P n lab (Fintype.card SB) (domA M) := by
  have hπB' : ∑ j, πB j = 1 := by simpa [Fin.sum_univ_two] using hπB
  have L := dgQ_mul_Q_eq_rhsQ hθA hθB hρ hq M hπA hπB' hM (fun x => fA πA (lab x)) (fun _ => gB πB)
  rw [Fintype.card_fin] at L
  have hQ : Q q M (fun x => fA πA (lab x)) (fun _ => gB πB) = Φ (domA M) := hΦ M hM
  have hd : dgQ θA θB ρ n (Fintype.card SB) M.card
      = dcoef F n (Fintype.card SB) θA θB ρ (domA M).card := by
    rw [card_domA hM]
    simp only [dgQ, dcoef]
  rw [hd, hQ] at L
  have hcardB : (freeB M).card = Fintype.card SB - (domA M).card := by
    have h1 := card_freeB hM
    have h2 := card_domA hM
    omega
  have hpair := pairSum_eq hθA hθB hρ hq hπA hπB hM hP lab
  have hb := bSum_eq hθA hθB hρ hq hπB hM hP lab
  have hE : (∑ k ∈ freeA M, ∑ l ∈ freeB M,
        Q q (insert (k, l) M) (fun x => fA πA (lab x)) (fun _ => gB πB))
      = ((Fintype.card SB - (domA M).card : ℕ) : F) * LinearAlgebra.BooleanLatticeInverse.U Φ
          (domA M) := by
    rw [LinearAlgebra.BooleanLatticeInverse.U_apply, Finset.compl_eq_univ_sdiff, ← freeA,
        Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hterm : ∀ l ∈ freeB M,
        Q q (insert (k, l) M) (fun x => fA πA (lab x)) (fun _ => gB πB)
          = Φ (insert k (domA M)) := by
      intro l hl
      rw [hΦ _ (isMatching_insert hM hk hl)]
      simp [domA, Finset.image_insert]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, hcardB]
  have hmA : (∑ u : Fin n, mean πA ((fun x => fA πA (lab x)) u)
        * Q q M (Function.update (fun x => fA πA (lab x)) u 1) (fun _ => gB πB)) = 0 := by
    simp [mean_fA hπA]
  have hmB : (∑ v : SB, mean πB ((fun _ => gB πB) v)
        * Q q M (fun x => fA πA (lab x)) (Function.update (fun _ => gB πB) v 1)) = 0 := by
    simp [mean_gB hπB]
  have hR : (∑ p ∈ M, Q q (M.erase p) (fun x => fA πA (lab x)) (fun _ => gB πB))
      = LinearAlgebra.BooleanLatticeInverse.D Φ (domA M) := by
    rw [LinearAlgebra.BooleanLatticeInverse.D_apply, ← sum_pairs_fst hM]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [hΦ _ (isMatching_erase hM p), domA_erase hM hp]
  rw [rhsQ] at L
  unfold LinearAlgebra.BooleanLatticeInverse.srcKB2
  linear_combination L + hpair + hb + 2 * hE + θA * hmA + θB * hmB + ρ * hR

omit [Fintype SB] [DecidableEq SB] in
theorem trueBelow_PhiTab (f : ℕ) :
    TrueBelow.{u} q πA πB (LinearAlgebra.BooleanLatticeInverse.PhiTab θA θB ρ πA πB f) (f + 1) := by
  induction f with
  | zero =>
    intro n SB _ _ M lab hM hlt
    rw [Q_empty_block hq.empty (by omega) (by omega)]
    rfl
  | succ f ih =>
    intro n SB _ _ M lab hM hlt
    by_cases h0 : n + Fintype.card SB = 0
    · rw [Q_empty_block hq.empty
        (by omega) (by omega), LinearAlgebra.BooleanLatticeInverse.PhiTab, ite_eq_left h0]
    · rw [LinearAlgebra.BooleanLatticeInverse.PhiTab, ite_eq_right h0]
      classical
      have hP : TrueBelow.{u} q πA πB (LinearAlgebra.BooleanLatticeInverse.PhiTab θA θB ρ πA πB f)
          (n + Fintype.card SB) :=
        ih.mono (by omega)
      set P := LinearAlgebra.BooleanLatticeInverse.PhiTab θA θB ρ πA πB f with hPdef
      let Φ : Finset (Fin n) → F := fun T =>
        if h : ∃ M' : Finset (Fin n × SB), IsMatching M' ∧ domA M' = T then
          Q q h.choose (fun x => fA πA (lab x)) (fun _ => gB πB) else 0
      have hΦ : ∀ M' : Finset (Fin n × SB), IsMatching M' →
          Q q M' (fun x => fA πA (lab x)) (fun _ => gB πB) = Φ (domA M') := by
        intro M' hM'
        have hex : ∃ M'' : Finset (Fin n × SB), IsMatching M'' ∧ domA M'' = domA M' :=
          ⟨M', hM', rfl⟩
        simp only [Φ, dite_eq_left hex]
        exact Q_congr_domA q hM' hex.choose_spec.1 hex.choose_spec.2.symm _ _
      have hsol : LinearAlgebra.BooleanLatticeInverse.IsBlockSol θA θB ρ (Fintype.card SB)
          (LinearAlgebra.BooleanLatticeInverse.srcKB2 πA πB P n lab (Fintype.card SB)) Φ := by
        intro T hT
        obtain ⟨M', hM', hd⟩ := exists_matching_domA (SB := SB) T hT
        have := centred_block_eq hθA hθB hρ hq hπA hπB hM' hP lab Φ hΦ
        rw [hd] at this
        exact this
      have hδ : 0 < θA * (n : F) + θB * (Fintype.card SB : F) := by
        rcases Nat.eq_zero_or_pos n with h | h
        · have h' : 0 < Fintype.card SB := by omega
          have := mul_pos hθB (Nat.cast_pos.mpr h')
          have : 0 ≤ θA * (n : F) := mul_nonneg hθA.le (Nat.cast_nonneg n)
          linarith
        · have := mul_pos hθA (Nat.cast_pos.mpr h)
          have : 0 ≤ θB * (Fintype.card SB : F) := mul_nonneg hθB.le (Nat.cast_nonneg _)
          linarith
      have hle : (domA M).card ≤ Fintype.card SB := by
        have h1 := card_freeB hM
        have h2 := card_domA hM
        omega
      have hb := (LinearAlgebra.BooleanLatticeInverse.isBlockSol_iff_of_pos hρ hδ _ _).mp hsol
          (domA M) hle
      rw [hΦ M hM]
      exact hb

theorem Q_centred_eq_PhiX {n : ℕ} (M : Finset (Fin n × SB)) (hM : IsMatching M)
    (lab : Fin n → Fin KA) :
    Q q M (fun x => fA πA (lab x)) (fun _ => gB πB)
      = LinearAlgebra.BooleanLatticeInverse.PhiX θA θB ρ πA πB n lab (Fintype.card SB) (domA M) :=
  trueBelow_PhiTab hθA hθB hρ hq hπA hπB (n + Fintype.card SB) n SB M lab hM
    (Nat.lt_succ_self _)

end Rhone.Probability.BooleanLatticeInverse
