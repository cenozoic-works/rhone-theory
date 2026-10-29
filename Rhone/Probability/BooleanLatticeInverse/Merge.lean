/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.BooleanLatticeInverse.Centred
public import Rhone.Probability.BooleanLatticeInverse.SlotDelete
public import Rhone.Probability.Multilinear.MultilinearRecursion

/-! # The merge terms of the recursion at centred test vectors for a biallelic `B` locus -/

@[expose] public section

universe u

namespace Rhone.Probability.BooleanLatticeInverse

open Finset LinearAlgebra.Recursion LinearAlgebra.Multilinear Multilinear SlotDeletion

variable {KA : ℕ} {F : Type*} [Field F]

def TrueBelow (q : Config KA 2 → F) (πA : Fin KA → F) (πB : Fin 2 → F)
    (P : LinearAlgebra.BooleanLatticeInverse.Tab KA F)
    (N : ℕ) : Prop :=
  ∀ (n : ℕ) (SB : Type u) [Fintype SB] [DecidableEq SB] (M : Finset (Fin n × SB))
    (lab : Fin n → Fin KA), IsMatching M → n + Fintype.card SB < N →
    Q q M (fun x => fA πA (lab x)) (fun _ => gB πB) = P n lab (Fintype.card SB) (domA M)

theorem TrueBelow.mono {q : Config KA 2 → F} {πA : Fin KA → F} {πB : Fin 2 → F}
    {P : LinearAlgebra.BooleanLatticeInverse.Tab KA F}
    {N N' : ℕ} (h : TrueBelow.{u} q πA πB P N) (hN : N' ≤ N) : TrueBelow.{u} q πA πB P N' :=
  fun n SB _ _ M lab hM hlt => h n SB M lab hM (lt_of_lt_of_le hlt hN)

section Pull

variable {n : ℕ}

theorem mem_pull {x : Fin (n + 1)} {S : Finset (Fin (n + 1))} {y : Fin n} :
    y ∈ LinearAlgebra.BooleanLatticeInverse.pull x S ↔ x.succAbove y ∈ S :=
        by simp [LinearAlgebra.BooleanLatticeInverse.pull]

theorem pull_erase_self (x : Fin (n + 1)) (S : Finset (Fin (n + 1))) :
    LinearAlgebra.BooleanLatticeInverse.pull x (S.erase x) =
        LinearAlgebra.BooleanLatticeInverse.pull x S := by
  ext y
  simp [mem_pull, Finset.mem_erase, Fin.succAbove_ne]

theorem pull_erase_succAbove (x : Fin (n + 1)) (z : Fin n) (S : Finset (Fin (n + 1))) :
    LinearAlgebra.BooleanLatticeInverse.pull x (S.erase (x.succAbove z)) =
        (LinearAlgebra.BooleanLatticeInverse.pull x S).erase z := by
  ext y
  simp [mem_pull, Finset.mem_erase, (Fin.succAbove_right_injective).eq_iff]

end Pull

section Expand

variable {ι : Type*} {K : ℕ} [DecidableEq ι]

theorem isMulti_expand2 {G : (ι → Fin K → F) → F} (hG : IsMulti G) (s : ι → Fin K → F)
    (u : ι) (a c : F) (x y : Fin K → F) :
    G (Function.update s u (a • x + c • y))
      = a * G (Function.update s u x) + c * G (Function.update s u y) := by
  rw [hG.add, hG.smul, hG.smul]

theorem isMulti_expand3 {G : (ι → Fin K → F) → F} (hG : IsMulti G) (s : ι → Fin K → F)
    (u : ι) (a c d : F) (x y z : Fin K → F) :
    G (Function.update s u (a • x + c • y - d • z))
      = a * G (Function.update s u x) + c * G (Function.update s u y)
        - d * G (Function.update s u z) := by
  rw [sub_eq_add_neg, ← neg_smul, hG.add, hG.add, hG.smul, hG.smul, hG.smul]
  ring

end Expand

theorem hadB_fam {SB : Type*} [DecidableEq SB] {v v' : SB} (hne : v ≠ v') (g : Fin 2 → F) :
    (fun y : {y : SB // y ≠ v'} => hadB v v' (fun _ => g) (y : SB))
      = Function.update (fun _ => g) (⟨v, hne⟩ : {y : SB // y ≠ v'}) (g * g) := by
  funext y
  by_cases hy : y = ⟨v, hne⟩
  · subst hy
    simp [hadB, hne]
  · have h1 : (y : SB) ≠ v := fun h => hy (Subtype.ext h)
    simp [hadB, hy, h1, y.2]

section Merge

variable {SB : Type u} [Fintype SB] [DecidableEq SB]
variable [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {πA : Fin KA → F} {πB : Fin 2 → F}
variable (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
variable {q : Config KA 2 → F} (hq : IsSolution θA θB ρ πA πB q)
variable (hπA : ∑ i, πA i = 1) (hπB : πB 0 + πB 1 = 1)
    {P : LinearAlgebra.BooleanLatticeInverse.Tab KA F}
include hθA hθB hρ hq hπA hπB

omit hπA in
theorem Q_delB_one {m : ℕ} {M : Finset (Fin m × SB)} (hM : IsMatching M) (v : SB)
    (s : Fin m → Fin KA → F) :
    Q q M s (Function.update (fun _ => gB πB) v 1)
      = Q q (restrB v M) s (fun _ => gB πB) := by
  have hπB' : ∑ j, πB j = 1 := by simpa [Fin.sum_univ_two] using hπB
  rw [Q_delB hθA hθB hρ hq hπB' hM v s (Function.update (fun _ => gB πB) v 1) (by simp)]
  congr 1
  funext y
  exact Function.update_of_ne y.2 _ _

omit hπB in
theorem Q_hadA_centred {n : ℕ} {M : Finset (Fin (n + 2) × SB)} (hM : IsMatching M)
    (hP : TrueBelow.{u} q πA πB P (n + 2 + Fintype.card SB)) (lab : Fin (n + 2) → Fin KA)
    (x' : Fin (n + 2)) (z : Fin (n + 1)) :
    Q q M (hadA (x'.succAbove z) x' fun x => fA πA (lab x)) (fun _ => gB πB)
      = LinearAlgebra.BooleanLatticeInverse.aTerm πA P (n + 1) (lab ∘ x'.succAbove) (lab x')
          (Fintype.card SB)
          (LinearAlgebra.BooleanLatticeInverse.pull x' (domA M)) z := by
  have hM1 := isMatching_pullM (x := x') hM
  have key := Q_delA hθA hθB hρ hq hπA hM x' (hadA (x'.succAbove z) x'
    (fun x => fA πA (lab x))) (by simp [hadA]) (fun _ => gB πB)
  rw [key]
  have hfam : (fun y => hadA (x'.succAbove z) x' (fun x => fA πA (lab x)) (x'.succAbove y))
      = Function.update (fun y => fA πA ((lab ∘ x'.succAbove) y)) z
          (fA πA (lab (x'.succAbove z)) * fA πA (lab x')) := by
    funext y
    by_cases hy : y = z
    · subst hy
      simp [hadA, Fin.succAbove_ne]
    · simp [hadA, hy, Fin.succAbove_ne]
  rw [hfam, fA_mul_fA, isMulti_expand3 (Q_isMultiA q (pullM x' M) (fun _ => gB πB))]
  have e1 : Q q (pullM x' M) (Function.update (fun y => fA πA ((lab ∘ x'.succAbove) y)) z 1)
        (fun _ => gB πB)
      = P n ((lab ∘ x'.succAbove) ∘ z.succAbove) (Fintype.card SB)
          (LinearAlgebra.BooleanLatticeInverse.pull z
              (LinearAlgebra.BooleanLatticeInverse.pull x' (domA M))) := by
    have k2 := Q_delA hθA hθB hρ hq hπA hM1 z
      (Function.update (fun y => fA πA ((lab ∘ x'.succAbove) y)) z 1) (by simp)
      (fun _ => gB πB)
    rw [k2]
    have : (fun y => Function.update (fun y => fA πA ((lab ∘ x'.succAbove) y)) z 1
        (z.succAbove y)) = fun y => fA πA (((lab ∘ x'.succAbove) ∘ z.succAbove) y) := by
      funext y
      simp
    rw [this, hP n SB _ ((lab ∘ x'.succAbove) ∘ z.succAbove) (isMatching_pullM hM1)
      (by omega), domA_pullM, domA_pullM]
  have e2 : Q q (pullM x' M) (Function.update (fun y => fA πA ((lab ∘ x'.succAbove) y)) z
        (fA πA (lab (x'.succAbove z)))) (fun _ => gB πB)
      = P (n + 1) (lab ∘ x'.succAbove) (Fintype.card SB)
          (LinearAlgebra.BooleanLatticeInverse.pull x' (domA M)) := by
    have hu : Function.update (fun y => fA πA ((lab ∘ x'.succAbove) y)) z
        (fA πA (lab (x'.succAbove z))) = fun y => fA πA ((lab ∘ x'.succAbove) y) :=
      Function.update_eq_self z (fun y => fA πA ((lab ∘ x'.succAbove) y))
    rw [hu, hP (n + 1) SB _ (lab ∘ x'.succAbove) hM1 (by omega), domA_pullM]
  have e3 : Q q (pullM x' M) (Function.update (fun y => fA πA ((lab ∘ x'.succAbove) y)) z
        (fA πA (lab x'))) (fun _ => gB πB)
      = P (n + 1) (Function.update (lab ∘ x'.succAbove) z (lab x')) (Fintype.card SB)
          (LinearAlgebra.BooleanLatticeInverse.pull x' (domA M)) := by
    have : Function.update (fun y => fA πA ((lab ∘ x'.succAbove) y)) z (fA πA (lab x'))
        = fun y => fA πA (Function.update (lab ∘ x'.succAbove) z (lab x') y) := by
      funext y
      by_cases hy : y = z
      · subst hy; simp
      · simp [hy]
    rw [this, hP (n + 1) SB _ (Function.update (lab ∘ x'.succAbove) z (lab x')) hM1
      (by omega), domA_pullM]
  rw [e1, e2, e3]
  rfl

omit hπA in
theorem Q_hadB_free {n : ℕ} {M : Finset (Fin n × SB)} (hM : IsMatching M)
    (hP : TrueBelow.{u} q πA πB P (n + Fintype.card SB)) (lab : Fin n → Fin KA)
    {l l' : SB} (hl : l ∈ freeB M) (hl' : l' ∈ freeB M) (hne : l ≠ l') :
    Q q M (fun x => fA πA (lab x)) (hadB l l' fun _ => gB πB)
      = LinearAlgebra.BooleanLatticeInverse.kapB πB * P n lab (Fintype.card SB - 2) (domA M)
        + LinearAlgebra.BooleanLatticeInverse.gamB πB * P n lab (Fintype.card SB - 1) (domA M) := by
  have hπB' : ∑ j, πB j = 1 := by simpa [Fin.sum_univ_two] using hπB
  have hcard : 0 < Fintype.card SB := Fintype.card_pos_iff.mpr ⟨l⟩
  have key := Q_delB hθA hθB hρ hq hπB' hM l' (fun x => fA πA (lab x))
    (hadB l l' fun _ => gB πB) (by simp [hadB])
  rw [key, hadB_fam hne, gB_mul_gB hπB,
    isMulti_expand2 (Q_isMultiB q (restrB l' M) (fun x => fA πA (lab x)))]
  have hl1 : (⟨l, hne⟩ : {y : SB // y ≠ l'}) ∈ freeB (restrB l' M) := mem_freeB_restrB.mpr hl
  have hM1 := isMatching_restrB (v₀ := l') hM
  have c1 := card_restrB_slots l'
  have c2 := card_restrB_slots (⟨l, hne⟩ : {y : SB // y ≠ l'})
  rw [Q_delB_one hθA hθB hρ hq hπB hM1 ⟨l, hne⟩,
    Function.update_eq_self (⟨l, hne⟩ : {y : SB // y ≠ l'}) (fun _ => gB πB)]
  have t1 := hP n {y : {y : SB // y ≠ l'} // y ≠ ⟨l, hne⟩} (restrB ⟨l, hne⟩ (restrB l' M))
    lab (isMatching_restrB hM1) (by omega)
  have t2 := hP n {y : SB // y ≠ l'} (restrB l' M) lab hM1 (by omega)
  rw [domA_restrB_of_free hl1, domA_restrB_of_free hl'] at t1
  rw [domA_restrB_of_free hl'] at t2
  have hc2 : Fintype.card {y : {y : SB // y ≠ l'} // y ≠ ⟨l, hne⟩} = Fintype.card SB - 2 := by
    omega
  rw [t1, t2, hc2, c1]

omit hπA in
theorem Q_hadB_pair {n : ℕ} {M : Finset (Fin n × SB)} (hM : IsMatching M)
    (hP : TrueBelow.{u} q πA πB P (n + Fintype.card SB)) (lab : Fin n → Fin KA)
    {l : SB} (hl : l ∈ freeB M) {p : Fin n × SB} (hp : p ∈ M) :
    Q q M (fun x => fA πA (lab x)) (hadB p.2 l fun _ => gB πB)
      = LinearAlgebra.BooleanLatticeInverse.kapB πB * P n lab (Fintype.card SB - 2)
          ((domA M).erase p.1)
        + LinearAlgebra.BooleanLatticeInverse.gamB πB * P n lab (Fintype.card SB - 1) (domA M) := by
  have hπB' : ∑ j, πB j = 1 := by simpa [Fin.sum_univ_two] using hπB
  have hcard : 0 < Fintype.card SB := Fintype.card_pos_iff.mpr ⟨l⟩
  have hne : p.2 ≠ l := by
    intro h
    refine mem_freeB.mp hl p.1 ?_
    rw [← h]
    exact hp
  have key := Q_delB hθA hθB hρ hq hπB' hM l (fun x => fA πA (lab x))
    (hadB p.2 l fun _ => gB πB) (by simp [hadB])
  rw [key, hadB_fam hne, gB_mul_gB hπB,
    isMulti_expand2 (Q_isMultiB q (restrB l M) (fun x => fA πA (lab x)))]
  have hM1 := isMatching_restrB (v₀ := l) hM
  have hp1 : (p.1, (⟨p.2, hne⟩ : {y : SB // y ≠ l})) ∈ restrB l M := mem_restrB.mpr hp
  have c1 := card_restrB_slots l
  have c2 := card_restrB_slots (⟨p.2, hne⟩ : {y : SB // y ≠ l})
  rw [Q_delB_one hθA hθB hρ hq hπB hM1 ⟨p.2, hne⟩,
    Function.update_eq_self (⟨p.2, hne⟩ : {y : SB // y ≠ l}) (fun _ => gB πB)]
  have t1 := hP n {y : {y : SB // y ≠ l} // y ≠ ⟨p.2, hne⟩} (restrB ⟨p.2, hne⟩ (restrB l M))
    lab (isMatching_restrB hM1) (by omega)
  have t2 := hP n {y : SB // y ≠ l} (restrB l M) lab hM1 (by omega)
  have e1 : domA (restrB ⟨p.2, hne⟩ (restrB l M)) = (domA M).erase p.1 := by
    have h := domA_restrB_of_mem hM1 hp1
    rw [domA_restrB_of_free hl] at h
    exact h
  rw [e1] at t1
  rw [domA_restrB_of_free hl] at t2
  have hc2 : Fintype.card {y : {y : SB // y ≠ l} // y ≠ ⟨p.2, hne⟩} = Fintype.card SB - 2 := by
    omega
  rw [t1, t2, hc2, c1]

theorem Q_hadAB_centred {n : ℕ} {M : Finset (Fin (n + 2) × SB)} (hM : IsMatching M)
    (hP : TrueBelow.{u} q πA πB P (n + 2 + Fintype.card SB)) (lab : Fin (n + 2) → Fin KA)
    {p p' : Fin (n + 2) × SB} (hp : p ∈ M) (hp' : p' ∈ M) (z : Fin (n + 1))
    (hz : p.1 = p'.1.succAbove z) :
    Q q M (hadA p.1 p'.1 fun x => fA πA (lab x)) (hadB p.2 p'.2 fun _ => gB πB)
      = LinearAlgebra.BooleanLatticeInverse.kapB πB * LinearAlgebra.BooleanLatticeInverse.aTerm πA P
          (n + 1) (lab ∘ p'.1.succAbove) (lab p'.1) (Fintype.card SB - 2)
            ((LinearAlgebra.BooleanLatticeInverse.pull p'.1 (domA M)).erase z) z
        + LinearAlgebra.BooleanLatticeInverse.gamB πB * LinearAlgebra.BooleanLatticeInverse.aTerm πA
            P (n + 1) (lab ∘ p'.1.succAbove) (lab p'.1)
            (Fintype.card SB - 1) (LinearAlgebra.BooleanLatticeInverse.pull p'.1 (domA M)) z := by
  have hπB' : ∑ j, πB j = 1 := by simpa [Fin.sum_univ_two] using hπB
  have hne1 : p.1 ≠ p'.1 := by
    rw [hz]
    exact Fin.succAbove_ne _ _
  have hne : p.2 ≠ p'.2 := fun h => hne1 (congrArg Prod.fst (hM.snd p hp p' hp' h))
  have hcard : 1 < Fintype.card SB := Fintype.one_lt_card_iff.mpr ⟨p.2, p'.2, hne⟩
  have key := Q_delB hθA hθB hρ hq hπB' hM p'.2 (hadA p.1 p'.1 fun x => fA πA (lab x))
    (hadB p.2 p'.2 fun _ => gB πB) (by simp [hadB])
  rw [key, hadB_fam hne, gB_mul_gB hπB,
    isMulti_expand2 (Q_isMultiB q (restrB p'.2 M) (hadA p.1 p'.1 fun x => fA πA (lab x)))]
  have hM1 := isMatching_restrB (v₀ := p'.2) hM
  have hM2 := isMatching_restrB (v₀ := (⟨p.2, hne⟩ : {y : SB // y ≠ p'.2})) hM1
  have hp1 : (p.1, (⟨p.2, hne⟩ : {y : SB // y ≠ p'.2})) ∈ restrB p'.2 M := mem_restrB.mpr hp
  have c1 := card_restrB_slots p'.2
  have c2 := card_restrB_slots (⟨p.2, hne⟩ : {y : SB // y ≠ p'.2})
  have dM1 : domA (restrB p'.2 M) = (domA M).erase p'.1 := domA_restrB_of_mem hM hp'
  have dM2 : domA (restrB ⟨p.2, hne⟩ (restrB p'.2 M))
      = ((domA M).erase p'.1).erase (p'.1.succAbove z) := by
    have h := domA_restrB_of_mem hM1 hp1
    rw [dM1] at h
    refine h.trans ?_
    change ((domA M).erase p'.1).erase p.1 = _
    rw [hz]
  rw [Q_delB_one hθA hθB hρ hq hπB hM1 ⟨p.2, hne⟩,
    Function.update_eq_self (⟨p.2, hne⟩ : {y : SB // y ≠ p'.2}) (fun _ => gB πB)]
  have h1 := Q_hadA_centred (SB := {y : SB // y ≠ p'.2}) hθA hθB hρ hq hπA hM1
    (hP.mono (N' := n + 2 + Fintype.card {y : SB // y ≠ p'.2}) (by omega)) lab p'.1 z
  have h2 := Q_hadA_centred (SB := {y : {y : SB // y ≠ p'.2} // y ≠ ⟨p.2, hne⟩}) hθA hθB hρ hq
    hπA hM2
    (hP.mono (N' := n + 2 + Fintype.card {y : {y : SB // y ≠ p'.2} // y ≠ ⟨p.2, hne⟩})
      (by omega)) lab p'.1 z
  have hc2 : Fintype.card {y : {y : SB // y ≠ p'.2} // y ≠ ⟨p.2, hne⟩} = Fintype.card SB - 2 := by
    omega
  rw [← hz] at h1 h2
  rw [dM1, pull_erase_self] at h1
  rw [dM2, pull_erase_succAbove, pull_erase_self, hc2] at h2
  rw [h1, h2, c1]

end Merge

end Rhone.Probability.BooleanLatticeInverse
