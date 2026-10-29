/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.BooleanLatticeInverse.Centred
public import Rhone.Probability.BooleanLatticeInverse.SlotDelete
public import Rhone.Probability.BooleanLatticeInverse.AsmState

/-! # Assembly of the explicit biallelic-`B` sampling probability from hierarchy values -/

@[expose] public section

namespace Rhone.Probability.BooleanLatticeInverse

open Finset LinearAlgebra.Recursion LinearAlgebra.Multilinear Multilinear SlotDeletion

variable {KA : ℕ} {F : Type*} [Field F] {n m : ℕ}

section PullMB

variable {SA : Type*} [Fintype SA] [DecidableEq SA]

def pullMB (y : Fin (m + 1)) (M : Finset (SA × Fin (m + 1))) : Finset (SA × Fin m) :=
  univ.filter fun p => (p.1, y.succAbove p.2) ∈ M

@[simp] theorem mem_pullMB {y : Fin (m + 1)} {M : Finset (SA × Fin (m + 1))}
    {p : SA × Fin m} : p ∈ pullMB y M ↔ (p.1, y.succAbove p.2) ∈ M := by simp [pullMB]

theorem isMatching_pullMB {y : Fin (m + 1)} {M : Finset (SA × Fin (m + 1))}
    (hM : IsMatching M) : IsMatching (pullMB y M) := by
  refine ⟨fun p hp p' hp' h => ?_, fun p hp p' hp' h => ?_⟩
  · rw [mem_pullMB] at hp hp'
    have he := hM.fst _ hp _ hp' h
    simp only [Prod.mk.injEq] at he
    exact Prod.ext h (Fin.succAbove_right_injective he.2)
  · rw [mem_pullMB] at hp hp'
    have he := hM.snd _ hp _ hp' (by simpa using congrArg y.succAbove h)
    simp only [Prod.mk.injEq] at he
    exact Prod.ext he.1 h

end PullMB

theorem pullM_zero_shA (M : Finset (Fin n × Fin m)) : pullM 0 (shA M) = M := by
  ext ⟨a, b⟩
  simp [mem_shA]

theorem pullMB_zero_shB (M : Finset (Fin n × Fin m)) : pullMB 0 (shB M) = M := by
  ext ⟨a, b⟩
  simp [mem_shB]

theorem pullM_zero_linkAB (M : Finset (Fin n × Fin m)) : pullM 0 (linkAB M) = shB M := by
  ext ⟨a, b⟩
  simp [mem_shB, mem_linkAB, Prod.ext_iff, Fin.succ_ne_zero]

theorem pullMB_zero_linkAB (M : Finset (Fin n × Fin m)) : pullMB 0 (linkAB M) = shA M := by
  ext ⟨a, b⟩
  simp [mem_shA, mem_linkAB, Prod.ext_iff, Fin.succ_ne_zero]

theorem pullM_succ_shA (x : Fin (n + 1)) (M : Finset (Fin (n + 1) × Fin m)) :
    pullM x.succ (shA M) = shA (pullM x M) := by
  ext ⟨a, b⟩
  refine Fin.cases ?_ (fun c => ?_) a <;>
    simp [mem_shA, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm]

theorem pullM_shB (x : Fin (n + 1)) (M : Finset (Fin (n + 1) × Fin m)) :
    pullM x (shB M) = shB (pullM x M) := by
  ext ⟨a, b⟩
  refine Fin.cases ?_ (fun d => ?_) b <;>
    simp [mem_shB, (Fin.succ_ne_zero _).symm]

theorem pullM_succ_linkAB (x : Fin (n + 1)) (M : Finset (Fin (n + 1) × Fin m)) :
    pullM x.succ (linkAB M) = linkAB (pullM x M) := by
  ext ⟨a, b⟩
  refine Fin.cases ?_ (fun c => ?_) a <;>
    refine Fin.cases ?_ (fun d => ?_) b <;>
    simp [mem_linkAB, Prod.ext_iff, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm]

theorem pullMB_shA (y : Fin (m + 1)) (M : Finset (Fin n × Fin (m + 1))) :
    pullMB y (shA M) = shA (pullMB y M) := by
  ext ⟨a, b⟩
  refine Fin.cases ?_ (fun c => ?_) a <;>
    simp [mem_shA, (Fin.succ_ne_zero _).symm]

theorem pullMB_succ_shB (y : Fin (m + 1)) (M : Finset (Fin n × Fin (m + 1))) :
    pullMB y.succ (shB M) = shB (pullMB y M) := by
  ext ⟨a, b⟩
  refine Fin.cases ?_ (fun d => ?_) b <;>
    simp [mem_shB, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm]

theorem pullMB_succ_linkAB (y : Fin (m + 1)) (M : Finset (Fin n × Fin (m + 1))) :
    pullMB y.succ (linkAB M) = linkAB (pullMB y M) := by
  ext ⟨a, b⟩
  refine Fin.cases ?_ (fun c => ?_) a <;>
    refine Fin.cases ?_ (fun d => ?_) b <;>
    simp [mem_linkAB, Prod.ext_iff, Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm]

theorem cons_update_succ {F : Type*} {K : ℕ} [DecidableEq (Fin n)] (v : Fin K → F)
    (s : Fin n → Fin K → F) (u : Fin n) (t : Fin K → F) :
    (Fin.cons v (Function.update s u t) : Fin (n + 1) → Fin K → F)
      = Function.update (Fin.cons v s) u.succ t := by
  funext j
  refine Fin.cases ?_ (fun i => ?_) j
  · simp [Function.update_of_ne (Fin.succ_ne_zero u).symm]
  · by_cases h : i = u <;> simp [h]

theorem isMulti_cons {K : ℕ} {G : (Fin (n + 1) → Fin K → F) → F} (hG : IsMulti G)
    (v : Fin K → F) : IsMulti (fun s : Fin n → Fin K → F => G (Fin.cons v s)) := by
  constructor
  · intro _ s u x y
    rw [cons_update_succ, cons_update_succ, cons_update_succ]
    exact hG.add _ _ _ _
  · intro _ s u c x
    rw [cons_update_succ, cons_update_succ]
    exact hG.smul _ _ _ _

theorem Qc_isMultiA (q : Config KA 2 → F) (r : List (LinearAlgebra.BooleanLatticeInverse.Slot KA))
    (M : Finset (Fin n × Fin m))
    (w : Fin m → Fin 2 → F) : IsMulti (fun s => Qc q r n m M s w) := by
  induction r generalizing n m M w with
  | nil => exact Q_isMultiA q M w
  | cons x r ih =>
    cases x with
    | freeA p => exact isMulti_cons (ih (shA M) w) _
    | freeB b => exact ih (shB M) _
    | pair p b => exact isMulti_cons (ih (linkAB M) _) _

theorem Qc_isMultiB (q : Config KA 2 → F) (r : List (LinearAlgebra.BooleanLatticeInverse.Slot KA))
    (M : Finset (Fin n × Fin m))
    (s : Fin n → Fin KA → F) : IsMulti (fun w => Qc q r n m M s w) := by
  induction r generalizing n m M s with
  | nil => exact Q_isMultiB q M s
  | cons x r ih =>
    cases x with
    | freeA p => exact ih (shA M) _
    | freeB b => exact isMulti_cons (ih (shB M) s) _
    | pair p b => exact isMulti_cons (ih (linkAB M) _) _

theorem cons_succAbove_succ {β : Type*} {n : ℕ} (e : β) (s : Fin (n + 1) → β)
    (x : Fin (n + 1)) :
    (fun y => (Fin.cons e s : Fin (n + 2) → β) (x.succ.succAbove y))
      = Fin.cons e (fun y => s (x.succAbove y)) :=
  Fin.cons_comp_succ_succAbove e s x

theorem Qc_single_A (q : Config KA 2 → F) (πA : Fin KA → F)
    (r : List (LinearAlgebra.BooleanLatticeInverse.Slot KA))
    (M : Finset (Fin (n + 1) × Fin m)) (s : Fin n → Fin KA → F) (w : Fin m → Fin 2 → F)
    (p : Fin KA) :
    Qc q r (n + 1) m M (Fin.cons (Pi.single p 1) s : Fin (n + 1) → Fin KA → F) w
      = πA p * Qc q r (n + 1) m M (Fin.cons (1 : Fin KA → F) s : Fin (n + 1) → Fin KA → F) w
        + Qc q r (n + 1) m M (Fin.cons (fA πA p) s : Fin (n + 1) → Fin KA → F) w := by
  have hM := Qc_isMultiA q r M w
  have h1 := hM.add (Fin.cons (1 : Fin KA → F) s : Fin (n + 1) → Fin KA → F) 0
    (πA p • (1 : Fin KA → F)) (fA πA p)
  have h2 := hM.smul (Fin.cons (1 : Fin KA → F) s : Fin (n + 1) → Fin KA → F) 0 (πA p)
    (1 : Fin KA → F)
  simp only [Fin.update_cons_zero] at h1 h2
  rw [single_eq_fA πA p, h1, h2]

theorem Qc_single_B (q : Config KA 2 → F) {πB : Fin 2 → F} (hπB : πB 0 + πB 1 = 1)
    (r : List (LinearAlgebra.BooleanLatticeInverse.Slot KA)) (M : Finset (Fin n × Fin (m + 1)))
        (s : Fin n → Fin KA → F)
    (w : Fin m → Fin 2 → F) (b : Fin 2) :
    Qc q r n (m + 1) M s (Fin.cons (Pi.single b 1) w : Fin (m + 1) → Fin 2 → F)
      = πB b * Qc q r n (m + 1) M s (Fin.cons (1 : Fin 2 → F) w : Fin (m + 1) → Fin 2 → F)
        + LinearAlgebra.BooleanLatticeInverse.sgnB b * Qc q r n (m + 1) M s
          (Fin.cons (gB πB) w : Fin (m + 1) → Fin 2 → F) := by
  have hM := Qc_isMultiB q r M s
  have h1 := hM.add (Fin.cons (1 : Fin 2 → F) w : Fin (m + 1) → Fin 2 → F) 0
    (πB b • (1 : Fin 2 → F)) (LinearAlgebra.BooleanLatticeInverse.sgnB (F := F) b • gB πB)
  have h2 := hM.smul (Fin.cons (1 : Fin 2 → F) w : Fin (m + 1) → Fin 2 → F) 0 (πB b)
    (1 : Fin 2 → F)
  have h3 := hM.smul (Fin.cons (1 : Fin 2 → F) w : Fin (m + 1) → Fin 2 → F) 0
      (LinearAlgebra.BooleanLatticeInverse.sgnB (F := F) b)
    (gB πB)
  simp only [Fin.update_cons_zero] at h1 h2 h3
  rw [single_eq_gB hπB b, h1, h2, h3]

theorem cons_const {β : Type*} {m : ℕ} (g : β) :
    (Fin.cons g (fun _ : Fin m => g) : Fin (m + 1) → β) = fun _ => g := by
  funext y
  refine Fin.cases ?_ (fun i => ?_) y <;> simp

theorem cons_succAbove_zero {β : Type*} {n : ℕ} (e : β) (s : Fin n → β) :
    (fun y => (Fin.cons e s : Fin (n + 1) → β) ((0 : Fin (n + 1)).succAbove y)) = s := by
  funext y
  simp

theorem cons_fA {F : Type*} [Field F] {n : ℕ} (πA : Fin KA → F) (p : Fin KA)
    (lab : Fin n → Fin KA) :
    (Fin.cons (fA πA p) (fun x => fA πA (lab x)) : Fin (n + 1) → Fin KA → F)
      = fun x => fA πA ((Fin.cons p lab : Fin (n + 1) → Fin KA) x) := by
  funext x
  refine Fin.cases ?_ (fun i => ?_) x <;> simp

section Solution

variable [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {πA : Fin KA → F} {πB : Fin 2 → F}
variable (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
variable {q : Config KA 2 → F} (hq : IsSolution θA θB ρ πA πB q)
variable (hπA : ∑ i, πA i = 1) (hπB : πB 0 + πB 1 = 1)
include hθA hθB hρ hq

include hπB in
theorem Q_delB_fin {SA : Type*} [Fintype SA] [DecidableEq SA] {M : Finset (SA × Fin (m + 1))}
    (hM : IsMatching M) (y : Fin (m + 1)) (s : SA → Fin KA → F) (w : Fin (m + 1) → Fin 2 → F)
    (hw : w y = 1) :
    Q q M s w = Q q (pullMB y M) s (fun v => w (y.succAbove v)) := by
  have hπB' : ∑ j, πB j = 1 := by rw [Fin.sum_univ_two]; exact hπB
  rw [Q_delB hθA hθB hρ hq hπB' hM y s w hw]
  have hE : restrB y M
      = mapM (Equiv.refl SA) (finSuccAboveEquiv y) (pullMB y M) := by
    ext ⟨a, b⟩
    rw [mem_restrB, mem_mapM, mem_pullMB]
    have : y.succAbove ((finSuccAboveEquiv y).symm b) = b.1 :=
      congrArg Subtype.val ((finSuccAboveEquiv y).apply_symm_apply b)
    simp only [Equiv.refl_symm, Equiv.refl_apply, this]
  rw [hE, Q_mapM]
  rfl

include hπA in
theorem Qc_delA (r : List (LinearAlgebra.BooleanLatticeInverse.Slot KA)) {n m : ℕ}
    {M : Finset (Fin (n + 1) × Fin m)}
    (hM : IsMatching M) (x : Fin (n + 1)) (s : Fin (n + 1) → Fin KA → F) (hs : s x = 1)
    (w : Fin m → Fin 2 → F) :
    Qc q r (n + 1) m M s w = Qc q r n m (pullM x M) (fun y => s (x.succAbove y)) w := by
  induction r generalizing n m M x s w with
  | nil => exact Q_delA hθA hθB hρ hq hπA hM x s hs w
  | cons h r ih =>
    cases h with
    | freeA p =>
      simp only [Qc]
      rw [ih (isMatching_shA hM) x.succ _ (by simpa using hs) w, pullM_succ_shA,
        cons_succAbove_succ]
    | freeB b =>
      simp only [Qc]
      rw [ih (isMatching_shB hM) x s hs, pullM_shB]
    | pair p b =>
      simp only [Qc]
      rw [ih (isMatching_linkAB hM) x.succ _ (by simpa using hs), pullM_succ_linkAB,
        cons_succAbove_succ]

include hπB in
theorem Qc_delB (r : List (LinearAlgebra.BooleanLatticeInverse.Slot KA)) {n m : ℕ}
    {M : Finset (Fin n × Fin (m + 1))}
    (hM : IsMatching M) (y : Fin (m + 1)) (s : Fin n → Fin KA → F)
    (w : Fin (m + 1) → Fin 2 → F) (hw : w y = 1) :
    Qc q r n (m + 1) M s w = Qc q r n m (pullMB y M) s (fun v => w (y.succAbove v)) := by
  induction r generalizing n m M y s w with
  | nil => exact Q_delB_fin hθA hθB hρ hq hπB hM y s w hw
  | cons h r ih =>
    cases h with
    | freeA p =>
      simp only [Qc]
      rw [ih (isMatching_shA hM) y _ w hw, pullMB_shA]
    | freeB b =>
      simp only [Qc]
      rw [ih (isMatching_shB hM) y.succ s _ (by simpa using hw), pullMB_succ_shB,
        cons_succAbove_succ]
    | pair p b =>
      simp only [Qc]
      rw [ih (isMatching_linkAB hM) y.succ _ _ (by simpa using hw), pullMB_succ_linkAB,
        cons_succAbove_succ]

include hπA hπB in
theorem Qc_centred_eq_asm
    (hPhi : ∀ (n m : ℕ) (M : Finset (Fin n × Fin m)) (lab : Fin n → Fin KA), IsMatching M →
      Q q M (fun x => fA πA (lab x)) (fun _ => gB πB) = LinearAlgebra.BooleanLatticeInverse.PhiX θA
          θB ρ πA πB n lab m (domA M))
    (r : List (LinearAlgebra.BooleanLatticeInverse.Slot KA)) {n m : ℕ} (M : Finset (Fin n × Fin m))
        (hM : IsMatching M)
    (lab : Fin n → Fin KA) :
    Qc q r n m M (fun x => fA πA (lab x)) (fun _ => gB πB)
      = LinearAlgebra.BooleanLatticeInverse.asm θA θB ρ πA πB r n lab m (domA M) := by
  induction r generalizing n m M lab with
  | nil => exact hPhi n m M lab hM
  | cons h r ih =>
    cases h with
    | freeA p =>
      simp only [Qc, LinearAlgebra.BooleanLatticeInverse.asm]
      rw [Qc_single_A q πA r (shA M), ← domA_shA,
        Qc_delA hθA hθB hρ hq hπA r (isMatching_shA hM) 0
          (Fin.cons (1 : Fin KA → F) (fun x => fA πA (lab x)) : Fin (n + 1) → Fin KA → F)
          (by simp) (fun _ => gB πB),
        pullM_zero_shA, cons_succAbove_zero, ih M hM lab, cons_fA,
        ih (shA M) (isMatching_shA hM) (Fin.cons p lab)]
    | freeB b =>
      simp only [Qc, LinearAlgebra.BooleanLatticeInverse.asm]
      rw [Qc_single_B q hπB r (shB M),
        Qc_delB hθA hθB hρ hq hπB r (isMatching_shB hM) 0 (fun x => fA πA (lab x))
          (Fin.cons (1 : Fin 2 → F) (fun _ : Fin m => gB πB) : Fin (m + 1) → Fin 2 → F)
          (by simp),
        pullMB_zero_shB, cons_succAbove_zero, ih M hM lab, cons_const,
        ih (shB M) (isMatching_shB hM) lab, domA_shB]
    | pair p b =>
      simp only [Qc, LinearAlgebra.BooleanLatticeInverse.asm]
      rw [Qc_single_A q πA r (linkAB M), Qc_single_B q hπB r _ _ _ b,
        Qc_single_B q hπB r _ _ _ b,
        Qc_delA hθA hθB hρ hq hπA r (isMatching_linkAB hM) 0
          (Fin.cons (1 : Fin KA → F) (fun x => fA πA (lab x)) : Fin (n + 1) → Fin KA → F)
          (by simp) (Fin.cons (1 : Fin 2 → F) (fun _ : Fin m => gB πB)
            : Fin (m + 1) → Fin 2 → F),
        pullM_zero_linkAB, cons_succAbove_zero,
        Qc_delB hθA hθB hρ hq hπB r (isMatching_shB hM) 0 (fun x => fA πA (lab x))
          (Fin.cons (1 : Fin 2 → F) (fun _ : Fin m => gB πB) : Fin (m + 1) → Fin 2 → F)
          (by simp),
        pullMB_zero_shB, cons_succAbove_zero, ih M hM lab,
        Qc_delA hθA hθB hρ hq hπA r (isMatching_linkAB hM) 0
          (Fin.cons (1 : Fin KA → F) (fun x => fA πA (lab x)) : Fin (n + 1) → Fin KA → F)
          (by simp) (Fin.cons (gB πB) (fun _ : Fin m => gB πB) : Fin (m + 1) → Fin 2 → F),
        pullM_zero_linkAB, cons_succAbove_zero, cons_const,
        ih (shB M) (isMatching_shB hM) lab, domA_shB,
        Qc_delB hθA hθB hρ hq hπB r (isMatching_linkAB hM) 0
          (Fin.cons (fA πA p) (fun x => fA πA (lab x)) : Fin (n + 1) → Fin KA → F)
          (Fin.cons (1 : Fin 2 → F) (fun _ : Fin m => gB πB) : Fin (m + 1) → Fin 2 → F)
          (by simp),
        pullMB_zero_linkAB, cons_succAbove_zero, cons_fA,
        ih (shA M) (isMatching_shA hM) (Fin.cons p lab), domA_shA,
        ih (linkAB M) (isMatching_linkAB hM) (Fin.cons p lab), domA_linkAB]
      ring

include hπA hπB in
theorem q_eq_qExplicitKB2_of
    (hPhi : ∀ (n m : ℕ) (M : Finset (Fin n × Fin m)) (lab : Fin n → Fin KA), IsMatching M →
      Q q M (fun x => fA πA (lab x)) (fun _ => gB πB) = LinearAlgebra.BooleanLatticeInverse.PhiX θA
          θB ρ πA πB n lab m (domA M))
    (ξ : Config KA 2) : q ξ = LinearAlgebra.BooleanLatticeInverse.qExplicitKB2 θA θB ρ πA πB ξ := by
  have hM : IsMatching (∅ : Finset (Fin 0 × Fin 0)) := ⟨by simp, by simp⟩
  have h := Qc_centred_eq_asm hθA hθB hρ hq hπA hπB hPhi
      (LinearAlgebra.BooleanLatticeInverse.slots ξ) ∅ hM Fin.elim0
  have hd : domA (∅ : Finset (Fin 0 × Fin 0)) = ∅ := by
    ext x
    exact x.elim0
  have e1 : (fun x => fA πA (Fin.elim0 x) : Fin 0 → Fin KA → F) = Fin.elim0 :=
    funext fun x => x.elim0
  have e2 : (fun _ : Fin 0 => gB πB) = (Fin.elim0 : Fin 0 → Fin 2 → F) :=
    funext fun x => x.elim0
  rw [hd, e1, e2] at h
  rw [← Qc_slots q ξ]
  exact h

end Solution

end Rhone.Probability.BooleanLatticeInverse
