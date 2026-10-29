/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.InfiniteAlleles.Relabel

/-! # Support reduction: enlarging the allele alphabet changes nothing -/

@[expose] public section

namespace Rhone.Probability.InfiniteAlleles

open Finset LinearAlgebra.Recursion LinearAlgebra.Recursion.Config

variable {KA KB K L : ℕ}

def pushf {ι κ M : Type*} [Fintype ι] [DecidableEq κ] [AddCommMonoid M] (e : ι ↪ κ)
    (g : ι → M) : κ → M := fun y => ∑ x, if e x = y then g x else 0

section Pushf

variable {ι κ M : Type*} [Fintype ι] [DecidableEq κ] [AddCommMonoid M] (e : ι ↪ κ)

@[simp] theorem pushf_apply_emb (g : ι → M) (x₀ : ι) : pushf e g (e x₀) = g x₀ := by
  classical
  simp only [pushf]
  rw [Finset.sum_eq_single x₀ (fun b _ hb => by simp [(e.injective.ne hb)])
    (fun h => absurd (Finset.mem_univ x₀) h)]
  simp

theorem pushf_eq_zero (g : ι → M) {y : κ} (h : ∀ x, e x ≠ y) : pushf e g y = 0 :=
  Finset.sum_eq_zero fun x _ => by simp [h x]

theorem pushf_zero : pushf e (fun _ => (0 : M)) = fun _ => (0 : M) := by
  funext y; simp [pushf]

omit [DecidableEq κ] in
theorem sum_eq_sum_emb [Fintype κ] (F : κ → M) (h : ∀ y, (∀ x, e x ≠ y) → F y = 0) :
    ∑ y, F y = ∑ x, F (e x) := by
  classical
  rw [← Finset.sum_map Finset.univ e F]
  refine (Finset.sum_subset (Finset.subset_univ _) fun y _ hy => h y fun x hx => hy ?_).symm
  exact Finset.mem_map.mpr ⟨x, Finset.mem_univ x, hx⟩

theorem sum_pushf [Fintype κ] (g : ι → M) : ∑ y, pushf e g y = ∑ x, g x := by
  rw [sum_eq_sum_emb e _ fun y hy => pushf_eq_zero e g hy]
  exact Finset.sum_congr rfl fun x _ => pushf_apply_emb e g x

theorem pushf_update [DecidableEq ι] (g : ι → M) (x₀ : ι) (v : M) :
    pushf e (Function.update g x₀ v) = Function.update (pushf e g) (e x₀) v := by
  funext y
  by_cases hy : ∀ x, e x ≠ y
  · rw [pushf_eq_zero e _ hy, Function.update_of_ne (fun hc => hy x₀ hc.symm),
      pushf_eq_zero e g hy]
  · obtain ⟨x, rfl⟩ : ∃ x, e x = y := by
      by_contra hc
      exact hy fun x hx => hc ⟨x, hx⟩
    by_cases hx : x = x₀
    · subst hx; simp
    · rw [pushf_apply_emb, Function.update_of_ne hx, Function.update_of_ne (e.injective.ne hx),
        pushf_apply_emb]

end Pushf

section Nat

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq κ] (e : ι ↪ κ)

theorem pushf_decf (g : ι → ℕ) (x₀ : ι) :
    pushf e (decf g x₀) = decf (pushf e g) (e x₀) := by
  have h1 : decf g x₀ = Function.update g x₀ (g x₀ - 1) := rfl
  have h2 : decf (pushf e g) (e x₀)
      = Function.update (pushf e g) (e x₀) (pushf e g (e x₀) - 1) := rfl
  rw [h1, h2, pushf_apply_emb, pushf_update]

theorem pushf_incf (g : ι → ℕ) (x₀ : ι) :
    pushf e (incf g x₀) = incf (pushf e g) (e x₀) := by
  have h1 : incf g x₀ = Function.update g x₀ (g x₀ + 1) := rfl
  have h2 : incf (pushf e g) (e x₀)
      = Function.update (pushf e g) (e x₀) (pushf e g (e x₀) + 1) := rfl
  rw [h1, h2, pushf_apply_emb, pushf_update]

end Nat

variable (e : Fin KA ↪ Fin K) (f : Fin KB ↪ Fin L)

def push (ξ : Config KA KB) : Config K L where
  a := pushf e ξ.a
  b := pushf f ξ.b
  c := pushf e fun i => pushf f (ξ.c i)

variable (ξ : Config KA KB)

@[simp] theorem push_a (i : Fin KA) : (push e f ξ).a (e i) = ξ.a i := pushf_apply_emb e _ i

@[simp] theorem push_b (j : Fin KB) : (push e f ξ).b (f j) = ξ.b j := pushf_apply_emb f _ j

theorem push_c_row (i : Fin KA) : (push e f ξ).c (e i) = pushf f (ξ.c i) :=
  pushf_apply_emb e _ i

@[simp] theorem push_c (i : Fin KA) (j : Fin KB) : (push e f ξ).c (e i) (f j) = ξ.c i j := by
  rw [show (push e f ξ).c (e i) (f j) = pushf f (ξ.c i) (f j) from
    congrFun (push_c_row e f ξ i) (f j), pushf_apply_emb]

theorem push_a_off {i' : Fin K} (h : ∀ i, e i ≠ i') : (push e f ξ).a i' = 0 :=
  pushf_eq_zero e _ h

theorem push_b_off {j' : Fin L} (h : ∀ j, f j ≠ j') : (push e f ξ).b j' = 0 :=
  pushf_eq_zero f _ h

theorem push_c_off_left {i' : Fin K} (h : ∀ i, e i ≠ i') (j' : Fin L) :
    (push e f ξ).c i' j' = 0 := by
  have hz : (push e f ξ).c i' = (fun _ => 0 : Fin L → ℕ) := pushf_eq_zero e _ h
  rw [hz]

theorem push_c_off_right (i' : Fin K) {j' : Fin L} (h : ∀ j, f j ≠ j') :
    (push e f ξ).c i' j' = 0 := by
  change pushf e (fun i => pushf f (ξ.c i)) i' j' = 0
  simp only [pushf, Finset.sum_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hi : e i = i'
  · simp [hi, pushf_eq_zero f (ξ.c i) h]
  · simp [hi]

@[simp] theorem cRow_push (i : Fin KA) : (push e f ξ).cRow (e i) = ξ.cRow i := by
  change ∑ j', (push e f ξ).c (e i) j' = ∑ j, ξ.c i j
  rw [push_c_row]
  exact sum_pushf f (ξ.c i)

theorem cRow_push_off {i' : Fin K} (h : ∀ i, e i ≠ i') : (push e f ξ).cRow i' = 0 :=
  Finset.sum_eq_zero fun j' _ => push_c_off_left e f ξ h j'

@[simp] theorem cCol_push (j : Fin KB) : (push e f ξ).cCol (f j) = ξ.cCol j := by
  change ∑ i', (push e f ξ).c i' (f j) = ∑ i, ξ.c i j
  rw [sum_eq_sum_emb e _ fun i' hi' => push_c_off_left e f ξ hi' (f j)]
  exact Finset.sum_congr rfl fun i _ => push_c e f ξ i j

theorem cCol_push_off {j' : Fin L} (h : ∀ j, f j ≠ j') : (push e f ξ).cCol j' = 0 :=
  Finset.sum_eq_zero fun i' _ => push_c_off_right e f ξ i' h

@[simp] theorem mA_push (i : Fin KA) : (push e f ξ).mA (e i) = ξ.mA i := by
  simp [Config.mA]

@[simp] theorem mB_push (j : Fin KB) : (push e f ξ).mB (f j) = ξ.mB j := by
  simp [Config.mB]

@[simp] theorem sumA_push : (push e f ξ).sumA = ξ.sumA := sum_pushf e ξ.a

@[simp] theorem sumB_push : (push e f ξ).sumB = ξ.sumB := sum_pushf f ξ.b

@[simp] theorem t_push : (push e f ξ).t = ξ.t := by
  change ∑ i', ∑ j', (push e f ξ).c i' j' = ∑ i, ∑ j, ξ.c i j
  rw [sum_eq_sum_emb e _ fun i' hi' => Finset.sum_eq_zero fun j' _ =>
    push_c_off_left e f ξ hi' j']
  exact Finset.sum_congr rfl fun i _ => cRow_push e f ξ i

@[simp] theorem nA_push : (push e f ξ).nA = ξ.nA := by simp [Config.nA]

@[simp] theorem nB_push : (push e f ξ).nB = ξ.nB := by simp [Config.nB]

@[simp] theorem n_push : (push e f ξ).n = ξ.n := by simp [Config.n]

theorem push_dropA (i : Fin KA) : push e f (ξ.dropA i) = (push e f ξ).dropA (e i) :=
  Config.ext (pushf_decf e ξ.a i) rfl rfl

theorem push_dropB (j : Fin KB) : push e f (ξ.dropB j) = (push e f ξ).dropB (f j) :=
  Config.ext rfl (pushf_decf f ξ.b j) rfl

theorem pushf_decC (m : Fin KA → Fin KB → ℕ) (i : Fin KA) (j : Fin KB) :
    (pushf e fun i' => pushf f (decC m i j i'))
      = decC (pushf e fun i' => pushf f (m i')) (e i) (f j) := by
  have h1 : (fun i' => pushf f (decC m i j i'))
      = Function.update (fun i' => pushf f (m i')) i (decf (pushf f (m i)) (f j)) := by
    have hc : (fun i' => pushf f (decC m i j i'))
        = pushf f ∘ Function.update m i (decf (m i) j) := rfl
    rw [hc, Function.comp_update, pushf_decf]
    rfl
  have h2 : decC (pushf e fun i' => pushf f (m i')) (e i) (f j)
      = Function.update (pushf e fun i' => pushf f (m i')) (e i)
        (decf ((pushf e fun i' => pushf f (m i')) (e i)) (f j)) := rfl
  rw [h1, h2, pushf_apply_emb, pushf_update]

theorem pushf_incC (m : Fin KA → Fin KB → ℕ) (i : Fin KA) (j : Fin KB) :
    (pushf e fun i' => pushf f (incC m i j i'))
      = incC (pushf e fun i' => pushf f (m i')) (e i) (f j) := by
  have h1 : (fun i' => pushf f (incC m i j i'))
      = Function.update (fun i' => pushf f (m i')) i (incf (pushf f (m i)) (f j)) := by
    have hc : (fun i' => pushf f (incC m i j i'))
        = pushf f ∘ Function.update m i (incf (m i) j) := rfl
    rw [hc, Function.comp_update, pushf_incf]
    rfl
  have h2 : incC (pushf e fun i' => pushf f (m i')) (e i) (f j)
      = Function.update (pushf e fun i' => pushf f (m i')) (e i)
        (incf ((pushf e fun i' => pushf f (m i')) (e i)) (f j)) := rfl
  rw [h1, h2, pushf_apply_emb, pushf_update]

theorem push_dropC (i : Fin KA) (j : Fin KB) :
    push e f (ξ.dropC i j) = (push e f ξ).dropC (e i) (f j) :=
  Config.ext rfl rfl (pushf_decC e f ξ.c i j)

theorem push_mergeAB (i : Fin KA) (j : Fin KB) :
    push e f (ξ.mergeAB i j) = (push e f ξ).mergeAB (e i) (f j) :=
  Config.ext (pushf_decf e ξ.a i) (pushf_decf f ξ.b j) (pushf_incC e f ξ.c i j)

theorem push_killA (i : Fin KA) (j : Fin KB) :
    push e f (ξ.killA i j) = (push e f ξ).killA (e i) (f j) :=
  Config.ext rfl (pushf_incf f ξ.b j) (pushf_decC e f ξ.c i j)

theorem push_killB (i : Fin KA) (j : Fin KB) :
    push e f (ξ.killB i j) = (push e f ξ).killB (e i) (f j) :=
  Config.ext (pushf_incf e ξ.a i) rfl (pushf_decC e f ξ.c i j)

theorem push_split (i : Fin KA) (j : Fin KB) :
    push e f (ξ.split i j) = (push e f ξ).split (e i) (f j) :=
  Config.ext (pushf_incf e ξ.a i) (pushf_incf f ξ.b j) (pushf_decC e f ξ.c i j)

@[simp] theorem coalA_push (i : Fin KA) : (push e f ξ).coalA (e i) = ξ.coalA i := by
  simp [Config.coalA]

@[simp] theorem coalB_push (j : Fin KB) : (push e f ξ).coalB (f j) = ξ.coalB j := by
  simp [Config.coalB]

@[simp] theorem coalC_push (i : Fin KA) (j : Fin KB) :
    (push e f ξ).coalC (e i) (f j) = ξ.coalC i j := by
  simp [Config.coalC]

@[simp] theorem coalAB_push (i : Fin KA) (j : Fin KB) :
    (push e f ξ).coalAB (e i) (f j) = ξ.coalAB i j := by
  simp [Config.coalAB]

@[simp] theorem dropIndA_push (i : Fin KA) : dropIndA (push e f ξ) (e i) = dropIndA ξ i := by
  simp [dropIndA]

@[simp] theorem dropIndB_push (j : Fin KB) : dropIndB (push e f ξ) (f j) = dropIndB ξ j := by
  simp [dropIndB]

@[simp] theorem killIndA_push (i : Fin KA) (j : Fin KB) :
    killIndA (push e f ξ) (e i) (f j) = killIndA ξ i j := by
  simp [killIndA]

@[simp] theorem killIndB_push (i : Fin KA) (j : Fin KB) :
    killIndB (push e f ξ) (e i) (f j) = killIndB ξ i j := by
  simp [killIndB]

theorem coalA_push_off {i' : Fin K} (h : ∀ i, e i ≠ i') : (push e f ξ).coalA i' = 0 :=
  Config.coalA_eq_zero_of _ (push_a_off e f ξ h)

theorem coalB_push_off {j' : Fin L} (h : ∀ j, f j ≠ j') : (push e f ξ).coalB j' = 0 :=
  Config.coalB_eq_zero_of _ (push_b_off e f ξ h)

theorem dropIndA_push_off {i' : Fin K} (h : ∀ i, e i ≠ i') : dropIndA (push e f ξ) i' = 0 :=
  dropIndA_eq_zero_of _ (push_a_off e f ξ h)

theorem dropIndB_push_off {j' : Fin L} (h : ∀ j, f j ≠ j') : dropIndB (push e f ξ) j' = 0 :=
  dropIndB_eq_zero_of _ (push_b_off e f ξ h)

theorem pushf_zero_c : (pushf e fun _ => pushf f (fun _ => (0 : ℕ))) = fun _ _ => 0 := by
  rw [pushf_zero f]
  exact pushf_zero e

@[simp] theorem push_zero : push e f (0 : Config KA KB) = 0 :=
  Config.ext (pushf_zero e) (pushf_zero f) (pushf_zero_c e f)

@[simp] theorem push_eA (i : Fin KA) :
    push e f (Config.eA i : Config KA KB) = Config.eA (e i) := by
  refine Config.ext ?_ (pushf_zero f) (pushf_zero_c e f)
  change pushf e (incf (fun _ => (0 : ℕ)) i) = incf (fun _ => (0 : ℕ)) (e i)
  rw [pushf_incf, pushf_zero]

@[simp] theorem push_eB (j : Fin KB) :
    push e f (Config.eB j : Config KA KB) = Config.eB (f j) := by
  refine Config.ext (pushf_zero e) ?_ (pushf_zero_c e f)
  change pushf f (incf (fun _ => (0 : ℕ)) j) = incf (fun _ => (0 : ℕ)) (f j)
  rw [pushf_incf, pushf_zero]

@[simp] theorem push_eC (i : Fin KA) (j : Fin KB) :
    push e f (Config.eC i j : Config KA KB) = Config.eC (e i) (f j) := by
  refine Config.ext (pushf_zero e) (pushf_zero f) ?_
  change pushf e (fun i' => pushf f (incC (fun _ _ => (0 : ℕ)) i j i'))
    = incC (fun _ _ => (0 : ℕ)) (e i) (f j)
  rw [pushf_incC, pushf_zero_c e f]

end Rhone.Probability.InfiniteAlleles
