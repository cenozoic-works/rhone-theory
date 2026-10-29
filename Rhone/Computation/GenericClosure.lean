/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Computation.CheckerClosureSpec
public import Mathlib.Logic.Equiv.Fin.Basic
/-! # General-allele finite-closure checker -/

@[expose] public section
namespace Rhone.Computation.GenericClosure
open LinearAlgebra.Recursion CheckerSpec

def counts : (d : Nat) → Nat → List (Fin d → Nat)
  | 0, _ => [fun i => Fin.elim0 i]
  | d + 1, N => (List.range (N + 1)).flatMap fun a =>
      (counts d (N - a)).map (Fin.cons a)

lemma mem_counts_iff (d N : Nat) (f : Fin d → Nat) :
    f ∈ counts d N ↔ (∑ i, f i) ≤ N := by
  induction d generalizing N with
  | zero =>
    have hf : f = (fun i => Fin.elim0 i) := by funext i; exact Fin.elim0 i
    simp [counts, hf]
  | succ d ih =>
    simp only [counts, List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨a, ha, tail, ht, rfl⟩
      have haN : a ≤ N := by simpa using ha
      have htN := (ih (N - a) tail).mp ht
      simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
      omega
    · intro hf
      rw [Fin.sum_univ_succ] at hf
      refine ⟨f 0, ?_, (fun j => f j.succ), (ih _ _).mpr ?_, ?_⟩
      · simp only [List.mem_range]
        omega
      · omega
      · funext i
        exact Fin.cases rfl (fun j => rfl) i

def matrix {KA KB : Nat} (c : Fin (KA * KB) → Nat) (i : Fin KA) (j : Fin KB) : Nat :=
  c (finProdFinEquiv (i, j))

lemma matrix_sum {KA KB : Nat} (c : Fin (KA * KB) → Nat) :
    (∑ i, ∑ j, matrix c i j) = ∑ k, c k := by
  change (∑ i, ∑ j, (fun p : Fin KA × Fin KB => c (finProdFinEquiv p)) (i, j)) = ∑ k, c k
  rw [← Fintype.sum_prod_type']
  exact Equiv.sum_comp finProdFinEquiv c

def flatten {KA KB : Nat} (c : Fin KA → Fin KB → Nat) (k : Fin (KA * KB)) : Nat :=
  c (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2

lemma matrix_flatten {KA KB : Nat} (c : Fin KA → Fin KB → Nat) : matrix (flatten c) = c := by
  funext i j
  simp [matrix, flatten]

lemma flatten_sum {KA KB : Nat} (c : Fin KA → Fin KB → Nat) :
    (∑ k, flatten c k) = ∑ i, ∑ j, c i j := by
  rw [← matrix_sum, matrix_flatten]

def configs (KA KB N : Nat) : List (Rhone.LinearAlgebra.Recursion.Config KA KB) :=
  if N = 0 then [0] else
  (counts (KA * KB) N).flatMap fun c =>
    let budget := N - ∑ k, c k
    (counts KA budget).flatMap fun a =>
      (counts KB budget).map fun b => ⟨a, b, matrix c⟩

lemma mem_configs_iff {KA KB N : Nat} (ξ : Rhone.LinearAlgebra.Recursion.Config KA KB) :
    ξ ∈ configs KA KB N ↔ InClosure N ξ := by
  by_cases hN : N = 0
  · subst N
    simp only [configs, ↓reduceIte, List.mem_singleton]
    constructor
    · intro hzero
      rw [hzero]
      simp [InClosure, Config.nA, Config.nB, Config.sumA, Config.sumB, Config.t]
    · intro h
      have hn : ξ.n = 0 := by
        have ha := h.1
        have hb := h.2
        dsimp [Config.nA, Config.nB] at ha hb
        dsimp [Config.n]
        omega
      exact ξ.eq_zero_of_n_eq_zero hn
  · simp only [configs, ite_eq_right hN, List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨c, hc, a, ha, b, hb, rfl⟩
      have hcN := (mem_counts_iff _ _ _).mp hc
      have haN := (mem_counts_iff _ _ _).mp ha
      have hbN := (mem_counts_iff _ _ _).mp hb
      have ht := matrix_sum c
      change (∑ i, a i) + (∑ i, ∑ j, matrix c i j) ≤ N ∧
        (∑ j, b j) + (∑ i, ∑ j, matrix c i j) ≤ N
      rw [ht]
      constructor <;> omega
    · intro h
      refine ⟨flatten ξ.c, (mem_counts_iff _ _ _).mpr ?_, ξ.a,
        (mem_counts_iff _ _ _).mpr ?_, ξ.b, (mem_counts_iff _ _ _).mpr ?_, ?_⟩
      · rw [flatten_sum]
        exact ξ.t_le_nA.trans h.1
      · rw [flatten_sum]
        have ha := h.1
        change (∑ i, ξ.a i) + (∑ i, ∑ j, ξ.c i j) ≤ N at ha
        omega
      · rw [flatten_sum]
        have hb := h.2
        change (∑ j, ξ.b j) + (∑ i, ∑ j, ξ.c i j) ≤ N at hb
        omega
      · rw [matrix_flatten]

def boundary {KA KB : Nat} (piA : Fin KA → Rat) (piB : Fin KB → Rat)
    (ξ : Rhone.LinearAlgebra.Recursion.Config KA KB) : Rat :=
  if ξ.n = 0 then 1 else
    (∑ i, (ξ.a i : Rat) * piA i) + (∑ j, (ξ.b j : Rat) * piB j) +
      ∑ i, ∑ j, (ξ.c i j : Rat) * piA i * piB j

lemma boundary_solution {KA KB : Nat} (thetaA thetaB rho : Rat)
    (piA : Fin KA → Rat) (piB : Fin KB → Rat)
    (f : Rhone.LinearAlgebra.Recursion.Config KA KB → Rat)
    (hf : IsSolution thetaA thetaB rho piA piB f)
    (ξ : Rhone.LinearAlgebra.Recursion.Config KA KB) (hn : ξ.n ≤ 1) :
    boundary piA piB ξ = f ξ := by
  rcases Nat.eq_zero_or_pos ξ.n with hz | hz
  · rw [ξ.eq_zero_of_n_eq_zero hz]
    simpa [boundary] using hf.empty.symm
  · have hone : ξ.n = 1 := by omega
    rcases ξ.exists_e_of_n_eq_one hone with ⟨i, rfl⟩ | ⟨j, rfl⟩ | ⟨i, j, rfl⟩
    · rw [hf.bdryA]
      simp only [boundary, Config.n_eA, Nat.one_ne_zero, ↓reduceIte]
      simp [Config.eA, incf, Function.update]
    · rw [hf.bdryB]
      simp only [boundary, Config.n_eB, Nat.one_ne_zero, ↓reduceIte]
      simp [Config.eB, incf, Function.update]
    · rw [hf.bdryC]
      simp only [boundary, Config.n_eC, Nat.one_ne_zero, ↓reduceIte]
      simp [Config.eC, Config.incC, incf, Function.update_apply, ite_apply]

instance {KA KB N : Nat} (ξ : Rhone.LinearAlgebra.Recursion.Config KA KB) :
    Decidable (InClosure N ξ) := inferInstanceAs (Decidable (ξ.nA ≤ N ∧ ξ.nB ≤ N))

def check {KA KB : Nat} (thetaA thetaB rho : Rat)
    (piA : Fin KA → Rat) (piB : Fin KB → Rat) (N : Nat)
    (f : Rhone.LinearAlgebra.Recursion.Config KA KB → Rat) : Bool :=
  decide (0 < thetaA ∧ 0 < thetaB ∧ 0 ≤ rho) &&
    (configs KA KB N).all (fun ξ =>
      if ξ.n ≤ 1 then decide (f ξ = boundary piA piB ξ)
      else decide (diag thetaA thetaB rho ξ * f ξ = rhs thetaA thetaB rho piA piB f ξ))

lemma check_true_iff {KA KB : Nat} (thetaA thetaB rho : Rat)
    (piA : Fin KA → Rat) (piB : Fin KB → Rat) (N : Nat)
    (f : Rhone.LinearAlgebra.Recursion.Config KA KB → Rat) :
    check thetaA thetaB rho piA piB N f = true ↔
      (0 < thetaA ∧ 0 < thetaB ∧ 0 ≤ rho) ∧
      ∀ ξ : Rhone.LinearAlgebra.Recursion.Config KA KB, InClosure N ξ →
        (ξ.n ≤ 1 → f ξ = boundary piA piB ξ) ∧
        (2 ≤ ξ.n → diag thetaA thetaB rho ξ * f ξ = rhs thetaA thetaB rho piA piB f ξ) := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  constructor
  · rintro ⟨hrates, hall⟩
    refine ⟨hrates, ?_⟩
    intro ξ hξ
    have hx := hall ξ ((mem_configs_iff ξ).mpr hξ)
    constructor
    · intro hn
      simpa only [ite_eq_left hn, decide_eq_true_eq] using hx
    · intro hn
      have hnot : ¬ ξ.n ≤ 1 := by omega
      simpa only [ite_eq_right hnot, decide_eq_true_eq] using hx
  · rintro ⟨hrates, hall⟩
    refine ⟨hrates, ?_⟩
    intro ξ hξ
    have hclosure := (mem_configs_iff ξ).mp hξ
    by_cases hn : ξ.n ≤ 1
    · simp only [ite_eq_left hn, decide_eq_true_eq]
      exact (hall ξ hclosure).1 hn
    · simp only [ite_eq_right hn, decide_eq_true_eq]
      exact (hall ξ hclosure).2 (by omega)

lemma check_sound {KA KB N : Nat} {thetaA thetaB rho : Rat}
    {piA : Fin KA → Rat} {piB : Fin KB → Rat}
    {f : Rhone.LinearAlgebra.Recursion.Config KA KB → Rat}
    (h : check thetaA thetaB rho piA piB N f = true) :
    ∃ (hA : 0 < thetaA) (hB : 0 < thetaB) (hR : 0 ≤ rho),
      ∀ ξ : Rhone.LinearAlgebra.Recursion.Config KA KB, InClosure N ξ →
        f ξ = q (πA := piA) (πB := piB) hA hB hR ξ := by
  obtain ⟨⟨hA, hB, hR⟩, hspec⟩ := (check_true_iff _ _ _ _ _ _ _).mp h
  refine ⟨hA, hB, hR, ?_⟩
  apply closure_eq_q hA hB hR
  · intro ξ hξ hn
    rw [(hspec ξ hξ).1 hn]
    exact boundary_solution _ _ _ _ _ _ (q_isSolution hA hB hR) ξ hn
  · intro ξ hξ hn
    exact (hspec ξ hξ).2 hn

lemma check_complete {KA KB N : Nat} (thetaA thetaB rho : Rat)
    (piA : Fin KA → Rat) (piB : Fin KB → Rat)
    (hA : 0 < thetaA) (hB : 0 < thetaB) (hR : 0 ≤ rho)
    (f : Rhone.LinearAlgebra.Recursion.Config KA KB → Rat)
    (hf : IsSolution thetaA thetaB rho piA piB f) :
    check thetaA thetaB rho piA piB N f = true := by
  apply (check_true_iff _ _ _ _ _ _ _).mpr
  refine ⟨⟨hA, hB, hR⟩, ?_⟩
  intro ξ _
  exact ⟨fun hn => (boundary_solution _ _ _ _ _ _ hf ξ hn).symm,
    fun hn => hf.recursion ξ hn⟩
end Rhone.Computation.GenericClosure
