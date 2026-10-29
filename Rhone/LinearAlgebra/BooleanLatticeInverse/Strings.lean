/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.LinearAlgebra.BooleanLatticeInverse.Lattice
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Data.Nat.Cast.Field
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Push

/-! # Primitive vectors, their strings, and the primitive decomposition -/

@[expose] public section

namespace Rhone.LinearAlgebra.BooleanLatticeInverse

open Finset

variable {F : Type*} [Field F] {i : ℕ}

def IsPrim (k : ℕ) (h : Finset (Fin i) → F) : Prop := IsLevel k h ∧ U h = 0

theorem isPrim_zero (k : ℕ) : IsPrim k (0 : Finset (Fin i) → F) := ⟨isLevel_zero k, map_zero _⟩

theorem IsPrim.add {k : ℕ} {f g : Finset (Fin i) → F} (hf : IsPrim k f) (hg : IsPrim k g) :
    IsPrim k (f + g) := ⟨hf.1.add hg.1, by rw [map_add, hf.2, hg.2, add_zero]⟩

theorem IsPrim.sub {k : ℕ} {f g : Finset (Fin i) → F} (hf : IsPrim k f) (hg : IsPrim k g) :
    IsPrim k (f - g) := ⟨hf.1.sub hg.1, by rw [map_sub, hf.2, hg.2, sub_zero]⟩

theorem IsPrim.smul {k : ℕ} {f : Finset (Fin i) → F} (hf : IsPrim k f) (c : F) :
    IsPrim k (c • f) := ⟨hf.1.smul c, by rw [map_smul, hf.2, smul_zero]⟩

theorem isPrim_sum {ι : Type*} {k : ℕ} (s : Finset ι) (f : ι → Finset (Fin i) → F)
    (h : ∀ a ∈ s, IsPrim k (f a)) : IsPrim k (∑ a ∈ s, f a) :=
  ⟨isLevel_sum s f fun a ha => (h a ha).1, by
    rw [map_sum]
    exact Finset.sum_eq_zero fun a ha => (h a ha).2⟩

theorem IsPrim.U_string {k : ℕ} {h : Finset (Fin i) → F} (hh : IsPrim k h) (s : ℕ) :
    U ((D ^ (s + 1)) h)
      = (((s : F) + 1) * ((i : F) - 2 * (k : F) - (s : F))) • (D ^ s) h := by
  rw [U_D_pow hh.1 s, hh.2, map_zero, zero_add]

def strCoef (F : Type*) [Field F] (i k e r : ℕ) : F :=
  ∏ u ∈ range r, ((e + r - u : ℕ) : F) * ((i : F) - 2 * (k : F) - (e : F) - (r : F) + (u : F) + 1)

theorem IsPrim.U_pow_D_pow {k : ℕ} {h : Finset (Fin i) → F} (hh : IsPrim k h) (e r : ℕ) :
    (U ^ r) ((D ^ (e + r)) h) = strCoef F i k e r • (D ^ e) h := by
  induction r with
  | zero => simp [strCoef]
  | succ r ih =>
    rw [pow_succ U r, Module.End.mul_apply, ← add_assoc, hh.U_string (e + r), map_smul, ih,
      smul_smul]
    congr 1
    rw [strCoef, strCoef, Finset.prod_range_succ', mul_comm]
    congr 1
    · refine Finset.prod_congr rfl fun u _ => ?_
      rw [show e + (r + 1) - (u + 1) = e + r - u from by omega]
      push_cast
      ring
    · simp only [Nat.sub_zero]
      push_cast
      ring

theorem IsPrim.U_pow_D_pow_eq_zero {k : ℕ} {h : Finset (Fin i) → F} (hh : IsPrim k h)
    {r s : ℕ} (hrs : s < r) : (U ^ r) ((D ^ s) h) = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 1 + s := ⟨r - 1 - s, by omega⟩
  have h0 := hh.U_pow_D_pow 0 s
  rw [zero_add] at h0
  rw [pow_add, Module.End.mul_apply, h0, map_smul, pow_zero, Module.End.one_apply, pow_succ,
    Module.End.mul_apply, hh.2, map_zero, smul_zero]

section CharZero

variable [CharZero F]

theorem IsPrim.le_of_D_pow_ne_zero {k : ℕ} {h : Finset (Fin i) → F} (hh : IsPrim k h) :
    ∀ {s : ℕ}, (D ^ s) h ≠ 0 → 2 * k + s ≤ i := by
  have key : ∀ m s : ℕ, i < k + s + m → (D ^ s) h ≠ 0 → 2 * k + s ≤ i := by
    intro m
    induction m with
    | zero =>
      intro s hs hne
      exact absurd ((hh.1.map_D_pow s).eq_zero_of_lt (by omega)) hne
    | succ m ih =>
      intro s hs hne
      by_cases h1 : (D ^ (s + 1)) h = 0
      · have h2 := hh.U_string s
        rw [h1, map_zero] at h2
        rcases smul_eq_zero.mp h2.symm with h3 | h3
        · rcases mul_eq_zero.mp h3 with h4 | h4
          · exact absurd h4 (Nat.cast_add_one_ne_zero s)
          · have h5 : ((i : ℕ) : F) = ((2 * k + s : ℕ) : F) := by
              push_cast
              linear_combination h4
            exact (Nat.cast_injective h5).ge
        · exact absurd h3 hne
      · have := ih (s + 1) (by omega) h1
        omega
  intro s hne
  exact key (i + 1) s (by omega) hne

theorem IsPrim.D_pow_eq_zero {k s : ℕ} {h : Finset (Fin i) → F} (hh : IsPrim k h)
    (hs : i < 2 * k + s) : (D ^ s) h = 0 := by
  by_contra hne
  have := hh.le_of_D_pow_ne_zero hne
  omega

theorem IsPrim.eq_zero {k : ℕ} {h : Finset (Fin i) → F} (hh : IsPrim k h) (hk : i < 2 * k) :
    h = 0 := by
  have := hh.D_pow_eq_zero (s := 0) (by omega)
  simpa using this

theorem strCoef_full_ne_zero {k : ℕ} (hk : 2 * k ≤ i) : strCoef F i k 0 (i - 2 * k) ≠ 0 := by
  rw [strCoef, Finset.prod_ne_zero_iff]
  intro u hu
  rw [Finset.mem_range] at hu
  refine mul_ne_zero (Nat.cast_ne_zero.mpr (by omega)) ?_
  rw [Nat.cast_sub hk]
  push_cast
  have : (i : F) - 2 * (k : F) - 0 - ((i : F) - 2 * (k : F)) + (u : F) + 1 = (u : F) + 1 := by
    ring
  rw [this]
  exact Nat.cast_add_one_ne_zero u

theorem exists_prim_decomp_lower : ∀ t : ℕ, 2 * t ≤ i + 1 →
    ∀ x : Finset (Fin i) → F, IsLevel t x →
      ∃ y : ℕ → (Finset (Fin i) → F), (∀ k, IsPrim k (y k)) ∧
        x = ∑ k ∈ range (t + 1), (D ^ (t - k)) (y k) := by
  intro t
  induction t with
  | zero =>
    intro _ x hx
    refine ⟨fun k => if k = 0 then x else 0, fun k => ?_, by simp⟩
    beta_reduce
    by_cases hk : k = 0
    · subst hk
      rw [ite_eq_left rfl]
      exact ⟨hx, hx.U_eq_zero⟩
    · rw [ite_eq_right hk]
      exact isPrim_zero k
  | succ t ih =>
    intro ht x hx
    obtain ⟨y, hy, hUx⟩ := ih (by omega) (U x) hx.map_U
    set c : ℕ → F := fun k => (((t - k : ℕ) : F) + 1) * ((i : F) - 2 * (k : F) - ((t - k : ℕ) : F))
      with hc
    have hc0 : ∀ k ∈ range (t + 1), c k ≠ 0 := by
      intro k hk
      rw [Finset.mem_range] at hk
      refine mul_ne_zero (Nat.cast_add_one_ne_zero _) ?_
      have h1 : (i : F) - 2 * (k : F) - ((t - k : ℕ) : F) = ((i - 2 * k - (t - k) : ℕ) : F) := by
        rw [Nat.cast_sub (show t - k ≤ i - 2 * k from by omega),
          Nat.cast_sub (show 2 * k ≤ i from by omega)]
        push_cast
        ring
      rw [h1]
      exact Nat.cast_ne_zero.mpr (by omega)
    set x' : Finset (Fin i) → F := ∑ k ∈ range (t + 1), (c k)⁻¹ • (D ^ (t + 1 - k)) (y k) with hx'
    have hUx' : U x' = U x := by
      rw [hx', map_sum, hUx]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' := Finset.mem_range.mp hk
      rw [map_smul, show t + 1 - k = (t - k) + 1 from by omega, (hy k).U_string (t - k),
        smul_smul, inv_mul_cancel₀ (hc0 k hk), one_smul]
    have hprim : IsPrim (t + 1) (x - x') := by
      refine ⟨hx.sub (isLevel_sum _ _ fun k hk => ?_), by rw [map_sub, hUx', sub_self]⟩
      have hk' := Finset.mem_range.mp hk
      have := ((hy k).1.map_D_pow (t + 1 - k)).smul (c k)⁻¹
      rwa [show k + (t + 1 - k) = t + 1 from by omega] at this
    refine ⟨fun k => if k ≤ t then (c k)⁻¹ • y k else if k = t + 1 then x - x' else 0,
      fun k => ?_, ?_⟩
    · beta_reduce
      by_cases h1 : k ≤ t
      · rw [ite_eq_left h1]
        exact (hy k).smul (c k)⁻¹
      · by_cases h2 : k = t + 1
        · rw [ite_eq_right h1, ite_eq_left h2, h2]
          exact hprim
        · rw [ite_eq_right h1, ite_eq_right h2]
          exact isPrim_zero k
    · rw [Finset.sum_range_succ]
      have h1 : ∑ k ∈ range (t + 1), (D ^ (t + 1 - k))
          (if k ≤ t then (c k)⁻¹ • y k else if k = t + 1 then x - x' else 0) = x' := by
        rw [hx']
        refine Finset.sum_congr rfl fun k hk => ?_
        have hk' := Finset.mem_range.mp hk
        rw [ite_eq_left (by omega), map_smul]
      rw [h1]
      simp

theorem exists_prim_decomp (t : ℕ) (x : Finset (Fin i) → F) (hx : IsLevel t x) :
    ∃ y : ℕ → (Finset (Fin i) → F), (∀ k, IsPrim k (y k)) ∧
      x = ∑ k ∈ range (t + 1), (D ^ (t - k)) (y k) := by
  rcases Nat.lt_or_ge i t with hit | hit
  · exact ⟨fun _ => 0, fun k => isPrim_zero k, by simp [hx.eq_zero_of_lt hit]⟩
  rcases Nat.lt_or_ge (i + 1) (2 * t) with h2t | h2t
  swap
  · exact exists_prim_decomp_lower t h2t x hx
  obtain ⟨y, hy, hCx⟩ := exists_prim_decomp_lower (i - t) (by omega) (C x) (hx.map_C hit)
  set g : ℕ → (Finset (Fin i) → F) := fun k =>
    (strCoef F i k 0 (i - 2 * k))⁻¹ • (U ^ (i - 2 * k)) (C (y k)) with hg
  have hgprim : ∀ k, k ≤ i - t → IsPrim k (g k) := by
    intro k hk
    refine ⟨IsLevel.smul (IsLevel.map_U_pow (i - 2 * k) ?_) _, ?_⟩
    · have := (hy k).1.map_C (by omega)
      rwa [show k + (i - 2 * k) = i - k from by omega]
    · rw [hg]
      simp only
      rw [map_smul, ← Module.End.mul_apply, ← pow_succ', ← C_D_pow,
        (hy k).D_pow_eq_zero (by omega), map_zero, smul_zero]
  have hgtop : ∀ k, k ≤ i - t → (D ^ (i - 2 * k)) (g k) = C (y k) := by
    intro k hk
    have h0 := (hy k).U_pow_D_pow 0 (i - 2 * k)
    rw [zero_add, pow_zero, Module.End.one_apply] at h0
    rw [hg]
    simp only
    rw [map_smul, ← C_D_pow, ← C_U_pow, h0, map_smul, smul_smul,
      inv_mul_cancel₀ (strCoef_full_ne_zero (by omega)), one_smul]
  refine ⟨fun k => if k ≤ i - t then strCoef F i k (t - k) (i - t - k) • g k else 0,
    fun k => ?_, ?_⟩
  · beta_reduce
    by_cases hk : k ≤ i - t
    · rw [ite_eq_left hk]
      exact (hgprim k hk).smul _
    · rw [ite_eq_right hk]
      exact isPrim_zero k
  · have hx2 : x = ∑ k ∈ range (i - t + 1), (U ^ (i - t - k)) (C (y k)) := by
      have := congrArg C hCx
      rw [C_C, map_sum] at this
      rw [this]
      exact Finset.sum_congr rfl fun k _ => C_D_pow _ _
    rw [hx2]
    have hsub : range (i - t + 1) ⊆ range (t + 1) := by
      intro k hk
      rw [Finset.mem_range] at hk ⊢
      omega
    rw [← Finset.sum_subset hsub]
    · refine Finset.sum_congr rfl fun k hk => ?_
      have hk' : k ≤ i - t := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      beta_reduce
      rw [ite_eq_left hk', map_smul, ← hgtop k hk']
      have := (hgprim k hk').U_pow_D_pow (t - k) (i - t - k)
      rwa [show t - k + (i - t - k) = i - 2 * k from by omega] at this
    · intro k _ hk
      rw [Finset.mem_range] at hk
      beta_reduce
      rw [ite_eq_right (by omega), map_zero]

end CharZero

end Rhone.LinearAlgebra.BooleanLatticeInverse
