/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.Algebra.Order.Field.GeomSum
public import Mathlib.Analysis.SpecificLimits.Basic

/-! # The comparison principle and the truncation remainder — the abstract core -/

@[expose] public section

namespace Rhone.Analysis.TruncationRemainder

open Filter Finset
open scoped Topology

variable {ι : Type*}

def BoundBy (V : ι → ℝ) (C : ℝ) (u : ι → ℝ) : Prop := ∀ i, |u i| ≤ C * V i

theorem BoundBy.mono {V : ι → ℝ} (hV : ∀ i, 0 ≤ V i) {C C' : ℝ} {u : ι → ℝ}
    (h : BoundBy V C u) (hC : C ≤ C') : BoundBy V C' u := fun i =>
  (h i).trans (mul_le_mul_of_nonneg_right hC (hV i))

theorem BoundBy.add {V : ι → ℝ} {C C' : ℝ} {u w : ι → ℝ}
    (h : BoundBy V C u) (h' : BoundBy V C' w) : BoundBy V (C + C') (fun i => u i + w i) := by
  intro i
  calc |u i + w i| ≤ |u i| + |w i| := abs_add_le _ _
    _ ≤ C * V i + C' * V i := add_le_add (h i) (h' i)
    _ = (C + C') * V i := by ring

theorem BoundBy.sub {V : ι → ℝ} {C C' : ℝ} {u w : ι → ℝ}
    (h : BoundBy V C u) (h' : BoundBy V C' w) : BoundBy V (C + C') (fun i => u i - w i) := by
  intro i
  calc |u i - w i| ≤ |u i| + |w i| := by
        simpa [sub_eq_add_neg, abs_neg] using abs_add_le (u i) (-w i)
    _ ≤ C * V i + C' * V i := add_le_add (h i) (h' i)
    _ = (C + C') * V i := by ring

theorem BoundBy.const_mul {V : ι → ℝ} {C a : ℝ} {u : ι → ℝ} (h : BoundBy V C u) :
    BoundBy V (|a| * C) (fun i => a * u i) := by
  intro i
  rw [abs_mul]
  calc |a| * |u i| ≤ |a| * (C * V i) := mul_le_mul_of_nonneg_left (h i) (abs_nonneg a)
    _ = |a| * C * V i := by ring

theorem BoundBy.zero (V : ι → ℝ) : BoundBy V 0 (fun _ => (0 : ℝ)) := by intro i; simp

def Dominates (V : ι → ℝ) (T : (ι → ℝ) → ι → ℝ) (δ : ℝ) : Prop :=
  ∀ (u : ι → ℝ) (C : ℝ), 0 ≤ C → BoundBy V C u → BoundBy V (C * (1 - δ)) (T u)

def UBoundedBy (V : ι → ℝ) (U : (ι → ℝ) → ι → ℝ) (cU : ℝ) : Prop :=
  ∀ (u : ι → ℝ) (C : ℝ), 0 ≤ C → BoundBy V C u → BoundBy V (C * cU) (U u)

def phiC (δ M C : ℝ) : ℝ := (1 - δ) * C + M

theorem phiC_nonneg {δ M C : ℝ} (hδ1 : δ ≤ 1) (hM : 0 ≤ M) (hC : 0 ≤ C) :
    0 ≤ phiC δ M C := by
  have h : (0:ℝ) ≤ 1 - δ := by linarith
  have := mul_nonneg h hC
  rw [phiC]
  linarith

theorem phiC_iterate_nonneg {δ M C : ℝ} (hδ1 : δ ≤ 1) (hM : 0 ≤ M) (hC : 0 ≤ C) (k : ℕ) :
    0 ≤ (phiC δ M)^[k] C := by
  induction k with
  | zero => simpa using hC
  | succ k ih => rw [Function.iterate_succ_apply']; exact phiC_nonneg hδ1 hM ih

theorem phiC_iterate_sub {δ M C₀ : ℝ} (hδ : δ ≠ 0) (k : ℕ) :
    (phiC δ M)^[k] C₀ - M / δ = (1 - δ) ^ k * (C₀ - M / δ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', phiC, pow_succ]
    have h : (1 - δ) * ((phiC δ M)^[k] C₀) + M - M / δ
        = (1 - δ) * ((phiC δ M)^[k] C₀ - M / δ) := by field_simp; ring
    rw [h, ih]; ring

theorem phiC_iterate_tendsto {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (M C₀ : ℝ) :
    Tendsto (fun k => (phiC δ M)^[k] C₀) atTop (𝓝 (M / δ)) := by
  have hpow : Tendsto (fun k : ℕ => (1 - δ) ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)
  have h := (hpow.mul_const (C₀ - M / δ)).add_const (M / δ)
  rw [zero_mul, zero_add] at h
  refine h.congr fun k => ?_
  have := phiC_iterate_sub (M := M) (C₀ := C₀) (ne_of_gt hδ) k
  linarith

theorem bound_of_fixedPoint {V : ι → ℝ} {T : (ι → ℝ) → ι → ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hT : Dominates V T δ)
    {u f : ι → ℝ} {M C₀ : ℝ} (hM : 0 ≤ M) (hC₀ : 0 ≤ C₀)
    (hu : ∀ i, u i = T u i + f i) (hbdd : BoundBy V C₀ u) (hf : BoundBy V M f) :
    BoundBy V (M / δ) u := by
  have step : ∀ C : ℝ, 0 ≤ C → BoundBy V C u → BoundBy V (phiC δ M C) u := by
    intro C hC hCu i
    have h1 : |T u i| ≤ C * (1 - δ) * V i := hT u C hC hCu i
    calc |u i| = |T u i + f i| := by rw [← hu i]
      _ ≤ |T u i| + |f i| := abs_add_le _ _
      _ ≤ C * (1 - δ) * V i + M * V i := add_le_add h1 (hf i)
      _ = phiC δ M C * V i := by rw [phiC]; ring
  have main : ∀ k, BoundBy V ((phiC δ M)^[k] C₀) u := by
    intro k
    induction k with
    | zero => simpa using hbdd
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact step _ (phiC_iterate_nonneg hδ1 hM hC₀ k) ih
  intro i
  refine ge_of_tendsto ((phiC_iterate_tendsto hδ hδ1 M C₀).mul_const (V i)) ?_
  filter_upwards with k using main k i

theorem eq_zero_of_fixedPoint {V : ι → ℝ} {T : (ι → ℝ) → ι → ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hT : Dominates V T δ)
    {w : ι → ℝ} {C₀ : ℝ} (hC₀ : 0 ≤ C₀) (hw : ∀ i, w i = T w i) (hbdd : BoundBy V C₀ w) :
    w = 0 := by
  have h : BoundBy V (0 / δ) w :=
    bound_of_fixedPoint hδ hδ1 hT (f := fun _ => 0) le_rfl hC₀ (by simpa using hw) hbdd
      (BoundBy.zero V)
  funext i
  have hi := h i
  rw [zero_div, zero_mul] at hi
  simpa using abs_nonpos_iff.mp hi

structure IsLinear (T : (ι → ℝ) → ι → ℝ) : Prop where
  map_add : ∀ (u w : ι → ℝ) (i : ι), T (fun j => u j + w j) i = T u i + T w i
  map_smul : ∀ (a : ℝ) (u : ι → ℝ) (i : ι), T (fun j => a * u j) i = a * T u i

theorem IsLinear.map_zero {T : (ι → ℝ) → ι → ℝ} (hT : IsLinear T) (i : ι) :
    T (fun _ => (0 : ℝ)) i = 0 := by
  simpa using hT.map_smul 0 (fun _ => (0 : ℝ)) i

theorem IsLinear.map_sub {T : (ι → ℝ) → ι → ℝ} (hT : IsLinear T) (u w : ι → ℝ) (i : ι) :
    T (fun j => u j - w j) i = T u i - T w i := by
  have h1 := hT.map_add u (fun j => -w j) i
  have h2 := hT.map_smul (-1) w i
  simp only [neg_one_mul] at h2
  simp only [sub_eq_add_neg]
  rw [h1, h2]

theorem IsLinear.map_sum_range {T : (ι → ℝ) → ι → ℝ} (hT : IsLinear T) (F : ℕ → ι → ℝ)
    (n : ℕ) (i : ι) :
    T (fun j => ∑ k ∈ Finset.range n, F k j) i = ∑ k ∈ Finset.range n, T (F k) i := by
  induction n with
  | zero => simp only [Finset.range_zero, Finset.sum_empty]; exact hT.map_zero i
  | succ n ih =>
    have hfun : (fun j => ∑ k ∈ Finset.range (n + 1), F k j)
        = (fun j => (∑ k ∈ Finset.range n, F k j) + F n j) := by
      funext j; rw [Finset.sum_range_succ]
    rw [hfun, hT.map_add, ih, Finset.sum_range_succ]

structure IsHierarchy (V : ι → ℝ) (T U : (ι → ℝ) → ι → ℝ) (v : ι → ℝ) (q : ℕ → ι → ℝ) :
    Prop where
  zero : ∀ i, q 0 i = T (q 0) i + v i
  succ : ∀ k i, q (k + 1) i = T (q (k + 1)) i + U (q k) i
  bdd : ∀ k, ∃ C, 0 ≤ C ∧ BoundBy V C (q k)

theorem coeff_bound {V : ι → ℝ} {T U : (ι → ℝ) → ι → ℝ} {δ cU : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hcU : 0 ≤ cU)
    (hT : Dominates V T δ) (hU : UBoundedBy V U cU)
    {v : ι → ℝ} {q : ℕ → ι → ℝ} (hq : IsHierarchy V T U v q)
    {P : ℝ} (hP : 0 ≤ P) (hq0 : BoundBy V P (q 0)) (k : ℕ) :
    BoundBy V (P * (cU / δ) ^ k) (q k) := by
  have hδ0 : δ ≠ 0 := ne_of_gt hδ
  have hratio : 0 ≤ cU / δ := div_nonneg hcU hδ.le
  induction k with
  | zero => simpa using hq0
  | succ k ih =>
    obtain ⟨C₀, hC₀, hb⟩ := hq.bdd (k + 1)
    have hMk : 0 ≤ P * (cU / δ) ^ k := mul_nonneg hP (pow_nonneg hratio k)
    have hUb : BoundBy V (P * (cU / δ) ^ k * cU) (U (q k)) := hU _ _ hMk ih
    have hfix := bound_of_fixedPoint hδ hδ1 hT (mul_nonneg hMk hcU) hC₀ (hq.succ k) hb hUb
    have heq : P * (cU / δ) ^ k * cU / δ = P * (cU / δ) ^ (k + 1) := by
      rw [pow_succ]; simp only [div_eq_mul_inv]; ring
    rwa [heq] at hfix

theorem coeff_bound_radius {V : ι → ℝ} {T U : (ι → ℝ) → ι → ℝ} {δ cU r : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hcU : 0 ≤ cU) (hr : r = δ / cU)
    (hT : Dominates V T δ) (hU : UBoundedBy V U cU)
    {v : ι → ℝ} {q : ℕ → ι → ℝ} (hq : IsHierarchy V T U v q)
    {P : ℝ} (hP : 0 ≤ P) (hq0 : BoundBy V P (q 0)) (k : ℕ) :
    BoundBy V (P * (r⁻¹) ^ k) (q k) := by
  have : r⁻¹ = cU / δ := by rw [hr, inv_div]
  rw [this]
  exact coeff_bound hδ hδ1 hcU hT hU hq hP hq0 k

def partialSum (σ : ℝ) (q : ℕ → ι → ℝ) (K : ℕ) : ι → ℝ :=
  fun i => ∑ k ∈ Finset.range K, σ ^ k * q k i

theorem partialSum_def (σ : ℝ) (q : ℕ → ι → ℝ) (K : ℕ) :
    partialSum σ q K = fun i => ∑ k ∈ Finset.range K, σ ^ k * q k i := rfl

theorem exists_bound_partialSum {V : ι → ℝ} {q : ℕ → ι → ℝ}
    (hb : ∀ k, ∃ C, 0 ≤ C ∧ BoundBy V C (q k)) (σ : ℝ) (K : ℕ) :
    ∃ C, 0 ≤ C ∧ BoundBy V C (partialSum σ q K) := by
  induction K with
  | zero =>
    refine ⟨0, le_rfl, ?_⟩
    intro i
    simp [partialSum]
  | succ K ih =>
    obtain ⟨C, hC, hb'⟩ := ih
    obtain ⟨D, hD, hb''⟩ := hb K
    refine ⟨C + |σ ^ K| * D, by positivity, ?_⟩
    have hfun : partialSum σ q (K + 1)
        = fun i => partialSum σ q K i + σ ^ K * q K i := by
      funext i; simp only [partialSum]; rw [Finset.sum_range_succ]
    rw [hfun]
    exact hb'.add hb''.const_mul

theorem partialSum_eq {V : ι → ℝ} {T U : (ι → ℝ) → ι → ℝ} {v : ι → ℝ} {q : ℕ → ι → ℝ}
    (hTlin : IsLinear T) (hUlin : IsLinear U) (hq : IsHierarchy V T U v q) (σ : ℝ) (K : ℕ)
    (i : ι) :
    partialSum σ q (K + 1) i
      = T (partialSum σ q (K + 1)) i + v i + σ * U (partialSum σ q K) i := by
  have hT1 : T (partialSum σ q (K + 1)) i
      = ∑ k ∈ Finset.range (K + 1), σ ^ k * T (q k) i := by
    rw [partialSum_def, hTlin.map_sum_range (fun k j => σ ^ k * q k j)]
    exact Finset.sum_congr rfl fun k _ => hTlin.map_smul _ _ _
  have hU1 : U (partialSum σ q K) i = ∑ k ∈ Finset.range K, σ ^ k * U (q k) i := by
    rw [partialSum_def, hUlin.map_sum_range (fun k j => σ ^ k * q k j)]
    exact Finset.sum_congr rfl fun k _ => hUlin.map_smul _ _ _
  rw [hT1, hU1]
  simp only [partialSum]
  rw [Finset.mul_sum, Finset.sum_range_succ' (fun k => σ ^ k * q k i) K,
    Finset.sum_range_succ' (fun k => σ ^ k * T (q k) i) K]
  have key : ∀ k ∈ Finset.range K, σ ^ (k + 1) * q (k + 1) i
      = σ ^ (k + 1) * T (q (k + 1)) i + σ * (σ ^ k * U (q k) i) := by
    intro k _
    rw [hq.succ k i]; ring
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, hq.zero i]
  ring

theorem remainder_rec {V : ι → ℝ} {T U : (ι → ℝ) → ι → ℝ} {v u : ι → ℝ} {q : ℕ → ι → ℝ}
    (hTlin : IsLinear T) (hUlin : IsLinear U) (hq : IsHierarchy V T U v q)
    {σ : ℝ} (hu : ∀ i, u i = T u i + σ * U u i + v i) (K : ℕ) (i : ι) :
    u i - partialSum σ q (K + 1) i
      = T (fun j => u j - partialSum σ q (K + 1) j) i
        + σ * U (fun j => u j - partialSum σ q K j) i := by
  rw [hTlin.map_sub, hUlin.map_sub, hu i, partialSum_eq hTlin hUlin hq σ K i]
  ring

theorem remainder_bound {V : ι → ℝ} {T U : (ι → ℝ) → ι → ℝ} {δ cU : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hcU : 0 ≤ cU)
    (hT : Dominates V T δ) (hU : UBoundedBy V U cU)
    (hTlin : IsLinear T) (hUlin : IsLinear U)
    {v u : ι → ℝ} {q : ℕ → ι → ℝ} (hq : IsHierarchy V T U v q)
    {σ Cu : ℝ} (hCu : 0 ≤ Cu) (hu : ∀ i, u i = T u i + σ * U u i + v i)
    (hubdd : BoundBy V Cu u) (K : ℕ) :
    BoundBy V (Cu * (|σ| * cU / δ) ^ K) (fun i => u i - partialSum σ q K i) := by
  have hδ0 : δ ≠ 0 := ne_of_gt hδ
  have hbase : 0 ≤ |σ| * cU / δ := div_nonneg (mul_nonneg (abs_nonneg σ) hcU) hδ.le
  induction K with
  | zero => simpa [partialSum] using hubdd
  | succ K ih =>
    obtain ⟨C₁, hC₁, hb₁⟩ := exists_bound_partialSum hq.bdd σ (K + 1)
    have hrem : BoundBy V (Cu + C₁) (fun i => u i - partialSum σ q (K + 1) i) :=
      hubdd.sub hb₁
    have ht0 : 0 ≤ Cu * (|σ| * cU / δ) ^ K := mul_nonneg hCu (pow_nonneg hbase K)
    have hUb : BoundBy V (Cu * (|σ| * cU / δ) ^ K * cU)
        (U (fun j => u j - partialSum σ q K j)) := hU _ _ ht0 ih
    have hfb : BoundBy V (|σ| * (Cu * (|σ| * cU / δ) ^ K * cU))
        (fun i => σ * U (fun j => u j - partialSum σ q K j) i) := hUb.const_mul
    have hfix := bound_of_fixedPoint (u := fun j => u j - partialSum σ q (K + 1) j)
      hδ hδ1 hT (mul_nonneg (abs_nonneg σ) (mul_nonneg ht0 hcU)) (add_nonneg hCu hC₁)
      (remainder_rec hTlin hUlin hq hu K) hrem hfb
    have heq : |σ| * (Cu * (|σ| * cU / δ) ^ K * cU) / δ
        = Cu * (|σ| * cU / δ) ^ (K + 1) := by
      rw [pow_succ]; simp only [div_eq_mul_inv]; ring
    rwa [heq] at hfix

private theorem geom_Ico_le {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (K M : ℕ) :
    ∑ k ∈ Finset.Ico K M, t ^ k ≤ t ^ K / (1 - t) :=
  geom_sum_Ico_le_of_lt_one ht0 ht1

theorem tail_bound {V : ι → ℝ} {q : ℕ → ι → ℝ} (hV : ∀ i, 0 ≤ V i) {P t σ : ℝ}
    (hP : 0 ≤ P) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hcoeff : ∀ k, BoundBy V (P * t ^ k) (fun i => σ ^ k * q k i))
    {u : ι → ℝ} (hconv : ∀ i, Tendsto (fun K => partialSum σ q K i) atTop (𝓝 (u i)))
    (K : ℕ) :
    BoundBy V (P * t ^ K / (1 - t)) (fun i => u i - partialSum σ q K i) := by
  intro i
  have hlim : Tendsto (fun M => |partialSum σ q M i - partialSum σ q K i|) atTop
      (𝓝 |u i - partialSum σ q K i|) := ((hconv i).sub_const _).abs
  refine le_of_tendsto hlim ?_
  filter_upwards [Filter.eventually_ge_atTop K] with M hM
  have hsplit : partialSum σ q M i - partialSum σ q K i
      = ∑ k ∈ Finset.Ico K M, σ ^ k * q k i := by
    simp only [partialSum]
    exact (Finset.sum_Ico_eq_sub _ hM).symm
  rw [hsplit]
  calc |∑ k ∈ Finset.Ico K M, σ ^ k * q k i| ≤ ∑ k ∈ Finset.Ico K M, |σ ^ k * q k i| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.Ico K M, P * t ^ k * V i := Finset.sum_le_sum fun k _ => hcoeff k i
    _ = P * V i * ∑ k ∈ Finset.Ico K M, t ^ k := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    _ ≤ P * V i * (t ^ K / (1 - t)) :=
        mul_le_mul_of_nonneg_left (geom_Ico_le ht0 ht1 K M) (mul_nonneg hP (hV i))
    _ = P * t ^ K / (1 - t) * V i := by ring

theorem BoundBy.min_of {V : ι → ℝ} {C C' : ℝ} {u : ι → ℝ}
    (h : BoundBy V C u) (h' : BoundBy V C' u) : BoundBy V (min C C') u := by
  intro i
  rcases le_total C C' with hc | hc
  · rw [min_eq_left hc]; exact h i
  · rw [min_eq_right hc]; exact h' i

theorem remainder_bound_min {V : ι → ℝ} {T U : (ι → ℝ) → ι → ℝ} {δ cU : ℝ}
    (hV : ∀ i, 0 ≤ V i) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hcU : 0 ≤ cU)
    (hT : Dominates V T δ) (hU : UBoundedBy V U cU)
    (hTlin : IsLinear T) (hUlin : IsLinear U)
    {v u : ι → ℝ} {q : ℕ → ι → ℝ} (hq : IsHierarchy V T U v q)
    {σ Cu P : ℝ} (hCu : 0 ≤ Cu) (hP : 0 ≤ P)
    (ht1 : |σ| * cU / δ < 1)
    (hu : ∀ i, u i = T u i + σ * U u i + v i) (hubdd : BoundBy V Cu u)
    (hcoeff : ∀ k, BoundBy V (P * (|σ| * cU / δ) ^ k) (fun i => σ ^ k * q k i))
    (hconv : ∀ i, Tendsto (fun K => partialSum σ q K i) atTop (𝓝 (u i)))
    (K : ℕ) :
    BoundBy V (min (Cu * (|σ| * cU / δ) ^ K) (P * (|σ| * cU / δ) ^ K / (1 - |σ| * cU / δ)))
      (fun i => u i - partialSum σ q K i) := by
  have hbase : 0 ≤ |σ| * cU / δ := div_nonneg (mul_nonneg (abs_nonneg σ) hcU) hδ.le
  exact (remainder_bound hδ hδ1 hcU hT hU hTlin hUlin hq hCu hu hubdd K).min_of
    (tail_bound hV hP hbase ht1 hcoeff hconv K)

theorem exists_K_of_tol {V : ι → ℝ} {T U : (ι → ℝ) → ι → ℝ} {δ cU : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hcU : 0 ≤ cU)
    (hT : Dominates V T δ) (hU : UBoundedBy V U cU)
    (hTlin : IsLinear T) (hUlin : IsLinear U)
    {v u : ι → ℝ} {q : ℕ → ι → ℝ} (hq : IsHierarchy V T U v q)
    {σ Cu : ℝ} (hCu : 0 ≤ Cu) (hu : ∀ i, u i = T u i + σ * U u i + v i)
    (hubdd : BoundBy V Cu u) (ht1 : |σ| * cU / δ < 1) {ε : ℝ} (hε : 0 < ε) (i : ι) :
    ∃ K, |u i - partialSum σ q K i| ≤ ε := by
  have hbase : 0 ≤ |σ| * cU / δ := div_nonneg (mul_nonneg (abs_nonneg σ) hcU) hδ.le
  have hpow : Tendsto (fun K : ℕ => (|σ| * cU / δ) ^ K) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hbase ht1
  have h := hpow.const_mul (Cu * V i)
  rw [mul_zero] at h
  obtain ⟨K, hK⟩ := (h.eventually (gt_mem_nhds hε)).exists
  refine ⟨K, ?_⟩
  have hb : |u i - partialSum σ q K i| ≤ Cu * (|σ| * cU / δ) ^ K * V i :=
    remainder_bound hδ hδ1 hcU hT hU hTlin hUlin hq hCu hu hubdd K i
  have heq : Cu * (|σ| * cU / δ) ^ K * V i = Cu * V i * (|σ| * cU / δ) ^ K := by ring
  linarith

end Rhone.Analysis.TruncationRemainder
