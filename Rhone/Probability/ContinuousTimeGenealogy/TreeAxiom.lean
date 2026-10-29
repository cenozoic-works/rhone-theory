/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.Data.Setoid.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Analysis.SpecialFunctions.Exp

/-! # Tree axiom for the continuous-time genealogy and the relation `~_∗ = ~_A ∩ ~_B` -/

@[expose] public section

namespace Rhone.Probability.ContinuousTimeGenealogy

variable {ι : Type*}

structure IsTreeHeight (d : ι → ι → ℝ) : Prop where
  self : ∀ i, d i i = 0
  symm : ∀ i j, d i j = d j i
  nonneg : ∀ i j, 0 ≤ d i j
  ultra : ∀ i j k, d i k ≤ max (d i j) (d j k)

def ResolvedBy (d : ι → ι → ℝ) (hgt : ι → ℝ) (i j : ι) : Prop :=
  d i j ≤ hgt i ∧ d i j ≤ hgt j

theorem resolvedBy_refl {d : ι → ι → ℝ} (hd : IsTreeHeight d) {hgt : ι → ℝ}
    (hn : ∀ i, 0 ≤ hgt i) (i : ι) : ResolvedBy d hgt i i :=
  ⟨by rw [hd.self i]; exact hn i, by rw [hd.self i]; exact hn i⟩

theorem resolvedBy_symm {d : ι → ι → ℝ} (hd : IsTreeHeight d) {hgt : ι → ℝ} {i j : ι}
    (hij : ResolvedBy d hgt i j) : ResolvedBy d hgt j i := by
  refine ⟨?_, ?_⟩
  · rw [hd.symm j i]
    exact hij.2
  · rw [hd.symm j i]
    exact hij.1

def d3 : Fin 3 → Fin 3 → ℝ :=
  fun i j => if i.val = 2 ∨ j.val = 2 then (if i.val = j.val then 0 else 5) else 0

def h3 : Fin 3 → ℝ := fun i => if i.val = 0 then 1 else 6

theorem isTreeHeight_d3 : IsTreeHeight d3 := by
  refine ⟨fun i => ?_, fun i j => ?_, fun i j => ?_, fun i j k => ?_⟩
  · fin_cases i <;> norm_num [d3]
  · fin_cases i <;> fin_cases j <;> norm_num [d3]
  · fin_cases i <;> fin_cases j <;> norm_num [d3]
  · fin_cases i <;> fin_cases j <;> fin_cases k <;> norm_num [d3]

theorem h3_nonneg : ∀ i, 0 ≤ h3 i := by
  intro i
  fin_cases i <;> norm_num [h3]

theorem resolvedBy_not_transitive :
    ¬ ∀ i j k : Fin 3, ResolvedBy d3 h3 i j → ResolvedBy d3 h3 j k → ResolvedBy d3 h3 i k := by
  intro htr
  have h01 : ResolvedBy d3 h3 0 1 := ⟨by norm_num [d3, h3], by norm_num [d3, h3]⟩
  have h12 : ResolvedBy d3 h3 1 2 := ⟨by norm_num [d3, h3], by norm_num [d3, h3]⟩
  have h02 := (htr 0 1 2 h01 h12).1
  norm_num [d3, h3] at h02

structure IsMarkHeight (d : ι → ι → ℝ) (hgt : ι → ℝ) : Prop where
  nonneg : ∀ i, 0 ≤ hgt i
  agree : ∀ i j, d i j ≤ hgt i → d i j ≤ hgt j → hgt i = hgt j

theorem resolvedBy_trans {d : ι → ι → ℝ} (hd : IsTreeHeight d) {hgt : ι → ℝ}
    (hm : IsMarkHeight d hgt) {i j k : ι}
    (hij : ResolvedBy d hgt i j) (hjk : ResolvedBy d hgt j k) : ResolvedBy d hgt i k := by
  have hEij : hgt i = hgt j := hm.agree i j hij.1 hij.2
  have hEjk : hgt j = hgt k := hm.agree j k hjk.1 hjk.2
  have hik : d i k ≤ max (d i j) (d j k) := hd.ultra i j k
  have hmax : max (d i j) (d j k) ≤ hgt i :=
    max_le hij.1 (by rw [hEij]; exact hjk.1)
  exact ⟨le_trans hik hmax, by rw [← hEjk, ← hEij]; exact le_trans hik hmax⟩

def markSetoid {d : ι → ι → ℝ} (hd : IsTreeHeight d) {hgt : ι → ℝ} (hm : IsMarkHeight d hgt) :
    Setoid ι where
  r := ResolvedBy d hgt
  iseqv :=
    ⟨resolvedBy_refl hd hm.nonneg, resolvedBy_symm hd, fun h₁ h₂ => resolvedBy_trans hd hm h₁ h₂⟩

@[simp] theorem markSetoid_apply {d : ι → ι → ℝ} (hd : IsTreeHeight d) {hgt : ι → ℝ}
    (hm : IsMarkHeight d hgt) (i j : ι) :
    markSetoid hd hm i j ↔ ResolvedBy d hgt i j := Iff.rfl

theorem resolvedBy_min (d : ι → ι → ℝ) (hA hB : ι → ℝ) (i j : ι) :
    ResolvedBy d (fun k => min (hA k) (hB k)) i j
      ↔ ResolvedBy d hA i j ∧ ResolvedBy d hB i j := by
  simp only [ResolvedBy, le_min_iff]
  tauto

theorem IsMarkHeight.min {d : ι → ι → ℝ} {hA hB : ι → ℝ} (hmA : IsMarkHeight d hA)
    (hmB : IsMarkHeight d hB) : IsMarkHeight d fun k => min (hA k) (hB k) where
  nonneg i := le_min (hmA.nonneg i) (hmB.nonneg i)
  agree i j hi hj := by
    rw [le_min_iff] at hi hj
    rw [hmA.agree i j hi.1 hj.1, hmB.agree i j hi.2 hj.2]

theorem markSetoid_min {d : ι → ι → ℝ} (hd : IsTreeHeight d) {hA hB : ι → ℝ}
    (hmA : IsMarkHeight d hA) (hmB : IsMarkHeight d hB) :
    markSetoid hd (hmA.min hmB) = markSetoid hd hmA ⊓ markSetoid hd hmB :=
  Setoid.ext fun i j => by
    rw [Setoid.inf_iff_and]
    exact resolvedBy_min d hA hB i j

theorem block_min (d : ι → ι → ℝ) (hA hB : ι → ℝ) (i : ι) :
    {j | ResolvedBy d (fun k => min (hA k) (hB k)) i j}
      = {j | ResolvedBy d hA i j} ∩ {j | ResolvedBy d hB i j} := by
  ext j
  exact resolvedBy_min d hA hB i j

end Rhone.Probability.ContinuousTimeGenealogy
