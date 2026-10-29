/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Mathlib.Algebra.AlgebraicCard
public import Mathlib.Analysis.Real.Cardinality
public import Mathlib.FieldTheory.RatFunc.AsPolynomial

/-! # A real point of the five-variable generic field -/

@[expose] public section

namespace Rhone.Algebra.SamplingUniform

open Polynomial Cardinal

theorem countable_polynomial (K : Type*) [CommRing K] [Countable K] : Countable K[X] := by
  rw [← Cardinal.mk_le_aleph0_iff]
  exact Polynomial.cardinalMk_le_max.trans (max_le Cardinal.mk_le_aleph0 le_rfl)

theorem countable_ratFunc (K : Type*) [Field K] [Countable K] : Countable (RatFunc K) := by
  have := countable_polynomial K
  exact Function.Surjective.countable
    (f := fun pq : K[X] × K[X] =>
      algebraMap K[X] (RatFunc K) pq.1 / algebraMap K[X] (RatFunc K) pq.2)
    (fun x => ⟨(x.num, x.denom), RatFunc.num_div_denom x⟩)

theorem not_countable_Ioo {s t : ℝ} (hst : s < t) : ¬ (Set.Ioo s t).Countable := by
  intro h
  have h2 := Cardinal.le_aleph0_iff_set_countable.mpr h
  rw [Cardinal.mk_Ioo_real hst] at h2
  exact absurd h2 (not_le.mpr Cardinal.aleph0_lt_continuum)

theorem exists_ratFunc_extension {K : Type*} [Field K] [Countable K] (f : K →+* ℝ)
    {s t : ℝ} (hst : s < t) :
    ∃ g : RatFunc K →+* ℝ, (∀ c, g (RatFunc.C c) = f c) ∧
      s < g RatFunc.X ∧ g RatFunc.X < t := by
  let _ : Algebra K ℝ := f.toAlgebra
  have hc : {x : ℝ | IsAlgebraic K x}.Countable := Algebraic.countable K ℝ
  obtain ⟨x, hx, hxa⟩ : ∃ x ∈ Set.Ioo s t, x ∉ {x : ℝ | IsAlgebraic K x} := by
    by_contra h
    apply not_countable_Ioo hst
    apply hc.mono
    intro y hy
    by_contra hy'
    exact h ⟨y, hy, hy'⟩
  have htr : Transcendental K x := hxa
  have hinj : Function.Injective (aeval x : K[X] →ₐ[K] ℝ) :=
    transcendental_iff_injective.mp htr
  let φ : K[X] →+* ℝ := (aeval x : K[X] →ₐ[K] ℝ).toRingHom
  have hφ : nonZeroDivisors K[X] ≤ (nonZeroDivisors ℝ).comap φ := by
    intro p hp
    rw [Submonoid.mem_comap]
    apply mem_nonZeroDivisors_of_ne_zero
    intro h0
    exact nonZeroDivisors.ne_zero hp (hinj (by simpa [φ] using h0))
  refine ⟨RatFunc.liftRingHom φ hφ, ?_, ?_, ?_⟩
  · intro c
    rw [RatFunc.liftRingHom_C]
    change (aeval x : K[X] →ₐ[K] ℝ) (Polynomial.C c) = f c
    rw [aeval_C]
    rfl
  · rw [RatFunc.liftRingHom_X]
    change s < (aeval x : K[X] →ₐ[K] ℝ) Polynomial.X
    rw [aeval_X]
    exact hx.1
  · rw [RatFunc.liftRingHom_X]
    change (aeval x : K[X] →ₐ[K] ℝ) Polynomial.X < t
    rw [aeval_X]
    exact hx.2

theorem exists_real_specialization :
    ∃ ι : RatFunc (RatFunc (RatFunc (RatFunc (RatFunc ℚ)))) →+* ℝ,
      0 < ι (RatFunc.C (RatFunc.C (RatFunc.C (RatFunc.C RatFunc.X)))) ∧
      0 < ι (RatFunc.C (RatFunc.C (RatFunc.C RatFunc.X))) ∧
      ι (RatFunc.C (RatFunc.C (RatFunc.C RatFunc.X))) < ι RatFunc.X := by
  have h1 : Countable (RatFunc ℚ) := countable_ratFunc ℚ
  have h2 : Countable (RatFunc (RatFunc ℚ)) := countable_ratFunc _
  have h3 : Countable (RatFunc (RatFunc (RatFunc ℚ))) := countable_ratFunc _
  have h4 : Countable (RatFunc (RatFunc (RatFunc (RatFunc ℚ)))) := countable_ratFunc _
  obtain ⟨g1, -, hρ, -⟩ :=
    exists_ratFunc_extension (algebraMap ℚ ℝ) (zero_lt_one' ℝ)
  obtain ⟨g2, hg2, hl, hl1⟩ := exists_ratFunc_extension g1 (zero_lt_one' ℝ)
  obtain ⟨g3, hg3, -, -⟩ := exists_ratFunc_extension g2 (zero_lt_one' ℝ)
  obtain ⟨g4, hg4, -, -⟩ := exists_ratFunc_extension g3 (zero_lt_one' ℝ)
  obtain ⟨g5, hg5, hθ, -⟩ := exists_ratFunc_extension g4 (by norm_num : (1 : ℝ) < 2)
  refine ⟨g5, ?_, ?_, ?_⟩
  · rw [hg5, hg4, hg3, hg2]
    exact hρ
  · rw [hg5, hg4, hg3]
    exact hl
  · rw [hg5, hg4, hg3]
    exact hl1.trans hθ

end Rhone.Algebra.SamplingUniform
