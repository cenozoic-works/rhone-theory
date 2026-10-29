/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.RateLumping

/-! # Lumping and the law of a continuous-time chain at a fixed time -/

@[expose] public section

namespace Rhone.MarkovChain

open Finset MeasureTheory ProbabilityTheory

namespace FinChain

variable {S T : Type*} [Fintype S] [Fintype T] [DecidableEq T] [MeasurableSpace S]
  [DiscreteMeasurableSpace S] [MeasurableSpace T] [DiscreteMeasurableSpace T]
  {C : FinChain S} {f : S → T} {D : FinChain T}

theorem Lumps.map_kernel (hL : C.Lumps f D) (x : S) :
    (C.kernel x).map f = D.kernel (f x) := by
  refine Measure.ext_of_singleton fun t => ?_
  have hset : f ⁻¹' {t} = ↑(univ.filter fun y => f y = t) := by
    ext y
    simp
  rw [Measure.map_apply Measurable.of_discrete (measurableSet_singleton t),
    kernel_apply_singleton, hset, ← sum_measure_singleton]
  simp only [kernel_apply_singleton]
  rw [← ENNReal.ofReal_sum_of_nonneg fun y _ => C.nonneg x y, hL x t]

end FinChain

namespace RateChain

variable {S T : Type*} [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]
  {R : RateChain S} {f : S → T} {R' : RateChain T}

theorem Lumps.semigroupChain_lumps (hL : R.Lumps f R') (t : ℝ) (ht : 0 ≤ t) :
    (R.semigroupChain t ht).Lumps f (R'.semigroupChain t ht) :=
  fun x s => hL.sum_semigroup_fibre t x s

theorem Lumps.semigroup_apply_of_injective (hL : R.Lumps f R') (hf : Function.Injective f)
    (t : ℝ) (x y : S) : R.semigroup t x y = R'.semigroup t (f x) (f y) := by
  rw [← hL.sum_semigroup_fibre t x (f y)]
  symm
  exact Finset.sum_eq_single_of_mem y (mem_filter.2 ⟨mem_univ y, rfl⟩) fun z hz hzy =>
    absurd (hf (mem_filter.1 hz).2) hzy

variable [MeasurableSpace S] [DiscreteMeasurableSpace S] [MeasurableSpace T]
  [DiscreteMeasurableSpace T]

theorem Lumps.map_semigroupChain_kernel (hL : R.Lumps f R') (t : ℝ) (ht : 0 ≤ t) (x : S) :
    ((R.semigroupChain t ht).kernel x).map f = (R'.semigroupChain t ht).kernel (f x) :=
  (hL.semigroupChain_lumps t ht).map_kernel x

theorem Lumps.map_semigroupChain_pathLaw (hL : R.Lumps f R') (t : ℝ) (ht : 0 ≤ t) (x : S) :
    ((R.semigroupChain t ht).pathLaw x).map (fun ω k => f (ω k)) =
      (R'.semigroupChain t ht).pathLaw (f x) :=
  (hL.semigroupChain_lumps t ht).map_pathLaw x

end RateChain

end Rhone.MarkovChain
