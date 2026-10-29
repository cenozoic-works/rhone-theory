/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeKingmanFiniteSupport
public import Rhone.Coalescent.SmcPrimeARGPairWordLaw

/-!
# Flat law of Kingman histories in counting-word and chronological-clock coordinates

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 1–6. -/

@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess SmcSupport MeasureTheory Set

noncomputable def oldPairWord (N : ℕ) (w : Fin (N - 1) → ℕ × ℕ) : ℕ → Action :=
  fun k => if hk : k < N - 1 then .inl (w ⟨k, hk⟩) else .inl (0, 0)

theorem oldPairWord_pair (N : ℕ) (w : Fin (N - 1) → ℕ × ℕ) :
    ∀ j < N - 1, ∃ ij, oldPairWord N w j = .inl ij := by
  intro j hj
  exact ⟨w ⟨j, hj⟩, by simp [oldPairWord, hj]⟩

theorem kingmanPrefixLaw_pair_partition (N : ℕ) :
    argPrefixLaw 0 (initialState N, (0, .inl ())) (N - 1) =
      Measure.sum (fun w : Fin (N - 1) → ℕ × ℕ =>
        argWordPrefixLaw 0 (initialState N, (0, .inl ())) (N - 1) (oldPairWord N w)) := by
  classical
  let E (w : Fin (N - 1) → ℕ × ℕ) := argWordSet (N - 1) (oldPairWord N w)
  have hm (w) : MeasurableSet (E w) := argWordSet_measurable _ _
  have hd : Pairwise (fun w v => Disjoint (E w) (E v)) := by
    intro w v hwv
    apply Set.disjoint_left.mpr
    intro h hw hv
    apply hwv
    funext j
    have hwj := hw j
    have hvj := hv j
    simp only [argActionFiber, Set.mem_ofPred_eq, oldPairWord, dite_eq_left j.isLt] at hwj hvj
    exact Sum.inl.inj (Option.some.inj (hwj.symm.trans hvj))
  have hc : (⋃ w, E w) =ᵐ[argPrefixLaw 0 (initialState N, (0, .inl ())) (N - 1)]
      Set.univ := by
    apply Filter.eventuallyEqSet_univ.mpr
    unfold argPrefixLaw
    apply (ae_map_iff (show AEMeasurable
      (fun ω : EventPath => fun k : Finset.Iic (N - 1) => ω k.val)
      ((eventProcess false 0).pathLaw (initialState N, (0, .inl ()))) from
        (measurable_pi_iff.mpr (fun k => measurable_pi_apply k.val)).aemeasurable)
      (MeasurableSet.iUnion hm)).mpr
    filter_upwards [eventProcess_chronologicalAncestryPath N false 0,
      eventProcess_kingmanTransition (initialState N, (0, .inl ()))] with ω hω hs
    have hp : ∀ j : Fin (N - 1), ∃ ij : ℕ × ℕ,
        (ω (j.val + 1)).2.2 = .inr (.inl ij) := by
      intro j
      have hc := kingman_path_count N ω (congrArg Prod.fst hω.1) hs j.val (by omega)
      have hn : 2 ≤ (ω j.val).1.2.2.1 := by have := j.isLt; omega
      obtain ⟨ij, _, _, hmark, _, _⟩ := (ite_eq_left hn).mp (hs j.val)
      exact ⟨ij, hmark⟩
    choose w hw using hp
    apply Set.mem_iUnion.mpr
    refine ⟨w, ?_⟩
    intro j
    simp [argActionFiber, argEventAction, oldPairWord, j.isLt, hw j]
  calc
    argPrefixLaw 0 (initialState N, (0, .inl ())) (N - 1) =
        (argPrefixLaw 0 (initialState N, (0, .inl ())) (N - 1)).restrict (⋃ w, E w) := by
      rw [Measure.restrict_congr_set hc, Measure.restrict_univ]
    _ = _ := by
      rw [Measure.restrict_iUnion hd hm]
      rfl

end Rhone.Coalescent.SmcPrime

@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess SmcSupport MeasureTheory
open scoped ENNReal

noncomputable def oldPairHistory (N : ℕ) (w : Fin (N - 1) → ℕ × ℕ)
    (τ : Fin (N - 1) → ℝ) : KingmanHistory N :=
  fun k => argFlatRun (initialState N, (0, .inl ())) (fun j => .inl (w j)) τ 0 k.val

noncomputable def oldPairDensity (N : ℕ) (w : Fin (N - 1) → ℕ × ℕ)
    (τ : Fin (N - 1) → ℝ) : ℝ≥0∞ :=
  argWordWeight 0 (initialState N, (0, .inl ())) (oldPairWord N w) (N - 1) τ 0

attribute [irreducible] oldPairDensity

theorem oldPairWord_fin_eq (N : ℕ) (w : Fin (N - 1) → ℕ × ℕ) :
    (fun j : Fin (N - 1) => oldPairWord N w j.val) = fun j => .inl (w j) := by
  funext j
  simp [oldPairWord, j.isLt]

theorem oldPairHistory_measurable (N : ℕ) :
    Measurable (fun p : (Fin (N - 1) → ℕ × ℕ) × (Fin (N - 1) → ℝ) =>
      oldPairHistory N p.1 p.2) := by
  apply measurable_from_prod_countable_right
  intro w
  apply measurable_pi_iff.mpr
  intro k
  exact (argFlatRun_eval_measurable (initialState N, (0, .inl ()))
    (fun j => .inl (w j)) k.val).comp (measurable_id.prodMk measurable_const)

theorem oldPairDensity_measurable (N : ℕ) :
    Measurable (fun p : (Fin (N - 1) → ℕ × ℕ) × (Fin (N - 1) → ℝ) =>
      oldPairDensity N p.1 p.2) := by
  let P := (Fin (N - 1) → ℕ × ℕ) × (Fin (N - 1) → ℝ)
  apply measurable_countable_choice (fun p : P => p.1) measurable_fst
    (fun w p => oldPairDensity N w p.2)
  intro w
  have hm : Measurable (fun p : (Fin (N - 1) → ℝ) × ℝ =>
      argWordWeight 0 (initialState N, (0, .inl ())) (oldPairWord N w) (N - 1) p.1 p.2) :=
    argWordWeight_measurable 0 (initialState N, (0, .inl ())) (oldPairWord N w) (N - 1)
  have hc : Measurable (fun p : P => (p.2, (0 : ℝ))) :=
    measurable_snd.prodMk measurable_const
  simpa only [oldPairDensity, Function.comp_def] using hm.comp hc

def oldPrefixHistory (N : ℕ) (hN : 0 < N) (h : ARGPrefix (N - 1)) : KingmanHistory N :=
  fun k => h ⟨k.val, Finset.mem_Iic.mpr (by have := k.isLt; omega)⟩

theorem oldPrefixHistory_measurable (N : ℕ) (hN : 0 < N) :
    Measurable (oldPrefixHistory N hN) :=
  measurable_pi_iff.mpr (fun _ => measurable_pi_apply _)

theorem oldPrefixHistory_law (N : ℕ) (hN : 0 < N) :
    (argPrefixLaw 0 (initialState N, (0, .inl ())) (N - 1)).map
      (oldPrefixHistory N hN) = kingmanHistoryLaw N := by
  rw [argPrefixLaw, Measure.map_map (oldPrefixHistory_measurable N hN)
    (measurable_pi_iff.mpr (fun k => measurable_pi_apply k.val))]
  rfl

theorem oldPrefixHistory_rebuild (N : ℕ) (hN : 0 < N)
    (w : Fin (N - 1) → ℕ × ℕ) (τ : Fin (N - 1) → ℝ) :
    oldPrefixHistory N hN
      (argWordRebuild (initialState N, (0, .inl ())) (oldPairWord N w) (N - 1) τ 0) =
        oldPairHistory N w τ := by
  change (fun k : Fin N => argFlatRun (initialState N, (0, .inl ()))
    (fun j => oldPairWord N w j.val) τ 0 k.val) = _
  rw [oldPairWord_fin_eq]
  rfl

end Rhone.Coalescent.SmcPrime

@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess SmcSupport MeasureTheory
open scoped ENNReal

theorem kingmanHistoryLaw_pair_flat (N : ℕ) (hN : 0 < N) :
    kingmanHistoryLaw N =
      (((Measure.count : Measure (Fin (N - 1) → ℕ × ℕ)).prod volume).withDensity
        (fun p => oldPairDensity N p.1 p.2)).map
          (fun p => oldPairHistory N p.1 p.2) := by
  apply Measure.ext_of_lintegral
  intro f hf
  have ho : Measurable (fun p : (Fin (N - 1) → ℕ × ℕ) × (Fin (N - 1) → ℝ) =>
      f (oldPairHistory N p.1 p.2)) := hf.comp (oldPairHistory_measurable N)
  rw [lintegral_map hf (oldPairHistory_measurable N),
    lintegral_withDensity_eq_lintegral_mul _ (oldPairDensity_measurable N) ho,
    lintegral_prod _ ((oldPairDensity_measurable N).mul ho).aemeasurable, lintegral_count]
  rw [← oldPrefixHistory_law N hN,
    lintegral_map hf (oldPrefixHistory_measurable N hN),
    kingmanPrefixLaw_pair_partition N, lintegral_sum_measure]
  apply tsum_congr
  intro w
  have hp : Measurable (fun h : ARGPrefix (N - 1) => f (oldPrefixHistory N hN h)) :=
    hf.comp (oldPrefixHistory_measurable N hN)
  rw [argPairWord_flat_lintegral 0 (by positivity) _ _ _ (oldPairWord_pair N w)
    (fun h => f (oldPrefixHistory N hN h)) hp]
  apply lintegral_congr
  intro τ
  rw [oldPrefixHistory_rebuild]
  simp only [oldPairDensity, Pi.mul_apply]

end Rhone.Coalescent.SmcPrime
