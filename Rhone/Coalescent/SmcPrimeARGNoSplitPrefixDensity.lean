/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module
public import Rhone.Coalescent.SmcPrimeARGNoSplitKernel
public import Rhone.Coalescent.SmcSupport.DensityTransport
public import Rhone.Coalescent.SmcSupport.ARGWordIntegral
public import Rhone.Coalescent.SmcPrimeKingmanSupport
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Exact killed finite-prefix density of the implemented unrestricted ARG process

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 1–7. -/
@[expose] public section
namespace Rhone.Coalescent.SmcSupport
open MeasureTheory ProbabilityTheory IntervalProcess
open scoped ENNReal

def argNoSplitPrefixSet (n : ℕ) : Set (ARGPrefix n) :=
  {h | ∀ j : Fin n, h ⟨j.val + 1, Finset.mem_Iic.mpr (by omega)⟩ ∈ argNoSplitEvent}

theorem argNoSplitPrefixSet_measurable (n : ℕ) : MeasurableSet (argNoSplitPrefixSet n) := by
  apply measurableSet_forall
  intro j
  exact argNoSplitEvent_measurable.preimage (measurable_pi_apply _)

noncomputable def argNoSplitPrefixLaw (R : ℝ) (z : AugmentedState) (n : ℕ) :
    Measure (ARGPrefix n) := (argPrefixLaw R z n).restrict (argNoSplitPrefixSet n)

instance argNoSplitPrefixLaw_finite (R : ℝ) (z : AugmentedState) (n : ℕ) :
    IsFiniteMeasure (argNoSplitPrefixLaw R z n) := by
  unfold argNoSplitPrefixLaw
  infer_instance

theorem argNoSplitPrefixLaw_next_map (R : ℝ) (z : AugmentedState) (n : ℕ) :
    (argNoSplitPrefixLaw R z (n + 1)).map (argPrefixSplit n) =
      (argNoSplitPrefixLaw R z n).compProd
        (((eventProcess false R).stepSeq n).restrict argNoSplitEvent_measurable) := by
  have he : argNoSplitPrefixSet (n + 1) = argPrefixSplit n ⁻¹'
      (argNoSplitPrefixSet n ×ˢ argNoSplitEvent) := by
    ext h
    change (∀ j : Fin (n + 1), _) ↔ (∀ j : Fin n, _) ∧ _
    constructor
    · intro hh
      exact ⟨fun j => hh ⟨j.val, by omega⟩, hh ⟨n, by omega⟩⟩
    · rintro ⟨hh, hn⟩ j
      by_cases hj : j.val < n
      · exact hh ⟨j.val, hj⟩
      · have hjn : j.val = n := by omega
        simpa only [argPrefixSplit, hjn] using hn
  rw [argNoSplitPrefixLaw, he, ← Measure.restrict_map (argPrefixSplit_measurable n)
    ((argNoSplitPrefixSet_measurable n).prod argNoSplitEvent_measurable)]
  have hmap : (argPrefixLaw R z (n + 1)).map (argPrefixSplit n) =
      ((eventProcess false R).pathLaw z).map
        (fun ω => ((fun k : Finset.Iic n => ω k.val), ω (n + 1))) := by
    rw [argPrefixLaw, Measure.map_map (argPrefixSplit_measurable n) (by fun_prop)]
    rfl
  rw [hmap, argPrefixLaw_next]
  ext t ht
  rw [Measure.restrict_apply ht,
    Measure.compProd_apply (ht.inter ((argNoSplitPrefixSet_measurable n).prod
      argNoSplitEvent_measurable)), Measure.compProd_apply ht]
  simp only [Kernel.restrict_apply, Measure.restrict_apply' argNoSplitEvent_measurable]
  have hsection (h : ARGPrefix n) :
      (eventProcess false R).stepSeq n h
        (Prod.mk h ⁻¹' (t ∩ argNoSplitPrefixSet n ×ˢ argNoSplitEvent)) =
      (argNoSplitPrefixSet n).indicator (fun h => (eventProcess false R).stepSeq n h
        ((Prod.mk h ⁻¹' t) ∩ argNoSplitEvent)) h := by
    classical
    by_cases hh : h ∈ argNoSplitPrefixSet n
    · rw [Set.indicator_of_mem hh]
      congr 1
      ext y
      simp [hh]
    · rw [Set.indicator_of_notMem hh]
      have hempty : Prod.mk h ⁻¹' (t ∩ argNoSplitPrefixSet n ×ˢ argNoSplitEvent) = ∅ := by
        ext y
        simp [hh]
      rw [hempty, measure_empty]
  simp_rw [hsection]
  rw [lintegral_indicator (argNoSplitPrefixSet_measurable n)]
  rfl
end Rhone.Coalescent.SmcSupport

namespace Rhone.Coalescent.SmcSupport
open MeasureTheory ProbabilityTheory IntervalProcess
open scoped ENNReal

noncomputable def argNoSplitPrefixWeight (R : ℝ) (n : ℕ) (h : ARGPrefix n) : ℝ≥0∞ :=
  ∏ j : Fin n, argNoSplitFactor R
    (h ⟨j.val, Finset.mem_Iic.mpr (by omega)⟩)
    (h ⟨j.val + 1, Finset.mem_Iic.mpr (by omega)⟩)

theorem argNoSplitPrefixWeight_measurable (R : ℝ) (n : ℕ) :
    Measurable (argNoSplitPrefixWeight R n) := by
  unfold argNoSplitPrefixWeight
  apply Finset.measurable_prod
  intro j _
  have hm := (argNoSplitFactor_joint_measurable R).comp
    (show Measurable (fun h : ARGPrefix n =>
      (h ⟨j.val, Finset.mem_Iic.mpr (by omega)⟩,
       h ⟨j.val + 1, Finset.mem_Iic.mpr (by omega)⟩)) from
         (measurable_pi_apply _).prodMk (measurable_pi_apply _))
  convert hm using 1
  funext h
  rfl

theorem argNoSplitPrefixWeight_join (R : ℝ) (n : ℕ) (p : ARGPrefix n × AugmentedState) :
    argNoSplitPrefixWeight R (n + 1) (argPrefixJoin n p) =
      argNoSplitPrefixWeight R n p.1 *
        argNoSplitFactor R (p.1 ⟨n, Finset.mem_Iic.mpr le_rfl⟩) p.2 := by
  unfold argNoSplitPrefixWeight
  rw [Fin.prod_univ_castSucc]
  apply congrArg₂ (· * ·)
  · apply Finset.prod_congr rfl
    intro j _
    simp only [argPrefixJoin, Fin.val_castSucc,
      dite_eq_left (show j.val ≤ n by omega),
      dite_eq_left (show j.val + 1 ≤ n by omega)]
  · simp [argPrefixJoin]

theorem argPrefixLaw_split_map (R : ℝ) (z : AugmentedState) (n : ℕ) :
    (argPrefixLaw R z (n + 1)).map (argPrefixSplit n) =
      (argPrefixLaw R z n).compProd ((eventProcess false R).stepSeq n) := by
  rw [argPrefixLaw, Measure.map_map (argPrefixSplit_measurable n) (by fun_prop)]
  exact argPrefixLaw_next R z n

theorem argPrefixSplit_withDensity (n : ℕ) (μ : Measure (ARGPrefix (n + 1)))
    (f : ARGPrefix (n + 1) → ℝ≥0∞) (hf : Measurable f) :
    (μ.withDensity f).map (argPrefixSplit n) =
      (μ.map (argPrefixSplit n)).withDensity (fun p => f (argPrefixJoin n p)) := by
  apply Measure.ext_of_lintegral
  intro g hg
  rw [lintegral_map hg (argPrefixSplit_measurable n),
    lintegral_withDensity_eq_lintegral_mul _ hf
      (show Measurable (fun h => g (argPrefixSplit n h)) from
        hg.comp (argPrefixSplit_measurable n)),
    lintegral_withDensity_eq_lintegral_mul _
      (show Measurable (fun p => f (argPrefixJoin n p)) from
        hf.comp (argPrefixJoin_measurable n)) hg,
    lintegral_map ((show Measurable (fun p => f (argPrefixJoin n p)) from
      hf.comp (argPrefixJoin_measurable n)).mul hg) (argPrefixSplit_measurable n)]
  apply lintegral_congr
  intro h
  change f h * g (argPrefixSplit n h) =
    f (argPrefixJoin n (argPrefixSplit n h)) * g (argPrefixSplit n h)
  rw [argPrefixJoin_split]

theorem argPrefixLaw_initial (R : ℝ) (z : AugmentedState) :
    argPrefixLaw R z 0 = Measure.dirac (fun _ => z) := by
  have he := Kernel.traj_map_frestrictLe_apply
    (X := fun _ : ℕ => AugmentedState) (κ := (eventProcess false R).stepSeq) 0 0 (fun _ => z)
  change argPrefixLaw R z 0 = _ at he
  simpa only [Kernel.partialTraj_self, Kernel.id_apply] using he

theorem argNoSplitPrefixLaw_density (R : ℝ) (hR : 0 ≤ R) (z : AugmentedState) (n : ℕ) :
    argNoSplitPrefixLaw R z n =
      (argPrefixLaw 0 z n).withDensity (argNoSplitPrefixWeight R n) := by
  induction n with
  | zero =>
    have hs : argNoSplitPrefixSet 0 = Set.univ := by ext h; simp [argNoSplitPrefixSet]
    have hw : argNoSplitPrefixWeight R 0 = fun _ => 1 := by
      funext h
      simp [argNoSplitPrefixWeight]
    simp [argNoSplitPrefixLaw, hs, argPrefixLaw_initial, hw]
  | succ n ih =>
    let g (h : ARGPrefix n) (y : AugmentedState) :=
      argNoSplitFactor R (h ⟨n, Finset.mem_Iic.mpr le_rfl⟩) y
    have hg : Measurable (Function.uncurry g) := by
      have hm := (argNoSplitFactor_joint_measurable R).comp
        (show Measurable (fun p : ARGPrefix n × AugmentedState =>
          (p.1 ⟨n, Finset.mem_Iic.mpr le_rfl⟩, p.2)) from
            ((measurable_pi_apply _).comp measurable_fst).prodMk measurable_snd)
      convert hm using 1
      funext p
      rfl
    have hk : ((eventProcess false R).stepSeq n).restrict argNoSplitEvent_measurable =
        ((eventProcess false 0).stepSeq n).withDensity g := by
      ext1 h
      rw [Kernel.restrict_apply, Kernel.withDensity_apply _ hg,
        Rhone.MarkovChain.DiscreteProcess.stepSeq, Kernel.comap_apply]
      exact eventKernel_noSplitFactor R hR _
    have : IsSFiniteKernel (((eventProcess false 0).stepSeq n).withDensity g) :=
      Kernel.IsSFiniteKernel.withDensity _ (fun _ _ => ENNReal.ofReal_ne_top)
    have hm : (argNoSplitPrefixLaw R z (n + 1)).map (argPrefixSplit n) =
        ((argPrefixLaw 0 z (n + 1)).withDensity
          (argNoSplitPrefixWeight R (n + 1))).map (argPrefixSplit n) := by
      rw [argNoSplitPrefixLaw_next_map, ih, hk,
        Measure.withDensity_compProd_withDensity (argNoSplitPrefixWeight_measurable R n) hg,
        argPrefixSplit_withDensity _ _ _ (argNoSplitPrefixWeight_measurable R (n + 1)),
        argPrefixLaw_split_map]
      congr 1
      funext p
      exact (argNoSplitPrefixWeight_join R n p).symm
    have he := congrArg (fun μ : Measure (ARGPrefix n × AugmentedState) =>
      μ.map (argPrefixJoin n)) hm
    rw [Measure.map_map (argPrefixJoin_measurable n) (argPrefixSplit_measurable n),
      Measure.map_map (argPrefixJoin_measurable n) (argPrefixSplit_measurable n)] at he
    have hid : argPrefixJoin n ∘ argPrefixSplit n = id := by
      funext h
      exact argPrefixJoin_split n h
    simpa only [hid, Measure.map_id] using he
end Rhone.Coalescent.SmcSupport
