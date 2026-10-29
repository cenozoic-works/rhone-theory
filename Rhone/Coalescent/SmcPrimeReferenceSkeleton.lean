/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeReferenceCutKernel

/-!
# The one-split reference measure and its tail and cut kernels

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 1–7. -/

@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open MeasureTheory ProbabilityTheory IntervalProcess
open scoped ENNReal

noncomputable def oneSplitReferenceFiber (N : ℕ) (h : KingmanHistory N) :
    Measure (OneSplitSkeleton N) :=
  let T := metricTreeFromHistory N h
  (indexedTreeCutMeasure T).bind (fun bt =>
    ((volume.restrict (Set.Ioo (0 : ℝ) 1)).prod (attachmentUniformLaw T bt.2)).map
      (fun xa => (h, bt.1, bt.2, xa.1, xa.2.1, xa.2.2)))

noncomputable def oneSplitReferenceMeasure (N : ℕ) : Measure (OneSplitSkeleton N) :=
  (kingmanHistoryLaw N).bind (oneSplitReferenceFiber N)

noncomputable def oneSplitTailMap (N : ℕ)
    (p : (KingmanHistory N × (ℕ × ℝ)) × (ℝ × (ℝ × ℝ))) : OneSplitSkeleton N :=
  let T := metricTreeFromHistory N p.1.1
  let a := attachmentTime T p.1.2.2 (-Real.log p.2.2.1)
  (p.1.1, p.1.2.1, p.1.2.2, p.2.1, a, attachmentTarget T a p.2.2.2)

theorem oneSplitTailMap_measurable (N : ℕ) : Measurable (oneSplitTailMap N) := by
  let P := (KingmanHistory N × (ℕ × ℝ)) × (ℝ × (ℝ × ℝ))
  have hm : Measurable (fun p : P =>
      let a := attachmentTime (metricTreeFromHistory N p.1.1) p.1.2.2 (-Real.log p.2.2.1)
      (a, attachmentTarget (metricTreeFromHistory N p.1.1) a p.2.2.2)) :=
    (attachmentMark_joint_measurable N).comp
    (((metricTreeFromHistory_measurable N).comp measurable_fst.fst).prodMk
      (measurable_fst.snd.snd.prodMk measurable_snd.snd))
  exact measurable_fst.fst.prodMk (measurable_fst.snd.fst.prodMk
    (measurable_fst.snd.snd.prodMk (measurable_snd.fst.prodMk hm)))

noncomputable def oneSplitTailKernel (N : ℕ) :
    Kernel (KingmanHistory N × (ℕ × ℝ)) (OneSplitSkeleton N) :=
  (Kernel.id.prod (Kernel.const _ (unitUniform.prod (unitUniform.prod unitUniform)))).map
    (oneSplitTailMap N)

instance oneSplitTailKernel_markov (N : ℕ) : IsMarkovKernel (oneSplitTailKernel N) :=
  Kernel.IsMarkovKernel.map _ (oneSplitTailMap_measurable N)

theorem oneSplitTailKernel_apply (N : ℕ) (h : KingmanHistory N) (bt : ℕ × ℝ) :
    oneSplitTailKernel N (h, bt) =
      ((volume.restrict (Set.Ioo (0 : ℝ) 1)).prod
        (attachmentUniformLaw (metricTreeFromHistory N h) bt.2)).map
          (fun xa => (h, bt.1, bt.2, xa.1, xa.2.1, xa.2.2)) := by
  rw [oneSplitTailKernel, Kernel.map_apply _ (oneSplitTailMap_measurable N),
    Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply, Measure.dirac_prod,
    Measure.map_map (oneSplitTailMap_measurable N) measurable_prodMk_left]
  let T := metricTreeFromHistory N h
  let a (uv : ℝ × ℝ) :=
    let t := attachmentTime T bt.2 (-Real.log uv.1)
    (t, attachmentTarget T t uv.2)
  have ha : Measurable a := measurable_attachmentUniformMap T bt.2
  change (unitUniform.prod (unitUniform.prod unitUniform)).map _ =
    (unitUniform.prod ((unitUniform.prod unitUniform).map a)).map _
  have hprod := Measure.map_prod_map unitUniform (unitUniform.prod unitUniform) measurable_id ha
  rw [Measure.map_id] at hprod
  rw [hprod, Measure.map_map (by fun_prop) (measurable_id.prodMap ha)]
  rfl

noncomputable def oneSplitCutKernel (N : ℕ) :
    Kernel (KingmanHistory N) (KingmanHistory N × (ℕ × ℝ)) :=
  Kernel.id.prod ((indexedTreeCutKernel N).comap
    (metricTreeFromHistory N) (metricTreeFromHistory_measurable N))

instance oneSplitCutKernel_sfinite (N : ℕ) : IsSFiniteKernel (oneSplitCutKernel N) := by
  unfold oneSplitCutKernel
  infer_instance

noncomputable def oneSplitReferenceKernel (N : ℕ) :
    Kernel (KingmanHistory N) (OneSplitSkeleton N) :=
  oneSplitTailKernel N ∘ₖ oneSplitCutKernel N

instance oneSplitReferenceKernel_sfinite (N : ℕ) : IsSFiniteKernel (oneSplitReferenceKernel N) := by
  unfold oneSplitReferenceKernel
  infer_instance

theorem oneSplitReferenceKernel_apply (N : ℕ) (h : KingmanHistory N) :
    oneSplitReferenceKernel N h = oneSplitReferenceFiber N h := by
  rw [oneSplitReferenceKernel, Kernel.comp_apply, oneSplitCutKernel, Kernel.prod_apply,
    Kernel.id_apply, Kernel.comap_apply, indexedTreeCutKernel_apply, Measure.dirac_prod]
  ext s hs
  rw [Measure.bind_apply hs (oneSplitTailKernel N).measurable.aemeasurable,
    lintegral_map ((oneSplitTailKernel N).measurable_coe hs) measurable_prodMk_left]
  unfold oneSplitReferenceFiber
  rw [Measure.bind_apply hs]
  · congr 1
    funext bt
    rw [oneSplitTailKernel_apply]
  · have hm : Measurable (fun bt : ℕ × ℝ => oneSplitTailKernel N (h, bt)) :=
      (oneSplitTailKernel N).measurable.comp measurable_prodMk_left
    simpa only [oneSplitTailKernel_apply] using hm.aemeasurable

theorem oneSplitReferenceFiber_measurable (N : ℕ) : Measurable (oneSplitReferenceFiber N) := by
  convert (oneSplitReferenceKernel N).measurable using 1
  funext h
  exact (oneSplitReferenceKernel_apply N h).symm
end Rhone.Coalescent.SmcPrime

@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open MeasureTheory ProbabilityTheory IntervalProcess
open scoped ENNReal

noncomputable def oneSplitReferenceSourceMap (N : ℕ) (h : KingmanHistory N)
    (p : (ℝ × ℝ) × (ℝ × (ℝ × ℝ))) : OneSplitSkeleton N :=
  oneSplitTailMap N ((h, indexedCutValue (metricTreeFromHistory N h) p.1), p.2)

theorem oneSplitReferenceSourceMap_measurable (N : ℕ) (h : KingmanHistory N) :
    Measurable (oneSplitReferenceSourceMap N h) :=
  (oneSplitTailMap_measurable N).comp
    ((measurable_const.prodMk ((indexedCutValue_measurable _).comp measurable_fst)).prodMk
      measurable_snd)

theorem oneSplitReferenceFiber_source (N : ℕ) (h : KingmanHistory N) :
    oneSplitReferenceFiber N h = ENNReal.ofReal (treeLength (metricTreeFromHistory N h)) •
      ((unitUniform.prod unitUniform).prod
        (unitUniform.prod (unitUniform.prod unitUniform))).map
          (oneSplitReferenceSourceMap N h) := by
  let T := metricTreeFromHistory N h
  have hk : Measurable (fun bt : ℕ × ℝ => oneSplitTailKernel N (h, bt)) :=
    (oneSplitTailKernel N).measurable.comp measurable_prodMk_left
  have heq : oneSplitReferenceFiber N h =
      (indexedTreeCutMeasure T).bind (fun bt => oneSplitTailKernel N (h, bt)) := by
    simp only [oneSplitReferenceFiber, oneSplitTailKernel_apply, T]
  rw [heq, ← indexedCutPoint_unnormalized_law T, Measure.bind_smul _ _ hk.aemeasurable]
  congr 1
  ext s hs
  rw [Measure.bind_apply hs hk.aemeasurable,
    lintegral_map
      (show Measurable (fun bt : ℕ × ℝ => oneSplitTailKernel N (h, bt) s) from
        ((oneSplitTailKernel N).measurable_coe hs).comp measurable_prodMk_left)
      (indexedCutValue_measurable T),
    Measure.map_apply (oneSplitReferenceSourceMap_measurable N h) hs,
    Measure.prod_apply ((oneSplitReferenceSourceMap_measurable N h) hs)]
  apply lintegral_congr
  intro uv
  rw [oneSplitTailKernel, Kernel.map_apply _ (oneSplitTailMap_measurable N),
    Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply, Measure.dirac_prod,
    Measure.map_map (oneSplitTailMap_measurable N) measurable_prodMk_left,
    Measure.map_apply ((oneSplitTailMap_measurable N).comp measurable_prodMk_left) hs]
  rfl

instance oneSplitReferenceFiber_sfinite (N : ℕ) (h : KingmanHistory N) :
    SFinite (oneSplitReferenceFiber N h) := by
  rw [← oneSplitReferenceKernel_apply]
  infer_instance

instance oneSplitReferenceMeasure_sfinite (N : ℕ) : SFinite (oneSplitReferenceMeasure N) := by
  have he : oneSplitReferenceMeasure N = oneSplitReferenceKernel N ∘ₘ kingmanHistoryLaw N := by
    unfold oneSplitReferenceMeasure
    congr 1
    funext h
    exact (oneSplitReferenceKernel_apply N h).symm
  rw [he]
  infer_instance
end Rhone.Coalescent.SmcPrime
