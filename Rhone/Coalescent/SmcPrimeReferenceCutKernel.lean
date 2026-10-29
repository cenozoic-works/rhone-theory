/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeIndexedCutLaw
public import Mathlib.Probability.Independence.Basic
public import Rhone.Coalescent.SmcPrimeAttachmentLaw
public import Rhone.Coalescent.SmcPrimeKingmanTreeLaw
public import Mathlib.Probability.Kernel.WithDensity

/-!
# The indexed cut kernel of the one-split reference measure

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 1–7. -/

@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open MeasureTheory ProbabilityTheory IntervalProcess

theorem proposalNoiseLaw_grouped :
    proposalNoiseLaw.map (fun u => (u 0, ((u 1, u 2), (u 3, u 4)))) =
      unitUniform.prod ((unitUniform.prod unitUniform).prod (unitUniform.prod unitUniform)) := by
  classical
  have hi : iIndepFun (fun i (u : ProposalNoise) => u i) proposalNoiseLaw :=
    iIndepFun_pi (μ := fun _ : Fin 5 => unitUniform) (X := fun _ x => x)
      (fun _ => aemeasurable_id)
  have hev (i : Fin 5) : proposalNoiseLaw.map (fun u => u i) = unitUniform :=
    (measurePreserving_eval (fun _ : Fin 5 => unitUniform) i).map_eq
  have hpair (i j : Fin 5) (hij : i ≠ j) :
      proposalNoiseLaw.map (fun u => (u i, u j)) = unitUniform.prod unitUniform := by
    rw [(hi.indepFun hij).map_prod_eq_prod_map_map (measurable_pi_apply i).aemeasurable
      (measurable_pi_apply j).aemeasurable, hev, hev]
  have htwo : proposalNoiseLaw.map (fun u => ((u 1, u 2), (u 3, u 4))) =
      (unitUniform.prod unitUniform).prod (unitUniform.prod unitUniform) := by
    rw [(hi.indepFun_prodMk_prodMk (fun i => measurable_pi_apply i) 1 2 3 4
      (by decide) (by decide) (by decide) (by decide)).map_prod_eq_prod_map_map
      (by fun_prop) (by fun_prop), hpair 1 2 (by decide), hpair 3 4 (by decide)]
  let B : Finset (Fin 5) := {1, 2, 3, 4}
  have hd : Disjoint ({0} : Finset (Fin 5)) B := by simp [B]
  have hind := hi.indepFun_finset ({0} : Finset (Fin 5)) B hd
    (fun i => measurable_pi_apply i)
  have hrest : Measurable (fun v : B → ℝ =>
      ((v ⟨1, by simp [B]⟩, v ⟨2, by simp [B]⟩),
       (v ⟨3, by simp [B]⟩, v ⟨4, by simp [B]⟩))) := by fun_prop
  have hwhole : IndepFun (fun u : ProposalNoise => u 0)
      (fun u => ((u 1, u 2), (u 3, u 4))) proposalNoiseLaw :=
    hind.comp (measurable_pi_apply (⟨0, by simp⟩ : ({0} : Finset (Fin 5)))) hrest
  rw [hwhole.map_prod_eq_prod_map_map (measurable_pi_apply 0).aemeasurable
    (by fun_prop), hev, htwo]
end Rhone.Coalescent.SmcPrime

@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open MeasureTheory ProbabilityTheory IntervalProcess
open scoped ENNReal

theorem indexedCutValue_joint_measurable (N : ℕ) :
    Measurable (fun p : Tree N × (ℝ × ℝ) => indexedCutValue p.1 p.2) := by
  apply measurable_prod_sigma_of_fibers
  intro m
  classical
  let : MeasurableSpace (Option (Fin m)) := ⊤
  let P := (Fin m → Branch N) × (ℝ × ℝ)
  let g (p : P) := chooseByRate (fun i => branchLength (p.1 i))
    (List.finRange m) (p.2.1 * treeLength ⟨m, p.1⟩)
  have hg : Measurable g := chooseByRate_measurable
    (fun i (p : P) => branchLength (p.1 i))
    (fun i => (branchLength_measurable N).comp ((measurable_pi_apply i).comp measurable_fst))
    (List.finRange m) (fun p : P => p.2.1 * treeLength ⟨m, p.1⟩)
    (measurable_snd.fst.mul ((treeLengthFiber_measurable N m).comp measurable_fst))
  let f (a : Option (Fin m)) (p : P) : ℕ × ℝ := match a with
    | none => (m, 0)
    | some i => (i.val, (p.1 i).2.1 + ((p.1 i).2.2 - (p.1 i).2.1) * p.2.2)
  have hf (a : Option (Fin m)) : Measurable (f a) := by
    cases a <;> dsimp [f, P] <;> fun_prop
  convert measurable_countable_choice g hg f hf using 1
  funext p
  simp only [indexedCutValue, g, f]
  cases chooseByRate (fun i => branchLength (p.1 i)) (List.finRange m)
    (p.2.1 * treeLength ⟨m, p.1⟩) <;> rfl

theorem treeLength_joint_measurable (N : ℕ) : Measurable (@treeLength N) := by
  apply measurable_sigma_of_fibers
  intro m
  exact treeLengthFiber_measurable N m

theorem attachmentMark_joint_measurable (N : ℕ) :
    Measurable (fun p : Tree N × ℝ × (ℝ × ℝ) =>
      let a := attachmentTime p.1 p.2.1 (-Real.log p.2.2.1)
      (a, attachmentTarget p.1 a p.2.2.2)) := by
  apply measurable_prod_sigma_of_fibers
  intro m
  let P := (Fin m → Branch N) × ℝ × (ℝ × ℝ)
  let a (p : P) := attachmentTime ⟨m, p.1⟩ p.2.1 (-Real.log p.2.2.1)
  have ha : Measurable a := by
    convert (attachmentAuxFiber_measurable N m (2 * m + 1)).comp
      (measurable_fst.prodMk (measurable_snd.fst.prodMk
        (Real.measurable_log.comp measurable_snd.snd.fst).neg)) using 1
    funext p
    rfl
  convert ha.prodMk ((attachmentTargetFiber_measurable N m).comp
    (measurable_fst.prodMk (ha.prodMk measurable_snd.snd.snd))) using 1
  funext p
  rfl

theorem indexedTreeCutMeasure_zero {N : ℕ} (T : Tree N) (hL : treeLength T = 0) :
    indexedTreeCutMeasure T = 0 := by
  classical
  unfold indexedTreeCutMeasure
  apply Finset.sum_eq_zero
  intro i _
  have hi : branchLength (T.2 i) = 0 := by
    have hle : branchLength (T.2 i) ≤ treeLength T :=
      Finset.single_le_sum (fun j _ => branchLength_nonneg (T.2 j)) (Finset.mem_univ i)
    exact le_antisymm (hL ▸ hle) (branchLength_nonneg _)
  by_cases hp : (T.2 i).1 = ∅ ∨ (T.2 i).1 = Finset.univ
  · simp [indexedBranchCutMeasure, hp]
  · have hm : max 0 ((T.2 i).2.2 - (T.2 i).2.1) = 0 := by
      simpa only [branchLength, ite_eq_right hp] using hi
    have hle := le_max_right 0 ((T.2 i).2.2 - (T.2 i).2.1)
    rw [hm] at hle
    simp [indexedBranchCutMeasure, hp, Set.Ioo_eq_empty_of_le (sub_nonpos.mp hle)]

theorem indexedCutPoint_unnormalized_law {N : ℕ} (T : Tree N) :
    ENNReal.ofReal (treeLength T) •
      (unitUniform.prod unitUniform).map (indexedCutValue T) = indexedTreeCutMeasure T := by
  by_cases hL : 0 < treeLength T
  · rw [indexedCutPoint_uniform_law T hL, smul_smul,
      ← ENNReal.ofReal_mul hL.le, mul_inv_cancel₀ hL.ne', ENNReal.ofReal_one, one_smul]
  · have hz : treeLength T = 0 := le_antisymm (le_of_not_gt hL) (treeLength_nonneg T)
    simp [hz, indexedTreeCutMeasure_zero T hz]

noncomputable def indexedUniformCutKernel (N : ℕ) : Kernel (Tree N) (ℕ × ℝ) :=
  (Kernel.id.prod (Kernel.const (Tree N) (unitUniform.prod unitUniform))).map
    (fun p => indexedCutValue p.1 p.2)

instance indexedUniformCutKernel_markov (N : ℕ) : IsMarkovKernel (indexedUniformCutKernel N) :=
  Kernel.IsMarkovKernel.map _ (indexedCutValue_joint_measurable N)

noncomputable def indexedTreeCutKernel (N : ℕ) : Kernel (Tree N) (ℕ × ℝ) :=
  (indexedUniformCutKernel N).withDensity (fun T _ => ENNReal.ofReal (treeLength T))

instance indexedTreeCutKernel_sfinite (N : ℕ) : IsSFiniteKernel (indexedTreeCutKernel N) :=
  Kernel.IsSFiniteKernel.withDensity _ (fun _ _ => ENNReal.ofReal_ne_top)

theorem indexedTreeCutKernel_apply (N : ℕ) (T : Tree N) :
    indexedTreeCutKernel N T = indexedTreeCutMeasure T := by
  rw [indexedTreeCutKernel, Kernel.withDensity_apply _
    ((treeLength_joint_measurable N).comp measurable_fst).ennreal_ofReal,
    withDensity_const, indexedUniformCutKernel,
    Kernel.map_apply _ (indexedCutValue_joint_measurable N), Kernel.prod_apply,
    Kernel.id_apply, Kernel.const_apply, Measure.dirac_prod,
    Measure.map_map (indexedCutValue_joint_measurable N) measurable_prodMk_left]
  exact indexedCutPoint_unnormalized_law T

instance indexedTreeCutMeasure_sfinite {N : ℕ} (T : Tree N) :
    SFinite (indexedTreeCutMeasure T) := by
  rw [← indexedTreeCutKernel_apply N T]
  infer_instance

theorem indexedTreeCutMeasure_measurable (N : ℕ) : Measurable (@indexedTreeCutMeasure N) := by
  convert (indexedTreeCutKernel N).measurable using 1
  funext T
  exact (indexedTreeCutKernel_apply N T).symm
end Rhone.Coalescent.SmcPrime
