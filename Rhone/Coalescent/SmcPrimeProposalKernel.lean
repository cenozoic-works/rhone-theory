/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeRegraftMeas
public import Rhone.Coalescent.FiniteIntervalMaterialKernel

/-!
# SMC′ marked proposal kernel

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 1–7. -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess MeasureTheory ProbabilityTheory

theorem attachmentTargetFiber_measurable (N m : ℕ) :
    Measurable (fun p : (Fin m → Branch N) × ℝ × ℝ =>
      attachmentTarget ⟨m, p.1⟩ p.2.1 p.2.2) := by
  classical
  let : MeasurableSpace (Option (Fin m)) := ⊤
  let P := (Fin m → Branch N) × ℝ × ℝ
  let A (p : P) : Finset (Fin m) := activeBranches ⟨m, p.1⟩ p.2.1
  have hA : Measurable A :=
    (activeBranchesFiber_measurable N m).comp (measurable_fst.prodMk measurable_snd.fst)
  let g (p : P) : Option (Fin m) := chooseByRate (fun _ => (1 : ℝ))
    (A p).toList (p.2.2 * (A p).card)
  have hg : Measurable g := by
    apply measurable_countable_choice A hA
      (fun a (p : P) => chooseByRate (fun _ => (1 : ℝ)) a.toList (p.2.2 * a.card))
    intro a
    exact chooseByRate_measurable (fun _ _ => (1 : ℝ)) (fun _ => measurable_const)
      a.toList (fun p : P => p.2.2 * a.card) (measurable_snd.snd.mul_const _)
  let f (a : Option (Fin m)) (p : P) : Finset (Fin N) :=
    match a with
    | none => Finset.univ
    | some i => (p.1 i).1
  have hf (a : Option (Fin m)) : Measurable (f a) := by
    cases a with
    | none => exact measurable_const
    | some i => exact ((measurable_pi_apply i).comp measurable_fst).fst
  have hchosen := measurable_countable_choice g hg f hf
  have hfinal : Measurable (fun p : P => if rootHeight ⟨m, p.1⟩ ≤ p.2.1 then
      Finset.univ else f (g p) p) :=
    measurable_const.piecewise
      (measurableSet_le ((rootHeightFiber_measurable N m).comp measurable_fst)
        measurable_snd.fst) hchosen
  convert hfinal using 1
  funext p
  unfold attachmentTarget
  dsimp only [A, g, f]
  split_ifs
  · rfl
  · cases chooseByRate (fun _ => (1 : ℝ))
      (activeBranches ⟨m, p.1⟩ p.2.1).toList
      (p.2.2 * (activeBranches ⟨m, p.1⟩ p.2.1).card) <;> simp

theorem proposalFiber_measurable (N m : ℕ) (R : ℝ) :
    Measurable (fun p : (Fin m → Branch N) × ProposalNoise => proposal R ⟨m, p.1⟩ p.2) := by
  classical
  let : MeasurableSpace (Option (Fin m)) := ⊤
  let P := (Fin m → Branch N) × ProposalNoise
  have hu (i : Fin 5) : Measurable (fun p : P => p.2 i) :=
    (measurable_pi_apply i).comp measurable_snd
  have hi (i : Fin m) : Measurable (fun p : P => p.1 i) :=
    (measurable_pi_apply i).comp measurable_fst
  have hlen : Measurable (fun p : P => treeLength ⟨m, p.1⟩) :=
    (treeLengthFiber_measurable N m).comp measurable_fst
  let g (p : P) : Option (Fin m) := chooseByRate (fun i => branchLength (p.1 i))
    (List.finRange m) (p.2 1 * treeLength ⟨m, p.1⟩)
  have hbl (i : Fin m) : Measurable (fun p : P => branchLength (p.1 i)) :=
    (branchLength_measurable N).comp (hi i)
  have hg : Measurable g :=
    chooseByRate_measurable (fun i (p : P) => branchLength (p.1 i))
      hbl (List.finRange m)
      (fun p : P => p.2 1 * treeLength ⟨m, p.1⟩) ((hu 1).mul hlen)
  let distance (p : P) := -Real.log (p.2 0) / (R / 2 * treeLength ⟨m, p.1⟩)
  have hd : Measurable distance :=
    (Real.measurable_log.comp (hu 0)).neg.div (measurable_const.mul hlen)
  let f (z : Option (Fin m)) (p : P) : Proposal N := match z with
    | none => (distance p, .inl (), ⟨m, p.1⟩)
    | some i =>
        let s := (p.1 i).1
        let t := (p.1 i).2.1 + ((p.1 i).2.2 - (p.1 i).2.1) * p.2 2
        let a := attachmentTime ⟨m, p.1⟩ t (-Real.log (p.2 3))
        let target := attachmentTarget ⟨m, p.1⟩ a (p.2 4)
        (distance p, .inr (s, t, a, target), regraft ⟨m, p.1⟩ s target t a)
  have hf (z : Option (Fin m)) : Measurable (f z) := by
    cases z with
    | none => exact hd.prodMk (measurable_const.prodMk
        ((measurable_sigma_mk (β := fun j => Fin j → Branch N) m).comp measurable_fst))
    | some i =>
      let t (p : P) := (p.1 i).2.1 + ((p.1 i).2.2 - (p.1 i).2.1) * p.2 2
      have ht : Measurable t :=
        (hi i).snd.fst.add (((hi i).snd.snd.sub (hi i).snd.fst).mul (hu 2))
      let a (p : P) := attachmentTime ⟨m, p.1⟩ (t p) (-Real.log (p.2 3))
      have ha : Measurable a := by
        convert (attachmentAuxFiber_measurable N m (2 * m + 1)).comp
          (measurable_fst.prodMk (ht.prodMk ((Real.measurable_log.comp (hu 3)).neg))) using 1
        funext p
        rfl
      let target (p : P) := attachmentTarget ⟨m, p.1⟩ (a p) (p.2 4)
      have htarget : Measurable target := by
        convert (attachmentTargetFiber_measurable N m).comp
          (measurable_fst.prodMk (ha.prodMk (hu 4))) using 1
        funext p
        rfl
      have hr : Measurable (fun p : P =>
          regraft ⟨m, p.1⟩ (p.1 i).1 (target p) (t p) (a p)) := by
        convert (regraftFiber_measurable N m).comp
          (measurable_fst.prodMk ((hi i).fst.prodMk (htarget.prodMk (ht.prodMk ha)))) using 1
        funext p
        rfl
      convert hd.prodMk ((measurable_inr.comp
        ((hi i).fst.prodMk (ht.prodMk (ha.prodMk htarget)))).prodMk hr) using 1
      funext p
      rfl
  convert measurable_countable_choice g hg f hf using 1
  funext p
  unfold proposal cutPoint
  dsimp only [g, f, distance]
  cases chooseByRate (fun i => branchLength (p.1 i)) (List.finRange m)
      (p.2 1 * treeLength ⟨m, p.1⟩) <;> simp

theorem proposal_measurable (N : ℕ) (R : ℝ) :
    Measurable (fun p : Tree N × ProposalNoise => proposal R p.1 p.2) := by
  apply measurable_prod_sigma_of_fibers
  intro m
  exact proposalFiber_measurable N m R

noncomputable def proposalNoiseLaw : Measure ProposalNoise :=
  Measure.pi (fun _ : Fin 5 => unitUniform)

instance proposalNoiseLaw_probability : IsProbabilityMeasure proposalNoiseLaw := by
  unfold proposalNoiseLaw
  infer_instance

noncomputable def proposalKernel (N : ℕ) (R : ℝ) : Kernel (Tree N) (Proposal N) :=
  (Kernel.id.prod (Kernel.const (Tree N) proposalNoiseLaw)).map
    (fun p => proposal R p.1 p.2)

instance proposalKernel_markov (N : ℕ) (R : ℝ) : IsMarkovKernel (proposalKernel N R) := by
  unfold proposalKernel
  exact Kernel.IsMarkovKernel.map _ (proposal_measurable N R)

end Rhone.Coalescent.SmcPrime
