/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeSpatialSource
public import Mathlib.MeasureTheory.Constructions.Projective

/-!
# The independent proposal stream induces the spatial trajectory law

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 1–7. -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open MeasureTheory ProbabilityTheory Finset Preorder

private def spatialAppend (N n : ℕ) (p : Iic n → SpatialState N)
    (y : SpatialState N) (i : Iic (n + 1)) : SpatialState N :=
  if h : i.val ≤ n then p ⟨i.val, mem_Iic.mpr h⟩ else y

private theorem spatialAppend_measurable (N n : ℕ) :
    Measurable (fun py : (Iic n → SpatialState N) × SpatialState N =>
      spatialAppend N n py.1 py.2) := by
  apply measurable_pi_iff.mpr
  intro i
  by_cases h : i.val ≤ n
  · simp only [spatialAppend, dite_eq_left h]
    exact (measurable_pi_apply (⟨i.val, mem_Iic.mpr h⟩ : Iic n)).comp measurable_fst
  · simpa [spatialAppend, h] using (measurable_snd : Measurable (fun py :
      (Iic n → SpatialState N) × SpatialState N => py.2))

private theorem sourceSpatialRun_congr (N : ℕ) (R : ℝ) (z : SpatialState N)
    (u v : ℕ → ProposalNoise) (n : ℕ) (h : ∀ j < n, u j = v j) :
    sourceSpatialRun N R z u n = sourceSpatialRun N R z v n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sourceSpatialRun]
    rw [ih (fun j hj => h j (Nat.lt_succ_of_lt hj)), h n (Nat.lt_succ_self n)]

private noncomputable def sourcePrefix (N : ℕ) (R : ℝ) (z : SpatialState N) (n : ℕ)
    (u : ℕ → ProposalNoise) : Iic n → SpatialState N := frestrictLe n (sourceSpatialRun N R z u)

private theorem sourcePrefix_measurable (N : ℕ) (R : ℝ) (z : SpatialState N) (n : ℕ) :
    Measurable (sourcePrefix N R z n) :=
  (measurable_frestrictLe n).comp (sourceSpatialRun_measurable N R z)

private def padSource (n : ℕ) (v : range n → ProposalNoise) (j : ℕ) : ProposalNoise :=
  if h : j ∈ range n then v ⟨j, h⟩ else fun _ => 0

private theorem padSource_measurable (n : ℕ) : Measurable (padSource n) := by
  apply measurable_pi_iff.mpr
  intro j
  by_cases h : j ∈ range n
  · simpa [padSource, h] using (measurable_pi_apply (⟨j, h⟩ : range n))
  · simp only [padSource, dite_eq_right h]
    exact measurable_const

private theorem sourcePrefix_noise_independent (N : ℕ) (R : ℝ) (z : SpatialState N) (n : ℕ) :
    IndepFun (sourcePrefix N R z n) (fun u => u n) sourceProposalStreamLaw := by
  have hi : iIndepFun (fun j (u : ℕ → ProposalNoise) => u j) sourceProposalStreamLaw :=
    iIndepFun_infinitePi (P := fun _ : ℕ => proposalNoiseLaw) (X := fun _ u => u)
      (fun _ => measurable_id)
  have hid := hi.indepFun_finset (range n) {n}
    (disjoint_singleton_right.mpr notMem_range_self) (fun j => measurable_pi_apply j)
  have hc := hid.comp
    ((sourcePrefix_measurable N R z n).comp (padSource_measurable n))
    (measurable_pi_apply ⟨n, mem_singleton_self n⟩)
  convert hc using 1
  · funext u i
    apply sourceSpatialRun_congr
    intro j hj
    simp only [padSource,
      dite_eq_left (mem_range.mpr (lt_of_lt_of_le hj (mem_Iic.mp i.property)))]
  · rfl

private theorem spatialKernel_apply_source (N : ℕ) (R : ℝ) (z : SpatialState N) :
    spatialKernel N R z = proposalNoiseLaw.map (spatialStep N R z) := by
  rw [spatialKernel, Kernel.map_apply _ (spatialStep_measurable N R),
    Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply, Measure.dirac_prod,
    Measure.map_map (spatialStep_measurable N R) measurable_prodMk_left]
  rfl

private theorem spatialExtension_apply (N : ℕ) (R : ℝ) (n : ℕ)
    (p : Iic n → SpatialState N) :
    Kernel.partialTraj (X := fun _ => SpatialState N) (spatialProcess N R).stepSeq n (n + 1) p =
      proposalNoiseLaw.map (fun u => spatialAppend N n p
        (spatialStep N R (p ⟨n, mem_Iic.mpr le_rfl⟩) u)) := by
  rw [Kernel.partialTraj_succ_self, Kernel.map_apply _
    (measurable_IicProdIoc (X := fun _ => SpatialState N) (m := n) (n := n + 1)),
    Kernel.prod_apply, Kernel.id_apply, Measure.dirac_prod,
    Measure.map_map (measurable_IicProdIoc (X := fun _ => SpatialState N) (m := n) (n := n + 1))
      measurable_prodMk_left,
    Kernel.map_apply _ (MeasurableEquiv.piSingleton (X := fun _ => SpatialState N) n).measurable,
    Measure.map_map
      ((measurable_IicProdIoc (X := fun _ => SpatialState N) (m := n) (n := n + 1)).comp
        measurable_prodMk_left)
      (MeasurableEquiv.piSingleton (X := fun _ => SpatialState N) n).measurable]
  change ((spatialKernel N R (p ⟨n, mem_Iic.mpr le_rfl⟩)).map _) = _
  rw [spatialKernel_apply_source]
  rw [Measure.map_map (f := spatialStep N R (p ⟨n, mem_Iic.mpr le_rfl⟩))
    (((measurable_IicProdIoc (X := fun _ => SpatialState N) (m := n) (n := n + 1)).comp
      measurable_prodMk_left).comp
      (MeasurableEquiv.piSingleton (X := fun _ => SpatialState N) n).measurable)
    ((spatialStep_measurable N R).comp (measurable_const.prodMk measurable_id))]
  congr 1
  funext u i
  dsimp [spatialAppend, Function.comp_def, IicProdIoc]
  split_ifs
  · rfl
  · simp [MeasurableEquiv.piSingleton]

private theorem sourcePrefix_succ_law (N : ℕ) (R : ℝ) (z : SpatialState N) (n : ℕ) :
    sourceProposalStreamLaw.map (sourcePrefix N R z (n + 1)) =
      Kernel.partialTraj (X := fun _ => SpatialState N) (spatialProcess N R).stepSeq n (n + 1)
        ∘ₘ (sourceProposalStreamLaw.map (sourcePrefix N R z n)) := by
  let F (pu : (Iic n → SpatialState N) × ProposalNoise) := spatialAppend N n pu.1
    (spatialStep N R (pu.1 ⟨n, mem_Iic.mpr le_rfl⟩) pu.2)
  have hF : Measurable F := (spatialAppend_measurable N n).comp
    (measurable_fst.prodMk ((spatialStep_measurable N R).comp
      (((measurable_pi_apply (⟨n, mem_Iic.mpr le_rfl⟩ : Iic n)).comp
        measurable_fst).prodMk measurable_snd)))
  have heq : sourcePrefix N R z (n + 1) =
      F ∘ (fun u => (sourcePrefix N R z n u, u n)) := by
    funext u i
    dsimp [sourcePrefix, F, spatialAppend, frestrictLe]
    split_ifs with h
    · rfl
    · have hi : i.val = n + 1 := by have := mem_Iic.mp i.property; omega
      rw [hi]
      rfl
  rw [heq, ← Measure.map_map hF
    ((sourcePrefix_measurable N R z n).prodMk (measurable_pi_apply n)),
    (sourcePrefix_noise_independent N R z n).map_prod_eq_prod_map_map
      (sourcePrefix_measurable N R z n).aemeasurable (measurable_pi_apply n).aemeasurable,
    show sourceProposalStreamLaw.map (fun u => u n) = proposalNoiseLaw from
      Measure.infinitePi_map_eval (fun _ : ℕ => proposalNoiseLaw) n,
    ← Measure.compProd_const, Measure.compProd_eq_comp_prod, Measure.map_comp _ _ hF]
  congr 1
  ext1 p
  rw [Kernel.map_apply _ hF, Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply,
    Measure.dirac_prod, Measure.map_map hF measurable_prodMk_left, spatialExtension_apply]
  rfl

private theorem sourcePrefix_law (N : ℕ) (R : ℝ) (z : SpatialState N) (n : ℕ) :
    sourceProposalStreamLaw.map (sourcePrefix N R z n) =
      Kernel.partialTraj (X := fun _ => SpatialState N) (spatialProcess N R).stepSeq 0 n
        (fun _ => z) := by
  induction n with
  | zero =>
    have he : sourcePrefix N R z 0 = fun _ _ => z := by
      funext u i
      have hi : i.val = 0 := by have := mem_Iic.mp i.property; omega
      dsimp [sourcePrefix, frestrictLe]
      rw [hi]
      rfl
    rw [he, Measure.map_const, measure_univ, one_smul, Kernel.partialTraj_self, Kernel.id_apply]
  | succ n ih =>
    rw [sourcePrefix_succ_law, ih, Kernel.partialTraj_succ_eq_comp (Nat.zero_le n),
      Kernel.comp_apply]

/-- Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 1–7. -/
theorem sourceSpatialRun_law (N : ℕ) (R : ℝ) (z : SpatialState N) :
    sourceProposalStreamLaw.map (sourceSpatialRun N R z) = (spatialProcess N R).pathLaw z := by
  apply IsProjectiveLimit.unique (P := fun I => ((spatialProcess N R).pathLaw z).map I.restrict)
    (fun I => ?_) (fun I => rfl)
  have hn : I ⊆ Finset.Iic (I.sup id) := fun i hi => Finset.mem_Iic.mpr (Finset.le_sup (f := id) hi)
  have hcomp : (I.restrict : (ℕ → SpatialState N) → _) =
      Finset.restrict₂ hn ∘ (frestrictLe (I.sup id)) := rfl
  change (sourceProposalStreamLaw.map (sourceSpatialRun N R z)).map I.restrict = _
  rw [hcomp, ← Measure.map_map (Finset.measurable_restrict₂ hn) (measurable_frestrictLe _),
    Measure.map_map (measurable_frestrictLe _) (sourceSpatialRun_measurable N R z)]
  change (sourceProposalStreamLaw.map (sourcePrefix N R z (I.sup id))).map _ = _
  rw [sourcePrefix_law, (spatialProcess N R).pathLaw_eq,
    ← Kernel.traj_map_frestrictLe_apply,
    Measure.map_map (Finset.measurable_restrict₂ hn) (measurable_frestrictLe _)]
  exact congrArg (fun f => ((spatialProcess N R).pathLaw z).map f) hcomp.symm
end Rhone.Coalescent.SmcPrime
