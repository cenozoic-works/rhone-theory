/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcSupport.BarrierProcess
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! # Common-noise coupling of the two sampler modes -/
@[expose] public section
namespace Rhone.Coalescent.SmcSupport
open IntervalProcess MeasureTheory ProbabilityTheory

theorem sigma_measurableEq {ι : Type*} [Countable ι] {β : ι → Type*}
    [∀ i, MeasurableSpace (β i)] [∀ i, MeasurableEq (β i)] :
    MeasurableEq (Sigma β) := by
  classical
  constructor
  apply measurableSet_prod_sigma_of_fibers
  intro i
  have h : MeasurableSet {p : Sigma β × β i | (⟨i,p.2⟩ : Sigma β) = p.1} := by
    apply measurableSet_prod_sigma_of_fibers
    intro j
    by_cases hij : i = j
    · subst j
      simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using
        (measurableSet_eq_fun measurable_snd measurable_fst :
        MeasurableSet {p : β i × β i | p.2 = p.1})
    · have he : {p : β j × β i | (⟨i, p.2⟩ : Sigma β) = ⟨j, p.1⟩} = ∅ := by
        ext p
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        intro hp
        exact hij (congrArg Sigma.fst hp)
      change MeasurableSet {p : β j × β i | (⟨i, p.2⟩ : Sigma β) = ⟨j, p.1⟩}
      rw [he]
      exact MeasurableSet.empty
  exact h.preimage measurable_swap

instance product_measurableEq {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableEq α] [MeasurableEq β] : MeasurableEq (α × β) := by
  constructor
  change MeasurableSet {p : (α × β) × (α × β) | p.1 = p.2}
  have h := (measurableSet_eq_fun
    (show Measurable (fun p : (α × β) × (α × β) => p.1.1) from measurable_fst.fst)
    measurable_snd.fst).inter
    (measurableSet_eq_fun measurable_fst.snd measurable_snd.snd)
  simpa only [Prod.ext_iff, Set.ofPred_and] using h

instance pi_measurableEq {ι : Type*} [Countable ι] {β : ι → Type*}
    [∀ i, MeasurableSpace (β i)] [∀ i, MeasurableEq (β i)] : MeasurableEq (∀ i, β i) := by
  constructor
  change MeasurableSet {p : (∀ i, β i) × (∀ i, β i) | p.1 = p.2}
  have h := measurableSet_forall (fun p : (∀ i, β i) × (∀ i, β i) =>
    fun i => p.1 i = p.2 i) (fun i => measurableSet_eq_fun
      ((measurable_pi_apply i).comp measurable_fst)
      ((measurable_pi_apply i).comp measurable_snd))
  simpa only [funext_iff] using h

instance sum_measurableEq {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableEq α] [MeasurableEq β] : MeasurableEq (α ⊕ β) := by
  constructor
  let e := MeasurableEquiv.sumProdSum α β α β
  have h : MeasurableSet {p | e.symm p ∈ Set.diagonal (α ⊕ β)} := by
    apply measurableSet_sum_iff.mpr
    constructor <;> apply measurableSet_sum_iff.mpr <;> constructor
    · change MeasurableSet {p : α × α | Sum.inl p.1 = (Sum.inl p.2 : α ⊕ β)}
      simpa only [Sum.inl.injEq, Set.diagonal] using
        (measurableSet_diagonal : MeasurableSet (Set.diagonal α))
    · change MeasurableSet {p : α × β | Sum.inl p.1 = (Sum.inr p.2 : α ⊕ β)}
      simp
    · change MeasurableSet {p : β × α | Sum.inr p.1 = (Sum.inl p.2 : α ⊕ β)}
      simp
    · change MeasurableSet {p : β × β | Sum.inr p.1 = (Sum.inr p.2 : α ⊕ β)}
      simpa only [Sum.inr.injEq, Set.diagonal] using
        (measurableSet_diagonal : MeasurableSet (Set.diagonal β))
  change MeasurableSet {p : (α ⊕ β) × (α ⊕ β) | p.1 = p.2}
  convert h.preimage e.measurable using 1
  ext p
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, e.symm_apply_apply, Set.mem_diagonal_iff]

instance material_measurableEq : MeasurableEq Material := sigma_measurableEq
instance liveState_measurableEq : MeasurableEq LiveState := sigma_measurableEq

instance trackedState_measurableEq : MeasurableEq TrackedState := inferInstance

abbrev JointState := TrackedState × TrackedState

instance : MeasurableSpace JointState :=
  inferInstanceAs (MeasurableSpace (TrackedState × TrackedState))

instance jointState_measurableEq : MeasurableEq JointState := product_measurableEq

def leftPath (ω : ℕ → JointState) : ℕ → TrackedState := fun k => (ω k).1

def rightPath (ω : ℕ → JointState) : ℕ → TrackedState := fun k => (ω k).2

noncomputable def jointSampleStep (R : ℝ) (z : JointState) (u : Noise) : JointState :=
  (trackedSampleStep false R z.1 u, trackedSampleStep true R z.2 u)

theorem jointSampleStep_measurable (R : ℝ) :
    Measurable (fun p : JointState × Noise => jointSampleStep R p.1 p.2) := by
  exact ((trackedSampleStep_measurable false R).comp
    (measurable_fst.fst.prodMk measurable_snd)).prodMk
    ((trackedSampleStep_measurable true R).comp
      (measurable_fst.snd.prodMk measurable_snd))

noncomputable def jointSamplerKernel (R : ℝ) : Kernel JointState JointState :=
  (Kernel.id.prod (Kernel.const JointState noiseLaw)).map
    (fun p => jointSampleStep R p.1 p.2)

instance jointSamplerKernel_markov (R : ℝ) : IsMarkovKernel (jointSamplerKernel R) := by
  unfold jointSamplerKernel
  exact Kernel.IsMarkovKernel.map _ (jointSampleStep_measurable R)

theorem jointSamplerKernel_apply (R : ℝ) (z : JointState) :
    jointSamplerKernel R z = noiseLaw.map (jointSampleStep R z) := by
  rw [jointSamplerKernel, Kernel.map_apply _ (jointSampleStep_measurable R),
    Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply, Measure.dirac_prod,
    Measure.map_map (jointSampleStep_measurable R) measurable_prodMk_left]
  rfl

noncomputable def jointSamplerProcess (R : ℝ) : Rhone.MarkovChain.DiscreteProcess JointState :=
  ⟨jointSamplerKernel R⟩

def jointInitial (n : ℕ) : JointState := (trackedInitial n, trackedInitial n)

theorem jointSamplerKernel_left (R : ℝ) (z : JointState) :
    (jointSamplerKernel R z).map Prod.fst = samplerKernel false R z.1 := by
  rw [jointSamplerKernel_apply, samplerKernel_apply,
    Measure.map_map measurable_fst
      (show Measurable (jointSampleStep R z) from
        (jointSampleStep_measurable R).comp (measurable_const.prodMk measurable_id))]
  rfl

theorem jointSamplerKernel_right (R : ℝ) (z : JointState) :
    (jointSamplerKernel R z).map Prod.snd = samplerKernel true R z.2 := by
  rw [jointSamplerKernel_apply, samplerKernel_apply,
    Measure.map_map measurable_snd
      (show Measurable (jointSampleStep R z) from
        (jointSampleStep_measurable R).comp (measurable_const.prodMk measurable_id))]
  rfl

theorem process_transition_relation {S : Type*} [MeasurableSpace S]
    (P : Rhone.MarkovChain.DiscreteProcess S) (A : S × S → Prop)
    (hA : MeasurableSet {p | A p})
    (hstep : ∀ x, ∀ᵐ y ∂P.step x, A (x, y)) (x : S) :
    ∀ᵐ ω ∂P.pathLaw x, ∀ k, A (ω k, ω (k + 1)) := by
  apply ae_all_iff.mpr
  intro k
  let f : ((_ : Finset.Iic k) → S) × S → S × S :=
    fun p => (p.1 ⟨k, Finset.mem_Iic.mpr le_rfl⟩, p.2)
  have hf : Measurable f :=
    ((measurable_pi_apply _).comp measurable_fst).prodMk measurable_snd
  have h : ∀ᵐ p ∂((Kernel.partialTraj (X := fun _ => S) P.stepSeq 0 k (fun _ => x)) ⊗ₘ
      (P.stepSeq k)), A (f p) := by
    apply Measure.ae_compProd_of_ae_ae (hA.preimage hf)
    exact Filter.Eventually.of_forall (fun z => hstep _)
  rw [Kernel.partialTraj_compProd_eq_map_traj (Nat.zero_le k)] at h
  exact ae_of_ae_map
    (f := fun ω : ℕ → S => (Preorder.frestrictLe k ω, ω (k + 1)))
    (p := fun p => A (f p)) (by fun_prop) h

theorem trackedSampleStep_good_agreement (R : ℝ) (z : TrackedState)
    (hz : Good z) (hp : z.2.1 ≠ .two) (u : Noise) :
    trackedSampleStep false R z u = trackedSampleStep true R z u := by
  apply trackedSampleStep_agreement
  cases h : z.2.1 with
  | zero =>
    have hz' : Valid z.1 ∧ AllMaterials FullAtoms z.1 ∧ 1 ≤ z.1.2.2.1 := by
      simpa [Good, h] using hz
    exact full_contacts z.1 hz'.2.1
  | one =>
    have hz' : Valid z.1 ∧
        (∀ i j, touches (z.1.2.2.2 i).2 (z.1.2.2.2 j).2) ∧ 1 ≤ z.1.2.2.1 := by
      simpa [Good, h] using hz
    exact hz'.2.1
  | two => exact (hp h).elim

theorem jointSamplerProcess_prefix_agreement (R : ℝ) (hR : 0 ≤ R)
    (n : ℕ) (hn : 0 < n) :
    ∀ᵐ ω ∂(jointSamplerProcess R).pathLaw (jointInitial n),
      ∀ k, (∀ j < k, (ω j).1.2.1 ≠ .two) → (ω k).1 = (ω k).2 := by
  have _ := hR
  let A : JointState × JointState → Prop := fun p =>
    (Good p.1.1 → Good p.2.1) ∧
    (Good p.1.1 ∧ p.1.1.2.1 ≠ .two ∧ p.1.1 = p.1.2 → p.2.1 = p.2.2)
  have hgood : MeasurableSet {p : JointState × JointState | Good p.1.1} :=
    good_measurable.preimage measurable_fst.fst
  have hgood' : MeasurableSet {p : JointState × JointState | Good p.2.1} :=
    good_measurable.preimage measurable_snd.fst
  have hphase : MeasurableSet {p : JointState × JointState | p.1.1.2.1 ≠ .two} :=
    (measurableSet_eq_fun measurable_fst.fst.snd.fst measurable_const).compl
  have heq : MeasurableSet {p : JointState × JointState | p.1.1 = p.1.2} :=
    measurableSet_eq_fun measurable_fst.fst measurable_fst.snd
  have heq' : MeasurableSet {p : JointState × JointState | p.2.1 = p.2.2} :=
    measurableSet_eq_fun measurable_snd.fst measurable_snd.snd
  have hA : MeasurableSet {p | A p} := by
    convert (hgood.compl.union hgood').inter
        ((hgood.inter (hphase.inter heq)).compl.union heq') using 1
    ext p
    simp only [A, Set.mem_inter_iff, Set.mem_union, Set.mem_compl_iff,
      Set.mem_ofPred_eq, imp_iff_not_or]
  have hs (z : JointState) : ∀ᵐ y ∂(jointSamplerProcess R).step z, A (z, y) := by
    change ∀ᵐ y ∂jointSamplerKernel R z, A (z, y)
    rw [jointSamplerKernel_apply]
    apply (ae_map_iff
      (show Measurable (jointSampleStep R z) from
        (jointSampleStep_measurable R).comp (measurable_const.prodMk measurable_id)).aemeasurable
      (hA.preimage measurable_prodMk_left)).mpr
    filter_upwards [noiseLaw_interior] with u hu
    refine ⟨fun hg => trackedSampleStep_good false R z.1 hg u
      (hu 0).1.le (hu 0).2 (hu 1).1.le (hu 1).2.le (hu 2).1 (hu 2).2, ?_⟩
    rintro ⟨hg, hp, he⟩
    change trackedSampleStep false R z.1 u = trackedSampleStep true R z.2 u
    rw [← he]
    exact trackedSampleStep_good_agreement R z.1 hg hp u
  have ht := process_transition_relation (jointSamplerProcess R) A hA hs (jointInitial n)
  have hi : ∀ᵐ ω ∂(jointSamplerProcess R).pathLaw (jointInitial n),
      ω 0 = jointInitial n := by
    apply ae_of_ae_map (f := fun ω : ℕ → JointState => ω 0)
      (p := fun z => z = jointInitial n) (measurable_pi_apply 0).aemeasurable
    rw [(jointSamplerProcess R).map_eval_zero]
    exact ae_dirac_iff (measurableSet_eq_fun measurable_id measurable_const) |>.mpr rfl
  filter_upwards [ht, hi] with ω ht hi
  have hg : ∀ k, Good (ω k).1 := by
    intro k
    induction k with
    | zero => rw [hi]; exact trackedInitial_good n hn
    | succ k ih => exact (ht k).1 ih
  intro k
  induction k with
  | zero => intro _; rw [hi]; rfl
  | succ k ih =>
    intro hp
    exact (ht k).2 ⟨hg k, hp k (Nat.lt_succ_self k),
      ih (fun j hj => hp j (hj.trans (Nat.lt_succ_self k)))⟩

end Rhone.Coalescent.SmcSupport
