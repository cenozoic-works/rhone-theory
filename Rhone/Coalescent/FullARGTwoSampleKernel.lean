/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.FullARGTwoSampleChain
public import Rhone.Coalescent.SmcSupport.ARGActionMixture

/-!
# One-step expectation of the two-locus reward under the unrestricted event kernel

Source: wilton_carmi_hobolth2015, eq. (5), Figure S1. -/
@[expose] public section

namespace Rhone.Coalescent.IntervalProcess
open SmcSupport MeasureTheory ProbabilityTheory
open scoped ENNReal

def twoLocusPre (x y : ℝ) : Set AugmentedState :=
  {z | carrierCount x z.1 = 2 ∧ carrierCount y z.1 = 2}

def twoLocusDone (x y : ℝ) : Set AugmentedState :=
  {z | carrierCount x z.1 ≤ 1 ∧ carrierCount y z.1 ≤ 1}

noncomputable def twoLocusHarmonic (x y ρ : ℝ) (z : AugmentedState) : ℝ :=
  twoLocusValue ρ (jointCarrierCount x y z.1)

noncomputable def twoLocusReward (x y ρ : ℝ) (w : AugmentedState) : ℝ :=
  twoLocusOutcome ρ (carrierCount x w.1) (carrierCount y w.1) (jointCarrierCount x y w.1)

theorem twoLocusPre_measurable (x y : ℝ) : MeasurableSet (twoLocusPre x y) :=
  (measurableSet_eq_fun ((carrierCount_measurable x).comp measurable_fst)
    measurable_const).inter
    (measurableSet_eq_fun ((carrierCount_measurable y).comp measurable_fst) measurable_const)

theorem twoLocusDone_measurable (x y : ℝ) : MeasurableSet (twoLocusDone x y) :=
  (measurableSet_le ((carrierCount_measurable x).comp measurable_fst) measurable_const).inter
    (measurableSet_le ((carrierCount_measurable y).comp measurable_fst) measurable_const)

theorem twoLocusPre_disjoint_done (x y : ℝ) : Disjoint (twoLocusPre x y) (twoLocusDone x y) := by
  rw [Set.disjoint_left]
  intro z hz hd
  have h1 := hz.1
  have h2 := hd.1
  omega

theorem twoLocusHarmonic_measurable (x y ρ : ℝ) : Measurable (twoLocusHarmonic x y ρ) :=
  (measurable_of_countable (twoLocusValue ρ)).comp
    ((jointCarrierCount_measurable x y).comp measurable_fst)

theorem twoLocusReward_measurable (x y ρ : ℝ) : Measurable (twoLocusReward x y ρ) :=
  (measurable_of_countable (fun p : ℕ × ℕ × ℕ => twoLocusOutcome ρ p.1 p.2.1 p.2.2)).comp
    (((carrierCount_measurable x).comp measurable_fst).prodMk
      (((carrierCount_measurable y).comp measurable_fst).prodMk
        ((jointCarrierCount_measurable x y).comp measurable_fst)))

theorem twoLocusReward_eq (x y ρ : ℝ) (w : AugmentedState) :
    twoLocusReward x y ρ w =
      (twoLocusPre x y).indicator (twoLocusHarmonic x y ρ) w +
        (twoLocusDone x y).indicator (fun _ => (1 : ℝ)) w := by
  by_cases hp : w ∈ twoLocusPre x y
  · have hd : w ∉ twoLocusDone x y := Set.disjoint_left.mp (twoLocusPre_disjoint_done x y) hp
    rw [Set.indicator_of_mem hp, Set.indicator_of_notMem hd, add_zero]
    unfold twoLocusReward twoLocusOutcome
    rw [ite_eq_left (show carrierCount x w.1 = 2 ∧ carrierCount y w.1 = 2 from hp)]
    rfl
  · rw [Set.indicator_of_notMem hp, zero_add]
    unfold twoLocusReward twoLocusOutcome
    rw [ite_eq_right (show ¬(carrierCount x w.1 = 2 ∧ carrierCount y w.1 = 2) from hp)]
    by_cases hd : w ∈ twoLocusDone x y
    · rw [Set.indicator_of_mem hd,
        ite_eq_left (show carrierCount x w.1 ≤ 1 ∧ carrierCount y w.1 ≤ 1 from hd)]
    · rw [Set.indicator_of_notMem hd,
        ite_eq_right (show ¬(carrierCount x w.1 ≤ 1 ∧ carrierCount y w.1 ≤ 1) from hd)]

theorem twoLocusReward_abs_le (x y ρ : ℝ) (hρ : 0 ≤ ρ) (w : AugmentedState) :
    |twoLocusReward x y ρ w| ≤ 1 := by
  unfold twoLocusReward twoLocusOutcome
  split_ifs
  · rw [abs_of_nonneg (twoLocusValue_nonneg ρ hρ _)]
    exact twoLocusValue_le_one ρ hρ _
  · simp
  · simp

theorem hullLo_le_of_materialContains (a : Material) (q : ℝ) (h : materialContains a q) :
    hullLo a ≤ q := by
  obtain ⟨k, hlo, hhi⟩ := h
  have hpos : (a.2 k).1 < (a.2 k).2 := lt_of_le_of_lt hlo hhi
  have := hullLo_le_atom a k
  rw [ite_eq_left hpos] at this
  exact this.trans hlo

theorem lt_hullHi_of_materialContains (a : Material) (q : ℝ) (h : materialContains a q) :
    q < hullHi a := by
  obtain ⟨k, hlo, hhi⟩ := h
  have hpos : (a.2 k).1 < (a.2 k).2 := lt_of_le_of_lt hlo hhi
  have := atom_le_hullHi a k
  rw [ite_eq_left hpos] at this
  exact hhi.trans_le this

theorem affine_cut_set_eq (lo len x y : ℝ) (hlen : 0 < len) :
    {u : ℝ | x < lo + len * u ∧ lo + len * u ≤ y} =
      Set.Ioc ((x - lo) / len) ((y - lo) / len) := by
  ext u
  simp only [Set.mem_ofPred_eq, Set.mem_Ioc]
  rw [div_lt_iff₀ hlen, le_div_iff₀ hlen]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith [mul_comm len u]

theorem unitUniform_real_affine_cut (lo len x y : ℝ) (hlen : 0 < len) (hx : lo ≤ x)
    (hxy : x ≤ y) (hy : y < lo + len) :
    unitUniform.real {u : ℝ | x < lo + len * u ∧ lo + len * u ≤ y} = (y - x) / len := by
  rw [affine_cut_set_eq lo len x y hlen, measureReal_def, unitUniform,
    Measure.restrict_apply measurableSet_Ioc]
  have ha : 0 ≤ (x - lo) / len := div_nonneg (by linarith) hlen.le
  have hb : (y - lo) / len < 1 := (div_lt_one hlen).mpr (by linarith)
  have heq : Set.Ioc ((x - lo) / len) ((y - lo) / len) ∩ Set.Ioo 0 1 =
      Set.Ioc ((x - lo) / len) ((y - lo) / len) := by
    apply Set.inter_eq_left.mpr
    intro u hu
    exact ⟨lt_of_le_of_lt ha hu.1, lt_of_le_of_lt hu.2 hb⟩
  rw [heq, Real.volume_Ioc, ENNReal.toReal_ofReal]
  · rw [← sub_div]
    congr 1
    ring
  · rw [← sub_div]
    exact div_nonneg (by linarith) hlen.le

theorem candidateRate_unrestricted_pair (R : ℝ) (s : State) (p : Fin s.2.2.1 × Fin s.2.2.1) :
    (candidateRate false R s (.inl p) : ℝ) = if p.1.val < p.2.val then 1 else 0 := by
  classical
  unfold candidateRate
  by_cases h : p.1.val < p.2.val <;> simp [h]

theorem carrierType_card_fst (x y : ℝ) (s : State) :
    (Finset.univ.filter fun i : Fin s.2.2.1 =>
        carrierType x y (s.2.2.2 i).2 = (true, true)).card +
      (Finset.univ.filter fun i : Fin s.2.2.1 =>
        carrierType x y (s.2.2.2 i).2 = (true, false)).card = carrierCount x s := by
  classical
  unfold carrierCount
  rw [materialCount_eq_sum, Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h1 : materialContains (s.2.2.2 i).2 x <;>
    by_cases h2 : materialContains (s.2.2.2 i).2 y <;> simp [carrierType, h1, h2]

theorem carrierType_card_snd (x y : ℝ) (s : State) :
    (Finset.univ.filter fun i : Fin s.2.2.1 =>
        carrierType x y (s.2.2.2 i).2 = (true, true)).card +
      (Finset.univ.filter fun i : Fin s.2.2.1 =>
        carrierType x y (s.2.2.2 i).2 = (false, true)).card = carrierCount y s := by
  classical
  unfold carrierCount
  rw [materialCount_eq_sum, Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h1 : materialContains (s.2.2.2 i).2 x <;>
    by_cases h2 : materialContains (s.2.2.2 i).2 y <;> simp [carrierType, h1, h2]

theorem carrierType_card_both (x y : ℝ) (s : State) :
    (Finset.univ.filter fun i : Fin s.2.2.1 =>
        carrierType x y (s.2.2.2 i).2 = (true, true)).card = jointCarrierCount x y s := by
  classical
  unfold jointCarrierCount
  rw [materialCount_eq_sum, Finset.card_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h1 : materialContains (s.2.2.2 i).2 x <;>
    by_cases h2 : materialContains (s.2.2.2 i).2 y <;> simp [carrierType, h1, h2]

theorem twoLocusReward_coal (R x y ρ : ℝ) (z : AugmentedState) (hz : z ∈ twoLocusPre x y)
    (i j : Fin z.1.2.2.1) (hij : i.val < j.val) (v : ℝ × ℝ) :
    twoLocusReward x y ρ (argActionStep R z (.inl (i, j)) v) - twoLocusHarmonic x y ρ z =
      pairOutcome ρ (jointCarrierCount x y z.1) (carrierType x y (z.1.2.2.2 i).2)
        (carrierType x y (z.1.2.2.2 j).2) := by
  have e : twoLocusReward x y ρ (argActionStep R z (.inl (i, j)) v) =
      twoLocusOutcome ρ (carrierCount x (coalSuccessor z.1 i j))
        (carrierCount y (coalSuccessor z.1 i j))
        (jointCarrierCount x y (coalSuccessor z.1 i j)) := rfl
  have hx := carrierCount_coalSuccessor x y z.1 i j hij
  have hy : carrierCount y (coalSuccessor z.1 i j) +
      ((carrierType x y (z.1.2.2.2 i).2).2 && (carrierType x y (z.1.2.2.2 j).2).2).toNat =
      carrierCount y z.1 := carrierCount_coalSuccessor y x z.1 i j hij
  have hb := jointCarrierCount_coalSuccessor x y z.1 i j hij
  rw [hz.1] at hx
  rw [hz.2] at hy
  have e1 : carrierCount x (coalSuccessor z.1 i j) =
      2 - ((carrierType x y (z.1.2.2.2 i).2).1 && (carrierType x y (z.1.2.2.2 j).2).1).toNat := by
    omega
  have e2 : carrierCount y (coalSuccessor z.1 i j) =
      2 - ((carrierType x y (z.1.2.2.2 i).2).2 && (carrierType x y (z.1.2.2.2 j).2).2).toNat := by
    omega
  have e3 : jointCarrierCount x y (coalSuccessor z.1 i j) =
      jointCarrierCount x y z.1 +
        (((carrierType x y (z.1.2.2.2 i).2).1 || (carrierType x y (z.1.2.2.2 j).2).1) &&
          ((carrierType x y (z.1.2.2.2 i).2).2 || (carrierType x y (z.1.2.2.2 j).2).2)).toNat -
        ((carrierType x y (z.1.2.2.2 i).2).1 && (carrierType x y (z.1.2.2.2 i).2).2).toNat -
        ((carrierType x y (z.1.2.2.2 j).2).1 && (carrierType x y (z.1.2.2.2 j).2).2).toNat := by
    omega
  rw [e, e1, e2, e3]
  rfl

open scoped Classical in
theorem twoLocusReward_split (R x y ρ : ℝ) (hxy : x < y) (z : AugmentedState)
    (hz : z ∈ twoLocusPre x y) (i : Fin z.1.2.2.1) (v : ℝ × ℝ) :
    twoLocusReward x y ρ (argActionStep R z (.inr i) v) =
      twoLocusHarmonic x y ρ z +
        (if (materialContains (z.1.2.2.2 i).2 x ∧ materialContains (z.1.2.2.2 i).2 y) ∧
            x < hullLo (z.1.2.2.2 i).2 + hullLength (z.1.2.2.2 i).2 * v.2 ∧
            hullLo (z.1.2.2.2 i).2 + hullLength (z.1.2.2.2 i).2 * v.2 ≤ y
          then twoLocusValue ρ (jointCarrierCount x y z.1 - 1) -
            twoLocusValue ρ (jointCarrierCount x y z.1)
          else 0) := by
  set c := hullLo (z.1.2.2.2 i).2 + hullLength (z.1.2.2.2 i).2 * v.2 with hc
  have e : twoLocusReward x y ρ (argActionStep R z (.inr i) v) =
      twoLocusOutcome ρ (carrierCount x (splitSuccessor z.1 i c))
        (carrierCount y (splitSuccessor z.1 i c))
        (jointCarrierCount x y (splitSuccessor z.1 i c)) := rfl
  have hb := jointCarrierCount_splitSuccessor x y hxy z.1 i c
  rw [e, carrierCount_splitSuccessor, carrierCount_splitSuccessor, hz.1, hz.2]
  unfold twoLocusOutcome twoLocusHarmonic
  rw [ite_eq_left (show (2 : ℕ) = 2 ∧ (2 : ℕ) = 2 from ⟨rfl, rfl⟩)]
  split_ifs at hb ⊢ with hs
  · have : jointCarrierCount x y (splitSuccessor z.1 i c) = jointCarrierCount x y z.1 - 1 := by
      omega
    rw [this]
    ring
  · have : jointCarrierCount x y (splitSuccessor z.1 i c) = jointCarrierCount x y z.1 := by
      omega
    rw [this, add_zero]

theorem eventKernel_twoLocusReward (R : ℝ) (hR : 0 ≤ R) (x y : ℝ) (hxy : x < y)
    (z : AugmentedState) (hz : z ∈ twoLocusPre x y) :
    ∫ w, twoLocusReward x y (R * (y - x)) w ∂eventKernel false R z =
      twoLocusHarmonic x y (R * (y - x)) z := by
  classical
  set ρ := R * (y - x) with hρdef
  have hρ : 0 ≤ ρ := mul_nonneg hR (by linarith)
  have hm : 2 ≤ z.1.2.2.1 := by
    have h1 := materialCount_le (fun a => materialContains a x) z.1
    have h2 : carrierCount x z.1 = 2 := hz.1
    unfold carrierCount at h2
    omega
  have htpos := unrestricted_totalRate_positive R z.1 hm
  have ht : 0 < (totalRate false R z.1 : ℝ) := by exact_mod_cast htpos
  have hΦ := twoLocusReward_measurable x y ρ
  set U := unitUniform.prod unitUniform with hU
  set hval := twoLocusHarmonic x y ρ z with hhval
  set cb := jointCarrierCount x y z.1 with hcb
  set Δ := twoLocusValue ρ (cb - 1) - twoLocusValue ρ cb with hΔ
  let I : ActionIndex z.1 → ℝ := fun a => ∫ v, twoLocusReward x y ρ (argActionStep R z a v) ∂U
  have hbound : ∀ (μ : Measure AugmentedState) [IsFiniteMeasure μ],
      Integrable (twoLocusReward x y ρ) μ := fun μ _ =>
    Integrable.of_bound hΦ.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun w => by
        rw [Real.norm_eq_abs]
        exact twoLocusReward_abs_le x y ρ hρ w)
  have hmix : ∫ w, twoLocusReward x y ρ w ∂eventKernel false R z =
      ∑ a : ActionIndex z.1,
        (candidateRate false R z.1 a : ℝ) / (totalRate false R z.1 : ℝ) * I a := by
    rw [eventKernel_ARG_action_mixture R z hm, integral_finsetSum_measure]
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [integral_smul_measure,
        integral_map (argActionStep_measurable R z a).aemeasurable hΦ.aestronglyMeasurable,
        ENNReal.toReal_ofReal (div_nonneg (NNReal.coe_nonneg _) ht.le), smul_eq_mul]
    · intro a _
      exact (hbound _).smul_measure ENNReal.ofReal_ne_top
  have hsumrate : ∑ a : ActionIndex z.1, (candidateRate false R z.1 a : ℝ) =
      (totalRate false R z.1 : ℝ) := by
    simp [totalRate]
  have hpair : ∑ p : Fin z.1.2.2.1 × Fin z.1.2.2.1,
      (candidateRate false R z.1 (.inl p) : ℝ) * (I (.inl p) - hval) =
      -((cb : ℝ) * (ρ / 2) * Δ) := by
    have hterm : ∀ p : Fin z.1.2.2.1 × Fin z.1.2.2.1,
        (candidateRate false R z.1 (.inl p) : ℝ) * (I (.inl p) - hval) =
          if p.1.val < p.2.val then
            pairOutcome ρ cb (carrierType x y (z.1.2.2.2 p.1).2)
              (carrierType x y (z.1.2.2.2 p.2).2)
          else 0 := by
      intro p
      rw [candidateRate_unrestricted_pair]
      by_cases hlt : p.1.val < p.2.val
      · rw [ite_eq_left hlt, ite_eq_left hlt, one_mul]
        have hconst : ∀ v, twoLocusReward x y ρ (argActionStep R z (.inl p) v) =
            hval + pairOutcome ρ cb (carrierType x y (z.1.2.2.2 p.1).2)
              (carrierType x y (z.1.2.2.2 p.2).2) := by
          intro v
          have := twoLocusReward_coal R x y ρ z hz p.1 p.2 hlt v
          linarith
        change ∫ v, twoLocusReward x y ρ (argActionStep R z (.inl p) v) ∂U - hval = _
        rw [integral_congr_ae (Filter.Eventually.of_forall hconst), integral_const,
          probReal_univ, one_smul]
        ring
      · rw [ite_eq_right hlt, ite_eq_right hlt, zero_mul]
    rw [Finset.sum_congr rfl (fun p _ => hterm p),
      sum_lt_pair_eq (fun i => carrierType x y (z.1.2.2.2 i).2) (pairOutcome ρ cb)
        (pairOutcome_symm ρ cb)]
    have hcb2 : cb ≤ 2 := by
      have h1 := materialCount_mono (P := fun a => materialContains a x ∧ materialContains a y)
        (Q := fun a => materialContains a x) (fun a ha => ha.1) z.1
      have h2 : carrierCount x z.1 = 2 := hz.1
      change cb ≤ carrierCount x z.1 at h1
      omega
    have h11 := carrierType_card_both x y z.1
    have h10 := carrierType_card_fst x y z.1
    have h01 := carrierType_card_snd x y z.1
    rw [hz.1] at h10
    rw [hz.2] at h01
    rw [← hcb] at h11
    refine pairOutcome_sum_value ρ hρ cb hcb2
      (fun t => ((Finset.univ.filter fun i : Fin z.1.2.2.1 =>
        carrierType x y (z.1.2.2.2 i).2 = t).card : ℝ)) ?_ ?_ ?_
    · exact_mod_cast h11
    · have : ((Finset.univ.filter fun i : Fin z.1.2.2.1 =>
          carrierType x y (z.1.2.2.2 i).2 = (true, false)).card : ℝ) = (2 : ℝ) - (cb : ℝ) := by
        have h := congrArg (fun n : ℕ => (n : ℝ)) h10
        simp only [Nat.cast_add, h11] at h
        push_cast at h
        linarith
      exact this
    · have : ((Finset.univ.filter fun i : Fin z.1.2.2.1 =>
          carrierType x y (z.1.2.2.2 i).2 = (false, true)).card : ℝ) = (2 : ℝ) - (cb : ℝ) := by
        have h := congrArg (fun n : ℕ => (n : ℝ)) h01
        simp only [Nat.cast_add, h11] at h
        push_cast at h
        linarith
      exact this
  have hsnd : U.map Prod.snd = unitUniform := by
    rw [hU, Measure.map_snd_prod, measure_univ, one_smul]
  have hsplit : ∑ i : Fin z.1.2.2.1,
      (candidateRate false R z.1 (.inr i) : ℝ) * (I (.inr i) - hval) =
      (cb : ℝ) * (ρ / 2) * Δ := by
    have hterm : ∀ i : Fin z.1.2.2.1,
        (candidateRate false R z.1 (.inr i) : ℝ) * (I (.inr i) - hval) =
          (if materialContains (z.1.2.2.2 i).2 x ∧ materialContains (z.1.2.2.2 i).2 y
            then 1 else 0) * ((ρ / 2) * Δ) := by
      intro i
      set lo := hullLo (z.1.2.2.2 i).2 with hlo
      set len := hullLength (z.1.2.2.2 i).2 with hlen
      by_cases hb : materialContains (z.1.2.2.2 i).2 x ∧ materialContains (z.1.2.2.2 i).2 y
      · rw [ite_eq_left hb, one_mul, candidateRate_split_eq false R hR]
        have hlox : lo ≤ x := hullLo_le_of_materialContains _ _ hb.1
        have hhiy : y < hullHi (z.1.2.2.2 i).2 := lt_hullHi_of_materialContains _ _ hb.2
        have hlenpos : 0 < len := by
          have : 0 < hullHi (z.1.2.2.2 i).2 - lo := by linarith
          rw [hlen, hullLength]
          exact lt_max_of_lt_right this
        have hleneq : len = hullHi (z.1.2.2.2 i).2 - lo := by
          rw [hlen, hullLength]
          exact max_eq_right (by linarith)
        set T : Set ℝ := {u : ℝ | x < lo + len * u ∧ lo + len * u ≤ y} with hT
        have hTm : MeasurableSet T := by
          rw [hT, affine_cut_set_eq lo len x y hlenpos]
          exact measurableSet_Ioc
        have hSm : MeasurableSet (Prod.snd ⁻¹' T : Set (ℝ × ℝ)) := hTm.preimage measurable_snd
        have hpt : ∀ v : ℝ × ℝ, twoLocusReward x y ρ (argActionStep R z (.inr i) v) =
            hval + (Prod.snd ⁻¹' T : Set (ℝ × ℝ)).indicator (fun _ => Δ) v := by
          intro v
          rw [twoLocusReward_split R x y ρ hxy z hz i v]
          by_cases hv : v.2 ∈ T
          · have hc : (materialContains (z.1.2.2.2 i).2 x ∧ materialContains (z.1.2.2.2 i).2 y) ∧
                x < hullLo (z.1.2.2.2 i).2 + hullLength (z.1.2.2.2 i).2 * v.2 ∧
                hullLo (z.1.2.2.2 i).2 + hullLength (z.1.2.2.2 i).2 * v.2 ≤ y := ⟨hb, hv⟩
            rw [Set.indicator_of_mem (show v ∈ Prod.snd ⁻¹' T from hv), ite_eq_left hc]
          · have hc : ¬((materialContains (z.1.2.2.2 i).2 x ∧
                materialContains (z.1.2.2.2 i).2 y) ∧
                x < hullLo (z.1.2.2.2 i).2 + hullLength (z.1.2.2.2 i).2 * v.2 ∧
                hullLo (z.1.2.2.2 i).2 + hullLength (z.1.2.2.2 i).2 * v.2 ≤ y) :=
              fun h => hv h.2
            rw [Set.indicator_of_notMem (show v ∉ Prod.snd ⁻¹' T from hv), ite_eq_right hc]
        have hmass : U.real (Prod.snd ⁻¹' T) = (y - x) / len := by
          rw [measureReal_def, ← Measure.map_apply measurable_snd hTm, hsnd, ← measureReal_def]
          exact unitUniform_real_affine_cut lo len x y hlenpos hlox hxy.le (by linarith)
        have hI : I (.inr i) = hval + (y - x) / len * Δ := by
          change ∫ v, twoLocusReward x y ρ (argActionStep R z (.inr i) v) ∂U = _
          rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
            integral_add (integrable_const _) ((integrable_const _).indicator hSm),
            integral_const, probReal_univ, one_smul, integral_indicator_const _ hSm, hmass,
            smul_eq_mul]
        rw [hI, hρdef]
        field_simp
        ring
      · rw [ite_eq_right hb, zero_mul]
        have hpt : ∀ v : ℝ × ℝ, twoLocusReward x y ρ (argActionStep R z (.inr i) v) = hval := by
          intro v
          have hc : ¬((materialContains (z.1.2.2.2 i).2 x ∧
              materialContains (z.1.2.2.2 i).2 y) ∧
              x < hullLo (z.1.2.2.2 i).2 + hullLength (z.1.2.2.2 i).2 * v.2 ∧
              hullLo (z.1.2.2.2 i).2 + hullLength (z.1.2.2.2 i).2 * v.2 ≤ y) :=
            fun h => hb h.1
          rw [twoLocusReward_split R x y ρ hxy z hz i v, ite_eq_right hc, add_zero]
        have hI : I (.inr i) = hval := by
          change ∫ v, twoLocusReward x y ρ (argActionStep R z (.inr i) v) ∂U = _
          rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const,
            probReal_univ, one_smul]
        rw [hI, sub_self, mul_zero]
    rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.sum_mul]
    have hcount : (∑ i : Fin z.1.2.2.1,
        (if materialContains (z.1.2.2.2 i).2 x ∧ materialContains (z.1.2.2.2 i).2 y
          then (1 : ℝ) else 0)) = (cb : ℝ) := by
      rw [hcb, jointCarrierCount, materialCount_eq_sum]
      push_cast
      rfl
    rw [hcount]
    ring
  have hkey : ∑ a : ActionIndex z.1, (candidateRate false R z.1 a : ℝ) * (I a - hval) = 0 := by
    rw [Fintype.sum_sum_type, hpair, hsplit]
    ring
  rw [hmix]
  have hexp : ∑ a : ActionIndex z.1,
      (candidateRate false R z.1 a : ℝ) / (totalRate false R z.1 : ℝ) * I a =
      (∑ a : ActionIndex z.1, (candidateRate false R z.1 a : ℝ) * (I a - hval)) /
          (totalRate false R z.1 : ℝ) +
        hval * ((∑ a : ActionIndex z.1, (candidateRate false R z.1 a : ℝ)) /
          (totalRate false R z.1 : ℝ)) := by
    rw [Finset.sum_div, Finset.sum_div, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  rw [hexp, hkey, hsumrate, div_self ht.ne', zero_div, zero_add, mul_one]

theorem eventKernel_twoLocus_step (R : ℝ) (hR : 0 ≤ R) (x y : ℝ) (hxy : x < y)
    (z : AugmentedState) (hz : z ∈ twoLocusPre x y) :
    ∫ w, (twoLocusPre x y).indicator (twoLocusHarmonic x y (R * (y - x))) w
        ∂eventKernel false R z +
      (eventKernel false R z).real (twoLocusDone x y) =
    twoLocusHarmonic x y (R * (y - x)) z := by
  have hρ : 0 ≤ R * (y - x) := mul_nonneg hR (by linarith)
  have h := eventKernel_twoLocusReward R hR x y hxy z hz
  have hI1 : Integrable ((twoLocusPre x y).indicator (twoLocusHarmonic x y (R * (y - x))))
      (eventKernel false R z) :=
    Integrable.of_bound
      ((twoLocusHarmonic_measurable x y _).indicator
        (twoLocusPre_measurable x y)).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun w => by
        rw [Real.norm_eq_abs]
        by_cases hw : w ∈ twoLocusPre x y
        · rw [Set.indicator_of_mem hw, twoLocusHarmonic,
            abs_of_nonneg (twoLocusValue_nonneg _ hρ _)]
          exact twoLocusValue_le_one _ hρ _
        · rw [Set.indicator_of_notMem hw, abs_zero]
          exact zero_le_one)
  have hI2 : Integrable ((twoLocusDone x y).indicator (fun _ => (1 : ℝ)))
      (eventKernel false R z) :=
    (integrable_const _).indicator (twoLocusDone_measurable x y)
  rw [integral_congr_ae (Filter.Eventually.of_forall (twoLocusReward_eq x y (R * (y - x)))),
    integral_add hI1 hI2] at h
  rw [← h]
  congr 1
  exact (integral_indicator_one (twoLocusDone_measurable x y)).symm

end Rhone.Coalescent.IntervalProcess
