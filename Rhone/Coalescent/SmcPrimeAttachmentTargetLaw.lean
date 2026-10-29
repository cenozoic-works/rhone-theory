/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeAttachmentBudget
public import Rhone.Coalescent.SmcPrimeProposalKernel
public import Rhone.Coalescent.SmcSupport.Selector

/-! # Conditional probabilities of the attachment target among old branches -/
@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open IntervalProcess MeasureTheory
open scoped ENNReal

noncomputable def attachmentTargetRate {N : ℕ} (T : Tree N)
    (s : ℝ) (c : Finset (Fin N)) : ℝ := by
  classical
  exact if rootHeight T ≤ s then (if c = Finset.univ then 1 else 0)
    else ((activeBranches T s).filter (fun i => (T.2 i).1 = c)).card

theorem measurable_attachmentTargetRate {N : ℕ} (T : Tree N) (c : Finset (Fin N)) :
    Measurable (fun s => attachmentTargetRate T s c) := by
  classical
  have hA : Measurable (fun s => activeBranches T s) :=
    (activeBranchesFiber_measurable N T.1).comp (measurable_const.prodMk measurable_id)
  have hc : Measurable (fun s =>
      (((activeBranches T s).filter (fun i => (T.2 i).1 = c)).card : ℝ)) :=
    (measurable_of_countable (fun A : Finset (Fin T.1) =>
      ((A.filter (fun i => (T.2 i).1 = c)).card : ℝ))).comp hA
  exact measurable_const.piecewise (measurableSet_le measurable_const measurable_id) hc

theorem attachmentTargetRate_nonneg {N : ℕ} (T : Tree N)
    (s : ℝ) (c : Finset (Fin N)) : 0 ≤ attachmentTargetRate T s c := by
  classical
  unfold attachmentTargetRate
  split_ifs <;> positivity

theorem attachmentSelector_partition {N : ℕ} (T : Tree N) (s : ℝ)
    (hA : (activeBranches T s).Nonempty) :
    unitUniform = ∑ i : Fin T.1,
      unitUniform.restrict {u | chooseByRate (fun _ => (1 : ℝ))
        (activeBranches T s).toList (u * (activeBranches T s).card) = some i} := by
  classical
  let : MeasurableSpace (Option (Fin T.1)) := ⊤
  let A := activeBranches T s
  let g (u : ℝ) := chooseByRate (fun _ : Fin T.1 => (1 : ℝ)) A.toList (u * A.card)
  let E (i : Fin T.1) : Set ℝ := {u | g u = some i}
  have hg : Measurable g := chooseByRate_measurable
    (fun _ _ => (1 : ℝ)) (fun _ => measurable_const) A.toList
    (fun u : ℝ => u * A.card) (measurable_id.mul_const _)
  have hE (i : Fin T.1) : MeasurableSet (E i) :=
    hg (show MeasurableSet ({some i} : Set (Option (Fin T.1))) from by trivial)
  have hd : Pairwise (fun i j => Disjoint (E i) (E j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro u hi hj
    exact hij (Option.some.inj (hi.symm.trans hj))
  have hsum : (A.toList.map (fun _ => (1 : ℝ))).sum = (A.card : ℝ) := by simp
  have hpos : 0 < (A.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hA
  have hcover : (⋃ i, E i) =ᵐ[unitUniform] Set.univ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    obtain ⟨i, hi, _⟩ := Rhone.Coalescent.SmcSupport.chooseByRate_exists_positive
      (fun _ : Fin T.1 => (1 : ℝ)) A.toList (fun _ _ => by positivity)
      (u * A.card) (mul_nonneg hu.1.le hpos.le) (by rw [hsum]; nlinarith [hu.2])
    exact propext ⟨fun _ => Set.mem_univ _, fun _ => Set.mem_iUnion.mpr ⟨i, hi⟩⟩
  calc
    unitUniform = unitUniform.restrict (⋃ i, E i) := by
      rw [Measure.restrict_congr_set hcover, Measure.restrict_univ]
    _ = ∑ i, unitUniform.restrict (E i) := by
      rw [Measure.restrict_iUnion hd hE, Measure.sum_fintype]

private theorem attachmentSelector_mass {N : ℕ} (T : Tree N) (s : ℝ)
    (hA : (activeBranches T s).Nonempty) (i : Fin T.1) :
    unitUniform {u | chooseByRate (fun _ => (1 : ℝ))
      (activeBranches T s).toList (u * (activeBranches T s).card) = some i} =
      if i ∈ activeBranches T s then
        ENNReal.ofReal (1 / ((activeBranches T s).card : ℝ)) else 0 := by
  classical
  by_cases hi : i ∈ activeBranches T s
  · have hsum : ((activeBranches T s).toList.map (fun _ => (1 : ℝ))).sum =
        ((activeBranches T s).card : ℝ) := by simp
    rw [ite_eq_left hi]
    simpa only [hsum] using chooseByRate_uniform_mass_general
      (fun _ : Fin T.1 => (1 : ℝ)) (activeBranches T s).toList
      (Finset.nodup_toList _) (fun _ _ => by positivity)
      (by rw [hsum]; exact_mod_cast Finset.card_pos.mpr hA) i (by simpa using hi)
  · rw [ite_eq_right hi]
    have hset : {u | chooseByRate (fun _ : Fin T.1 => (1 : ℝ))
        (activeBranches T s).toList (u * (activeBranches T s).card) = some i} = ∅ := by
      ext u
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      exact hi (by simpa using chooseByRate_mem _ _ _ i h)
    rw [hset, measure_empty]

theorem attachment_target_mass {N : ℕ} (T : Tree N)
    (hT : TreeTemporalCover T) (s : ℝ) (hs : 0 ≤ s) (c : Finset (Fin N)) :
    (unitUniform.map (fun u => attachmentTarget T s u)) {c} =
      ENNReal.ofReal (attachmentTargetRate T s c / attachmentRate T s) := by
  classical
  have hf : Measurable (fun u => attachmentTarget T s u) :=
    (attachmentTargetFiber_measurable N T.1).comp
      (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  by_cases hr : rootHeight T ≤ s
  · by_cases hc : c = Finset.univ
    · subst c
      simp [attachmentTarget, attachmentTargetRate, attachmentRate, hr]
    · simp [attachmentTarget, attachmentTargetRate, attachmentRate, hr, hc,
        Ne.symm hc]
  · have hA := hT s hs (lt_of_not_ge hr)
    let A := activeBranches T s
    let g (u : ℝ) := chooseByRate (fun _ : Fin T.1 => (1 : ℝ)) A.toList (u * A.card)
    let E (i : Fin T.1) : Set ℝ := {u | g u = some i}
    let F : Set ℝ := {u | attachmentTarget T s u = c}
    have hF : MeasurableSet F := hf (measurableSet_singleton c)
    have hcover : unitUniform = ∑ i, unitUniform.restrict (E i) :=
      attachmentSelector_partition T s hA
    rw [Measure.map_apply hf (measurableSet_singleton c)]
    change unitUniform F = _
    rw [hcover, Measure.finsetSum_apply]
    have hbranch (i : Fin T.1) :
        (unitUniform.restrict (E i)) F =
          if (T.2 i).1 = c then unitUniform (E i) else 0 := by
      rw [Measure.restrict_apply hF]
      have hi (u : ℝ) (hu : u ∈ E i) : attachmentTarget T s u = (T.2 i).1 := by
        simp only [attachmentTarget, ite_eq_right hr]
        change (match g u with | none => Finset.univ | some j => (T.2 j).1) = _
        rw [hu]
      by_cases hc : (T.2 i).1 = c
      · rw [ite_eq_left hc]
        congr 1
        ext u
        exact ⟨fun h => h.2, fun h => ⟨(hi u h).trans hc, h⟩⟩
      · rw [ite_eq_right hc]
        have hempty : F ∩ E i = ∅ := by
          ext u
          simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
          rintro ⟨hu, he⟩
          exact hc ((hi u he).symm.trans hu)
        rw [hempty, measure_empty]
    simp_rw [hbranch]
    dsimp only [E, g, A]
    simp_rw [attachmentSelector_mass T s hA]
    let B := A.filter (fun i => (T.2 i).1 = c)
    have hterm (i : Fin T.1) :
        (if (T.2 i).1 = c then
          if i ∈ A then ENNReal.ofReal (1 / (A.card : ℝ)) else 0 else 0) =
        if i ∈ B then ENNReal.ofReal (1 / (A.card : ℝ)) else 0 := by
      by_cases ha : i ∈ A <;> by_cases hc : (T.2 i).1 = c <;> simp [B, ha, hc]
    change (∑ i : Fin T.1, if (T.2 i).1 = c then
      if i ∈ A then ENNReal.ofReal (1 / (A.card : ℝ)) else 0 else 0) = _
    simp_rw [hterm]
    rw [← Finset.sum_filter]
    simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_const,
      nsmul_eq_mul]
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    simp only [attachmentTargetRate, attachmentRate, ite_eq_right hr]
    congr 1
    change (B.card : ℝ) * (1 / (A.card : ℝ)) = (B.card : ℝ) / (A.card : ℝ)
    ring

end Rhone.Coalescent.SmcPrime
