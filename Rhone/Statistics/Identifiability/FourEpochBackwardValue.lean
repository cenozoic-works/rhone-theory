/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Statistics.Identifiability.MutationFourEpochRates
public import Rhone.Statistics.Identifiability.MutationConstantTail
public import Rhone.Statistics.Identifiability.IntegrableMarkovBasic

/-! # Backward value of the four-epoch model: absolute continuity and Lipschitz bounds -/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology Matrix Matrix.Norms.Operator
set_option backward.isDefEq.respectTransparency false

namespace Rhone.Statistics.Identifiability.FourEpochBackward
open MutationPulseKernel MutationConstantTail
local notation "State" => MutationPulseKernel.State

def remaining (a b t : ℝ) : ℝ := max (b - max t a) 0

theorem remaining_nonneg (a b t : ℝ) : 0 ≤ remaining a b t := le_max_right _ _

theorem remaining_lipschitz (a b : ℝ) : LipschitzWith 1 (remaining a b) := by
  unfold remaining
  simpa only [zero_add, id_eq] using
    ((LipschitzWith.const b).sub (LipschitzWith.id.max_const a)).max_const 0

theorem remaining_before {a b t : ℝ} (hab : a ≤ b) (ht : t ≤ a) :
    remaining a b t = b-a := by simp [remaining, max_eq_right ht, max_eq_left (sub_nonneg.mpr
        hab)]

theorem remaining_inside {a b t : ℝ} (ha : a ≤ t) (hb : t ≤ b) :
    remaining a b t = b-t := by simp [remaining, max_eq_left ha, max_eq_left (sub_nonneg.mpr hb)]

theorem remaining_after {a b t : ℝ} (hab : a ≤ b) (ht : b ≤ t) :
    remaining a b t = 0 := by simp [remaining, max_eq_left (hab.trans ht), max_eq_right
        (sub_nonpos.mpr ht)]

theorem exp_B_lipschitzOn {lam r k : ℝ} (hlam : 0 ≤ lam) (hr : 0 ≤ r) (hk : 0 ≤ k) :
    LipschitzOnWith ‖B lam r k‖₊ (fun t : ℝ => NormedSpace.exp (t • B lam r k)) (Ici 0) := by
  apply (convex_Ici (0 : ℝ)).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun t _ => (hasDerivAt_exp_smul_const (B lam r k) t).hasDerivWithinAt)
  intro t ht
  apply NNReal.coe_le_coe.mp
  change ‖NormedSpace.exp (t • B lam r k) * B lam r k‖ ≤ ‖B lam r k‖
  exact (norm_mul_le _ _).trans (by
    simpa using mul_le_mul_of_nonneg_right
      (exp_B_norm_le_one hlam hr hk ht) (norm_nonneg (B lam r k)))

theorem exp_remaining_ac {lam r k : ℝ} (hlam : 0 ≤ lam) (hr : 0 ≤ r) (hk : 0 ≤ k)
    (a b s t : ℝ) : AbsolutelyContinuousOnInterval
      (fun x => NormedSpace.exp (remaining a b x • B lam r k)) s t := by
  exact ((exp_B_lipschitzOn hlam hr hk).comp (remaining_lipschitz a b).lipschitzOnWith
    (fun x _ => remaining_nonneg a b x)).absolutelyContinuousOnInterval

noncomputable def matrixEntry (i j : State) : Matrix State State ℝ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => A i j
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

@[simp] theorem matrixEntry_apply (i j : State) (A : Matrix State State ℝ) :
    matrixEntry i j A = A i j := rfl

theorem exp_remaining_entry_ac {lam r k : ℝ} (hlam : 0 ≤ lam) (hr : 0 ≤ r) (hk : 0 ≤ k)
    (a b s t : ℝ) (i j : State) : AbsolutelyContinuousOnInterval
      (fun x => NormedSpace.exp (remaining a b x • B lam r k) i j) s t := by
  exact ac_comp_lipschitz (E := Matrix State State ℝ) (F := ℝ)
    (f := fun x => NormedSpace.exp (remaining a b x • B lam r k))
    (g := matrixEntry i j) (exp_remaining_ac hlam hr hk a b s t) (matrixEntry i j).lipschitzWith

theorem ac_mulVec {A : ℝ → Matrix State State ℝ} {v : ℝ → State → ℝ} {a b : ℝ}
    (hA : ∀ i j, AbsolutelyContinuousOnInterval (fun t => A t i j) a b)
    (hv : ∀ i, AbsolutelyContinuousOnInterval (fun t => v t i) a b) (i : State) :
    AbsolutelyContinuousOnInterval (fun t => (A t *ᵥ v t) i) a b := by
  change AbsolutelyContinuousOnInterval (fun t => ∑ j : State, A t i j * v t j) a b
  exact ac_finset_sum Finset.univ (fun j _ => (hA i j).mul (hv j))

noncomputable def value (ε δ M A τ r k t : ℝ) : State → ℝ :=
  NormedSpace.exp (remaining 0 ε t • B (δ+A/ε) r k) *ᵥ
    (NormedSpace.exp (remaining ε τ t • B δ r k) *ᵥ
      (NormedSpace.exp (remaining τ (τ + ε) t • B (δ+M/ε) r k) *ᵥ tailPayoff δ r k))

theorem value_ac {ε δ M A : ℝ} (hε : 0 < ε) (hδ : 0 ≤ δ) (hM : 0 ≤ M) (hA : 0 ≤ A)
    {r k : ℝ} (hr : 0 ≤ r) (hk : 0 ≤ k) (τ s t : ℝ) (i : State) :
    AbsolutelyContinuousOnInterval (fun x => value ε δ M A τ r k x i) s t := by
  apply ac_mulVec (exp_remaining_entry_ac (add_nonneg hδ (div_nonneg hA hε.le)) hr hk 0 ε s t)
  intro j
  apply ac_mulVec (exp_remaining_entry_ac hδ hr hk ε τ s t)
  intro l
  apply ac_mulVec (exp_remaining_entry_ac (add_nonneg hδ (div_nonneg hM hε.le)) hr hk τ (τ + ε) s
      t)
  intro m
  exact (LipschitzWith.const _).lipschitzOnWith.absolutelyContinuousOnInterval

theorem exp_B_preserves_bounds {lam r k t : ℝ} (hlam : 0 ≤ lam) (hr : 0 ≤ r)
    (hk : 0 ≤ k) (ht : 0 ≤ t) {v : State → ℝ}
    (hv0 : ∀ i, 0 ≤ v i) (hv1 : ∀ i, v i ≤ 1) :
    (∀ i, 0 ≤ (NormedSpace.exp (t • B lam r k) *ᵥ v) i) ∧
    (∀ i, (NormedSpace.exp (t • B lam r k) *ᵥ v) i ≤ 1) := by
  constructor
  · exact matrix_mulVec_nonneg _ _ (exp_B_nonneg hlam hr ht) hv0
  · intro i
    exact (mulVec_mono _ (exp_B_nonneg hlam hr ht) hv1 i).trans
      (exp_B_row_le_one hlam hr hk ht i)

theorem value_bounds {ε δ M A : ℝ} (hε : 0 < ε) (hδ : 0 ≤ δ) (hM : 0 ≤ M) (hA : 0 ≤ A)
    {r k : ℝ} (hr : 0 ≤ r) (hk : 0 ≤ k) (τ t : ℝ) :
    (∀ i, 0 ≤ value ε δ M A τ r k t i) ∧ (∀ i, value ε δ M A τ r k t i ≤ 1) := by
  have h2 := exp_B_preserves_bounds (add_nonneg hδ (div_nonneg hM hε.le)) hr hk
    (remaining_nonneg τ (τ + ε) t) (tailPayoff_nonneg (k := k) hδ hr) (tailPayoff_le_one (k := k)
        hδ hr)
  have h1 := exp_B_preserves_bounds hδ hr hk (remaining_nonneg ε τ t) h2.1 h2.2
  exact exp_B_preserves_bounds (add_nonneg hδ (div_nonneg hA hε.le)) hr hk
    (remaining_nonneg 0 ε t) h1.1 h1.2

theorem exp_B_mulVec_absorbing (lam r k t : ℝ) (v : State → ℝ) :
    (NormedSpace.exp (t • B lam r k) *ᵥ v) 4 = v 4 := by
  simp only [Matrix.mulVec, dotProduct, exp_B_absorbing_row]
  simp [Matrix.one_apply]

@[simp] theorem value_absorbing (ε δ M A τ r k t : ℝ) : value ε δ M A τ r k t 4 = 1 := by
  simp only [value, exp_B_mulVec_absorbing, tailPayoff_absorbing]

theorem value_zero {ε τ : ℝ} (hε : 0 < ε) (hτ : ε ≤ τ) (δ M A r k : ℝ) :
    value ε δ M A τ r k 0 = fourEpochVector ε δ M r k (tailPayoff δ r k) (A,τ) := by
  rw [fourEpochVector_eq_exp_product (ne_of_gt hε)]
  simp only [value, remaining_before hε.le le_rfl,
    remaining_before hτ hε.le, remaining_before (show τ ≤ τ + ε by linarith) (hε.le.trans hτ)]
  simp

noncomputable def matrixAction (v : State → ℝ) :
    Matrix State State ℝ →L[ℝ] (State → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => A *ᵥ v
      map_add' := by intros; exact Matrix.add_mulVec _ _ _
      map_smul' := by intros; exact Matrix.smul_mulVec _ _ _ }

@[simp] theorem matrixAction_apply (v : State → ℝ) (A : Matrix State State ℝ) :
    matrixAction v A = A *ᵥ v := rfl

theorem exp_backward_hasDerivAt (B : Matrix State State ℝ) (v : State → ℝ) (b t : ℝ) :
    HasDerivAt (fun s => NormedSpace.exp ((b-s) • B) *ᵥ v)
      (-(B *ᵥ (NormedSpace.exp ((b-t) • B) *ᵥ v))) t := by
  have h := (matrixAction v).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_exp_smul_const' B (b-t)).scomp t ((hasDerivAt_id t).const_sub b))
  simpa only [neg_smul, one_smul, matrixAction_apply, Matrix.neg_mulVec,
    Matrix.mulVec_mulVec, Function.comp_def] using h

theorem exp_backward_coordinate_hasDerivAt (B : Matrix State State ℝ) (v : State → ℝ)
    (b t : ℝ) (i : State) :
    HasDerivAt (fun s => (NormedSpace.exp ((b-s) • B) *ᵥ v) i)
      (-(B *ᵥ (NormedSpace.exp ((b-t) • B) *ᵥ v)) i) t := by
  exact (ContinuousLinearMap.proj i).hasFDerivAt.comp_hasDerivAt t
    (exp_backward_hasDerivAt B v b t)

theorem tailPayoff_generator_zero {δ r k : ℝ} (hδ : 0 ≤ δ) (hr : 0 ≤ r) (hk : 0 ≤ k) :
    B δ r k *ᵥ tailPayoff δ r k = 0 := by
  have h := exp_backward_hasDerivAt (B δ r k) (tailPayoff δ r k) 0 0
  have he : (fun s : ℝ => NormedSpace.exp ((0-s) • B δ r k) *ᵥ tailPayoff δ r k) =
      fun _ => tailPayoff δ r k := funext (fun s => tailPayoff_harmonic hδ hr hk (0-s))
  rw [he] at h
  simpa using h.unique (hasDerivAt_const (0 : ℝ) (tailPayoff δ r k))

theorem value_early {ε τ t : ℝ} (hε : 0 ≤ ε) (hτ : ε ≤ τ) (ht0 : 0 ≤ t) (htε : t ≤ ε)
    (δ M A r k : ℝ) :
    value ε δ M A τ r k t = NormedSpace.exp ((ε-t) • B (δ+A/ε) r k) *ᵥ
      (NormedSpace.exp ((τ-ε) • B δ r k) *ᵥ
        (NormedSpace.exp (ε • B (δ+M/ε) r k) *ᵥ tailPayoff δ r k)) := by
  simp only [value, remaining_inside ht0 htε, remaining_before hτ htε,
    remaining_before (show τ ≤ τ + ε by linarith) (htε.trans hτ)]
  simp

theorem value_quiet {ε τ t : ℝ} (hε : 0 ≤ ε) (_hτ : ε ≤ τ) (htε : ε ≤ t) (htτ : t ≤ τ)
    (δ M A r k : ℝ) :
    value ε δ M A τ r k t = NormedSpace.exp ((τ-t) • B δ r k) *ᵥ
      (NormedSpace.exp (ε • B (δ+M/ε) r k) *ᵥ tailPayoff δ r k) := by
  simp only [value, remaining_after hε htε, remaining_inside htε htτ,
    remaining_before (show τ ≤ τ + ε by linarith) htτ]
  simp

theorem value_late {ε τ t : ℝ} (hε : 0 ≤ ε) (hτ : ε ≤ τ) (htτ : τ ≤ t) (htend : t ≤ τ + ε)
    (δ M A r k : ℝ) :
    value ε δ M A τ r k t = NormedSpace.exp ((τ + ε-t) • B (δ+M/ε) r k) *ᵥ
      tailPayoff δ r k := by
  simp only [value, remaining_after hε (hτ.trans htτ), remaining_after hτ htτ,
    remaining_inside htτ htend]
  simp

theorem value_tail {ε τ t : ℝ} (hε : 0 ≤ ε) (hτ : ε ≤ τ) (htend : τ + ε ≤ t)
    (δ M A r k : ℝ) : value ε δ M A τ r k t = tailPayoff δ r k := by
  have htτ : τ ≤ t := (le_add_of_nonneg_right hε).trans htend
  simp only [value, remaining_after hε (hτ.trans htτ), remaining_after hτ htτ,
    remaining_after (show τ ≤ τ + ε by linarith) htend]
  simp

theorem value_hasDerivAt {ε δ M A τ r k t : ℝ} (hε : 0 < ε) (hτ : ε ≤ τ)
    (hδ : 0 ≤ δ) (hr : 0 ≤ r) (hk : 0 ≤ k) (ht0 : 0 < t)
    (hte : t ≠ ε) (htτ : t ≠ τ) (htend : t ≠ τ + ε) (i : State) :
    HasDerivAt (fun s => value ε δ M A τ r k s i)
      (-(B (fourEpochRate ε δ M A τ t) r k *ᵥ value ε δ M A τ r k t) i) t := by
  by_cases he : t < ε
  · have heq : (fun s => value ε δ M A τ r k s i) =ᶠ[𝓝 t]
        (fun s => (NormedSpace.exp ((ε-s) • B (δ+A/ε) r k) *ᵥ
          (NormedSpace.exp ((τ-ε) • B δ r k) *ᵥ
            (NormedSpace.exp (ε • B (δ+M/ε) r k) *ᵥ tailPayoff δ r k))) i) := by
      filter_upwards [Ioo_mem_nhds ht0 he] with s hs
      exact congrFun (value_early hε.le hτ hs.1.le hs.2.le δ M A r k) i
    rw [fourEpochRate, ite_eq_left he, value_early hε.le hτ ht0.le he.le]
    exact heq.hasDerivAt_iff.mpr (exp_backward_coordinate_hasDerivAt _ _ ε t i)
  · have he' : ε < t := lt_of_le_of_ne (le_of_not_gt he) (Ne.symm hte)
    by_cases hq : t < τ
    · have heq : (fun s => value ε δ M A τ r k s i) =ᶠ[𝓝 t]
          (fun s => (NormedSpace.exp ((τ-s) • B δ r k) *ᵥ
            (NormedSpace.exp (ε • B (δ+M/ε) r k) *ᵥ tailPayoff δ r k)) i) := by
        filter_upwards [Ioo_mem_nhds he' hq] with s hs
        exact congrFun (value_quiet hε.le hτ hs.1.le hs.2.le δ M A r k) i
      rw [fourEpochRate, ite_eq_right he, ite_eq_left hq, value_quiet hε.le hτ he'.le hq.le]
      exact heq.hasDerivAt_iff.mpr (exp_backward_coordinate_hasDerivAt _ _ τ t i)
    · have hq' : τ < t := lt_of_le_of_ne (le_of_not_gt hq) (Ne.symm htτ)
      by_cases hl : t < τ + ε
      · have heq : (fun s => value ε δ M A τ r k s i) =ᶠ[𝓝 t]
            (fun s => (NormedSpace.exp ((τ + ε-s) • B (δ+M/ε) r k) *ᵥ tailPayoff δ r k) i) := by
          filter_upwards [Ioo_mem_nhds hq' hl] with s hs
          exact congrFun (value_late hε.le hτ hs.1.le hs.2.le δ M A r k) i
        rw [fourEpochRate, ite_eq_right he, ite_eq_right hq, ite_eq_left hl,
          value_late hε.le hτ hq'.le hl.le]
        exact heq.hasDerivAt_iff.mpr (exp_backward_coordinate_hasDerivAt _ _ (τ + ε) t i)
      · have hl' : τ + ε < t := lt_of_le_of_ne (le_of_not_gt hl) (Ne.symm htend)
        have heq : (fun s => value ε δ M A τ r k s i) =ᶠ[𝓝 t]
            (fun _ => tailPayoff δ r k i) := by
          filter_upwards [Ioi_mem_nhds hl'] with s hs
          exact congrFun (value_tail hε.le hτ hs.le δ M A r k) i
        rw [fourEpochRate, ite_eq_right he, ite_eq_right hq, ite_eq_right hl,
          value_tail hε.le hτ hl'.le,
          tailPayoff_generator_zero hδ hr hk]
        simpa using heq.hasDerivAt_iff.mpr (hasDerivAt_const t (tailPayoff δ r k i))

theorem value_ae_hasDerivAt {ε δ M A τ r k : ℝ} (hε : 0 < ε) (hτ : ε ≤ τ)
    (hδ : 0 ≤ δ) (hr : 0 ≤ r) (hk : 0 ≤ k) :
    ∀ᵐ t, 0 ≤ t → ∀ i, HasDerivAt (fun s => value ε δ M A τ r k s i)
      (-(B (fourEpochRate ε δ M A τ t) r k *ᵥ value ε δ M A τ r k t) i) t := by
  filter_upwards [volume.ae_ne (0 : ℝ), volume.ae_ne ε, volume.ae_ne τ,
    volume.ae_ne (τ + ε)] with t h0 he hq hl ht i
  exact value_hasDerivAt hε hτ hδ hr hk (lt_of_le_of_ne ht (Ne.symm h0)) he hq hl i

end Rhone.Statistics.Identifiability.FourEpochBackward
