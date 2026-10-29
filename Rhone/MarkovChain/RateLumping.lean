/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.MarkovChain.LumpingTrajectory
public import Rhone.MarkovChain.JumpHold
public import Rhone.MarkovChain.Semigroup

/-! # Lumping a continuous-time chain along a function of the state -/

@[expose] public section

namespace Rhone.MarkovChain.RateChain

open Finset Matrix NormedSpace MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {S T : Type*} [Fintype S] [Fintype T] [DecidableEq T]

def Lumps (R : RateChain S) (f : S → T) (R' : RateChain T) : Prop :=
  ∀ x t, ∑ y with f y = t, R.Q x y = R'.Q (f x) t

def IsLumpable (R : RateChain S) (f : S → T) : Prop :=
  ∀ x x', f x = f x' → ∀ t, ∑ y with f y = t, R.Q x y = ∑ y with f y = t, R.Q x' y

open Classical in
noncomputable def lump (R : RateChain S) (f : S → T) : RateChain T where
  Q t t' := if h : ∃ x, f x = t then ∑ y with f y = t', R.Q h.choose y else 0
  off_diag_nonneg t t' htt' := by
    split_ifs with h
    · refine Finset.sum_nonneg fun y hy => R.off_diag_nonneg _ y fun hxy => htt' ?_
      rw [← h.choose_spec, hxy, (Finset.mem_filter.1 hy).2]
    · exact le_rfl
  row_sum t := by
    by_cases h : ∃ x, f x = t
    · simp only [h, ↓reduceDIte]
      rw [Finset.sum_fiberwise univ f fun y => R.Q h.choose y, R.row_sum]
    · simp [h]

variable {R : RateChain S} {f : S → T} {R' : RateChain T}

theorem IsLumpable.lumps_lump (h : R.IsLumpable f) : R.Lumps f (R.lump f) := by
  intro x t
  have hex : ∃ x', f x' = f x := ⟨x, rfl⟩
  simp only [lump, hex, ↓reduceDIte]
  exact h x _ hex.choose_spec.symm t

theorem Lumps.isLumpable (hL : R.Lumps f R') : R.IsLumpable f := by
  intro x x' hxx' t
  rw [hL x t, hL x' t, hxx']

theorem Lumps.mulVec_comp (hL : R.Lumps f R') (g : T → ℝ) :
    R.Q *ᵥ (g ∘ f) = (R'.Q *ᵥ g) ∘ f := by
  funext x
  change ∑ y, R.Q x y * (g ∘ f) y = ∑ t, R'.Q (f x) t * g t
  refine (Finset.sum_fiberwise univ f fun y => R.Q x y * (g ∘ f) y).symm.trans ?_
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← hL x t, Finset.sum_mul]
  exact Finset.sum_congr rfl fun y hy => by
    rw [Function.comp_apply, (Finset.mem_filter.1 hy).2]

theorem Lumps.sum_Q_mul_comp (hL : R.Lumps f R') (g : T → ℝ) (x : S) :
    ∑ y, R.Q x y * g (f y) = ∑ t, R'.Q (f x) t * g t :=
  congrFun (hL.mulVec_comp g) x

section Semigroup

variable [DecidableEq S]

theorem Lumps.pow_mulVec_comp (hL : R.Lumps f R') (c : ℝ) (n : ℕ) (g : T → ℝ) :
    (c • R.Q) ^ n *ᵥ (g ∘ f) = ((c • R'.Q) ^ n *ᵥ g) ∘ f := by
  induction n generalizing g with
  | zero => simp
  | succ n ih =>
    have h1 : (c • R.Q) *ᵥ (g ∘ f) = ((c • R'.Q) *ᵥ g) ∘ f := by
      rw [Matrix.smul_mulVec, Matrix.smul_mulVec, hL.mulVec_comp]
      rfl
    rw [pow_succ, pow_succ, ← mulVec_mulVec, ← mulVec_mulVec, h1, ih]

private theorem hasSum_exp_mulVec {U : Type*} [Fintype U] [DecidableEq U] (B : Matrix U U ℝ)
    (v : U → ℝ) (u : U) :
    HasSum (fun n : ℕ => ((n.factorial : ℝ)⁻¹) * (B ^ n *ᵥ v) u) ((exp B *ᵥ v) u) := by
  have hentry : ∀ y, HasSum (fun n : ℕ => ((n.factorial : ℝ)⁻¹) * (B ^ n) u y) (exp B u y) := by
    intro y
    open scoped Matrix.Norms.Operator in
    exact (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℝ u y)).hasSum
      (exp_series_hasSum_exp' (𝕂 := ℝ) B)
  have hsum := hasSum_sum (s := univ) fun y _ => (hentry y).mul_right (v y)
  refine hsum.congr_fun fun n => ?_
  change ((n.factorial : ℝ)⁻¹) * ∑ y, (B ^ n) u y * v y = _
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by ring

theorem Lumps.semigroup_mulVec_comp (hL : R.Lumps f R') (t : ℝ) (g : T → ℝ) :
    R.semigroup t *ᵥ (g ∘ f) = (R'.semigroup t *ᵥ g) ∘ f := by
  funext x
  have h1 := hasSum_exp_mulVec (t • R.Q) (g ∘ f) x
  have h2 := hasSum_exp_mulVec (t • R'.Q) g (f x)
  have h3 : ∀ n : ℕ, ((n.factorial : ℝ)⁻¹) * ((t • R.Q) ^ n *ᵥ (g ∘ f)) x =
      ((n.factorial : ℝ)⁻¹) * ((t • R'.Q) ^ n *ᵥ g) (f x) := fun n => by
    rw [hL.pow_mulVec_comp t n g]
    rfl
  exact h1.unique (h2.congr_fun h3)

theorem Lumps.sum_semigroup_fibre (hL : R.Lumps f R') (t : ℝ) (x : S) (s : T) :
    ∑ y with f y = s, R.semigroup t x y = R'.semigroup t (f x) s := by
  have h := congrFun (hL.semigroup_mulVec_comp t fun u => if u = s then (1 : ℝ) else 0) x
  simp only [mulVec, dotProduct, Function.comp_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', mem_univ, ↓reduceIte] at h
  rw [Finset.sum_filter]
  exact h

end Semigroup

theorem Lumps.expectedCost_preimage [DecidableEq S] (hL : R.Lumps f R') {B : Finset T}
    (hA : R.jumpChain.IsAbsorbingSet (preimageFinset f B))
    (hR : R.jumpChain.Reaches (preimageFinset f B))
    (hq : ∀ x, x ∉ preimageFinset f B → R.rate x ≠ 0)
    (hB : R'.jumpChain.IsAbsorbingSet B) (hR' : R'.jumpChain.Reaches B)
    (hq' : ∀ t, t ∉ B → R'.rate t ≠ 0) (c : T → ℝ) (x : S) :
    R.expectedCost (preimageFinset f B) (c ∘ f) x = R'.expectedCost B c (f x) := by
  refine (congrFun (eq_expectedCost_of_generator hA hR hq
    (u := fun y => R'.expectedCost B c (f y)) (fun a ha => ?_) fun y hy => ?_) x).symm
  · exact expectedCost_of_mem hB (mem_preimageFinset.1 ha) c
  · have hy' : f y ∉ B := fun h => hy (mem_preimageFinset.2 h)
    rw [hL.sum_Q_mul_comp (R'.expectedCost B c) y, expectedCost_generator hB hR' c hy' (hq' _ hy')]
    rfl

theorem Lumps.rate_eq (hL : R.Lumps f R') (hj : ∀ x y, x ≠ y → f x = f y → R.Q x y = 0)
    (x : S) : R.rate x = R'.rate (f x) := by
  rw [rate, rate, ← hL x (f x)]
  congr 1
  symm
  exact Finset.sum_eq_single_of_mem x (Finset.mem_filter.2 ⟨mem_univ x, rfl⟩) fun y hy hyx =>
    hj x y (Ne.symm hyx) (Finset.mem_filter.1 hy).2.symm

variable [DecidableEq S]

theorem Lumps.jumpChain_lumps (hL : R.Lumps f R')
    (hj : ∀ x y, x ≠ y → f x = f y → R.Q x y = 0) : R.jumpChain.Lumps f R'.jumpChain := by
  intro x t
  have hrate := hL.rate_eq hj x
  simp only [jumpChain_P, jumpMatrix]
  by_cases hx : R.rate x = 0
  · have hx' : R'.rate (f x) = 0 := hrate ▸ hx
    simp only [hx, hx', ↓reduceIte]
    rw [Finset.sum_ite_eq]
    simp [Finset.mem_filter]
  · have hx' : R'.rate (f x) ≠ 0 := hrate ▸ hx
    simp only [hx, hx', ↓reduceIte]
    by_cases ht : f x = t
    · simp only [ht, ↓reduceIte]
      refine Finset.sum_eq_zero fun y hy => ?_
      by_cases hxy : x = y
      · simp [hxy]
      · simp only [hxy, ↓reduceIte]
        rw [hj x y hxy (ht.trans (Finset.mem_filter.1 hy).2.symm), zero_div]
    · simp only [ht, ↓reduceIte]
      rw [← hrate, ← hL x t, Finset.sum_div]
      refine Finset.sum_congr rfl fun y hy => ?_
      have hxy : x ≠ y := fun h => ht (h ▸ (Finset.mem_filter.1 hy).2)
      simp only [hxy, ↓reduceIte]

theorem Lumps.costBefore_map (hL : R.Lumps f R')
    (hj : ∀ x y, x ≠ y → f x = f y → R.Q x y = 0) (B : Finset T) (c : T → ℝ)
    (p : (ℕ → S) × (ℕ → ℝ)) :
    R.costBefore (preimageFinset f B) (c ∘ f) p =
      R'.costBefore B c (Prod.map (fun ω n => f (ω n)) id p) := by
  unfold costBefore holdTime
  refine tsum_congr fun k => ?_
  simp only [mem_preimageFinset, Prod.map_fst, Prod.map_snd, id, Function.comp_apply,
    hL.rate_eq hj]

variable [MeasurableSpace S] [DiscreteMeasurableSpace S]

omit [Fintype T] [DecidableEq T] in
theorem measurable_costBefore (R : RateChain S) (A : Finset S) (c : S → ℝ) :
    Measurable (R.costBefore A c) := by
  unfold costBefore
  simp_rw [ENNReal.tsum_eq_iSup_sum]
  refine .iSup fun s => s.measurable_fun_sum fun k _ => ?_
  have h1 : Measurable fun p : (ℕ → S) × (ℕ → ℝ) => p.1 k :=
    (measurable_pi_apply k).comp measurable_fst
  have h2 : Measurable fun p : (ℕ → S) × (ℕ → ℝ) => p.2 k :=
    (measurable_pi_apply k).comp measurable_snd
  refine Measurable.ite (h1 (MeasurableSet.of_discrete (s := (A : Set S)))) measurable_const ?_
  refine ENNReal.measurable_ofReal.comp ?_
  exact ((Measurable.of_discrete (f := c)).comp h1).mul
    (h2.div ((Measurable.of_discrete (f := R.rate)).comp h1))

variable [MeasurableSpace T] [DiscreteMeasurableSpace T]

theorem Lumps.map_jumpHoldLaw (hL : R.Lumps f R')
    (hj : ∀ x y, x ≠ y → f x = f y → R.Q x y = 0) (x : S) :
    (R.jumpHoldLaw x).map (Prod.map (fun ω n => f (ω n)) id) = R'.jumpHoldLaw (f x) := by
  have hF : Measurable fun (ω : ℕ → S) (n : ℕ) => f (ω n) :=
    measurable_pi_iff.2 fun n => (Measurable.of_discrete (f := f)).comp (measurable_pi_apply n)
  rw [jumpHoldLaw, jumpHoldLaw, ← Measure.map_prod_map _ _ hF measurable_id,
    (hL.jumpChain_lumps hj).map_pathLaw, Measure.map_id]

theorem Lumps.map_costBefore (hL : R.Lumps f R')
    (hj : ∀ x y, x ≠ y → f x = f y → R.Q x y = 0) (B : Finset T) (c : T → ℝ) (x : S) :
    (R.jumpHoldLaw x).map (R.costBefore (preimageFinset f B) (c ∘ f)) =
      (R'.jumpHoldLaw (f x)).map (R'.costBefore B c) := by
  have hF : Measurable fun (ω : ℕ → S) (n : ℕ) => f (ω n) :=
    measurable_pi_iff.2 fun n => (Measurable.of_discrete (f := f)).comp (measurable_pi_apply n)
  rw [← hL.map_jumpHoldLaw hj x,
    Measure.map_map (R'.measurable_costBefore B c) (hF.prodMap measurable_id)]
  congr 1
  funext p
  exact hL.costBefore_map hj B c p

theorem Lumps.lintegral_costBefore_preimage (hL : R.Lumps f R')
    (hj : ∀ x y, x ≠ y → f x = f y → R.Q x y = 0) (B : Finset T) (c : T → ℝ) (x : S) :
    ∫⁻ p, R.costBefore (preimageFinset f B) (c ∘ f) p ∂R.jumpHoldLaw x =
      ∫⁻ p, R'.costBefore B c p ∂R'.jumpHoldLaw (f x) := by
  have hF : Measurable fun (ω : ℕ → S) (n : ℕ) => f (ω n) :=
    measurable_pi_iff.2 fun n => (Measurable.of_discrete (f := f)).comp (measurable_pi_apply n)
  rw [← hL.map_jumpHoldLaw hj x,
    lintegral_map (R'.measurable_costBefore B c) (hF.prodMap measurable_id)]
  exact lintegral_congr fun p => hL.costBefore_map hj B c p

end Rhone.MarkovChain.RateChain
