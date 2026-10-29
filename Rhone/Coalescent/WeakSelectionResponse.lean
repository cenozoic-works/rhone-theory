/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Diffusion.TwoLocusStationary
public import Rhone.Coalescent.WeakSelectionTwoLocus
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # The weak-selection sampling response is the derivative of the stationary sampling moments -/

@[expose] public section

namespace Rhone

open MvPolynomial MeasureTheory Filter Topology LinearAlgebra.Recursion Analysis.TruncationRemainder
  Coalescent.TruncationRemainder

variable {KA KB : ℕ}

open Classical in
theorem Coalescent.eq_sum_of_finite_dep (T : (Config KA KB → ℝ) →ₗ[ℝ] ℝ) (D : Finset (Config KA KB))
    (hD : ∀ u v : Config KA KB → ℝ, (∀ η ∈ D, u η = v η) → T u = T v)
    (w : Config KA KB → ℝ) :
    T w = ∑ η ∈ D, w η * T (fun ζ => if ζ = η then 1 else 0) := by
  rw [hD w (∑ η ∈ D, w η • fun ζ => if ζ = η then (1 : ℝ) else 0)]
  · simp only [map_sum, map_smul, smul_eq_mul]
  · intro η hη
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq D η w]
    simp [hη]

theorem Coalescent.integral_comm_of_finite_dep {S : Type*} [MeasurableSpace S] {ν : Measure S}
    (T : (Config KA KB → ℝ) →ₗ[ℝ] ℝ) (D : Finset (Config KA KB))
    (hD : ∀ u v : Config KA KB → ℝ, (∀ η ∈ D, u η = v η) → T u = T v)
    (u : Config KA KB → S → ℝ) (hu : ∀ η, Integrable (u η) ν) :
    Integrable (fun x => T fun η => u η x) ν ∧
      ∫ x, T (fun η => u η x) ∂ν = T fun η => ∫ x, u η x ∂ν := by
  classical
  have key := Coalescent.eq_sum_of_finite_dep T D hD
  rw [show (fun x => T fun η => u η x) = _ from funext fun x => key _,
    key (fun η => ∫ x, u η x ∂ν)]
  refine ⟨integrable_finsetSum _ fun η _ => (hu η).mul_const _, ?_⟩
  rw [integral_finsetSum _ fun η _ => (hu η).mul_const _]
  simp_rw [integral_mul_const]

noncomputable def Coalescent.rhsLin (θA θB ρ : ℝ) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ)
    (ξ : Config KA KB) :
    (Config KA KB → ℝ) →ₗ[ℝ] ℝ where
  toFun u := rhs θA θB ρ πA πB u ξ
  map_add' u v := Rhone.LinearAlgebra.Recursion.rhs_add θA θB ρ πA πB u v ξ
  map_smul' c u := Rhone.LinearAlgebra.Recursion.rhs_smul θA θB ρ πA πB c u ξ

noncomputable def Coalescent.selLin (i₀ : Fin KA) (ξ : Config KA KB) : (Config KA KB → ℝ) →ₗ[ℝ] ℝ
    where
  toFun u := sel i₀ u ξ
  map_add' u v := by
    simp only [sel, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    ring
  map_smul' c u := by
    change sel i₀ (fun η => c * u η) ξ = c * sel i₀ u ξ
    have e : ∑ j, ((ξ.b j : ℕ) : ℝ) * (c * u (bToC ξ i₀ j)) =
        c * ∑ j, ((ξ.b j : ℕ) : ℝ) * u (bToC ξ i₀ j) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    simp only [sel, e]
    ring

noncomputable def Coalescent.downSet (ξ : Config KA KB) : Finset (Config KA KB) :=
  (Config.finite_le (KA := KA) (KB := KB) (ξ.nA + ξ.nB)).toFinset

theorem Coalescent.rhsLin_dep (θA θB ρ : ℝ) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ) (ξ : Config KA KB)
    (u v : Config KA KB → ℝ) (h : ∀ η ∈ Coalescent.downSet ξ, u η = v η) :
    Coalescent.rhsLin θA θB ρ πA πB ξ u = Coalescent.rhsLin θA θB ρ πA πB ξ v :=
  rhs_congr θA θB ρ πA πB ξ fun η h1 h2 =>
    h η (by simp only [Coalescent.downSet, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]; omega)

noncomputable def Coalescent.selSet (i₀ : Fin KA) (ξ : Config KA KB) : Finset (Config KA KB) := by
  classical
  exact insert ξ (insert (incA ξ i₀) (Finset.univ.image (bToC ξ i₀)))

theorem Coalescent.selLin_dep (i₀ : Fin KA) (ξ : Config KA KB) (u v : Config KA KB → ℝ)
    (h : ∀ η ∈ Coalescent.selSet i₀ ξ, u η = v η) : Coalescent.selLin i₀ ξ u = Coalescent.selLin i₀
        ξ v := by
  classical
  have h1 : u ξ = v ξ := h ξ (by simp [Coalescent.selSet])
  have h2 : u (incA ξ i₀) = v (incA ξ i₀) := h _ (by simp [Coalescent.selSet])
  have h3 : ∀ j, u (bToC ξ i₀ j) = v (bToC ξ i₀ j) := fun j => h _ (by simp [Coalescent.selSet])
  change sel i₀ u ξ = sel i₀ v ξ
  simp only [sel, h1, h2, h3]

open Classical in
theorem Coalescent.rhs_eq_sum (θA θB ρ : ℝ) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ) (ξ : Config KA KB)
    (u : Config KA KB → ℝ) :
    rhs θA θB ρ πA πB u ξ = ∑ η ∈ Coalescent.downSet ξ, u η *
      Coalescent.rhsLin θA θB ρ πA πB ξ (fun ζ => if ζ = η then 1 else 0) :=
  Coalescent.eq_sum_of_finite_dep _ _ (Coalescent.rhsLin_dep θA θB ρ πA πB ξ) u

theorem Coalescent.eval_sampleMonomial_mem_unit {x : Fin KA × Fin KB → ℝ}
    (hx : x ∈ Diffusion.gameteSimplex KA KB)
    (ξ : Config KA KB) :
    0 ≤ eval x (Diffusion.sampleMonomial ξ) ∧ eval x (Diffusion.sampleMonomial ξ) ≤ 1 := by
  have hxle : ∀ g, x g ≤ 1 := fun g =>
    hx.2 ▸ Finset.single_le_sum (fun h _ => hx.1 h) (Finset.mem_univ g)
  have hprod : ∀ {ι : Type} (s : Finset ι) (f : ι → ℝ), (∀ i ∈ s, 0 ≤ f i ∧ f i ≤ 1) →
      0 ≤ ∏ i ∈ s, f i ∧ ∏ i ∈ s, f i ≤ 1 := fun s f h =>
    ⟨Finset.prod_nonneg fun i hi => (h i hi).1,
      Finset.prod_le_one₀ (fun i hi => (h i hi).1) fun i hi => (h i hi).2⟩
  have hpow : ∀ {y : ℝ} (n : ℕ), 0 ≤ y ∧ y ≤ 1 → 0 ≤ y ^ n ∧ y ^ n ≤ 1 := fun n h =>
    ⟨pow_nonneg h.1 n, pow_le_one₀ h.1 h.2⟩
  have hA : ∀ i, 0 ≤ eval x (Diffusion.margA (KB := KB) i) ∧ eval x (Diffusion.margA (KB := KB) i) ≤
      1 := by
    intro i
    simp only [Diffusion.margA, map_sum, eval_X]
    refine ⟨Finset.sum_nonneg fun j _ => hx.1 _, ?_⟩
    calc ∑ j, x (i, j) ≤ ∑ i', ∑ j, x (i', j) :=
          Finset.single_le_sum (f := fun i' => ∑ j, x (i', j))
            (fun i' _ => Finset.sum_nonneg fun j _ => hx.1 _) (Finset.mem_univ i)
      _ = 1 := by rw [← hx.2, Fintype.sum_prod_type]
  have hB : ∀ j, 0 ≤ eval x (Diffusion.margB (KA := KA) j) ∧ eval x (Diffusion.margB (KA := KA) j) ≤
      1 := by
    intro j
    simp only [Diffusion.margB, map_sum, eval_X]
    refine ⟨Finset.sum_nonneg fun i _ => hx.1 _, ?_⟩
    calc ∑ i, x (i, j) ≤ ∑ j', ∑ i, x (i, j') :=
          Finset.single_le_sum (f := fun j' => ∑ i, x (i, j'))
            (fun j' _ => Finset.sum_nonneg fun i _ => hx.1 _) (Finset.mem_univ j)
      _ = 1 := by rw [← hx.2, Fintype.sum_prod_type, Finset.sum_comm]
  have hPA := hprod Finset.univ _ fun i _ => hpow (ξ.a i) (hA i)
  have hPB := hprod Finset.univ _ fun j _ => hpow (ξ.b j) (hB j)
  have hPC := hprod Finset.univ _ fun i _ => hprod Finset.univ _ fun j _ =>
    hpow (ξ.c i j) ⟨hx.1 (i, j), hxle (i, j)⟩
  simp only [Diffusion.sampleMonomial, Diffusion.partA, Diffusion.partB, Diffusion.partC, map_mul,
      map_prod, map_pow, eval_X]
  refine ⟨mul_nonneg (mul_nonneg hPA.1 hPB.1) hPC.1, ?_⟩
  have hPQ := mul_le_mul hPA.2 hPB.2 hPB.1 zero_le_one
  rw [one_mul] at hPQ
  have h3 := mul_le_mul hPQ hPC.2 hPC.1 zero_le_one
  rwa [one_mul] at h3

theorem Coalescent.integrable_eval_simplex (ν : Measure (Diffusion.gameteSimplex KA KB))
    [IsFiniteMeasure ν]
    (p : MvPolynomial (Fin KA × Fin KB) ℝ) :
    Integrable (fun x : Diffusion.gameteSimplex KA KB => eval (x : Fin KA × Fin KB → ℝ) p) ν :=
  ((MvPolynomial.continuous_eval p).comp continuous_subtype_val).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

noncomputable def Coalescent.samplingMoment (ν : Measure (Diffusion.gameteSimplex KA KB))
    (ξ : Config KA KB) :
    ℝ :=
  ∫ x, eval (x : Fin KA × Fin KB → ℝ) (Diffusion.sampleMonomial ξ) ∂ν

section Stationary

variable {θA θB ρ : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ} {i₀ : Fin KA} {σ : ℝ}
  {ν : Measure (Diffusion.gameteSimplex KA KB)}

theorem Diffusion.IsStationaryLaw.samplingMoment_recursion (hπA : ∑ i, πA i = 1)
    (hπB : ∑ j, πB j = 1)
    (hν : Diffusion.IsStationaryLaw θA θB ρ πA πB i₀ σ ν) (ξ : Config KA KB) :
    diag θA θB ρ ξ * Coalescent.samplingMoment ν ξ =
      rhs θA θB ρ πA πB (Coalescent.samplingMoment ν) ξ + σ * sel i₀ (Coalescent.samplingMoment ν)
          ξ := by
  have := hν.1
  have h := hν.2 (Diffusion.sampleMonomial ξ)
  have hI := Coalescent.integrable_eval_simplex ν
  set u : Config KA KB → Diffusion.gameteSimplex KA KB → ℝ :=
    fun η x => eval (x : Fin KA × Fin KB → ℝ) (Diffusion.sampleMonomial η) with hu
  have he : ∀ x : Diffusion.gameteSimplex KA KB,
      eval (x : Fin KA × Fin KB → ℝ)
          (Diffusion.twoLocusGenerator θA θB ρ πA πB i₀ σ (Diffusion.sampleMonomial ξ)) =
        (Coalescent.rhsLin θA θB ρ πA πB ξ fun η => u η x) - diag θA θB ρ ξ * u ξ x +
          σ * Coalescent.selLin i₀ ξ fun η => u η x :=
    fun x => Diffusion.eval_twoLocusGenerator_sampleMonomial θA θB ρ hπA hπB i₀ σ x.2.2 ξ
  rw [integral_congr_ae (Eventually.of_forall he)] at h
  obtain ⟨hR, hRi⟩ := Coalescent.integral_comm_of_finite_dep (ν := ν)
      (Coalescent.rhsLin θA θB ρ πA πB ξ)
      (Coalescent.downSet ξ)
    (Coalescent.rhsLin_dep θA θB ρ πA πB ξ) u fun η => hI _
  obtain ⟨hS, hSi⟩ := Coalescent.integral_comm_of_finite_dep (ν := ν) (Coalescent.selLin i₀ ξ)
      (Coalescent.selSet i₀ ξ)
    (Coalescent.selLin_dep i₀ ξ) u fun η => hI _
  have i1 : Integrable (fun x => (Coalescent.rhsLin θA θB ρ πA πB ξ fun η => u η x) -
      diag θA θB ρ ξ * u ξ x) ν := hR.sub ((hI _).const_mul _)
  have i2 : Integrable (fun x => σ * Coalescent.selLin i₀ ξ fun η => u η x) ν := hS.const_mul _
  have i3 : Integrable (fun x => diag θA θB ρ ξ * u ξ x) ν := (hI _).const_mul _
  rw [integral_add i1 i2, integral_sub hR i3, integral_const_mul, integral_const_mul, hRi,
    hSi] at h
  change rhs θA θB ρ πA πB (Coalescent.samplingMoment ν) ξ - diag θA θB ρ ξ *
      Coalescent.samplingMoment ν ξ +
    σ * sel i₀ (Coalescent.samplingMoment ν) ξ = 0 at h
  linarith

theorem Diffusion.IsStationaryLaw.samplingMoment_empty
    (hν : Diffusion.IsStationaryLaw θA θB ρ πA πB i₀ σ ν) :
    Coalescent.samplingMoment ν 0 = 1 := by
  have := hν.1
  simp [Coalescent.samplingMoment, Diffusion.sampleMonomial, Diffusion.partA, Diffusion.partB,
      Diffusion.partC]

theorem Diffusion.IsStationaryLaw.abs_samplingMoment_le
    (hν : Diffusion.IsStationaryLaw θA θB ρ πA πB i₀ σ ν)
    (ξ : Config KA KB) : |Coalescent.samplingMoment ν ξ| ≤ 1 := by
  have := hν.1
  have := norm_integral_le_of_norm_le_const (μ := ν) (C := 1)
    (f := fun x : Diffusion.gameteSimplex KA KB
        => eval (x : Fin KA × Fin KB → ℝ) (Diffusion.sampleMonomial ξ))
    (Eventually.of_forall fun x => by
      obtain ⟨h0, h1⟩ := Coalescent.eval_sampleMonomial_mem_unit x.2 ξ
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      exact h1)
  simpa [Coalescent.samplingMoment] using this

theorem Diffusion.IsStationaryLaw.samplingMoment_eq_q (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hπA : ∑ i, πA i = 1) (hπB : ∑ j, πB j = 1)
        (hν : Diffusion.IsStationaryLaw θA θB ρ πA πB i₀ 0 ν) :
    Coalescent.samplingMoment ν = Rhone.LinearAlgebra.Recursion.q (πA := πA) (πB := πB) hθA hθB
        hρ :=
  Coalescent.eq_q_of_recursion hθA hθB hρ hν.samplingMoment_empty fun ξ _ => by
    rw [hν.samplingMoment_recursion hπA hπB ξ, zero_mul, add_zero]

end Stationary

section Limit

variable {θA θB ρ : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ}

theorem Coalescent.tendsto_of_recursion (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) {ι : Type*}
    {l : Filter ι} {u s : ι → Config KA KB → ℝ} {c : ι → ℝ} {c₀ : ℝ}
    {s₀ w : Config KA KB → ℝ} (hc : Tendsto c l (𝓝 c₀))
    (hs : ∀ ξ, Tendsto (fun k => s k ξ) l (𝓝 (s₀ ξ)))
    (hu : ∀ᶠ k in l, u k 0 = c k ∧ ∀ ξ : Config KA KB, 1 ≤ ξ.n →
      diag θA θB ρ ξ * u k ξ = rhs θA θB ρ πA πB (u k) ξ + s k ξ)
    (hw0 : w 0 = c₀)
    (hw : ∀ ξ : Config KA KB, 1 ≤ ξ.n → diag θA θB ρ ξ * w ξ = rhs θA θB ρ πA πB w ξ + s₀ ξ)
    (ξ : Config KA KB) : Tendsto (fun k => u k ξ) l (𝓝 (w ξ)) := by
  suffices H : ∀ N : ℕ, ∀ ξ : Config KA KB, ξ.nA + ξ.nB = N →
      Tendsto (fun k => u k ξ) l (𝓝 (w ξ)) from H _ ξ rfl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N IH =>
  have hinj := Coalescent.levelOp_injective (πA := πA) (πB := πB) hθA hθB hρ N
  set E := LinearEquiv.ofInjectiveEndo (Coalescent.levelOp θA θB ρ πA πB N) hinj with hE
  have hEcont : Continuous (E.symm : (↥{ξ : Config KA KB | ξ.nA + ξ.nB = N} → ℝ) →
      (↥{ξ : Config KA KB | ξ.nA + ξ.nB = N} → ℝ)) :=
    E.symm.toLinearMap.continuous_of_finiteDimensional
  let b : (Config KA KB → ℝ) → ℝ → (Config KA KB → ℝ) →
      ↥{ξ : Config KA KB | ξ.nA + ξ.nB = N} → ℝ := fun g c0 sg ζ =>
    if 1 ≤ (ζ : Config KA KB).n then rhs θA θB ρ πA πB (offLevel N g) ζ + sg ζ else c0
  have hlevel : ∀ (g : Config KA KB → ℝ) (c0 : ℝ) (sg : Config KA KB → ℝ), g 0 = c0 →
      (∀ ξ : Config KA KB, 1 ≤ ξ.n → diag θA θB ρ ξ * g ξ = rhs θA θB ρ πA πB g ξ + sg ξ) →
      (fun ζ : ↥{ξ : Config KA KB | ξ.nA + ξ.nB = N} => g ζ) = E.symm (b g c0 sg) := by
    intro g c0 sg hg0 hg
    rw [eq_comm, LinearEquiv.symm_apply_eq]
    funext ζ
    rw [hE, LinearEquiv.coe_ofInjectiveEndo]
    simp only [Coalescent.levelOp, LinearMap.coe_mk, AddHom.coe_mk, b]
    split_ifs with hn
    · have hsplit : rhs θA θB ρ πA πB g ζ = rhs θA θB ρ πA πB
          (extZero N fun ζ : ↥{ξ : Config KA KB | ξ.nA + ξ.nB = N} => g ζ) ζ +
          rhs θA θB ρ πA πB (offLevel N g) ζ := by
        rw [← Rhone.LinearAlgebra.Recursion.rhs_add]
        congr 1
        funext η
        simp only [extZero, offLevel]
        by_cases h : η.nA + η.nB = N <;> simp [h]
      linarith [hg ζ hn]
    · rw [(ζ : Config KA KB).eq_zero_of_n_eq_zero (by omega), hg0]
  have hb : Tendsto (fun k => b (u k) (c k) (s k)) l (𝓝 (b w c₀ s₀)) := by
    rw [tendsto_pi_nhds]
    intro ζ
    have hζ : (ζ : Config KA KB).nA + (ζ : Config KA KB).nB = N := ζ.2
    simp only [b]
    split_ifs with hn
    · refine Tendsto.add ?_ (hs ζ)
      rw [Coalescent.rhs_eq_sum θA θB ρ πA πB ζ (offLevel N w)]
      refine Tendsto.congr
          (fun k => (Coalescent.rhs_eq_sum θA θB ρ πA πB ζ (offLevel N (u k))).symm) ?_
      refine tendsto_finsetSum _ fun η hη => Tendsto.mul_const _ ?_
      have hle : η.nA + η.nB ≤ N := by
        simp only [Coalescent.downSet, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hη
        omega
      simp only [offLevel]
      by_cases hlev : η.nA + η.nB = N
      · simp only [hlev, ite_true]
        exact tendsto_const_nhds
      · simp only [hlev, ite_false]
        exact IH _ (by omega) η rfl
    · exact hc
  have hv : Tendsto (fun k => fun ζ : ↥{ξ : Config KA KB | ξ.nA + ξ.nB = N} => u k ζ) l
      (𝓝 fun ζ => w ζ) := by
    rw [hlevel w c₀ s₀ hw0 hw]
    refine Tendsto.congr' ?_ ((hEcont.tendsto _).comp hb)
    filter_upwards [hu] with k hk
    exact (hlevel (u k) (c k) (s k) hk.1 hk.2).symm
  intro ξ hξ
  exact ((continuous_apply (⟨ξ, hξ⟩ : ↥{ξ : Config KA KB | ξ.nA + ξ.nB = N})).tendsto _).comp hv

end Limit

section Derivative

variable {θA θB ρ : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ} {i₀ : Fin KA}

theorem Coalescent.tendsto_sel {ι : Type*} {l : Filter ι} (i₀ : Fin KA) {u : ι → Config KA KB → ℝ}
    {w : Config KA KB → ℝ} (h : ∀ η, Tendsto (fun k => u k η) l (𝓝 (w η)))
    (ξ : Config KA KB) : Tendsto (fun k => sel i₀ (u k) ξ) l (𝓝 (sel i₀ w ξ)) := by
  simp only [sel]
  exact (((h ξ).const_mul _).add (tendsto_finsetSum _ fun j _ => (h _).const_mul _)).sub
    ((h _).const_mul _)

theorem Coalescent.abs_sel_le (i₀ : Fin KA) {u : Config KA KB → ℝ} (hu : ∀ η, |u η| ≤ 1)
    (ξ : Config KA KB) :
    |sel i₀ u ξ| ≤ ((ξ.mA i₀ : ℕ) : ℝ) + ∑ j, ((ξ.b j : ℕ) : ℝ) + ((ξ.n : ℕ) : ℝ) := by
  have hm : ∀ (a : ℕ) (η : Config KA KB), |(a : ℝ) * u η| ≤ a := fun a η => by
    rw [abs_mul, Nat.abs_cast]
    exact mul_le_of_le_one_right (Nat.cast_nonneg _) (hu η)
  have h2 : |∑ j, ((ξ.b j : ℕ) : ℝ) * u (bToC ξ i₀ j)| ≤ ∑ j, ((ξ.b j : ℕ) : ℝ) :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => hm _ _)
  have h1 := hm (ξ.mA i₀) ξ
  have h3 := hm ξ.n (incA ξ i₀)
  simp only [sel]
  have e := abs_add_le (((ξ.mA i₀ : ℕ) : ℝ) * u ξ + ∑ j, ((ξ.b j : ℕ) : ℝ) * u (bToC ξ i₀ j))
    (-(((ξ.n : ℕ) : ℝ) * u (incA ξ i₀)))
  rw [← sub_eq_add_neg, abs_neg] at e
  linarith [abs_add_le (((ξ.mA i₀ : ℕ) : ℝ) * u ξ) (∑ j, ((ξ.b j : ℕ) : ℝ) * u (bToC ξ i₀ j))]

theorem Coalescent.tendsto_samplingMoment (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hπA : ∑ i, πA i = 1) (hπB : ∑ j, πB j = 1) {ν : ℝ → Measure (Diffusion.gameteSimplex KA KB)}
    (hν : ∀ σ, Diffusion.IsStationaryLaw θA θB ρ πA πB i₀ σ (ν σ)) (ξ : Config KA KB) :
    Tendsto (fun σ => Coalescent.samplingMoment (ν σ) ξ) (𝓝 0)
      (𝓝 (Rhone.LinearAlgebra.Recursion.q (πA := πA) (πB := πB) hθA hθB hρ ξ)) := by
  have hq := q_isSolution (πA := πA) (πB := πB) hθA hθB hρ
  refine Coalescent.tendsto_of_recursion (πA := πA) (πB := πB) hθA hθB hρ
      (c := fun _ => 1) (c₀ := 1)
    (s := fun σ η => σ * sel i₀ (Coalescent.samplingMoment (ν σ)) η) (s₀ := fun _ => 0)
    tendsto_const_nhds (fun η => ?_)
    (Eventually.of_forall fun σ => ⟨(hν σ).samplingMoment_empty, fun η _ =>
      (hν σ).samplingMoment_recursion hπA hπB η⟩) hq.empty
    (fun η _ => by
      show _ = _ + 0
      rw [add_zero]
      exact Rhone.Probability.Denominator.recursion_all hθA hθB hρ hq η) ξ
  set B : ℝ := ((η.mA i₀ : ℕ) : ℝ) + ∑ j, ((η.b j : ℕ) : ℝ) + ((η.n : ℕ) : ℝ)
  refine squeeze_zero_norm (a := fun σ : ℝ => |σ| * B) (fun σ => ?_) ?_
  · rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left
      (Coalescent.abs_sel_le i₀ (fun ζ => (hν σ).abs_samplingMoment_le ζ) η) (abs_nonneg _)
  · simpa using ((continuous_abs.tendsto (0 : ℝ)).mul_const B)

theorem Coalescent.hasDerivAt_samplingMoment (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    (hπA : ∑ i, πA i = 1) (hπB : ∑ j, πB j = 1) {ν : ℝ → Measure (Diffusion.gameteSimplex KA KB)}
    (hν : ∀ σ, Diffusion.IsStationaryLaw θA θB ρ πA πB i₀ σ (ν σ)) (ξ : Config KA KB) :
    HasDerivAt (fun σ => Coalescent.samplingMoment (ν σ) ξ)
      (Coalescent.selResponse (πA := πA) (πB := πB) hθA hθB hρ i₀ ξ) 0 := by
  set q := Rhone.LinearAlgebra.Recursion.q (πA := πA) (πB := πB) hθA hθB hρ with hqdef
  have hq := q_isSolution (πA := πA) (πB := πB) hθA hθB hρ
  have h0 : Coalescent.samplingMoment (ν 0) = q := (hν 0).samplingMoment_eq_q hθA hθB hρ hπA hπB
  have hm := Coalescent.tendsto_samplingMoment hθA hθB hρ hπA hπB hν
  rw [hasDerivAt_iff_tendsto_slope]
  have hslope : ∀ σ : ℝ, slope (fun σ => Coalescent.samplingMoment (ν σ) ξ) 0 σ =
      σ⁻¹ * (Coalescent.samplingMoment (ν σ) ξ - q ξ) := fun σ => by
    rw [slope_def_field, h0, sub_zero, div_eq_inv_mul]
  rw [show slope (fun σ => Coalescent.samplingMoment (ν σ) ξ) 0 = _ from funext hslope]
  refine Coalescent.tendsto_of_recursion (πA := πA) (πB := πB) hθA hθB hρ
    (u := fun σ η => σ⁻¹ * (Coalescent.samplingMoment (ν σ) η - q η)) (c := fun _ => 0) (c₀ := 0)
    (s := fun σ η => sel i₀ (Coalescent.samplingMoment (ν σ)) η) (s₀ := sel i₀ q)
    tendsto_const_nhds
        (fun η => Coalescent.tendsto_sel i₀ (fun ζ => (hm ζ).mono_left nhdsWithin_le_nhds) η)
    ?_ (Coalescent.selResponse_spec hθA hθB hρ i₀).1 (Coalescent.selResponse_spec hθA hθB hρ i₀).2 ξ
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  have hσ' : σ ≠ 0 := hσ
  refine ⟨by
    simp only [(hν σ).samplingMoment_empty, hqdef, hq.empty, sub_self, mul_zero], fun η hη => ?_⟩
  have h1 := (hν σ).samplingMoment_recursion hπA hπB η
  have h2 := Rhone.Probability.Denominator.recursion_all hθA hθB hρ hq η
  have hr : rhs θA θB ρ πA πB (fun η => σ⁻¹ * (Coalescent.samplingMoment (ν σ) η - q η)) η =
      σ⁻¹ * (rhs θA θB ρ πA πB (Coalescent.samplingMoment (ν σ)) η - rhs θA θB ρ πA πB q η) := by
    rw [Rhone.LinearAlgebra.Recursion.rhs_smul, Rhone.LinearAlgebra.Recursion.rhs_sub]
  have hs1 : σ⁻¹ * σ = 1 := inv_mul_cancel₀ hσ'
  rw [hr]
  linear_combination σ⁻¹ * (h1 - h2) + sel i₀ (Coalescent.samplingMoment (ν σ)) η * hs1

theorem Coalescent.exists_stationary_hasDerivAt_samplingMoment (hθA : 0 < θA) (hθB : 0 < θB)
    (hρ : 0 ≤ ρ)
    (hπA0 : ∀ i, 0 ≤ πA i) (hπB0 : ∀ j, 0 ≤ πB j) (hπA : ∑ i, πA i = 1) (hπB : ∑ j, πB j = 1)
    (i₀ : Fin KA) :
    ∃ ν : ℝ → Measure (Diffusion.gameteSimplex KA KB),
      (∀ σ, Diffusion.IsStationaryLaw θA θB ρ πA πB i₀ σ (ν σ)) ∧
      ∀ ξ : Config KA KB, HasDerivAt (fun σ => Coalescent.samplingMoment (ν σ) ξ)
        (Coalescent.selResponse (πA := πA) (πB := πB) hθA hθB hρ i₀ ξ) 0 := by
  choose ν hν using fun σ =>
    Diffusion.exists_isStationaryLaw hθA.le hθB.le hρ hπA0 hπB0 hπA hπB i₀ σ
  exact ⟨ν, hν, Coalescent.hasDerivAt_samplingMoment hθA hθB hρ hπA hπB hν⟩

end Derivative

end Rhone
