/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.RecombinationExpansion.Kernel
public import Rhone.Probability.Denominator.Product

/-! # Large-ρ limits of the recursion terms: `q → q_A(m^A) q_B(m^B)` -/

@[expose] public section

namespace Rhone.Probability.RecombinationExpansion

open Filter Topology
open LinearAlgebra.Recursion LinearAlgebra.Recursion.Config Analysis.RecombinationExpansion

variable {KA KB : ℕ} {θA θB : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ}

section Continuity

variable {α : Type*} {l : Filter α}

theorem tendsto_rhs (f : α → Config KA KB → ℝ) (G : Config KA KB → ℝ)
    (hf : ∀ η, Tendsto (fun r => f r η) l (𝓝 (G η))) (ρ₀ : ℝ) (ξ : Config KA KB) :
    Tendsto (fun r => rhs θA θB ρ₀ πA πB (f r) ξ) l (𝓝 (rhs θA θB ρ₀ πA πB G ξ)) := by
  simp only [rhs]
  refine Tendsto.add (Tendsto.add (Tendsto.add (Tendsto.add (Tendsto.add
    (Tendsto.add ?_ ?_) ?_) ?_) ?_) ?_) ?_
  · exact tendsto_finsetSum _ fun i _ => tendsto_const_nhds.mul (hf _)
  · exact tendsto_finsetSum _ fun j _ => tendsto_const_nhds.mul (hf _)
  · exact tendsto_finsetSum _ fun i _ =>
      tendsto_finsetSum _ fun j _ => tendsto_const_nhds.mul (hf _)
  · exact tendsto_finsetSum _ fun i _ =>
      tendsto_finsetSum _ fun j _ => tendsto_const_nhds.mul (hf _)
  · exact tendsto_const_nhds.mul (tendsto_finsetSum _ fun i _ => tendsto_const_nhds.mul
      ((tendsto_const_nhds.mul (hf _)).add
        (tendsto_finsetSum _ fun j _ => tendsto_const_nhds.mul (hf _))))
  · exact tendsto_const_nhds.mul (tendsto_finsetSum _ fun j _ => tendsto_const_nhds.mul
      ((tendsto_const_nhds.mul (hf _)).add
        (tendsto_finsetSum _ fun i _ => tendsto_const_nhds.mul (hf _))))
  · exact tendsto_const_nhds.mul (tendsto_finsetSum _ fun i _ =>
      tendsto_finsetSum _ fun j _ => tendsto_const_nhds.mul (hf _))

theorem tendsto_Lop (f : α → Config KA KB → ℝ) (G : Config KA KB → ℝ)
    (hf : ∀ η, Tendsto (fun r => f r η) l (𝓝 (G η))) (ρ₀ : ℝ) (ξ : Config KA KB) :
    Tendsto (fun r => Lop θA θB ρ₀ πA πB (f r) ξ) l (𝓝 (Lop θA θB ρ₀ πA πB G ξ)) := by
  simp only [Lop]
  exact (tendsto_const_nhds.mul (hf ξ)).sub (tendsto_rhs f G hf ρ₀ ξ)

theorem tendsto_L0 (f : α → Config KA KB → ℝ) (G : Config KA KB → ℝ)
    (hf : ∀ η, Tendsto (fun r => f r η) l (𝓝 (G η))) (ξ : Config KA KB) :
    Tendsto (fun r => L0 θA θB πA πB (f r) ξ) l (𝓝 (L0 θA θB πA πB G ξ)) :=
  tendsto_Lop f G hf 0 ξ

theorem tendsto_L1 (f : α → Config KA KB → ℝ) (G : Config KA KB → ℝ)
    (hf : ∀ η, Tendsto (fun r => f r η) l (𝓝 (G η))) (ξ : Config KA KB) :
    Tendsto (fun r => L1 (f r) ξ) l (𝓝 (L1 G ξ)) := by
  simp only [L1]
  exact (tendsto_const_nhds.mul (hf ξ)).sub
    (tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => tendsto_const_nhds.mul (hf _))

end Continuity

theorem nA_of_mA_eq {ξ η : Config KA KB} (h : η.mA = ξ.mA) : η.nA = ξ.nA := by
  rw [← ξ.sum_mA, ← η.sum_mA, h]

theorem nB_of_mB_eq {ξ η : Config KA KB} (h : η.mB = ξ.mB) : η.nB = ξ.nB := by
  rw [← ξ.sum_mB, ← η.sum_mB, h]

@[simp] theorem nA_sectorBase (ξ : Config KA KB) : (sectorBase ξ).nA = ξ.nA :=
  nA_of_mA_eq (mA_sectorBase ξ)

@[simp] theorem nB_sectorBase (ξ : Config KA KB) : (sectorBase ξ).nB = ξ.nB :=
  nB_of_mB_eq (mB_sectorBase ξ)

theorem two_le_n_of_two_le (ξ : Config KA KB) (_hA : 2 ≤ ξ.nA) (hB : 2 ≤ ξ.nB) : 2 ≤ ξ.n := by
  have h1 := ξ.n_add_t
  have h2 := ξ.t_le_nA
  omega

section Limit

variable {Q : ℝ → Config KA KB → ℝ} {Φ : Config KA KB → ℝ}

theorem L1_limit_eq_zero (hθA : 0 < θA) (hθB : 0 < θB)
    (hQ : ∀ ρ : ℝ, 0 < ρ → IsSolution θA θB ρ πA πB (Q ρ))
    (hlim : ∀ η : Config KA KB,
      Tendsto (fun ρ => Q ρ η - qHat θA θB πA πB η) atTop (𝓝 (Φ η)))
    (ξ : Config KA KB) (hn : 2 ≤ ξ.n) : L1 Φ ξ = 0 := by
  have hnum : Tendsto (fun ρ : ℝ =>
      (twoQ1 θA θB πA πB ξ - L0 θA θB πA πB (fun η => Q ρ η - qHat θA θB πA πB η) ξ) * ρ⁻¹)
      atTop (𝓝 ((twoQ1 θA θB πA πB ξ - L0 θA θB πA πB Φ ξ) * 0)) :=
    (tendsto_const_nhds.sub (tendsto_L0 _ Φ hlim ξ)).mul tendsto_inv_atTop_zero
  have heq : ∀ᶠ ρ : ℝ in atTop,
      (twoQ1 θA θB πA πB ξ - L0 θA θB πA πB (fun η => Q ρ η - qHat θA θB πA πB η) ξ) * ρ⁻¹
        = L1 (fun η => Q ρ η - qHat θA θB πA πB η) ξ := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with ρ hρ
    have hL := LDelta hθA hθB (hQ ρ hρ) ξ hn
    rw [Lop_split] at hL
    have hρ' : ρ ≠ 0 := ne_of_gt hρ
    field_simp
    linarith [hL]
  have h2 := hnum.congr' heq
  have h3 := tendsto_L1 (fun ρ : ℝ => fun η => Q ρ η - qHat θA θB πA πB η) Φ hlim ξ
  have := tendsto_nhds_unique h3 h2
  rw [this, mul_zero]

theorem Delta_limit_eq_zero_of_min_le_one (hθA : 0 < θA) (hθB : 0 < θB)
    (hQ : ∀ ρ : ℝ, 0 < ρ → IsSolution θA θB ρ πA πB (Q ρ))
    (hlim : ∀ η : Config KA KB,
      Tendsto (fun ρ => Q ρ η - qHat θA θB πA πB η) atTop (𝓝 (Φ η)))
    (ξ : Config KA KB) (hmin : ξ.nA ≤ 1 ∨ ξ.nB ≤ 1) : Φ ξ = 0 := by
  have h0 : Tendsto (fun ρ : ℝ => Q ρ ξ - qHat θA θB πA πB ξ) atTop (𝓝 0) := by
    refine Tendsto.congr' ?_ (tendsto_const_nhds (x := (0 : ℝ)))
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with ρ hρ
    have h := Denominator.eq_qHat_of_min_le_one hθA hθB (le_of_lt hρ) (hQ ρ hρ) ξ hmin
    have hb : Denominator.qHat θA θB πA πB ξ = qHat θA θB πA πB ξ := rfl
    rw [h, hb, sub_self]
  exact tendsto_nhds_unique (hlim ξ) h0

theorem Delta_limit_eq_zero (hθA : 0 < θA) (hθB : 0 < θB)
    (hQ : ∀ ρ : ℝ, 0 < ρ → IsSolution θA θB ρ πA πB (Q ρ))
    (hlim : ∀ η : Config KA KB,
      Tendsto (fun ρ => Q ρ η - qHat θA θB πA πB η) atTop (𝓝 (Φ η)))
    (ξ : Config KA KB) : Φ ξ = 0 := by
  have key : ∀ N : ℕ, ∀ ζ : Config KA KB, ζ.nA + ζ.nB = N → Φ ζ = 0 := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro ζ hN
      by_cases hmin : ζ.nA ≤ 1 ∨ ζ.nB ≤ 1
      · exact Delta_limit_eq_zero_of_min_le_one hθA hθB hQ hlim ζ hmin
      · have hA2' : 2 ≤ ζ.nA := by omega
        have hB2' : 2 ≤ ζ.nB := by omega
        have hsector : ∀ η : Config KA KB, η.mA = ζ.mA → η.mB = ζ.mB → L1 Φ η = 0 := by
          intro η hηA hηB
          refine L1_limit_eq_zero hθA hθB hQ hlim η (two_le_n_of_two_le η ?_ ?_)
          · rw [nA_of_mA_eq hηA]; exact hA2'
          · rw [nB_of_mB_eq hηB]; exact hB2'
        have hconst : ∀ η : Config KA KB, η.mA = ζ.mA → η.mB = ζ.mB →
            Φ η = Φ (sectorBase ζ) := fun η hηA hηB =>
          eq_at_sectorBase (ζ := ζ) hsector η.t η rfl hηA hηB
        set β := sectorBase ζ with hβ
        have hβt : β.t = 0 := t_sectorBase ζ
        have hβA : β.nA = ζ.nA := nA_sectorBase ζ
        have hβB : β.nB = ζ.nB := nB_sectorBase ζ
        have hβn : 2 ≤ β.n := two_le_n_of_two_le β (by omega) (by omega)
        have hL0 : L0 θA θB πA πB Φ β = 0 := by
          have hval : ∀ᶠ ρ : ℝ in atTop,
              L0 θA θB πA πB (fun η => Q ρ η - qHat θA θB πA πB η) β
                = twoQ1 θA θB πA πB β := by
            filter_upwards [eventually_gt_atTop (0 : ℝ)] with ρ hρ
            have hL := LDelta hθA hθB (hQ ρ hρ) β hβn
            rw [Lop_split, L1_of_t_eq_zero _ hβt, mul_zero, add_zero] at hL
            exact hL
          have h1 : Tendsto (fun ρ : ℝ =>
              L0 θA θB πA πB (fun η => Q ρ η - qHat θA θB πA πB η) β) atTop
              (𝓝 (L0 θA θB πA πB Φ β)) :=
            tendsto_L0 (θA := θA) (θB := θB) (πA := πA) (πB := πB)
              (fun ρ : ℝ => fun η => Q ρ η - qHat θA θB πA πB η) Φ hlim β
          have h2 : Tendsto (fun ρ : ℝ =>
              L0 θA θB πA πB (fun η => Q ρ η - qHat θA θB πA πB η) β) atTop
              (𝓝 (twoQ1 θA θB πA πB β)) := by
            refine Tendsto.congr' ?_ tendsto_const_nhds
            filter_upwards [hval] with ρ hρ
            exact hρ.symm
          have h3 := tendsto_nhds_unique h1 h2
          rw [h3, twoQ1_eq_zero_of_t_le_one β (by omega)]
        have hsplitm : ∀ (i : Fin KA) (j : Fin KB), β.a i ≠ 0 → β.b j ≠ 0 →
            Φ (β.mergeAB i j) = Φ β + (0 : ℝ) := by
          intro i j ha hb
          rw [add_zero, hconst (β.mergeAB i j) (by rw [β.mA_mergeAB j ha, mA_sectorBase ζ])
            (by rw [β.mB_mergeAB i hb, mB_sectorBase ζ]), hconst β (mA_sectorBase ζ)
            (mB_sectorBase ζ)]
        have hres := residual_t_zero (q2 := Φ) (σ := fun _ => (0 : ℝ)) β hβt hL0 hsplitm
        have hdropA : (∑ i, (((β.a i * (β.a i - 1) : ℕ) : ℝ) + θA * πA i * ((β.a i : ℕ) : ℝ))
            * Φ (β.dropA i)) = 0 := by
          refine Finset.sum_eq_zero fun i _ => ?_
          by_cases hai : β.a i = 0
          · rw [hai]; simp
          · have hlt : (β.dropA i).nA + (β.dropA i).nB < N := by
              have h1 := β.nA_dropA i hai
              have h2 : (β.dropA i).nB = β.nB := rfl
              omega
            rw [ih _ hlt (β.dropA i) rfl, mul_zero]
        have hdropB : (∑ j, (((β.b j * (β.b j - 1) : ℕ) : ℝ) + θB * πB j * ((β.b j : ℕ) : ℝ))
            * Φ (β.dropB j)) = 0 := by
          refine Finset.sum_eq_zero fun j _ => ?_
          by_cases hbj : β.b j = 0
          · rw [hbj]; simp
          · have hlt : (β.dropB j).nA + (β.dropB j).nB < N := by
              have h1 := β.nB_dropB j hbj
              have h2 : (β.dropB j).nA = β.nA := rfl
              omega
            rw [ih _ hlt (β.dropB j) rfl, mul_zero]
        have hmerge : (∑ i : Fin KA, ∑ j : Fin KB,
            ((β.coalAB i j : ℕ) : ℝ) * (0 : ℝ)) = 0 := by simp
        rw [hdropA, hdropB, hmerge] at hres
        have hcoef : 0 < ((β.nA * (β.nA - 1) : ℕ) : ℝ) + θA * ((β.nA : ℕ) : ℝ)
            + ((β.nB * (β.nB - 1) : ℕ) : ℝ) + θB * ((β.nB : ℕ) : ℝ) := by
          have h1 : (0 : ℝ) ≤ ((β.nA * (β.nA - 1) : ℕ) : ℝ) := Nat.cast_nonneg _
          have h2 : (0 : ℝ) ≤ ((β.nB * (β.nB - 1) : ℕ) : ℝ) := Nat.cast_nonneg _
          have h3 : (0 : ℝ) < θA * ((β.nA : ℕ) : ℝ) :=
            mul_pos hθA (by exact_mod_cast (by omega : 0 < β.nA))
          have h4 : (0 : ℝ) ≤ θB * ((β.nB : ℕ) : ℝ) :=
            mul_nonneg hθB.le (Nat.cast_nonneg _)
          linarith
        have hβzero : Φ β = 0 := by
          rcases mul_eq_zero.1 (by linarith [hres] : (((β.nA * (β.nA - 1) : ℕ) : ℝ)
            + θA * ((β.nA : ℕ) : ℝ) + ((β.nB * (β.nB - 1) : ℕ) : ℝ)
            + θB * ((β.nB : ℕ) : ℝ)) * Φ β = 0) with h | h
          · exact absurd h (ne_of_gt hcoef)
          · exact h
        rw [hconst ζ rfl rfl]
        exact hβzero
  exact key (ξ.nA + ξ.nB) ξ rfl

theorem tendsto_qHat_of_tendsto (hθA : 0 < θA) (hθB : 0 < θB)
    (hQ : ∀ ρ : ℝ, 0 < ρ → IsSolution θA θB ρ πA πB (Q ρ))
    (hex : ∀ η : Config KA KB, ∃ L : ℝ, Tendsto (fun ρ => Q ρ η) atTop (𝓝 L))
    (ξ : Config KA KB) :
    Tendsto (fun ρ => Q ρ ξ) atTop (𝓝 (qOne θA πA ξ.mA * qOne θB πB ξ.mB)) := by
  classical
  set Φ : Config KA KB → ℝ := fun η => (hex η).choose - qHat θA θB πA πB η with hΦ
  have hlim : ∀ η : Config KA KB,
      Tendsto (fun ρ => Q ρ η - qHat θA θB πA πB η) atTop (𝓝 (Φ η)) := fun η =>
    ((hex η).choose_spec).sub tendsto_const_nhds
  have hzero := Delta_limit_eq_zero hθA hθB hQ hlim ξ
  have hval : (hex ξ).choose = qHat θA θB πA πB ξ := by
    have : (hex ξ).choose - qHat θA θB πA πB ξ = 0 := hzero
    linarith
  have := (hex ξ).choose_spec
  rwa [hval] at this

end Limit

end Rhone.Probability.RecombinationExpansion
