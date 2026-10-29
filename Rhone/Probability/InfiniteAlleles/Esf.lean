/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.InfiniteAlleles.Limit
public import Rhone.LinearAlgebra.Recursion.OneLocus

/-! # The Ewens sampling formula as the `K → ∞` limit of the one-locus PIM marginal -/

@[expose] public section

namespace Rhone.Probability.InfiniteAlleles

open Finset Filter Topology LinearAlgebra.Recursion LinearAlgebra.Recursion.Config

section Tail

variable {F : Type*} [Field F]

def risingTail (y : F) (k : ℕ) : F := ∏ r ∈ Finset.Ico 1 k, (y + (r : ℕ))

theorem rising_eq_mul_risingTail (y : F) {k : ℕ} (hk : k ≠ 0) :
    rising y k = y * risingTail y k := by
  have hk' : 0 < k := Nat.pos_of_ne_zero hk
  rw [rising, Finset.range_eq_Ico, Finset.prod_eq_prod_Ico_succ_bot hk']
  simp [risingTail]

theorem risingTail_zero (k : ℕ) : risingTail (0 : F) k = ((Nat.factorial (k - 1) : ℕ) : F) := by
  cases k with
  | zero => simp [risingTail]
  | succ n =>
    have hfac : (∏ r ∈ Finset.Ico 1 (n + 1), r) = Nat.factorial n :=
      Finset.prod_Ico_id_eq_factorial n
    simp only [risingTail, zero_add, Nat.add_sub_cancel, ← hfac]
    push_cast
    rfl

end Tail

section Esf

variable {K : ℕ} {F : Type*} [Field F]

noncomputable def esfLab (θ : F) (m : Fin K → ℕ) : F :=
  (θ ^ obs m * ∏ i ∈ Finset.univ.filter (fun i => m i ≠ 0), ((Nat.factorial (m i - 1) : ℕ) : F))
    / rising θ (∑ i, m i)

noncomputable def qOnePoly (θ x : F) (m : Fin K → ℕ) : F :=
  (θ ^ obs m * ∏ i ∈ Finset.univ.filter (fun i => m i ≠ 0), risingTail (θ * x) (m i))
    / rising θ (∑ i, m i)

@[simp] theorem qOnePoly_zero (θ : F) (m : Fin K → ℕ) : qOnePoly θ 0 m = esfLab θ m := by
  simp only [qOnePoly, esfLab, mul_zero, risingTail_zero]

theorem qOne_uniform (θ x : F) (m : Fin K → ℕ) :
    qOne θ (fun _ => x) m = x ^ obs m * qOnePoly θ x m := by
  have hsplit : (∏ i, rising (θ * x) (m i))
      = (θ * x) ^ obs m
        * ∏ i ∈ Finset.univ.filter (fun i => m i ≠ 0), risingTail (θ * x) (m i) := by
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i => m i ≠ 0)
          (fun i => rising (θ * x) (m i))]
    have h2 : (∏ i ∈ Finset.univ.filter (fun i => ¬ (m i ≠ 0)), rising (θ * x) (m i)) = 1 := by
      refine Finset.prod_eq_one fun i hi => ?_
      simp only [Finset.mem_filter, not_not] at hi
      rw [hi.2, rising_zero]
    rw [h2, mul_one,
      Finset.prod_congr rfl (fun i hi =>
        rising_eq_mul_risingTail (θ * x) (Finset.mem_filter.mp hi).2),
      Finset.prod_mul_distrib, Finset.prod_const]
    rfl
  simp only [qOne, qOnePoly, hsplit, mul_pow]
  ring

end Esf

section Limit

variable {K : ℕ}

theorem continuous_qOnePoly (θ : ℝ) (m : Fin K → ℕ) :
    Continuous fun x : ℝ => qOnePoly θ x m := by
  unfold qOnePoly risingTail
  fun_prop

theorem tendsto_qOne_resc (θ : ℝ) (m : Fin K → ℕ) :
    Tendsto (fun x : ℝ => (x ^ obs m)⁻¹ * qOne θ (fun _ => x) m) (𝓝[>] (0 : ℝ))
      (𝓝 (esfLab θ m)) := by
  have hcont : Tendsto (fun x : ℝ => qOnePoly θ x m) (𝓝[>] (0 : ℝ)) (𝓝 (qOnePoly θ 0 m)) :=
    ((continuous_qOnePoly θ m).tendsto 0).mono_left nhdsWithin_le_nhds
  rw [qOnePoly_zero] at hcont
  refine Tendsto.congr' ?_ hcont
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hxne : x ≠ 0 := ne_of_gt hx
  rw [qOne_uniform, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hxne), one_mul]

end Limit

variable {KA KB : ℕ} {θA θB ρ : ℝ}

theorem obsTot_of_nB_zero {ξ : Config KA KB} (h : ξ.nB = 0) : obsTot ξ = obs ξ.a := by
  have ht : ξ.t = 0 := by simp only [Rhone.LinearAlgebra.Recursion.Config.nB] at h; omega
  have hb : ξ.sumB = 0 := by simp only [Rhone.LinearAlgebra.Recursion.Config.nB] at h; omega
  have hc : ξ.c = fun _ _ => 0 := ξ.c_eq_zero_of_t ht
  have hbz : ξ.b = fun _ => 0 := ξ.b_eq_zero_of_sumB hb
  have hmA : ξ.mA = ξ.a := by
    funext i
    simp [Config.mA, Config.cRow, hc]
  have hmB : ξ.mB = fun _ => 0 := by
    funext j
    simp [Config.mB, Config.cCol, hc, hbz]
  simp [obsTot, obsA, obsB, hmA, hmB, obs_eq_zero_of_const_zero]

theorem PIA_edge_eq_esfLab (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (ξ : Config KA KB)
    (h0 : ξ.nB = 0) : PIA hθA hθB hρ ξ = esfLab θA ξ.a := by
  have h1 : Tendsto (fun x : ℝ => Qresc hθA hθB hρ x ξ) (𝓝[>] (0 : ℝ))
      (𝓝 (PIA hθA hθB hρ ξ)) := tendsto_Qresc hθA hθB hρ ξ
  have h2 : Tendsto (fun x : ℝ => Qresc hθA hθB hρ x ξ) (𝓝[>] (0 : ℝ))
      (𝓝 (esfLab θA ξ.a)) := by
    refine Tendsto.congr' ?_ (tendsto_qOne_resc θA ξ.a)
    filter_upwards [self_mem_nhdsWithin] with x _
    have hq : LinearAlgebra.Recursion.q (πA := fun _ : Fin KA => x) (πB := fun _ : Fin KB => x)
        hθA hθB hρ ξ = qOne θA (fun _ => x) ξ.a :=
      (LinearAlgebra.Recursion.q_isSolution hθA hθB hρ).eq_qOne_of_nB hθA ξ h0
    rw [Qresc, resc, obsTot_of_nB_zero h0, hq]
  exact tendsto_nhds_unique h1 h2

end Rhone.Probability.InfiniteAlleles
