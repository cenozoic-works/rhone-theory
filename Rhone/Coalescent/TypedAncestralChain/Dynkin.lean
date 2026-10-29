/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.TypedAncestralChain.Tail

/-! # Well-posedness of the Dynkin operator of the typed ancestral chain -/

@[expose] public section

namespace Rhone.Coalescent.TypedAncestralChain

open Finset TwoLocusGenealogy LinearAlgebra.Recursion

variable {n KA KB : ℕ} {θA θB ρ : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ}

def Transient (s : TS n KA KB) : Prop := WF s.st.1 ∧ s.st.1 ≠ ∅

theorem dtotS_pos_of_transient (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) {s : TS n KA KB}
    (hs : Transient s) : 0 < dtotS θA θB ρ s :=
  dtot_pos hθA hθB hρ hs.1 (Finset.nonempty_iff_ne_empty.2 hs.2)

theorem sum_transS_of_not_transient {s : TS n KA KB} (hw : WF s.st.1) (hs : ¬ Transient s)
    (u : TS n KA KB → ℝ) : (∑ t, transS θA θB ρ πA πB s t * u t) = u s := by
  have hemp : s.st.1 = ∅ := by
    by_contra hc
    exact hs ⟨hw, hc⟩
  have hz : ¬ 0 < dtotS θA θB ρ s := by
    have h0 : dtotS θA θB ρ s = 0 := by rw [dtotS, hemp, dtot_empty]
    rw [h0]
    exact lt_irrefl 0
  have hval : ∀ t : TS n KA KB, transS θA θB ρ πA πB s t * u t
      = if t = s then u t else 0 := by
    intro t
    rw [transS_of_nonpos hz]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun t _ => hval t,
    Finset.sum_ite_eq' Finset.univ s u, ite_eq_left (Finset.mem_univ s)]

theorem abs_mstep_le (h : Adm θA θB ρ πA πB) (N : ℕ) (u : TS n KA KB → ℝ) (s : TS n KA KB) :
    |mstep θA θB ρ πA πB N u s| ≤ mstep θA θB ρ πA πB N (fun t => |u t|) s := by
  induction N generalizing s with
  | zero => exact le_rfl
  | succ N ih =>
    rw [mstep_succ, mstep_succ]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun t _ => ?_)
    rw [abs_mul, abs_of_nonneg (transS_nonneg h.thA h.thB h.rho h.piA h.piB s t)]
    exact mul_le_mul_of_nonneg_left (ih t) (transS_nonneg h.thA h.thB h.rho h.piA h.piB s t)

theorem mstep_fix {u : TS n KA KB → ℝ}
    (hfix : ∀ s, WF s.st.1 → u s = ∑ t, transS θA θB ρ πA πB s t * u t) (N : ℕ)
    {s : TS n KA KB} (hw : WF s.st.1) : mstep θA θB ρ πA πB N u s = u s := by
  induction N generalizing s with
  | zero => rfl
  | succ N ih =>
    rw [mstep_succ]
    have hval : ∀ t : TS n KA KB, transS θA θB ρ πA πB s t * mstep θA θB ρ πA πB N u t
        = transS θA θB ρ πA πB s t * u t := by
      intro t
      by_cases hwt : WF t.st.1
      · rw [ih hwt]
      · rw [transS_eq_zero_of_not_wf hw hwt, zero_mul, zero_mul]
    rw [Finset.sum_congr rfl fun t _ => hval t, ← hfix s hw]

theorem eq_zero_of_fix (h : Adm θA θB ρ πA πB) (hθA : 0 < θA) (hθB : 0 < θB)
    {u : TS n KA KB → ℝ} (hzero : ∀ s, ¬ Transient s → u s = 0)
    (hfix : ∀ s, Transient s → u s = ∑ t, transS θA θB ρ πA πB s t * u t) : u = 0 := by
  obtain ⟨N₀, hN₀⟩ := uniform_horizon h hθA hθB
  have hfixAll : ∀ s, WF s.st.1 → u s = ∑ t, transS θA θB ρ πA πB s t * u t := by
    intro s hw
    by_cases hs : Transient s
    · exact hfix s hs
    · rw [sum_transS_of_not_transient hw hs u]
  obtain ⟨s₀, hs₀⟩ := Finite.exists_max fun t : TS n KA KB => |u t|
  set M := |u s₀| with hM
  have hMnn : 0 ≤ M := abs_nonneg _
  have hMzero : M ≤ 0 := by
    by_cases hs : Transient s₀
    · have hbound : ∀ t : TS n KA KB, WF t.st.1 → |u t| ≤ M * indNot t := by
        intro t _
        by_cases hab : t.st.1 = ∅
        · rw [indNot, ite_eq_left hab, mul_zero, hzero t (fun hc => hc.2 hab)]
          simp
        · rw [indNot, ite_eq_right hab, mul_one]
          exact hs₀ t
      have h1 : M = |mstep θA θB ρ πA πB N₀ u s₀| := by
        rw [mstep_fix hfixAll N₀ hs.1]
      have h2 : |mstep θA θB ρ πA πB N₀ u s₀|
          ≤ mstep θA θB ρ πA πB N₀ (fun t => |u t|) s₀ := abs_mstep_le h N₀ u s₀
      have h3 : mstep θA θB ρ πA πB N₀ (fun t => |u t|) s₀
          ≤ M * surv θA θB ρ πA πB N₀ s₀ := mstep_le_mul h N₀ hbound hs.1
      have h4 : M * surv θA θB ρ πA πB N₀ s₀ ≤ M * (1 / 2) :=
        mul_le_mul_of_nonneg_left (hN₀ s₀ hs.1) hMnn
      linarith
    · rw [hM, hzero s₀ hs]
      norm_num
  have hMeq : M = 0 := le_antisymm hMzero hMnn
  funext t
  have hle := hs₀ t
  rw [hMeq] at hle
  exact abs_eq_zero.1 (le_antisymm hle (abs_nonneg _))

noncomputable def stepLin (θA θB ρ : ℝ) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ) :
    (TS n KA KB → ℝ) →ₗ[ℝ] (TS n KA KB → ℝ) where
  toFun u := fun s => ∑ t, transS θA θB ρ πA πB s t * u t
  map_add' u v := by
    funext s
    simp only [Pi.add_apply, mul_add]
    rw [Finset.sum_add_distrib]
  map_smul' c u := by
    funext s
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ => by ring

noncomputable instance instDecidableTransient (s : TS n KA KB) : Decidable (Transient s) :=
  Classical.dec _

noncomputable def projTr : (TS n KA KB → ℝ) →ₗ[ℝ] (TS n KA KB → ℝ) where
  toFun u := fun s => if Transient s then u s else 0
  map_add' u v := by
    funext s
    by_cases hs : Transient s <;> simp [hs]
  map_smul' c u := by
    funext s
    by_cases hs : Transient s <;> simp [hs]

noncomputable def dynkinOp (θA θB ρ : ℝ) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ) :
    (TS n KA KB → ℝ) →ₗ[ℝ] (TS n KA KB → ℝ) :=
  LinearMap.id - projTr ∘ₗ stepLin θA θB ρ πA πB

theorem dynkinOp_apply_of_transient {s : TS n KA KB} (hs : Transient s)
    (u : TS n KA KB → ℝ) :
    dynkinOp θA θB ρ πA πB u s = u s - ∑ t, transS θA θB ρ πA πB s t * u t := by
  have hp : projTr (stepLin θA θB ρ πA πB u) s
      = if Transient s then (∑ t, transS θA θB ρ πA πB s t * u t) else 0 := rfl
  simp only [dynkinOp, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
    Pi.sub_apply, hp, ite_eq_left hs]

theorem dynkinOp_apply_of_not_transient {s : TS n KA KB} (hs : ¬ Transient s)
    (u : TS n KA KB → ℝ) : dynkinOp θA θB ρ πA πB u s = u s := by
  have hp : projTr (stepLin θA θB ρ πA πB u) s
      = if Transient s then (∑ t, transS θA θB ρ πA πB s t * u t) else 0 := rfl
  simp only [dynkinOp, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
    Pi.sub_apply, hp, ite_eq_right hs, sub_zero]

theorem dynkinOp_injective (h : Adm θA θB ρ πA πB) (hθA : 0 < θA) (hθB : 0 < θB) :
    Function.Injective (dynkinOp (n := n) θA θB ρ πA πB) := by
  intro u v huv
  have hd : dynkinOp (n := n) θA θB ρ πA πB (u - v) = 0 := by
    rw [map_sub, huv, sub_self]
  have hzero : ∀ s, ¬ Transient s → (u - v) s = 0 := by
    intro s hs
    have hc := congrFun hd s
    rwa [dynkinOp_apply_of_not_transient hs] at hc
  have hfix : ∀ s, Transient s →
      (u - v) s = ∑ t, transS θA θB ρ πA πB s t * (u - v) t := by
    intro s hs
    have hc := congrFun hd s
    rw [dynkinOp_apply_of_transient hs] at hc
    have h0 : (0 : TS n KA KB → ℝ) s = 0 := rfl
    rw [h0] at hc
    linarith [hc]
  have := eq_zero_of_fix h hθA hθB hzero hfix
  have h2 : u - v = 0 := this
  exact sub_eq_zero.1 h2

theorem dynkinOp_bijective (h : Adm θA θB ρ πA πB) (hθA : 0 < θA) (hθB : 0 < θB) :
    Function.Bijective (dynkinOp (n := n) θA θB ρ πA πB) :=
  ⟨dynkinOp_injective h hθA hθB,
    (LinearMap.injective_iff_surjective).1 (dynkinOp_injective h hθA hθB)⟩

theorem existsUnique_dynkin (h : Adm θA θB ρ πA πB) (hθA : 0 < θA) (hθB : 0 < θB)
    (r : TS n KA KB → ℝ) :
    ∃! u : TS n KA KB → ℝ, (∀ s, ¬ Transient s → u s = r s)
      ∧ ∀ s, Transient s → u s - (∑ t, transS θA θB ρ πA πB s t * u t) = r s := by
  obtain ⟨u, hu⟩ := (dynkinOp_bijective h hθA hθB).2 r
  refine ⟨u, ⟨fun s hs => ?_, fun s hs => ?_⟩, ?_⟩
  · have hc := congrFun hu s
    rwa [dynkinOp_apply_of_not_transient hs] at hc
  · have hc := congrFun hu s
    rwa [dynkinOp_apply_of_transient hs] at hc
  · rintro v ⟨hv1, hv2⟩
    refine dynkinOp_injective h hθA hθB ?_
    rw [hu]
    funext s
    by_cases hs : Transient s
    · rw [dynkinOp_apply_of_transient hs, hv2 s hs]
    · rw [dynkinOp_apply_of_not_transient hs, hv1 s hs]

theorem existsUnique_generator (h : Adm θA θB ρ πA πB) (hθA : 0 < θA) (hθB : 0 < θB)
    (r : TS n KA KB → ℝ) :
    ∃! u : TS n KA KB → ℝ, (∀ s, ¬ Transient s → u s = 0)
      ∧ ∀ s, Transient s →
        dtotS θA θB ρ s * ((∑ t, transS θA θB ρ πA πB s t * u t) - u s) = - r s := by
  classical
  obtain ⟨u, ⟨hu1, hu2⟩, huniq⟩ := existsUnique_dynkin h hθA hθB
    (fun s => if Transient s then r s / dtotS θA θB ρ s else 0)
  have hconv : ∀ v : TS n KA KB → ℝ,
      ((∀ s, ¬ Transient s → v s = 0)
        ∧ ∀ s, Transient s →
          dtotS θA θB ρ s * ((∑ t, transS θA θB ρ πA πB s t * v t) - v s) = - r s)
      ↔ ((∀ s, ¬ Transient s → v s
            = if Transient s then r s / dtotS θA θB ρ s else 0)
        ∧ ∀ s, Transient s → v s - (∑ t, transS θA θB ρ πA πB s t * v t)
            = if Transient s then r s / dtotS θA θB ρ s else 0) := by
    intro v
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun s hs => by rw [h1 s hs, ite_eq_right hs], fun s hs => ?_⟩
      have hd : 0 < dtotS θA θB ρ s := dtotS_pos_of_transient hθA hθB h.rho hs
      rw [ite_eq_left hs, eq_div_iff hd.ne']
      have := h2 s hs
      nlinarith [this]
    · rintro ⟨h1, h2⟩
      refine ⟨fun s hs => by rw [h1 s hs, ite_eq_right hs], fun s hs => ?_⟩
      have hd : 0 < dtotS θA θB ρ s := dtotS_pos_of_transient hθA hθB h.rho hs
      have := h2 s hs
      rw [ite_eq_left hs] at this
      field_simp at this
      nlinarith [this]
  refine ⟨u, (hconv u).2 ⟨hu1, hu2⟩, fun v hv => huniq v ((hconv v).1 hv)⟩

def IsDynkinSol (θA θB ρ : ℝ) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ)
    (r u : TS n KA KB → ℝ) : Prop :=
  (∀ s, ¬ Transient s → u s = 0)
    ∧ ∀ s, Transient s →
      dtotS θA θB ρ s * ((∑ t, transS θA θB ρ πA πB s t * u t) - u s) = - r s

theorem existsUnique_u (h : Adm θA θB ρ πA πB) (hθA : 0 < θA) (hθB : 0 < θB)
    (r : TS n KA KB → ℝ) : ∃! u : TS n KA KB → ℝ, IsDynkinSol θA θB ρ πA πB r u :=
  existsUnique_generator h hθA hθB r

theorem existsUnique_w (h : Adm θA θB ρ πA πB) (hθA : 0 < θA) (hθB : 0 < θB)
    (rA rB uA uB : TS n KA KB → ℝ) :
    ∃! w : TS n KA KB → ℝ,
      IsDynkinSol θA θB ρ πA πB (fun s => rA s * uB s + rB s * uA s) w :=
  existsUnique_generator h hθA hθB _

end Rhone.Coalescent.TypedAncestralChain
