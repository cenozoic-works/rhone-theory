/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.TwoLocusGenealogy.Limit
public import Rhone.LinearAlgebra.Recursion.Unique
public import Rhone.LinearAlgebra.PerturbedLinearLimit

/-!
# The two-locus sampling recursion as a finite linear system

Source: griffiths1991_two_locus_graph, eq. (2.7), pp. 107–108. -/

@[expose] public section
noncomputable section
namespace Rhone.Coalescent.WFTwoLocusLimit
open Finset Filter Topology Matrix LinearAlgebra.Recursion TwoLocusGenealogy

variable {KA KB : ℕ}

def levelSet (KA KB N : ℕ) : Finset (Config KA KB) :=
  (Config.finite_le N).toFinset.filter fun ξ => 1 ≤ ξ.n

theorem mem_levelSet {N : ℕ} {ξ : Config KA KB} :
    ξ ∈ levelSet KA KB N ↔ ξ.nA + ξ.nB ≤ N ∧ 1 ≤ ξ.n := by
  simp [levelSet]

abbrev Idx (KA KB N : ℕ) := {ξ : Config KA KB // ξ ∈ levelSet KA KB N}

open Classical in
def indCfg (ξ : Config KA KB) : Config KA KB → ℝ := fun η => if η = ξ then 1 else 0

open Classical in
def genMat (θA θB ρ : ℝ) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ) (N : ℕ) :
    Matrix (Idx KA KB N) (Idx KA KB N) ℝ :=
  fun ξ ξ' => rhs θA θB ρ πA πB (indCfg ξ'.1) ξ.1 - if ξ = ξ' then diag θA θB ρ ξ.1 else 0

def genRhs (θA θB ρ : ℝ) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ) (N : ℕ) : Idx KA KB N → ℝ :=
  fun ξ => rhs θA θB ρ πA πB (indCfg 0) ξ.1

def extend {N : ℕ} (v : Idx KA KB N → ℝ) : Config KA KB → ℝ :=
  fun η => ∑ ξ', v ξ' * indCfg ξ'.1 η

open Classical in
theorem extend_apply {N : ℕ} (v : Idx KA KB N → ℝ) (η : Config KA KB) :
    extend v η = if h : η ∈ levelSet KA KB N then v ⟨η, h⟩ else 0 := by
  unfold extend indCfg
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨η, h⟩]
    · simp
    · intro b _ hb
      rw [ite_eq_right (fun h' => hb (Subtype.ext h'.symm)), mul_zero]
    · intro h'; exact absurd (Finset.mem_univ _) h'
  · refine Finset.sum_eq_zero fun ξ' _ => ?_
    rw [ite_eq_right (fun h' : η = ξ'.1 => h (by rw [h']; exact ξ'.2)), mul_zero]

theorem rhs_finsetSum {ι : Type*} (θA θB ρ : ℝ) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ)
    (s : Finset ι) (f : ι → Config KA KB → ℝ) (ξ : Config KA KB) :
    rhs θA θB ρ πA πB (fun η => ∑ k ∈ s, f k η) ξ = ∑ k ∈ s, rhs θA θB ρ πA πB (f k) ξ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using rhs_zero θA θB ρ πA πB ξ
  | insert k s hk ih =>
    simp only [Finset.sum_insert hk]
    rw [rhs_add, ih]

theorem genMat_mulVec (θA θB ρ : ℝ) (πA : Fin KA → ℝ) (πB : Fin KB → ℝ) {N : ℕ}
    (v : Idx KA KB N → ℝ) (ξ : Idx KA KB N) :
    (genMat θA θB ρ πA πB N *ᵥ v) ξ =
      rhs θA θB ρ πA πB (extend v) ξ.1 - diag θA θB ρ ξ.1 * v ξ := by
  classical
  simp only [Matrix.mulVec, dotProduct, genMat, sub_mul, Finset.sum_sub_distrib]
  congr 1
  · unfold extend
    rw [rhs_finsetSum]
    refine Finset.sum_congr rfl fun ξ' _ => ?_
    rw [rhs_smul, mul_comm]
  · rw [Finset.sum_eq_single ξ]
    · simp
    · intro b _ hb
      rw [ite_eq_right (Ne.symm hb), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h

/-- Adapted from `Rhone.LinearAlgebra.Recursion.within_block_eq_zero`. -/
theorem homogeneous_eq_zero_of_one_le {θA θB ρ : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ}
    (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) {h : Config KA KB → ℝ} {N : ℕ}
    (h0 : h 0 = 0)
    (hrec : ∀ ξ : Config KA KB, 1 ≤ ξ.n → ξ.nA + ξ.nB ≤ N →
      diag θA θB ρ ξ * h ξ = rhs θA θB ρ πA πB h ξ) :
    ∀ ξ : Config KA KB, ξ.nA + ξ.nB ≤ N → h ξ = 0 := by
  suffices H : ∀ L : ℕ, L ≤ N → ∀ ξ : Config KA KB, ξ.nA + ξ.nB = L → h ξ = 0 from
    fun ξ hξ => H _ hξ ξ rfl
  intro L
  induction L using Nat.strong_induction_on with
  | _ L IH =>
    intro hLN ξ hξ
    have hbelow : ∀ η : Config KA KB, η.nA + η.nB < L → h η = 0 :=
      fun η hη => IH _ hη (by omega) η rfl
    obtain ⟨ζ, hζS, hζmax⟩ :=
      Set.exists_max_image {ζ : Config KA KB | ζ.nA + ζ.nB = L} (fun ζ => |h ζ|)
        (Config.finite_level L) ⟨ξ, hξ⟩
    have hζlev : ζ.nA + ζ.nB = L := hζS
    have hzero : |h ζ| = 0 := by
      by_cases hn : ζ.n = 0
      · rw [Config.eq_zero_of_n_eq_zero ζ hn, h0, abs_zero]
      have hn1 : 1 ≤ ζ.n := by omega
      have heq0 := hrec ζ hn1 (by omega)
      rw [rhs_of_vanishing_below θA θB ρ πA πB ζ fun η h1 h2 h3 => hbelow η (by omega)]
        at heq0
      set M : ℝ := |h ζ| with hMdef
      have hMnn : (0 : ℝ) ≤ M := abs_nonneg _
      have hDpos : 0 < diag θA θB ρ ζ := diag_pos hθA hθB hρ hn1
      have hA : |∑ i, ∑ j, ((ζ.coalAB i j : ℕ) : ℝ) * h (ζ.mergeAB i j)|
          ≤ ((2 * (ζ.sumA * ζ.sumB) : ℕ) : ℝ) * M := by
        calc |∑ i, ∑ j, ((ζ.coalAB i j : ℕ) : ℝ) * h (ζ.mergeAB i j)|
            ≤ ∑ i, |∑ j, ((ζ.coalAB i j : ℕ) : ℝ) * h (ζ.mergeAB i j)| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ i, ∑ j, ((ζ.coalAB i j : ℕ) : ℝ) * M := by
              refine Finset.sum_le_sum fun i _ => ?_
              refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun j _ => ?_)
              rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
              by_cases ha : ζ.a i = 0
              · rw [ζ.coalAB_eq_zero_left j ha]; simp
              by_cases hb : ζ.b j = 0
              · rw [ζ.coalAB_eq_zero_right i hb]; simp
              obtain ⟨e1, e2⟩ := ζ.mergeAB_same ha hb
              refine mul_le_mul_of_nonneg_left (hζmax _ ?_) (Nat.cast_nonneg _)
              change (ζ.mergeAB i j).nA + (ζ.mergeAB i j).nB = L
              omega
          _ = ((2 * (ζ.sumA * ζ.sumB) : ℕ) : ℝ) * M := by
              rw [← ζ.sum_coalAB]
              push_cast
              simp [Finset.sum_mul]
      have hB : |∑ i, ∑ j, ((ζ.c i j : ℕ) : ℝ) * h (ζ.split i j)| ≤ ((ζ.t : ℕ) : ℝ) * M := by
        calc |∑ i, ∑ j, ((ζ.c i j : ℕ) : ℝ) * h (ζ.split i j)|
            ≤ ∑ i, |∑ j, ((ζ.c i j : ℕ) : ℝ) * h (ζ.split i j)| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ i, ∑ j, ((ζ.c i j : ℕ) : ℝ) * M := by
              refine Finset.sum_le_sum fun i _ => ?_
              refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun j _ => ?_)
              rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
              by_cases hc : ζ.c i j = 0
              · rw [hc]; simp
              obtain ⟨e1, e2⟩ := ζ.split_same hc
              refine mul_le_mul_of_nonneg_left (hζmax _ ?_) (Nat.cast_nonneg _)
              change (ζ.split i j).nA + (ζ.split i j).nB = L
              omega
          _ = ((ζ.t : ℕ) : ℝ) * M := by
              rw [← ζ.sum_c]
              push_cast
              simp [Finset.sum_mul]
      have habs : diag θA θB ρ ζ * M
          = |(∑ i, ∑ j, ((ζ.coalAB i j : ℕ) : ℝ) * h (ζ.mergeAB i j))
              + ρ * ∑ i, ∑ j, ((ζ.c i j : ℕ) : ℝ) * h (ζ.split i j)| := by
        rw [← heq0, abs_mul, abs_of_pos hDpos]
      have hchain : diag θA θB ρ ζ * M
          ≤ ((2 * (ζ.sumA * ζ.sumB) : ℕ) : ℝ) * M + ρ * (((ζ.t : ℕ) : ℝ) * M) := by
        rw [habs]
        refine le_trans (abs_add_le _ _) ?_
        rw [abs_mul, abs_of_nonneg hρ]
        exact add_le_add hA (mul_le_mul_of_nonneg_left hB hρ)
      have hc1 : ((2 * (ζ.sumA * ζ.sumB) : ℕ) : ℝ) ≤ ((ζ.n * (ζ.n - 1) : ℕ) : ℝ) := by
        exact_mod_cast ζ.two_mul_sumA_mul_sumB_le
      have hlev1 : 1 ≤ ζ.nA + ζ.nB := by have := ζ.n_add_t; omega
      have hP : 0 < θA * ((ζ.nA : ℕ) : ℝ) + θB * ((ζ.nB : ℕ) : ℝ) := by
        rcases Nat.eq_zero_or_pos ζ.nA with h0 | h0
        · have hb : 0 < ζ.nB := by omega
          have h1 : (0 : ℝ) < θB * ((ζ.nB : ℕ) : ℝ) := mul_pos hθB (by exact_mod_cast hb)
          have h2 : (0 : ℝ) ≤ θA * ((ζ.nA : ℕ) : ℝ) := mul_nonneg hθA.le (Nat.cast_nonneg _)
          linarith
        · have h1 : (0 : ℝ) < θA * ((ζ.nA : ℕ) : ℝ) := mul_pos hθA (by exact_mod_cast h0)
          have h2 : (0 : ℝ) ≤ θB * ((ζ.nB : ℕ) : ℝ) := mul_nonneg hθB.le (Nat.cast_nonneg _)
          linarith
      have hDge : ((2 * (ζ.sumA * ζ.sumB) : ℕ) : ℝ)
          + (θA * ((ζ.nA : ℕ) : ℝ) + θB * ((ζ.nB : ℕ) : ℝ)) + ρ * ((ζ.t : ℕ) : ℝ)
            ≤ diag θA θB ρ ζ := by
        simp only [Rhone.LinearAlgebra.Recursion.diag]
        linarith [hc1]
      by_contra hne
      have hMpos : 0 < M := lt_of_le_of_ne hMnn (Ne.symm hne)
      nlinarith [hchain, hDge, hP, hMpos, mul_pos hP hMpos]
    have := hζmax ξ hξ
    rw [hzero] at this
    exact abs_eq_zero.mp (le_antisymm this (abs_nonneg _))

open Classical in
theorem genMat_det_ne_zero {θA θB ρ : ℝ} (πA : Fin KA → ℝ) (πB : Fin KB → ℝ) (N : ℕ)
    (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) : (genMat θA θB ρ πA πB N).det ≠ 0 := by
  classical
  intro hdet
  obtain ⟨v, hv, hQv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  apply hv
  have hz : ∀ η : Config KA KB, η.nA + η.nB ≤ N → extend v η = 0 := by
    refine homogeneous_eq_zero_of_one_le (πA := πA) (πB := πB) hθA hθB hρ ?_ ?_
    · have hnm : (0 : Config KA KB) ∉ levelSet KA KB N := fun h => by
        have := (mem_levelSet.mp h).2
        simp [Config.n] at this
      rw [extend_apply, dite_eq_right hnm]
    · intro η hn hl
      have hmem : η ∈ levelSet KA KB N := mem_levelSet.mpr ⟨hl, hn⟩
      have h1 := congrFun hQv ⟨η, hmem⟩
      rw [genMat_mulVec] at h1
      rw [extend_apply, dite_eq_left hmem]
      simp only [Pi.zero_apply] at h1
      linarith
  funext ξ
  have h1 := hz ξ.1 (mem_levelSet.mp ξ.2).1
  rw [extend_apply, dite_eq_left ξ.2] at h1
  exact h1

theorem genMat_mulVec_qProb {θA θB ρ : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ} (N : ℕ)
    (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (hπA : ∀ i, 0 ≤ πA i) (hsA : ∑ i, πA i = 1)
    (hπB : ∀ j, 0 ≤ πB j) (hsB : ∑ j, πB j = 1) :
    genMat θA θB ρ πA πB N *ᵥ (fun ξ => qProb θA θB ρ πA πB ξ.1) +
      genRhs θA θB ρ πA πB N = 0 := by
  classical
  funext ξ
  simp only [Pi.add_apply, Pi.zero_apply, genMat_mulVec, genRhs]
  have hagree : ∀ η : Config KA KB, η.nA ≤ ξ.1.nA → η.nB ≤ ξ.1.nB →
      (fun η => extend (fun ξ' : Idx KA KB N => qProb θA θB ρ πA πB ξ'.1) η +
        indCfg 0 η) η = qProb θA θB ρ πA πB η := by
    intro η h1 h2
    have hl : η.nA + η.nB ≤ N := le_trans (by omega) (mem_levelSet.mp ξ.2).1
    simp only [extend_apply, indCfg]
    by_cases hn : 1 ≤ η.n
    · have hmem : η ∈ levelSet KA KB N := mem_levelSet.mpr ⟨hl, hn⟩
      have hne : η ≠ 0 := by
        rintro rfl
        simp [Config.n] at hn
      rw [dite_eq_left hmem, ite_eq_right hne, add_zero]
    · have h0 : η = 0 := Config.eq_zero_of_n_eq_zero η (by omega)
      subst h0
      have hnm : (0 : Config KA KB) ∉ levelSet KA KB N := fun h => hn (mem_levelSet.mp h).2
      rw [dite_eq_right hnm, ite_eq_left rfl, zero_add, qProb_zero]
  have hsum : rhs θA θB ρ πA πB (extend fun ξ' : Idx KA KB N => qProb θA θB ρ πA πB ξ'.1) ξ.1 +
      rhs θA θB ρ πA πB (indCfg 0) ξ.1 = rhs θA θB ρ πA πB (qProb θA θB ρ πA πB) ξ.1 := by
    rw [← rhs_add]
    exact rhs_congr θA θB ρ πA πB ξ.1 hagree
  have hn : ξ.1.n ≠ 0 := by have := (mem_levelSet.mp ξ.2).2; omega
  have hrec := qProb_recursion hθA hθB hρ hπA hsA hπB hsB hn
  linarith

open Classical in
theorem tendsto_qProb_of_expansion {θA θB ρ : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ}
    {N : ℕ} (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (hπA : ∀ i, 0 ≤ πA i)
    (hsA : ∑ i, πA i = 1) (hπB : ∀ j, 0 ≤ πB j) (hsB : ∑ j, πB j = 1)
    {P : ℕ → Matrix (Idx KA KB N) (Idx KA KB N) ℝ} {p h : ℕ → Idx KA KB N → ℝ}
    (hP : Tendsto (fun M : ℕ => (M : ℝ) • (P M - 1)) atTop
      (𝓝 ((1 / 2 : ℝ) • genMat θA θB ρ πA πB N)))
    (hp : Tendsto (fun M : ℕ => (M : ℝ) • p M) atTop
      (𝓝 ((1 / 2 : ℝ) • genRhs θA θB ρ πA πB N)))
    (hfix : ∀ᶠ M in atTop, h M = P M *ᵥ h M + p M) :
    Tendsto h atTop (𝓝 fun ξ => qProb θA θB ρ πA πB ξ.1) := by
  classical
  set Q := (1 / 2 : ℝ) • genMat θA θB ρ πA πB N with hQ
  set r := (1 / 2 : ℝ) • genRhs θA θB ρ πA πB N with hr
  have hdet : Q.det ≠ 0 := by
    rw [hQ, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (genMat_det_ne_zero πA πB N hθA hθB hρ)
  have hE : Tendsto (fun M : ℕ => (M : ℝ) • (P M - 1) - Q) atTop (𝓝 0) := by
    have := hP.sub (tendsto_const_nhds (x := Q))
    rwa [sub_self] at this
  have he : Tendsto (fun M : ℕ => (M : ℝ) • p M - r) atTop (𝓝 0) := by
    have := hp.sub (tendsto_const_nhds (x := r))
    rwa [sub_self] at this
  have hε : ∀ᶠ M : ℕ in atTop, (1 / (M : ℝ)) ≠ 0 := by
    filter_upwards [eventually_ge_atTop 1] with M hM
    have : (0 : ℝ) < M := by exact_mod_cast hM
    positivity
  have hfix' : ∀ᶠ M : ℕ in atTop, h M = (1 + (1 / (M : ℝ)) • (Q + ((M : ℝ) • (P M - 1) - Q)))
      *ᵥ h M + (1 / (M : ℝ)) • (r + ((M : ℝ) • p M - r)) := by
    filter_upwards [hfix, eventually_ge_atTop 1] with M hM hM1
    have hM0 : (M : ℝ) ≠ 0 := by have : (1 : ℝ) ≤ M := by exact_mod_cast hM1
                                 linarith
    have h1 : (1 : Matrix (Idx KA KB N) (Idx KA KB N) ℝ) +
        (1 / (M : ℝ)) • (Q + ((M : ℝ) • (P M - 1) - Q)) = P M := by
      rw [add_sub_cancel, smul_smul, one_div, inv_mul_cancel₀ hM0, one_smul, add_sub_cancel]
    have h2 : (1 / (M : ℝ)) • (r + ((M : ℝ) • p M - r)) = p M := by
      rw [add_sub_cancel, smul_smul, one_div, inv_mul_cancel₀ hM0, one_smul]
    rw [h1, h2]
    exact hM
  obtain ⟨h₀, hlim, hsol, huniq⟩ :=
    Rhone.LinearAlgebra.PerturbedLinearLimit.tendsto_of_fixed_perturbed hdet hE he hε hfix'
  have hq : Q *ᵥ (fun ξ : Idx KA KB N => qProb θA θB ρ πA πB ξ.1) + r = 0 := by
    have h1 := genMat_mulVec_qProb N hθA hθB hρ hπA hsA hπB hsB
    rw [hQ, hr, Matrix.smul_mulVec, ← smul_add, h1, smul_zero]
  rw [huniq _ hq] at *
  exact hlim

end Rhone.Coalescent.WFTwoLocusLimit
