/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Coalescent.WeakSelectionEdge
public import Rhone.LinearAlgebra.Recursion.Exist
public import Rhone.Probability.Denominator.Marginal

/-! # The first-order selection response of the two-locus corpus at every configuration -/

@[expose] public section
namespace Rhone.Coalescent
open Finset LinearAlgebra.Recursion Analysis.TruncationRemainder TruncationRemainder

section WellPosed

variable {KA KB : ℕ} {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F} {πA : Fin KA → F} {πB : Fin KB → F}

theorem one_le_level_of_one_le_n {ξ : Config KA KB} (hn : 1 ≤ ξ.n) : 1 ≤ ξ.nA + ξ.nB := by
  have := ξ.n_add_t; omega

theorem homogeneous_eq_zero_le_of_empty (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    {h : Config KA KB → F} {N : ℕ} (h0 : h 0 = 0)
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
      · rw [ζ.eq_zero_of_n_eq_zero hn, h0, abs_zero]
      have hn1 : 1 ≤ ζ.n := by omega
      have heq := hrec ζ hn1 (by omega)
      rw [rhs_of_vanishing_below θA θB ρ πA πB ζ
        (fun η h1 h2 h3 => hbelow η (by omega))] at heq
      set M : F := |h ζ| with hMdef
      have hMnn : (0 : F) ≤ M := abs_nonneg _
      have hDpos : 0 < diag θA θB ρ ζ := Rhone.LinearAlgebra.Recursion.diag_pos hθA hθB hρ hn1
      have hA : |∑ i, ∑ j, ((ζ.coalAB i j : ℕ) : F) * h (ζ.mergeAB i j)|
          ≤ ((2 * (ζ.sumA * ζ.sumB) : ℕ) : F) * M := by
        calc |∑ i, ∑ j, ((ζ.coalAB i j : ℕ) : F) * h (ζ.mergeAB i j)|
            ≤ ∑ i, |∑ j, ((ζ.coalAB i j : ℕ) : F) * h (ζ.mergeAB i j)| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ i, ∑ j, ((ζ.coalAB i j : ℕ) : F) * M := by
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
          _ = ((2 * (ζ.sumA * ζ.sumB) : ℕ) : F) * M := by
              rw [← ζ.sum_coalAB]
              push_cast
              simp [Finset.sum_mul]
      have hB : |∑ i, ∑ j, ((ζ.c i j : ℕ) : F) * h (ζ.split i j)| ≤ ((ζ.t : ℕ) : F) * M := by
        calc |∑ i, ∑ j, ((ζ.c i j : ℕ) : F) * h (ζ.split i j)|
            ≤ ∑ i, |∑ j, ((ζ.c i j : ℕ) : F) * h (ζ.split i j)| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ i, ∑ j, ((ζ.c i j : ℕ) : F) * M := by
              refine Finset.sum_le_sum fun i _ => ?_
              refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun j _ => ?_)
              rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
              by_cases hc : ζ.c i j = 0
              · rw [hc]; simp
              obtain ⟨e1, e2⟩ := ζ.split_same hc
              refine mul_le_mul_of_nonneg_left (hζmax _ ?_) (Nat.cast_nonneg _)
              change (ζ.split i j).nA + (ζ.split i j).nB = L
              omega
          _ = ((ζ.t : ℕ) : F) * M := by
              rw [← ζ.sum_c]
              push_cast
              simp [Finset.sum_mul]
      have habs : diag θA θB ρ ζ * M
          = |(∑ i, ∑ j, ((ζ.coalAB i j : ℕ) : F) * h (ζ.mergeAB i j))
              + ρ * ∑ i, ∑ j, ((ζ.c i j : ℕ) : F) * h (ζ.split i j)| := by
        rw [← heq, abs_mul, abs_of_pos hDpos]
      have hchain : diag θA θB ρ ζ * M
          ≤ ((2 * (ζ.sumA * ζ.sumB) : ℕ) : F) * M + ρ * (((ζ.t : ℕ) : F) * M) := by
        rw [habs]
        refine le_trans (abs_add_le _ _) ?_
        rw [abs_mul, abs_of_nonneg hρ]
        exact add_le_add hA (mul_le_mul_of_nonneg_left hB hρ)
      have hc1 : ((2 * (ζ.sumA * ζ.sumB) : ℕ) : F) ≤ ((ζ.n * (ζ.n - 1) : ℕ) : F) := by
        exact_mod_cast ζ.two_mul_sumA_mul_sumB_le
      have hlev1 := one_le_level_of_one_le_n hn1
      have hP : 0 < θA * ((ζ.nA : ℕ) : F) + θB * ((ζ.nB : ℕ) : F) := by
        rcases Nat.eq_zero_or_pos ζ.nA with h0' | h0'
        · have hb : 0 < ζ.nB := by omega
          have h1 : (0 : F) < θB * ((ζ.nB : ℕ) : F) := mul_pos hθB (by exact_mod_cast hb)
          have h2 : (0 : F) ≤ θA * ((ζ.nA : ℕ) : F) := mul_nonneg hθA.le (Nat.cast_nonneg _)
          linarith
        · have h1 : (0 : F) < θA * ((ζ.nA : ℕ) : F) := mul_pos hθA (by exact_mod_cast h0')
          have h2 : (0 : F) ≤ θB * ((ζ.nB : ℕ) : F) := mul_nonneg hθB.le (Nat.cast_nonneg _)
          linarith
      have hDge : ((2 * (ζ.sumA * ζ.sumB) : ℕ) : F)
          + (θA * ((ζ.nA : ℕ) : F) + θB * ((ζ.nB : ℕ) : F)) + ρ * ((ζ.t : ℕ) : F)
            ≤ diag θA θB ρ ζ := by
        simp only [Rhone.LinearAlgebra.Recursion.diag]
        linarith [hc1]
      by_contra hne
      have hMpos : 0 < M := lt_of_le_of_ne hMnn (Ne.symm hne)
      nlinarith [hchain, hDge, hP, hMpos, mul_pos hP hMpos]
    have := hζmax ξ hξ
    rw [hzero] at this
    exact abs_eq_zero.mp (le_antisymm this (abs_nonneg _))

noncomputable def levelOp (θA θB ρ : F) (πA : Fin KA → F) (πB : Fin KB → F) (N : ℕ) :
    (↥{ξ : Config KA KB | ξ.nA + ξ.nB = N} → F) →ₗ[F]
      (↥{ξ : Config KA KB | ξ.nA + ξ.nB = N} → F) where
  toFun v := fun ξ =>
    if 1 ≤ (ξ : Config KA KB).n
      then diag θA θB ρ (ξ : Config KA KB) * v ξ
        - rhs θA θB ρ πA πB (extZero N v) (ξ : Config KA KB)
      else v ξ
  map_add' v w := by
    have hext : extZero N (v + w) = fun η => extZero N v η + extZero N w η := by
      funext η; simp only [extZero]; split_ifs <;> simp
    funext ξ
    simp only [Pi.add_apply, hext, Rhone.LinearAlgebra.Recursion.rhs_add]
    split_ifs with hn
    · ring
    · rfl
  map_smul' c v := by
    have hext : extZero N (c • v) = fun η => c * extZero N v η := by
      funext η; simp only [extZero]; split_ifs <;> simp
    funext ξ
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, hext,
      Rhone.LinearAlgebra.Recursion.rhs_smul]
    split_ifs with hn
    · ring
    · rfl

theorem levelOp_injective (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (N : ℕ) :
    Function.Injective (levelOp θA θB ρ πA πB N) := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  have hv' : ∀ (η : Config KA KB) (hη : η.nA + η.nB = N),
      (if 1 ≤ η.n
        then diag θA θB ρ η * v ⟨η, hη⟩ - rhs θA θB ρ πA πB (extZero N v) η
        else v ⟨η, hη⟩) = 0 := by
    intro η hη
    exact congrFun hv ⟨η, hη⟩
  have hz : ∀ η : Config KA KB, η.nA + η.nB ≠ N → extZero N v η = 0 := by
    intro η hη; simp [extZero, hη]
  have hon : ∀ (η : Config KA KB) (h : η.nA + η.nB = N), extZero N v η = v ⟨η, h⟩ := by
    intro η h; simp [extZero, h]
  have h0 : extZero N v (0 : Config KA KB) = 0 := by
    by_cases hl : (0 : Config KA KB).nA + (0 : Config KA KB).nB = N
    · have h3 := hv' 0 hl
      rw [ite_eq_right (show ¬ (1 ≤ (0 : Config KA KB).n) by simp)] at h3
      rw [hon 0 hl]; exact h3
    · exact hz 0 hl
  have hrec : ∀ ξ : Config KA KB, 1 ≤ ξ.n → ξ.nA + ξ.nB ≤ N →
      diag θA θB ρ ξ * extZero N v ξ = rhs θA θB ρ πA πB (extZero N v) ξ := by
    intro ξ hn hl
    by_cases hlev : ξ.nA + ξ.nB = N
    · have h2 := hv' ξ hlev
      rw [ite_eq_left hn] at h2
      rw [hon ξ hlev]
      linear_combination h2
    · have hb : ∀ η : Config KA KB, η.nA ≤ ξ.nA → η.nB ≤ ξ.nB → extZero N v η = 0 :=
        fun η h1 h2 => hz η (by omega)
      rw [hz ξ hlev, mul_zero,
        rhs_congr θA θB ρ πA πB (q₂ := fun _ => (0 : F)) ξ hb, rhs_zero]
  have key := homogeneous_eq_zero_le_of_empty (πA := πA) (πB := πB) hθA hθB hρ h0 hrec
  funext ξ
  have := key ξ (le_of_eq ξ.2)
  rw [hon ξ ξ.2] at this
  simpa using this

theorem exists_levelSolve (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (N : ℕ) (c : F)
    (s g : Config KA KB → F) :
    ∃ u : Config KA KB → F,
      (∀ η : Config KA KB, η.nA + η.nB ≠ N → u η = g η) ∧
      (∀ ξ : Config KA KB, ξ.nA + ξ.nB = N → ξ.n = 0 → u ξ = c) ∧
      (∀ ξ : Config KA KB, ξ.nA + ξ.nB = N → 1 ≤ ξ.n →
        diag θA θB ρ ξ * u ξ = rhs θA θB ρ πA πB u ξ + s ξ) := by
  obtain ⟨v, hv⟩ := (LinearMap.injective_iff_surjective.mp
      (levelOp_injective (πA := πA) (πB := πB) hθA hθB hρ N))
    (fun ξ => if 1 ≤ (ξ : Config KA KB).n
      then rhs θA θB ρ πA πB (offLevel N g) (ξ : Config KA KB) + s ξ
      else c)
  have hv' : ∀ (η : Config KA KB) (hη : η.nA + η.nB = N),
      (if 1 ≤ η.n
        then diag θA θB ρ η * v ⟨η, hη⟩ - rhs θA θB ρ πA πB (extZero N v) η
        else v ⟨η, hη⟩)
      = (if 1 ≤ η.n then rhs θA θB ρ πA πB (offLevel N g) η + s η else c) := by
    intro η hη
    exact congrFun hv ⟨η, hη⟩
  refine ⟨glue N g v, fun η hη => by simp [glue, hη], ?_, ?_⟩
  · intro ξ hlev hn
    have h2 := hv' ξ hlev
    rw [ite_eq_right (show ¬ (1 ≤ ξ.n) by omega),
      ite_eq_right (show ¬ (1 ≤ ξ.n) by omega)] at h2
    simpa [glue, hlev] using h2
  · intro ξ hlev hn
    have h2 := hv' ξ hlev
    rw [ite_eq_left hn, ite_eq_left hn] at h2
    have hu : glue N g v ξ = v ⟨ξ, hlev⟩ := by simp [glue, hlev]
    rw [hu, glue_eq_add, Rhone.LinearAlgebra.Recursion.rhs_add]
    linear_combination h2

def SolvesInhomUpTo (θA θB ρ : F) (πA : Fin KA → F) (πB : Fin KB → F) (c : F)
    (s : Config KA KB → F) (N : ℕ) (u : Config KA KB → F) : Prop :=
  u 0 = c ∧ ∀ ξ : Config KA KB, 1 ≤ ξ.n → ξ.nA + ξ.nB ≤ N →
    diag θA θB ρ ξ * u ξ = rhs θA θB ρ πA πB u ξ + s ξ

theorem SolvesInhomUpTo.eq_of_le (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) {c : F}
    {s : Config KA KB → F} {N : ℕ} {u w : Config KA KB → F}
    (hu : SolvesInhomUpTo θA θB ρ πA πB c s N u) (hw : SolvesInhomUpTo θA θB ρ πA πB c s N w) :
    ∀ ξ : Config KA KB, ξ.nA + ξ.nB ≤ N → u ξ = w ξ := by
  have h0 : u 0 - w 0 = 0 := by rw [hu.1, hw.1, sub_self]
  have hrec : ∀ ξ : Config KA KB, 1 ≤ ξ.n → ξ.nA + ξ.nB ≤ N →
      diag θA θB ρ ξ * (u ξ - w ξ) = rhs θA θB ρ πA πB (fun η => u η - w η) ξ := by
    intro ξ hn hl
    rw [rhs_sub, mul_sub, hu.2 ξ hn hl, hw.2 ξ hn hl]
    ring
  intro ξ hξ
  have := homogeneous_eq_zero_le_of_empty (πA := πA) (πB := πB) (h := fun η => u η - w η)
    hθA hθB hρ h0 hrec ξ hξ
  exact sub_eq_zero.mp this

theorem exists_solvesInhomUpTo (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (c : F)
    (s : Config KA KB → F) (N : ℕ) :
    ∃ u : Config KA KB → F, SolvesInhomUpTo θA θB ρ πA πB c s N u := by
  induction N with
  | zero =>
    refine ⟨fun _ => c, rfl, ?_⟩
    intro ξ hn hl
    have := one_le_level_of_one_le_n hn
    omega
  | succ N ih =>
    obtain ⟨g, hg0, hg⟩ := ih
    obtain ⟨u, hoff, -, hrec⟩ :=
      exists_levelSolve (πA := πA) (πB := πB) hθA hθB hρ (N + 1) c s g
    have hlow : ∀ η : Config KA KB, η.nA + η.nB ≤ N → u η = g η :=
      fun η hη => hoff η (by omega)
    refine ⟨u, ?_, ?_⟩
    · rw [hlow 0 (by simp), hg0]
    · intro ξ hn hl
      by_cases hlev : ξ.nA + ξ.nB = N + 1
      · exact hrec ξ hlev hn
      · have hle : ξ.nA + ξ.nB ≤ N := by omega
        have hcongr : rhs θA θB ρ πA πB u ξ = rhs θA θB ρ πA πB g ξ :=
          rhs_congr θA θB ρ πA πB ξ fun η h1 h2 => hlow η (by omega)
        rw [hlow ξ hle, hcongr]
        exact hg ξ hn hle

theorem existsUnique_inhomogeneous (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (c : F)
    (s : Config KA KB → F) :
    ∃! u : Config KA KB → F, u 0 = c ∧ ∀ ξ : Config KA KB, 1 ≤ ξ.n →
      diag θA θB ρ ξ * u ξ = rhs θA θB ρ πA πB u ξ + s ξ := by
  choose ap hap using exists_solvesInhomUpTo (πA := πA) (πB := πB) hθA hθB hρ c s
  have hcoh : ∀ {M N : ℕ}, M ≤ N → ∀ ξ : Config KA KB, ξ.nA + ξ.nB ≤ M →
      ap M ξ = ap N ξ := by
    intro M N hMN ξ hξ
    refine SolvesInhomUpTo.eq_of_le (πA := πA) (πB := πB) hθA hθB hρ (hap M)
      ⟨(hap N).1, fun η hn hl => (hap N).2 η hn (le_trans hl hMN)⟩ ξ hξ
  refine ⟨fun ξ => ap (ξ.nA + ξ.nB) ξ, ⟨?_, ?_⟩, ?_⟩
  · exact (hap _).1
  · intro ξ hn
    have hcongr : rhs θA θB ρ πA πB (fun η => ap (η.nA + η.nB) η) ξ
        = rhs θA θB ρ πA πB (ap (ξ.nA + ξ.nB)) ξ :=
      rhs_congr θA θB ρ πA πB ξ fun η h1 h2 => hcoh (by omega) η le_rfl
    rw [hcongr]
    exact (hap _).2 ξ hn le_rfl
  · rintro w ⟨hw0, hw⟩
    funext ξ
    exact SolvesInhomUpTo.eq_of_le (πA := πA) (πB := πB) hθA hθB hρ
      ⟨hw0, fun η hn _ => hw η hn⟩ (hap (ξ.nA + ξ.nB)) ξ le_rfl

theorem eq_q_of_recursion (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) {u : Config KA KB → F}
    (hu0 : u 0 = 1)
    (hu : ∀ ξ : Config KA KB, 1 ≤ ξ.n → diag θA θB ρ ξ * u ξ = rhs θA θB ρ πA πB u ξ) :
    u = Rhone.LinearAlgebra.Recursion.q (πA := πA) (πB := πB) hθA hθB hρ := by
  have hq := q_isSolution (πA := πA) (πB := πB) hθA hθB hρ
  refine (existsUnique_inhomogeneous (πA := πA) (πB := πB) hθA hθB hρ 1
    (fun _ => 0)).unique ⟨hu0, fun ξ hn => by rw [add_zero]; exact hu ξ hn⟩
    ⟨hq.empty, fun ξ _ => ?_⟩
  rw [add_zero]
  exact Rhone.Probability.Denominator.recursion_all hθA hθB hρ hq ξ

end WellPosed

section Response

variable {KA KB : ℕ} {θA θB ρ : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ}

theorem sel_congr_of_pos (i₀ : Fin KA) {u w : Config KA KB → ℝ}
    (huw : ∀ η : Config KA KB, 1 ≤ η.n → u η = w η) {ξ : Config KA KB} (hξ : 1 ≤ ξ.n) :
    sel i₀ u ξ = sel i₀ w ξ := by
  have hsum : (∑ j, ((ξ.b j : ℕ) : ℝ) * u (bToC ξ i₀ j))
      = ∑ j, ((ξ.b j : ℕ) : ℝ) * w (bToC ξ i₀ j) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hb : ξ.b j = 0
    · rw [hb]; simp
    · rw [huw _ (by rw [n_bToC ξ i₀ hb]; exact hξ)]
  simp only [sel]
  rw [hsum, huw ξ hξ, huw _ (by rw [n_incA]; omega)]

noncomputable def selResponse (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (i₀ : Fin KA) :
    Config KA KB → ℝ :=
  Classical.choose (existsUnique_inhomogeneous (πA := πA) (πB := πB) hθA hθB hρ 0
    (sel i₀ (Rhone.LinearAlgebra.Recursion.q (πA := πA) (πB := πB) hθA hθB hρ))).exists

theorem selResponse_spec (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (i₀ : Fin KA) :
    selResponse (πA := πA) (πB := πB) hθA hθB hρ i₀ 0 = 0 ∧
      ∀ ξ : Config KA KB, 1 ≤ ξ.n →
        diag θA θB ρ ξ * selResponse (πA := πA) (πB := πB) hθA hθB hρ i₀ ξ
          = rhs θA θB ρ πA πB (selResponse (πA := πA) (πB := πB) hθA hθB hρ i₀) ξ
            + sel i₀ (Rhone.LinearAlgebra.Recursion.q (πA := πA) (πB := πB) hθA hθB hρ) ξ :=
  Classical.choose_spec (existsUnique_inhomogeneous (πA := πA) (πB := πB) hθA hθB hρ 0
    (sel i₀ (Rhone.LinearAlgebra.Recursion.q (πA := πA) (πB := πB) hθA hθB hρ))).exists

theorem selResponse_empty (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (i₀ : Fin KA) :
    selResponse (πA := πA) (πB := πB) hθA hθB hρ i₀ (0 : Config KA KB) = 0 :=
  (selResponse_spec hθA hθB hρ i₀).1

theorem selResponse_recursion (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (i₀ : Fin KA)
    {q : Config KA KB → ℝ} (hq : IsSolution θA θB ρ πA πB q) (ξ : Config KA KB)
    (hn : 1 ≤ ξ.n) :
    diag θA θB ρ ξ * selResponse (πA := πA) (πB := πB) hθA hθB hρ i₀ ξ
      = rhs θA θB ρ πA πB (selResponse (πA := πA) (πB := πB) hθA hθB hρ i₀) ξ
        + sel i₀ q ξ := by
  rw [q_unique hθA hθB hρ hq]
  exact (selResponse_spec hθA hθB hρ i₀).2 ξ hn

theorem selResponse_unique (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (i₀ : Fin KA)
    {q : Config KA KB → ℝ} (hq : IsSolution θA θB ρ πA πB q) {u : Config KA KB → ℝ}
    (hu0 : u 0 = 0)
    (hu : ∀ ξ : Config KA KB, 1 ≤ ξ.n →
      diag θA θB ρ ξ * u ξ = rhs θA θB ρ πA πB u ξ + sel i₀ q ξ) :
    u = selResponse (πA := πA) (πB := πB) hθA hθB hρ i₀ := by
  rw [q_unique hθA hθB hρ hq] at hu
  exact (existsUnique_inhomogeneous (πA := πA) (πB := πB) hθA hθB hρ 0
    (sel i₀ (Rhone.LinearAlgebra.Recursion.q (πA := πA) (πB := πB) hθA hθB hρ))).unique ⟨hu0, hu⟩
    (selResponse_spec hθA hθB hρ i₀)

theorem selResponse_of_nB_eq_zero (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (i₀ : Fin KA)
    (ξ : Config KA KB) (hB : ξ.nB = 0) :
    selResponse (πA := πA) (πB := πB) hθA hθB hρ i₀ ξ = tiltResponse θA πA i₀ ξ.a := by
  have hq := q_isSolution (πA := πA) (πB := πB) hθA hθB hρ
  refine edge_response_unique (θB := θB) (ρ := ρ) (πB := πB) hθA i₀ _ ?_ ?_ ξ hB
  · intro η hη
    rw [η.eq_zero_of_n_eq_zero hη]
    exact selResponse_empty hθA hθB hρ i₀
  · intro η hηB hηn
    rw [← sel_eq_sel_edgeNeutral hθA hq i₀ η hηB]
    exact selResponse_recursion hθA hθB hρ i₀ hq η hηn

theorem IsHierarchy.zero_eq_q (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) {i₀ : Fin KA}
    {V : Config KA KB → ℝ} {q : ℕ → Config KA KB → ℝ}
    (hq : IsHierarchy V (Tplus θA θB ρ πA πB) (Umodel θA θB ρ i₀) (vplus θA θB ρ πA πB) q)
    (ξ : Config KA KB) (hn : 1 ≤ ξ.n) :
    q 0 ξ = Rhone.LinearAlgebra.Recursion.q (πA := πA) (πB := πB) hθA hθB hρ ξ := by
  set f : Config KA KB → ℝ := fun η => if η.n = 0 then 1 else q 0 η with hf
  have hfq : ∀ η : Config KA KB, 1 ≤ η.n → f η = q 0 η := by
    intro η hη
    have : η.n ≠ 0 := by omega
    simp [hf, this]
  have key := eq_q_of_recursion (πA := πA) (πB := πB) hθA hθB hρ (u := f) (by simp [hf]) ?_
  · rw [← hfq ξ hn, key]
  · intro η hηn
    have hD := (Rhone.LinearAlgebra.Recursion.diag_pos hθA hθB hρ hηn).ne'
    have h := hq.zero η
    rw [Tplus_add_vplus, Tfull] at h
    rw [hfq η hηn, h]
    field_simp
    rfl

theorem IsHierarchy.one_eq_selResponse (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ)
    {i₀ : Fin KA} {V : Config KA KB → ℝ} {q : ℕ → Config KA KB → ℝ}
    (hq : IsHierarchy V (Tplus θA θB ρ πA πB) (Umodel θA θB ρ i₀) (vplus θA θB ρ πA πB) q)
    (ξ : Config KA KB) (hn : 1 ≤ ξ.n) :
    q 1 ξ = selResponse (πA := πA) (πB := πB) hθA hθB hρ i₀ ξ := by
  have hr : ∀ η : Config KA KB, 1 ≤ η.n → restr (q 1) η = q 1 η := by
    intro η hη
    have : η.n ≠ 0 := by omega
    simp [restr, this]
  rw [← hr ξ hn]
  refine congrFun (selResponse_unique hθA hθB hρ i₀
    (q_isSolution (πA := πA) (πB := πB) hθA hθB hρ) (u := restr (q 1)) (by simp [restr])
    ?_) ξ
  intro η hηn
  have hD := (Rhone.LinearAlgebra.Recursion.diag_pos hθA hθB hρ hηn).ne'
  have h := hq.succ 0 η
  rw [zero_add, Tplus, Tfull, Umodel] at h
  have hsel : sel i₀ (q 0) η
      = sel i₀ (Rhone.LinearAlgebra.Recursion.q (πA := πA) (πB := πB) hθA hθB hρ) η :=
    sel_congr_of_pos i₀ (fun ζ hζ => IsHierarchy.zero_eq_q hθA hθB hρ hq ζ hζ) hηn
  rw [hr η hηn, h, ← hsel]
  field_simp

end Response

end Rhone.Coalescent
