/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Algebra.Rational.BlockOp

/-! # Well-posedness of the killed-PIM recursion over an arbitrary field -/

@[expose] public section

namespace Rhone.Algebra.Rational

open Finset LinearAlgebra.Recursion LinearAlgebra.Recursion.Config

variable {KA KB : ℕ} {F : Type*} [Field F]
variable {θA θB ρ : F} {πA : Fin KA → F} {πB : Fin KB → F}

theorem homogeneous_eq_zero_le' (hinj : ∀ N, Function.Injective (bOp θA θB ρ πA πB N))
    {h : Config KA KB → F} {N : ℕ}
    (hbd : ∀ ξ : Config KA KB, ξ.n ≤ 1 → ξ.nA + ξ.nB ≤ N → h ξ = 0)
    (hrec : ∀ ξ : Config KA KB, 2 ≤ ξ.n → ξ.nA + ξ.nB ≤ N →
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
    have hext : ∀ η : Config KA KB, η.nA + η.nB ≤ L →
        extZ L (fun ζ : Lvl KA KB L => h ζ) η = h η := by
      intro η hη
      by_cases hl : η.nA + η.nB = L
      · rw [extZ_of_mem L _ η hl]
      · rw [extZ_of_not_mem L _ hl, hbelow η (by omega)]
    have hzero : bOp θA θB ρ πA πB L (fun ζ : Lvl KA KB L => h ζ) = 0 := by
      funext ζ
      have hζ : (ζ : Config KA KB).nA + (ζ : Config KA KB).nB = L := ζ.2
      rw [bOp_apply]
      split_ifs with hn
      · have hcongr : rhs θA θB ρ πA πB (extZ L (fun ζ : Lvl KA KB L => h ζ))
            (ζ : Config KA KB) = rhs θA θB ρ πA πB h (ζ : Config KA KB) :=
          rhs_congr θA θB ρ πA πB (ζ : Config KA KB) fun η h1 h2 => hext η (by omega)
        rw [hcongr, hrec (ζ : Config KA KB) hn (by omega)]
        simp
      · have := hbd (ζ : Config KA KB) (by omega) (by omega)
        simpa using this
    have hv := (injective_iff_map_eq_zero (bOp θA θB ρ πA πB L)).mp (hinj L) _ hzero
    exact congrFun hv ⟨ξ, hξ⟩

theorem homogeneous_eq_zero' (hinj : ∀ N, Function.Injective (bOp θA θB ρ πA πB N))
    {h : Config KA KB → F}
    (hbd : ∀ ξ : Config KA KB, ξ.n ≤ 1 → h ξ = 0)
    (hrec : ∀ ξ : Config KA KB, 2 ≤ ξ.n → diag θA θB ρ ξ * h ξ = rhs θA θB ρ πA πB h ξ) :
    ∀ ξ : Config KA KB, h ξ = 0 := fun ξ =>
  homogeneous_eq_zero_le' (N := ξ.nA + ξ.nB) hinj (fun η hη _ => hbd η hη)
    (fun η hη _ => hrec η hη) ξ le_rfl

theorem sub_eq_zero_of_n_le_one {q₁ q₂ : Config KA KB → F}
    (h₁ : IsSolution θA θB ρ πA πB q₁) (h₂ : IsSolution θA θB ρ πA πB q₂)
    (ξ : Config KA KB) (hn : ξ.n ≤ 1) : q₁ ξ - q₂ ξ = 0 := by
  rcases Nat.lt_or_ge ξ.n 1 with h | h
  · have hz : ξ = 0 := ξ.eq_zero_of_n_eq_zero (by omega)
    subst hz; rw [h₁.empty, h₂.empty, sub_self]
  · rcases ξ.exists_e_of_n_eq_one (by omega) with ⟨i, rfl⟩ | ⟨j, rfl⟩ | ⟨i, j, rfl⟩
    · rw [h₁.bdryA, h₂.bdryA, sub_self]
    · rw [h₁.bdryB, h₂.bdryB, sub_self]
    · rw [h₁.bdryC, h₂.bdryC, sub_self]

theorem unique_of_isSolution' (hinj : ∀ N, Function.Injective (bOp θA θB ρ πA πB N))
    {q₁ q₂ : Config KA KB → F} (h₁ : IsSolution θA θB ρ πA πB q₁)
    (h₂ : IsSolution θA θB ρ πA πB q₂) : q₁ = q₂ := by
  have hrec : ∀ ξ : Config KA KB, 2 ≤ ξ.n →
      diag θA θB ρ ξ * (q₁ ξ - q₂ ξ) = rhs θA θB ρ πA πB (fun η => q₁ η - q₂ η) ξ := by
    intro ξ hn
    rw [rhs_sub, mul_sub, h₁.recursion ξ hn, h₂.recursion ξ hn]
  funext ξ
  have := homogeneous_eq_zero' hinj (sub_eq_zero_of_n_le_one h₁ h₂) hrec ξ
  linear_combination this

theorem solvesUpTo_eq_of_le' (hinj : ∀ N, Function.Injective (bOp θA θB ρ πA πB N)) {N : ℕ}
    {q₁ q₂ : Config KA KB → F} (h₁ : SolvesUpTo θA θB ρ πA πB N q₁)
    (h₂ : SolvesUpTo θA θB ρ πA πB N q₂) :
    ∀ ξ : Config KA KB, ξ.nA + ξ.nB ≤ N → q₁ ξ = q₂ ξ := by
  have hbd : ∀ ξ : Config KA KB, ξ.n ≤ 1 → ξ.nA + ξ.nB ≤ N → q₁ ξ - q₂ ξ = 0 := by
    intro ξ hn _
    rcases Nat.lt_or_ge ξ.n 1 with h | h
    · have hz : ξ = 0 := ξ.eq_zero_of_n_eq_zero (by omega)
      subst hz; rw [h₁.empty, h₂.empty, sub_self]
    · rcases ξ.exists_e_of_n_eq_one (by omega) with ⟨i, rfl⟩ | ⟨j, rfl⟩ | ⟨i, j, rfl⟩
      · rw [h₁.bdryA, h₂.bdryA, sub_self]
      · rw [h₁.bdryB, h₂.bdryB, sub_self]
      · rw [h₁.bdryC, h₂.bdryC, sub_self]
  have hrec : ∀ ξ : Config KA KB, 2 ≤ ξ.n → ξ.nA + ξ.nB ≤ N →
      diag θA θB ρ ξ * (q₁ ξ - q₂ ξ) = rhs θA θB ρ πA πB (fun η => q₁ η - q₂ η) ξ := by
    intro ξ hn hl
    rw [rhs_sub, mul_sub, h₁.recursion ξ hn hl, h₂.recursion ξ hn hl]
  intro ξ hξ
  have := homogeneous_eq_zero_le' hinj hbd hrec ξ hξ
  linear_combination this

def glueL (N : ℕ) (g : Config KA KB → F) (v : Lvl KA KB N → F) : Config KA KB → F :=
  fun η => if h : η.nA + η.nB = N then v ⟨η, h⟩ else g η

def offLev (N : ℕ) (g : Config KA KB → F) : Config KA KB → F :=
  fun η => if η.nA + η.nB = N then 0 else g η

theorem glueL_eq_add (N : ℕ) (g : Config KA KB → F) (v : Lvl KA KB N → F) :
    glueL N g v = fun η => extZ N v η + offLev N g η := by
  funext η
  simp only [glueL, extZ, offLev]
  by_cases h : η.nA + η.nB = N <;> simp [h]

theorem exists_glue' (hinj : ∀ N, Function.Injective (bOp θA θB ρ πA πB N)) (N : ℕ)
    (g : Config KA KB → F) :
    ∃ u : Config KA KB → F,
      (∀ η : Config KA KB, η.nA + η.nB ≠ N → u η = g η) ∧
      (∀ ξ : Config KA KB, ξ.nA + ξ.nB = N → ξ.n ≤ 1 → u ξ = Config.bdryVal πA πB ξ) ∧
      (∀ ξ : Config KA KB, ξ.nA + ξ.nB = N → 2 ≤ ξ.n →
        diag θA θB ρ ξ * u ξ = rhs θA θB ρ πA πB u ξ) := by
  obtain ⟨v, hv⟩ := (LinearMap.injective_iff_surjective.mp (hinj N))
    (fun ξ => if 2 ≤ (ξ : Config KA KB).n
      then rhs θA θB ρ πA πB (offLev N g) (ξ : Config KA KB)
      else Config.bdryVal πA πB (ξ : Config KA KB))
  have hv' : ∀ (η : Config KA KB) (hη : η.nA + η.nB = N),
      (if 2 ≤ η.n
        then diag θA θB ρ η * v ⟨η, hη⟩ - rhs θA θB ρ πA πB (extZ N v) η
        else v ⟨η, hη⟩)
      = (if 2 ≤ η.n then rhs θA θB ρ πA πB (offLev N g) η
          else Config.bdryVal πA πB η) := fun η hη => congrFun hv ⟨η, hη⟩
  refine ⟨glueL N g v, fun η hη => by simp [glueL, hη], ?_, ?_⟩
  · intro ξ hlev hn
    have h2 := hv' ξ hlev
    rw [ite_eq_right (show ¬ (2 ≤ ξ.n) by omega), ite_eq_right (show ¬ (2 ≤ ξ.n) by omega)] at h2
    simpa [glueL, hlev] using h2
  · intro ξ hlev hn
    have h2 := hv' ξ hlev
    rw [ite_eq_left hn, ite_eq_left hn] at h2
    have hu : glueL N g v ξ = v ⟨ξ, hlev⟩ := by simp [glueL, hlev]
    rw [hu, glueL_eq_add, rhs_add]
    linear_combination h2

theorem exists_solvesUpTo' (hinj : ∀ N, Function.Injective (bOp θA θB ρ πA πB N)) (N : ℕ) :
    ∃ q : Config KA KB → F, SolvesUpTo θA θB ρ πA πB N q := by
  induction N with
  | zero =>
    refine ⟨Config.bdryVal πA πB, Config.bdryVal_zero, fun i => Config.bdryVal_eA i,
      fun j => Config.bdryVal_eB j, fun i j => Config.bdryVal_eC i j, ?_⟩
    intro ξ hn hl
    exfalso
    have := ξ.n_add_t
    omega
  | succ N ih =>
    obtain ⟨g, hg⟩ := ih
    obtain ⟨u, hoff, hbdry, hrec⟩ := exists_glue' hinj (N + 1) g
    have hlow : ∀ η : Config KA KB, η.nA + η.nB ≤ N → u η = g η :=
      fun η hη => hoff η (by omega)
    have hb : ∀ ξ : Config KA KB, ξ.n ≤ 1 → u ξ = Config.bdryVal πA πB ξ := by
      intro ξ hn
      by_cases hlev : ξ.nA + ξ.nB = N + 1
      · exact hbdry ξ hlev hn
      · rw [hoff ξ hlev]
        rcases Nat.lt_or_ge ξ.n 1 with h | h
        · have hz : ξ = 0 := ξ.eq_zero_of_n_eq_zero (by omega)
          subst hz; rw [hg.empty, Config.bdryVal_zero]
        · rcases ξ.exists_e_of_n_eq_one (by omega) with ⟨i, rfl⟩ | ⟨j, rfl⟩ | ⟨i, j, rfl⟩
          · rw [hg.bdryA, Config.bdryVal_eA]
          · rw [hg.bdryB, Config.bdryVal_eB]
          · rw [hg.bdryC, Config.bdryVal_eC]
    refine ⟨u, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hb 0 (by simp), Config.bdryVal_zero]
    · exact fun i => by rw [hb _ (by simp), Config.bdryVal_eA]
    · exact fun j => by rw [hb _ (by simp), Config.bdryVal_eB]
    · exact fun i j => by rw [hb _ (by simp), Config.bdryVal_eC]
    · intro ξ hn hl
      by_cases hlev : ξ.nA + ξ.nB = N + 1
      · exact hrec ξ hlev hn
      · have hle : ξ.nA + ξ.nB ≤ N := by omega
        have hcongr : rhs θA θB ρ πA πB u ξ = rhs θA θB ρ πA πB g ξ :=
          rhs_congr θA θB ρ πA πB ξ fun η h1 h2 => hlow η (by omega)
        rw [hlow ξ hle, hcongr]
        exact hg.recursion ξ hn hle

noncomputable def approx' (hinj : ∀ N, Function.Injective (bOp θA θB ρ πA πB N)) (N : ℕ) :
    Config KA KB → F :=
  Classical.choose (exists_solvesUpTo' hinj N)

theorem approx'_spec (hinj : ∀ N, Function.Injective (bOp θA θB ρ πA πB N)) (N : ℕ) :
    SolvesUpTo θA θB ρ πA πB N (approx' hinj N) :=
  Classical.choose_spec (exists_solvesUpTo' hinj N)

theorem approx'_coherent (hinj : ∀ N, Function.Injective (bOp θA θB ρ πA πB N)) {M N : ℕ}
    (hMN : M ≤ N) (ξ : Config KA KB) (hξ : ξ.nA + ξ.nB ≤ M) :
    approx' hinj M ξ = approx' hinj N ξ :=
  solvesUpTo_eq_of_le' hinj (approx'_spec hinj M) ((approx'_spec hinj N).mono hMN) ξ hξ

theorem exists_isSolution' (hinj : ∀ N, Function.Injective (bOp θA θB ρ πA πB N)) :
    ∃ q : Config KA KB → F, IsSolution θA θB ρ πA πB q := by
  refine ⟨fun ξ => approx' hinj (ξ.nA + ξ.nB) ξ, ?_, ?_, ?_, ?_, ?_⟩
  · exact (approx'_spec hinj _).empty
  · exact fun i => (approx'_spec hinj _).bdryA i
  · exact fun j => (approx'_spec hinj _).bdryB j
  · exact fun i j => (approx'_spec hinj _).bdryC i j
  · intro ξ hn
    have hcongr : rhs θA θB ρ πA πB (fun η => approx' hinj (η.nA + η.nB) η) ξ
        = rhs θA θB ρ πA πB (approx' hinj (ξ.nA + ξ.nB)) ξ :=
      rhs_congr θA θB ρ πA πB ξ fun η h1 h2 => approx'_coherent hinj (by omega) η le_rfl
    rw [hcongr]
    exact (approx'_spec hinj _).recursion ξ hn le_rfl

def DetNeZero (θA θB ρ : F) (πA : Fin KA → F) (πB : Fin KB → F) : Prop :=
  ∀ N : ℕ, (bMat θA θB ρ πA πB N).det ≠ 0

theorem injective_of_detNeZero (h : DetNeZero θA θB ρ πA πB) :
    ∀ N, Function.Injective (bOp θA θB ρ πA πB N) :=
  fun N => bOp_injective_of_det_ne_zero N (h N)

noncomputable def qOfDet (h : DetNeZero θA θB ρ πA πB) : Config KA KB → F :=
  Classical.choose (exists_isSolution' (injective_of_detNeZero h))

theorem qOfDet_isSolution (h : DetNeZero θA θB ρ πA πB) :
    IsSolution θA θB ρ πA πB (qOfDet h) :=
  Classical.choose_spec (exists_isSolution' (injective_of_detNeZero h))

theorem qOfDet_unique (h : DetNeZero θA θB ρ πA πB) {q' : Config KA KB → F}
    (hq : IsSolution θA θB ρ πA πB q') : q' = qOfDet h :=
  unique_of_isSolution' (injective_of_detNeZero h) hq (qOfDet_isSolution h)

end Rhone.Algebra.Rational
