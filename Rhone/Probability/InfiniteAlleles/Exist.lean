/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.InfiniteAlleles.Unique
public import Rhone.LinearAlgebra.Recursion.Exist

/-! # Existence of solutions of the infinite-alleles recursion by approximation and gluing -/

@[expose] public section

namespace Rhone.Probability.InfiniteAlleles

open Finset LinearAlgebra.Recursion LinearAlgebra.Recursion.Config

variable {KA KB : ℕ} {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {θA θB ρ : F}

structure SolvesUpToIA (θA θB ρ : F) (N : ℕ) (q : Config KA KB → F) : Prop where
  empty : q 0 = 1
  bdryA : ∀ i, q (Config.eA i) = 1
  bdryB : ∀ j, q (Config.eB j) = 1
  recursion : ∀ ξ : Config KA KB, 2 ≤ ξ.nA + ξ.nB → ξ.nA + ξ.nB ≤ N →
    diag θA θB ρ ξ * q ξ = rhsIA θA θB ρ q ξ

omit [LinearOrder F] [IsStrictOrderedRing F] in
theorem SolvesUpToIA.mono {N M : ℕ} (hNM : M ≤ N) {q : Config KA KB → F}
    (h : SolvesUpToIA θA θB ρ N q) : SolvesUpToIA θA θB ρ M q :=
  { empty := h.empty, bdryA := h.bdryA, bdryB := h.bdryB
    recursion := fun ξ hn hl => h.recursion ξ hn (le_trans hl hNM) }

theorem SolvesUpToIA.eq_of_le (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) {N : ℕ}
    {q₁ q₂ : Config KA KB → F} (h₁ : SolvesUpToIA θA θB ρ N q₁)
    (h₂ : SolvesUpToIA θA θB ρ N q₂) :
    ∀ ξ : Config KA KB, ξ.nA + ξ.nB ≤ N → q₁ ξ = q₂ ξ := by
  have hbd : ∀ ξ : Config KA KB, ξ.nA + ξ.nB ≤ 1 → q₁ ξ - q₂ ξ = 0 := by
    intro ξ hξ
    rcases level_le_one_cases ξ hξ with rfl | ⟨i, rfl⟩ | ⟨j, rfl⟩
    · rw [h₁.empty, h₂.empty, sub_self]
    · rw [h₁.bdryA, h₂.bdryA, sub_self]
    · rw [h₁.bdryB, h₂.bdryB, sub_self]
  have hrec : ∀ ξ : Config KA KB, 2 ≤ ξ.nA + ξ.nB → ξ.nA + ξ.nB ≤ N →
      diag θA θB ρ ξ * (q₁ ξ - q₂ ξ) = rhsIA θA θB ρ (fun η => q₁ η - q₂ η) ξ := by
    intro ξ hn hl
    rw [rhsIA_sub, mul_sub, h₁.recursion ξ hn hl, h₂.recursion ξ hn hl]
  intro ξ hξ
  have := homogeneousIA_eq_zero_le hθA hθB hρ hbd hrec ξ hξ
  linarith [this]

noncomputable def blockOpIA (θA θB ρ : F) (N : ℕ) :
    (↥{ξ : Config KA KB | ξ.nA + ξ.nB = N} → F) →ₗ[F]
      (↥{ξ : Config KA KB | ξ.nA + ξ.nB = N} → F) where
  toFun v := fun ξ =>
    if 2 ≤ (ξ : Config KA KB).nA + (ξ : Config KA KB).nB
      then diag θA θB ρ (ξ : Config KA KB) * v ξ
        - rhsIA θA θB ρ (extZero N v) (ξ : Config KA KB)
      else v ξ
  map_add' v w := by
    have hext : extZero N (v + w) = fun η => extZero N v η + extZero N w η := by
      funext η; simp only [extZero]; split_ifs <;> simp
    funext ξ
    simp only [Pi.add_apply, hext, rhsIA_add]
    split_ifs with hn
    · ring
    · rfl
  map_smul' c v := by
    have hext : extZero N (c • v) = fun η => c * extZero N v η := by
      funext η; simp only [extZero]; split_ifs <;> simp
    funext ξ
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, hext, rhsIA_smul]
    split_ifs with hn
    · ring
    · rfl

theorem blockOpIA_injective (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (N : ℕ) :
    Function.Injective (blockOpIA (KA := KA) (KB := KB) θA θB ρ N) := by
  rw [injective_iff_map_eq_zero]
  intro v hv
  have hv' : ∀ (η : Config KA KB) (hη : η.nA + η.nB = N),
      (if 2 ≤ η.nA + η.nB
        then diag θA θB ρ η * v ⟨η, hη⟩ - rhsIA θA θB ρ (extZero N v) η
        else v ⟨η, hη⟩) = 0 := by
    intro η hη
    exact congrFun hv ⟨η, hη⟩
  have hz : ∀ η : Config KA KB, η.nA + η.nB ≠ N → extZero N v η = 0 := by
    intro η hη; simp [extZero, hη]
  have hon : ∀ (η : Config KA KB) (h : η.nA + η.nB = N), extZero N v η = v ⟨η, h⟩ := by
    intro η h; simp [extZero, h]
  have hbd : ∀ ξ : Config KA KB, ξ.nA + ξ.nB ≤ 1 → extZero N v ξ = 0 := by
    intro ξ hn
    by_cases hl : ξ.nA + ξ.nB = N
    · have h3 := hv' ξ hl
      rw [ite_eq_right (show ¬ (2 ≤ ξ.nA + ξ.nB) by omega)] at h3
      rw [hon ξ hl]; exact h3
    · exact hz ξ hl
  have hrec : ∀ ξ : Config KA KB, 2 ≤ ξ.nA + ξ.nB → ξ.nA + ξ.nB ≤ N →
      diag θA θB ρ ξ * extZero N v ξ = rhsIA θA θB ρ (extZero N v) ξ := by
    intro ξ hn hl
    by_cases hlev : ξ.nA + ξ.nB = N
    · have h2 := hv' ξ hlev
      rw [ite_eq_left hn] at h2
      rw [hon ξ hlev]
      linarith [h2]
    · have hb : ∀ η : Config KA KB, η.nA ≤ ξ.nA → η.nB ≤ ξ.nB → extZero N v η = 0 :=
        fun η h1 h2 => hz η (by omega)
      rw [hz ξ (by omega), mul_zero,
        rhsIA_congr θA θB ρ (q₂ := fun _ => (0 : F)) ξ hb, rhsIA_zero]
  have key := homogeneousIA_eq_zero_le hθA hθB hρ hbd hrec
  funext ξ
  have := key ξ (le_of_eq ξ.2)
  rw [hon ξ ξ.2] at this
  simpa using this

theorem exists_glueIA (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (N : ℕ)
    (g : Config KA KB → F) :
    ∃ u : Config KA KB → F,
      (∀ η : Config KA KB, η.nA + η.nB ≠ N → u η = g η) ∧
      (∀ ξ : Config KA KB, ξ.nA + ξ.nB = N → ξ.nA + ξ.nB ≤ 1 → u ξ = 1) ∧
      (∀ ξ : Config KA KB, ξ.nA + ξ.nB = N → 2 ≤ ξ.nA + ξ.nB →
        diag θA θB ρ ξ * u ξ = rhsIA θA θB ρ u ξ) := by
  obtain ⟨v, hv⟩ := (LinearMap.injective_iff_surjective.mp
      (blockOpIA_injective (KA := KA) (KB := KB) hθA hθB hρ N))
    (fun ξ => if 2 ≤ (ξ : Config KA KB).nA + (ξ : Config KA KB).nB
      then rhsIA θA θB ρ (offLevel N g) (ξ : Config KA KB)
      else 1)
  have hv' : ∀ (η : Config KA KB) (hη : η.nA + η.nB = N),
      (if 2 ≤ η.nA + η.nB
        then diag θA θB ρ η * v ⟨η, hη⟩ - rhsIA θA θB ρ (extZero N v) η
        else v ⟨η, hη⟩)
      = (if 2 ≤ η.nA + η.nB then rhsIA θA θB ρ (offLevel N g) η else 1) := by
    intro η hη
    exact congrFun hv ⟨η, hη⟩
  refine ⟨glue N g v, fun η hη => by simp [glue, hη], ?_, ?_⟩
  · intro ξ hlev hn
    have h2 := hv' ξ hlev
    rw [ite_eq_right (show ¬ (2 ≤ ξ.nA + ξ.nB) by omega),
      ite_eq_right (show ¬ (2 ≤ ξ.nA + ξ.nB) by omega)] at h2
    simpa [glue, hlev] using h2
  · intro ξ hlev hn
    have h2 := hv' ξ hlev
    rw [ite_eq_left hn, ite_eq_left hn] at h2
    have hu : glue N g v ξ = v ⟨ξ, hlev⟩ := by simp [glue, hlev]
    rw [hu, glue_eq_add, rhsIA_add]
    linarith [h2]

theorem exists_solvesUpToIA (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (N : ℕ) :
    ∃ q : Config KA KB → F, SolvesUpToIA θA θB ρ N q := by
  induction N with
  | zero =>
    refine ⟨fun _ => (1 : F), rfl, fun _ => rfl, fun _ => rfl, ?_⟩
    intro ξ hn hl
    omega
  | succ N ih =>
    obtain ⟨g, hg⟩ := ih
    obtain ⟨u, hoff, hbdry, hrec⟩ := exists_glueIA hθA hθB hρ (N + 1) g
    have hlow : ∀ η : Config KA KB, η.nA + η.nB ≤ N → u η = g η :=
      fun η hη => hoff η (by omega)
    have hb : ∀ ξ : Config KA KB, ξ.nA + ξ.nB ≤ 1 → u ξ = 1 := by
      intro ξ hn
      by_cases hlev : ξ.nA + ξ.nB = N + 1
      · exact hbdry ξ hlev hn
      · rw [hoff ξ hlev]
        rcases level_le_one_cases ξ hn with rfl | ⟨i, rfl⟩ | ⟨j, rfl⟩
        · exact hg.empty
        · exact hg.bdryA i
        · exact hg.bdryB j
    refine ⟨u, ?_, ?_, ?_, ?_⟩
    · exact hb 0 (by simp)
    · exact fun i => hb _ (by simp [Config.eA, Config.nA, Config.nB, Config.sumA, Config.sumB,
        Config.t, sum_incf])
    · exact fun j => hb _ (by simp [Config.eB, Config.nA, Config.nB, Config.sumA, Config.sumB,
        Config.t, sum_incf])
    · intro ξ hn hl
      by_cases hlev : ξ.nA + ξ.nB = N + 1
      · exact hrec ξ hlev hn
      · have hle : ξ.nA + ξ.nB ≤ N := by omega
        have hcongr : rhsIA θA θB ρ u ξ = rhsIA θA θB ρ g ξ :=
          rhsIA_congr θA θB ρ ξ fun η h1 h2 => hlow η (by omega)
        rw [hlow ξ hle, hcongr]
        exact hg.recursion ξ hn hle

noncomputable def approxIA (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (N : ℕ) :
    Config KA KB → F :=
  Classical.choose (exists_solvesUpToIA (KA := KA) (KB := KB) hθA hθB hρ N)

theorem approxIA_spec (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (N : ℕ) :
    SolvesUpToIA θA θB ρ N (approxIA (KA := KA) (KB := KB) hθA hθB hρ N) :=
  Classical.choose_spec (exists_solvesUpToIA (KA := KA) (KB := KB) hθA hθB hρ N)

theorem approxIA_coherent (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) {M N : ℕ} (hMN : M ≤ N)
    (ξ : Config KA KB) (hξ : ξ.nA + ξ.nB ≤ M) :
    approxIA (KA := KA) (KB := KB) hθA hθB hρ M ξ
      = approxIA (KA := KA) (KB := KB) hθA hθB hρ N ξ :=
  SolvesUpToIA.eq_of_le hθA hθB hρ (approxIA_spec hθA hθB hρ M)
    ((approxIA_spec hθA hθB hρ N).mono hMN) ξ hξ

theorem exists_isSolutionIA (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) :
    ∃ q : Config KA KB → F, IsSolutionIA θA θB ρ q := by
  refine ⟨fun ξ => approxIA (KA := KA) (KB := KB) hθA hθB hρ (ξ.nA + ξ.nB) ξ, ?_, ?_, ?_, ?_⟩
  · exact (approxIA_spec hθA hθB hρ _).empty
  · exact fun i => (approxIA_spec hθA hθB hρ _).bdryA i
  · exact fun j => (approxIA_spec hθA hθB hρ _).bdryB j
  · intro ξ hn
    have hcongr : rhsIA θA θB ρ
        (fun η => approxIA (KA := KA) (KB := KB) hθA hθB hρ (η.nA + η.nB) η) ξ
        = rhsIA θA θB ρ (approxIA (KA := KA) (KB := KB) hθA hθB hρ (ξ.nA + ξ.nB)) ξ :=
      rhsIA_congr θA θB ρ ξ fun η h1 h2 =>
        approxIA_coherent hθA hθB hρ (by omega) η le_rfl
    rw [hcongr]
    exact (approxIA_spec hθA hθB hρ _).recursion ξ hn le_rfl

noncomputable def PIA (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) : Config KA KB → F :=
  Classical.choose (exists_isSolutionIA (KA := KA) (KB := KB) hθA hθB hρ)

theorem PIA_isSolutionIA (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) :
    IsSolutionIA θA θB ρ (PIA (KA := KA) (KB := KB) hθA hθB hρ) :=
  Classical.choose_spec (exists_isSolutionIA (KA := KA) (KB := KB) hθA hθB hρ)

theorem PIA_unique (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) {q' : Config KA KB → F}
    (h : IsSolutionIA θA θB ρ q') : q' = PIA (KA := KA) (KB := KB) hθA hθB hρ :=
  IsSolutionIA.unique hθA hθB hρ h (PIA_isSolutionIA hθA hθB hρ)

theorem existsUnique_isSolutionIA (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) :
    ∃! q : Config KA KB → F, IsSolutionIA θA θB ρ q :=
  ⟨PIA hθA hθB hρ, PIA_isSolutionIA hθA hθB hρ, fun _ h => PIA_unique hθA hθB hρ h⟩

end Rhone.Probability.InfiniteAlleles
