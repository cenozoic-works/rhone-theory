/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.TwoLocusGenealogy.OneStepLaw

/-! # The coalescence part of the first-step analysis -/

@[expose] public section

namespace Rhone.Coalescent.TwoLocusGenealogy

open Finset LinearAlgebra.Recursion

variable {n KA KB : ℕ} {σA : Fin n → Fin KA} {σB : Fin n → Fin KB}
variable {F : Type*} [Field F]

variable (σA σB)

def bil (f : Config KA KB → F) (ξ : Config KA KB) (p q : Lin n) : F :=
  (∑ i, ((uA σA p i : ℕ) : F) * ((uA σA q i : ℕ) : F) * f (ξ.dropA i))
    + (∑ i, ∑ j, ((uA σA p i : ℕ) : F) * ((uC σA σB q i j : ℕ) : F) * f (ξ.dropA i))
    + (∑ i, ∑ j, ((uC σA σB p i j : ℕ) : F) * ((uA σA q i : ℕ) : F) * f (ξ.dropA i))
    + (∑ j, ((uB σB p j : ℕ) : F) * ((uB σB q j : ℕ) : F) * f (ξ.dropB j))
    + (∑ i, ∑ j, ((uB σB p j : ℕ) : F) * ((uC σA σB q i j : ℕ) : F) * f (ξ.dropB j))
    + (∑ i, ∑ j, ((uC σA σB p i j : ℕ) : F) * ((uB σB q j : ℕ) : F) * f (ξ.dropB j))
    + (∑ i, ∑ j, ((uC σA σB p i j : ℕ) : F) * ((uC σA σB q i j : ℕ) : F) * f (ξ.dropC i j))
    + (∑ i, ∑ j, ((uA σA p i : ℕ) : F) * ((uB σB q j : ℕ) : F) * f (ξ.mergeAB i j))
    + (∑ i, ∑ j, ((uB σB p j : ℕ) : F) * ((uA σA q i : ℕ) : F) * f (ξ.mergeAB i j))

variable {σA σB}

theorem mem_erase_swap {L : Finset (Lin n)} {p q : Lin n} (hp : p ∈ L) (hq : q ∈ L.erase p) :
    p ∈ L.erase q :=
  Finset.mem_erase.2 ⟨fun h => (Finset.ne_of_mem_erase hq) h.symm, hp⟩

section CoalTerm

variable {g : Finset (Lin n) → F} {f : Config KA KB → F}
variable (hgf : ∀ M, WF M → Clean σA σB M → g M = f (cfg σA σB M))
variable (hg0 : ∀ M, ¬ Clean σA σB M → g M = 0)

include hgf hg0

theorem coal_term {L : Finset (Lin n)} (hw : WF L) (hcl : Clean σA σB L) {p q : Lin n}
    (hp : p ∈ L) (hq : q ∈ L.erase p) :
    g (coalL L p q) = bil σA σB f (cfg σA σB L) p q := by
  have hqL : q ∈ L := Finset.mem_of_mem_erase hq
  have hpq : p ∈ L.erase q := mem_erase_swap hp hq
  rcases clean_class hw hcl hp with ⟨i₀, hip⟩ | ⟨j₀, hjp⟩ | ⟨i₀, j₀, hcp⟩ <;>
    rcases clean_class hw hcl hqL with ⟨i₁, hiq⟩ | ⟨j₁, hjq⟩ | ⟨i₁, j₁, hcq⟩
  · by_cases hii : i₀ = i₁
    · subst hii
      obtain ⟨hcln, hcfg⟩ := coal_AA hw hcl hp hq hip hiq
      rw [hgf _ (hw.coal hp hqL) hcln, hcfg, bil, uA_eq hip, uA_eq hiq,
        uB_eq_zero_of_carA hip.1, uB_eq_zero_of_carA hiq.1,
        uC_eq_zero_of_emptyB hip.2.1, uC_eq_zero_of_emptyB hiq.2.1]
      simp [eV]
    · obtain ⟨k, hk⟩ := hip.1
      obtain ⟨l, hl⟩ := hiq.1
      rw [hg0 _ (notClean_coal_A (σB := σB) hk hl
        (by rw [hip.2.2 k hk, hiq.2.2 l hl]; exact hii)), bil, uA_eq hip, uA_eq hiq,
        uB_eq_zero_of_carA hip.1, uB_eq_zero_of_carA hiq.1,
        uC_eq_zero_of_emptyB hip.2.1, uC_eq_zero_of_emptyB hiq.2.1]
      simp [eV, Ne.symm hii]
  · obtain ⟨hcln, hcfg⟩ := coal_AB hw hcl hp hq hip hjq
    rw [hgf _ (hw.coal hp hqL) hcln, hcfg, bil, uA_eq hip, uA_eq_zero_of_emptyA hjq.1,
      uB_eq_zero_of_carA hip.1, uB_eq hjq, uC_eq_zero_of_emptyB hip.2.1,
      uC_eq_zero_of_emptyA hjq.1]
    simp [eV]
  · by_cases hii : i₀ = i₁
    · subst hii
      obtain ⟨hcln, hcfg⟩ := coal_AC hw hcl hp hq hip hcq
      rw [hgf _ (hw.coal hp hqL) hcln, hcfg, bil, uA_eq hip, uA_eq_zero_of_carB hcq.2.1,
        uB_eq_zero_of_carA hip.1, uB_eq_zero_of_carA hcq.1,
        uC_eq_zero_of_emptyB hip.2.1, uC_eq hcq]
      simp [eV, eM_apply]
    · obtain ⟨k, hk⟩ := hip.1
      obtain ⟨l, hl⟩ := hcq.1
      rw [hg0 _ (notClean_coal_A (σB := σB) hk hl
        (by rw [hip.2.2 k hk, hcq.2.2.1 l hl]; exact hii)), bil, uA_eq hip,
        uA_eq_zero_of_carB hcq.2.1, uB_eq_zero_of_carA hip.1, uB_eq_zero_of_carA hcq.1,
        uC_eq_zero_of_emptyB hip.2.1, uC_eq hcq]
      simp [eV, eM_apply, Ne.symm hii]
  · obtain ⟨hcln, hcfg⟩ := coal_AB hw hcl hqL hpq hiq hjp
    rw [coalL_comm, hgf _ (hw.coal hqL hp) hcln, hcfg, bil, uA_eq_zero_of_emptyA hjp.1,
      uA_eq hiq, uB_eq hjp, uB_eq_zero_of_carA hiq.1, uC_eq_zero_of_emptyA hjp.1,
      uC_eq_zero_of_emptyB hiq.2.1]
    simp [eV]
  · by_cases hjj : j₀ = j₁
    · subst hjj
      obtain ⟨hcln, hcfg⟩ := coal_BB hw hcl hp hq hjp hjq
      rw [hgf _ (hw.coal hp hqL) hcln, hcfg, bil, uA_eq_zero_of_emptyA hjp.1,
        uA_eq_zero_of_emptyA hjq.1, uB_eq hjp, uB_eq hjq,
        uC_eq_zero_of_emptyA hjp.1, uC_eq_zero_of_emptyA hjq.1]
      simp [eV]
    · obtain ⟨k, hk⟩ := hjp.2.1
      obtain ⟨l, hl⟩ := hjq.2.1
      rw [hg0 _ (notClean_coal_B (σA := σA) hk hl
        (by rw [hjp.2.2 k hk, hjq.2.2 l hl]; exact hjj)), bil, uA_eq_zero_of_emptyA hjp.1,
        uA_eq_zero_of_emptyA hjq.1, uB_eq hjp, uB_eq hjq,
        uC_eq_zero_of_emptyA hjp.1, uC_eq_zero_of_emptyA hjq.1]
      simp [eV, Ne.symm hjj]
  · by_cases hjj : j₀ = j₁
    · subst hjj
      obtain ⟨hcln, hcfg⟩ := coal_BC hw hcl hp hq hjp hcq
      rw [hgf _ (hw.coal hp hqL) hcln, hcfg, bil, uA_eq_zero_of_emptyA hjp.1,
        uA_eq_zero_of_carB hcq.2.1, uB_eq hjp, uB_eq_zero_of_carA hcq.1,
        uC_eq_zero_of_emptyA hjp.1, uC_eq hcq]
      simp [eV, eM_apply]
    · obtain ⟨k, hk⟩ := hjp.2.1
      obtain ⟨l, hl⟩ := hcq.2.1
      rw [hg0 _ (notClean_coal_B (σA := σA) hk hl
        (by rw [hjp.2.2 k hk, hcq.2.2.2 l hl]; exact hjj)), bil, uA_eq_zero_of_emptyA hjp.1,
        uA_eq_zero_of_carB hcq.2.1, uB_eq hjp, uB_eq_zero_of_carA hcq.1,
        uC_eq_zero_of_emptyA hjp.1, uC_eq hcq]
      simp [eV, eM_apply, Ne.symm hjj]
  · by_cases hii : i₁ = i₀
    · subst hii
      obtain ⟨hcln, hcfg⟩ := coal_AC hw hcl hqL hpq hiq hcp
      rw [coalL_comm, hgf _ (hw.coal hqL hp) hcln, hcfg, bil, uA_eq_zero_of_carB hcp.2.1,
        uA_eq hiq, uB_eq_zero_of_carA hcp.1, uB_eq_zero_of_carA hiq.1, uC_eq hcp,
        uC_eq_zero_of_emptyB hiq.2.1]
      simp [eV, eM_apply]
    · obtain ⟨k, hk⟩ := hcp.1
      obtain ⟨l, hl⟩ := hiq.1
      rw [hg0 _ (notClean_coal_A (σB := σB) hk hl
        (by rw [hcp.2.2.1 k hk, hiq.2.2 l hl]; exact fun hc => hii hc.symm)), bil,
        uA_eq_zero_of_carB hcp.2.1, uA_eq hiq, uB_eq_zero_of_carA hcp.1,
        uB_eq_zero_of_carA hiq.1, uC_eq hcp, uC_eq_zero_of_emptyB hiq.2.1]
      simp [eV, eM_apply, hii]
  · by_cases hjj : j₁ = j₀
    · subst hjj
      obtain ⟨hcln, hcfg⟩ := coal_BC hw hcl hqL hpq hjq hcp
      rw [coalL_comm, hgf _ (hw.coal hqL hp) hcln, hcfg, bil, uA_eq_zero_of_carB hcp.2.1,
        uA_eq_zero_of_emptyA hjq.1, uB_eq_zero_of_carA hcp.1, uB_eq hjq, uC_eq hcp,
        uC_eq_zero_of_emptyA hjq.1]
      simp [eV, eM_apply]
    · obtain ⟨k, hk⟩ := hcp.2.1
      obtain ⟨l, hl⟩ := hjq.2.1
      rw [hg0 _ (notClean_coal_B (σA := σA) hk hl
        (by rw [hcp.2.2.2 k hk, hjq.2.2 l hl]; exact fun hc => hjj hc.symm)), bil,
        uA_eq_zero_of_carB hcp.2.1, uA_eq_zero_of_emptyA hjq.1, uB_eq_zero_of_carA hcp.1,
        uB_eq hjq, uC_eq hcp, uC_eq_zero_of_emptyA hjq.1]
      simp [eV, eM_apply, hjj]
  · by_cases hij : i₀ = i₁ ∧ j₀ = j₁
    · obtain ⟨rfl, rfl⟩ := hij
      obtain ⟨hcln, hcfg⟩ := coal_CC hw hcl hp hq hcp hcq
      rw [hgf _ (hw.coal hp hqL) hcln, hcfg, bil, uA_eq_zero_of_carB hcp.2.1,
        uA_eq_zero_of_carB hcq.2.1, uB_eq_zero_of_carA hcp.1, uB_eq_zero_of_carA hcq.1,
        uC_eq hcp, uC_eq hcq]
      simp [eM_apply]
    · have hne : i₀ ≠ i₁ ∨ j₀ ≠ j₁ := by
        by_cases h1 : i₀ = i₁
        · exact Or.inr fun h2 => hij ⟨h1, h2⟩
        · exact Or.inl h1
      have h0 : ¬ Clean σA σB (coalL L p q) := by
        rcases hne with h | h
        · obtain ⟨k, hk⟩ := hcp.1
          obtain ⟨l, hl⟩ := hcq.1
          exact notClean_coal_A (σB := σB) hk hl
            (by rw [hcp.2.2.1 k hk, hcq.2.2.1 l hl]; exact h)
        · obtain ⟨k, hk⟩ := hcp.2.1
          obtain ⟨l, hl⟩ := hcq.2.1
          exact notClean_coal_B (σA := σA) hk hl
            (by rw [hcp.2.2.2 k hk, hcq.2.2.2 l hl]; exact h)
      rw [hg0 _ h0, bil, uA_eq_zero_of_carB hcp.2.1, uA_eq_zero_of_carB hcq.2.1,
        uB_eq_zero_of_carA hcp.1, uB_eq_zero_of_carA hcq.1, uC_eq hcp, uC_eq hcq]
      rcases hne with h | h
      · simp [eM_apply, Ne.symm h]
      · simp [eM_apply, Ne.symm h]

end CoalTerm

end Rhone.Coalescent.TwoLocusGenealogy
