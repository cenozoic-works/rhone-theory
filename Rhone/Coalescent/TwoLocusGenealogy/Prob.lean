/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.TwoLocusGenealogy.Limit

/-! # The sampling probability of the ancestral recombination graph -/

@[expose] public section

namespace Rhone.Coalescent.TwoLocusGenealogy

open Finset LinearAlgebra.Recursion

variable {n KA KB : ℕ} {σA : Fin n → Fin KA} {σB : Fin n → Fin KB}
variable {θA θB ρ : ℝ} {πA : Fin KA → ℝ} {πB : Fin KB → ℝ}

noncomputable def hitProb (σA : Fin n → Fin KA) (σB : Fin n → Fin KB) (θA θB ρ : ℝ)
    (πA : Fin KA → ℝ) (πB : Fin KB → ℝ) (L : Finset (Lin n)) : ℝ :=
  ⨆ N, hitN σA σB θA θB ρ πA πB N L

theorem hitProb_eq_qProb {L : Finset (Lin n)} (hw : WF L) (hcl : Clean σA σB L) :
    hitProb σA σB θA θB ρ πA πB L = qProb θA θB ρ πA πB (cfg σA σB L) := by
  have h : (fun N => hitN σA σB θA θB ρ πA πB N L)
      = fun N => fitN θA θB ρ πA πB N (cfg σA σB L) :=
    funext fun N => hitN_eq_fitN N hw hcl
  simp only [hitProb, qProb, h]

theorem hitProb_eq_q (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (hπA : ∀ i, 0 ≤ πA i)
    (hsA : ∑ i, πA i = 1) (hπB : ∀ j, 0 ≤ πB j) (hsB : ∑ j, πB j = 1) {L : Finset (Lin n)}
    (hw : WF L) (hcl : Clean σA σB L) :
    hitProb σA σB θA θB ρ πA πB L
      = LinearAlgebra.Recursion.q (πA := πA) (πB := πB) hθA hθB hρ (cfg σA σB L) := by
  rw [hitProb_eq_qProb hw hcl, qProb_eq_q hθA hθB hρ hπA hsA hπB hsB]

def fullState (n : ℕ) : Finset (Lin n) := Finset.univ.image fun k => ({k}, {k})

theorem singleton_pair_injective :
    Function.Injective fun k : Fin n => ((({k} : Finset (Fin n)), ({k} : Finset (Fin n))) :
      Lin n) := by
  intro k l h
  have h1 : ({k} : Finset (Fin n)) = {l} := congrArg Prod.fst h
  simpa using h1

theorem mem_fullState {p : Lin n} :
    p ∈ fullState n ↔ ∃ k : Fin n, p = ({k}, {k}) := by
  simp [fullState, eq_comm]

theorem fullState_wf : WF (fullState n) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨k, rfl⟩ := mem_fullState.1 hp
    exact Or.inl ⟨k, Finset.mem_singleton_self k⟩
  · intro p hp q hq hne
    obtain ⟨k, rfl⟩ := mem_fullState.1 hp
    obtain ⟨l, rfl⟩ := mem_fullState.1 hq
    have hkl : k ≠ l := fun h => hne (by rw [h])
    simpa using hkl
  · intro p hp q hq hne
    obtain ⟨k, rfl⟩ := mem_fullState.1 hp
    obtain ⟨l, rfl⟩ := mem_fullState.1 hq
    have hkl : k ≠ l := fun h => hne (by rw [h])
    simpa using hkl

theorem fullState_clean : Clean σA σB (fullState n) := by
  intro p hp
  obtain ⟨k, rfl⟩ := mem_fullState.1 hp
  refine ⟨fun a ha b hb => ?_, fun a ha b hb => ?_⟩
  · rw [Finset.mem_singleton.1 ha, Finset.mem_singleton.1 hb]
  · rw [Finset.mem_singleton.1 ha, Finset.mem_singleton.1 hb]

def cSample (σA : Fin n → Fin KA) (σB : Fin n → Fin KB) : Config KA KB :=
  ⟨fun _ => 0, fun _ => 0, fun i j => (Finset.univ.filter fun k => σA k = i ∧ σB k = j).card⟩

theorem isC_singleton {i : Fin KA} {j : Fin KB} {k : Fin n} :
    IsC σA σB i j (({k} : Finset (Fin n)), ({k} : Finset (Fin n)))
      ↔ (σA k = i ∧ σB k = j) := by
  constructor
  · rintro ⟨_, _, h1, h2⟩
    exact ⟨h1 k (Finset.mem_singleton_self k), h2 k (Finset.mem_singleton_self k)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨k, Finset.mem_singleton_self k⟩, ⟨k, Finset.mem_singleton_self k⟩,
      fun a ha => by rw [Finset.mem_singleton.1 ha]; exact h1,
      fun a ha => by rw [Finset.mem_singleton.1 ha]; exact h2⟩

theorem cfg_fullState : cfg σA σB (fullState n) = cSample σA σB := by
  have hinj : ∀ a ∈ (Finset.univ : Finset (Fin n)), ∀ b ∈ (Finset.univ : Finset (Fin n)),
      ((({a} : Finset (Fin n)), ({a} : Finset (Fin n))) : Lin n)
        = ((({b} : Finset (Fin n)), ({b} : Finset (Fin n))) : Lin n) → a = b :=
    fun _ _ _ _ h => singleton_pair_injective h
  refine Config.ext ?_ ?_ ?_
  · funext i
    change cfgA σA (fullState n) i = 0
    rw [cfgA, Finset.sum_apply, fullState, Finset.sum_image hinj]
    refine Finset.sum_eq_zero fun k _ => ?_
    have h := uA_eq_zero_of_carB (σA := σA)
      (p := (({k} : Finset (Fin n)), ({k} : Finset (Fin n)))) ⟨k, Finset.mem_singleton_self k⟩
    exact congrFun h i
  · funext j
    change cfgB σB (fullState n) j = 0
    rw [cfgB, Finset.sum_apply, fullState, Finset.sum_image hinj]
    refine Finset.sum_eq_zero fun k _ => ?_
    have h := uB_eq_zero_of_carA (σB := σB)
      (p := (({k} : Finset (Fin n)), ({k} : Finset (Fin n)))) ⟨k, Finset.mem_singleton_self k⟩
    exact congrFun h j
  · funext i j
    change cfgC σA σB (fullState n) i j
      = (Finset.univ.filter fun k => σA k = i ∧ σB k = j).card
    rw [cfgC, Finset.sum_apply, Finset.sum_apply, fullState, Finset.sum_image hinj,
      Finset.card_filter]
    exact Finset.sum_congr rfl fun k _ => by simp only [uC, isC_singleton]

theorem hitProb_fullState (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (hπA : ∀ i, 0 ≤ πA i)
    (hsA : ∑ i, πA i = 1) (hπB : ∀ j, 0 ≤ πB j) (hsB : ∑ j, πB j = 1) :
    hitProb σA σB θA θB ρ πA πB (fullState n)
      = LinearAlgebra.Recursion.q (πA := πA) (πB := πB) hθA hθB hρ (cSample σA σB) := by
  rw [hitProb_eq_q hθA hθB hρ hπA hsA hπB hsB fullState_wf fullState_clean, cfg_fullState]

def relabel (e : Equiv.Perm (Fin n)) (L : Finset (Lin n)) : Finset (Lin n) :=
  L.image fun p => (p.1.image e, p.2.image e)

theorem relabelLin_injective (e : Equiv.Perm (Fin n)) :
    Function.Injective fun p : Lin n => ((p.1.image e, p.2.image e) : Lin n) := by
  intro p q h
  have h1 : p.1.image e = q.1.image e := congrArg Prod.fst h
  have h2 : p.2.image e = q.2.image e := congrArg Prod.snd h
  refine Prod.ext ?_ ?_
  · exact Finset.image_injective e.injective h1
  · exact Finset.image_injective e.injective h2

theorem mem_relabel {e : Equiv.Perm (Fin n)} {L : Finset (Lin n)} {p : Lin n} :
    p ∈ relabel e L ↔ ∃ r ∈ L, (r.1.image e, r.2.image e) = p := by
  simp [relabel]

theorem isA_relabel (e : Equiv.Perm (Fin n)) (i : Fin KA) (p : Lin n) :
    IsA σA i ((p.1.image e, p.2.image e) : Lin n) ↔ IsA (σA ∘ e) i p := by
  simp [IsA, Finset.image_nonempty, Finset.image_eq_empty]

theorem isB_relabel (e : Equiv.Perm (Fin n)) (j : Fin KB) (p : Lin n) :
    IsB σB j ((p.1.image e, p.2.image e) : Lin n) ↔ IsB (σB ∘ e) j p := by
  simp [IsB, Finset.image_nonempty, Finset.image_eq_empty]

theorem isC_relabel (e : Equiv.Perm (Fin n)) (i : Fin KA) (j : Fin KB) (p : Lin n) :
    IsC σA σB i j ((p.1.image e, p.2.image e) : Lin n) ↔ IsC (σA ∘ e) (σB ∘ e) i j p := by
  simp [IsC, Finset.image_nonempty]

theorem monoA_relabel (e : Equiv.Perm (Fin n)) (p : Lin n) :
    MonoA σA ((p.1.image e, p.2.image e) : Lin n) ↔ MonoA (σA ∘ e) p := by
  simp [MonoA]

theorem monoB_relabel (e : Equiv.Perm (Fin n)) (p : Lin n) :
    MonoB σB ((p.1.image e, p.2.image e) : Lin n) ↔ MonoB (σB ∘ e) p := by
  simp [MonoB]

theorem wf_relabel (e : Equiv.Perm (Fin n)) {L : Finset (Lin n)} (h : WF L) :
    WF (relabel e L) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨r, hr, rfl⟩ := mem_relabel.1 hp
    rcases h.carries r hr with hc | hc
    · exact Or.inl (by simpa using hc)
    · exact Or.inr (by simpa using hc)
  · intro p hp q hq hne
    obtain ⟨r, hr, rfl⟩ := mem_relabel.1 hp
    obtain ⟨s, hs, rfl⟩ := mem_relabel.1 hq
    have hrs : r ≠ s := fun hc => hne (by rw [hc])
    have := h.disjA r hr s hs hrs
    simpa [Finset.disjoint_left, Finset.mem_image] using
      fun x hx hx' => (Finset.disjoint_left.1 this) hx hx'
  · intro p hp q hq hne
    obtain ⟨r, hr, rfl⟩ := mem_relabel.1 hp
    obtain ⟨s, hs, rfl⟩ := mem_relabel.1 hq
    have hrs : r ≠ s := fun hc => hne (by rw [hc])
    have := h.disjB r hr s hs hrs
    simpa [Finset.disjoint_left, Finset.mem_image] using
      fun x hx hx' => (Finset.disjoint_left.1 this) hx hx'

theorem clean_relabel (e : Equiv.Perm (Fin n)) {L : Finset (Lin n)}
    (h : Clean (σA ∘ e) (σB ∘ e) L) : Clean σA σB (relabel e L) := by
  intro p hp
  obtain ⟨r, hr, rfl⟩ := mem_relabel.1 hp
  exact ⟨(monoA_relabel e r).2 (h.monoA hr), (monoB_relabel e r).2 (h.monoB hr)⟩

theorem cfg_relabel (e : Equiv.Perm (Fin n)) (L : Finset (Lin n)) :
    cfg σA σB (relabel e L) = cfg (σA ∘ e) (σB ∘ e) L := by
  have hinj : ∀ a ∈ L, ∀ b ∈ L,
      ((a.1.image e, a.2.image e) : Lin n) = ((b.1.image e, b.2.image e) : Lin n) → a = b :=
    fun _ _ _ _ hh => relabelLin_injective e hh
  refine Config.ext ?_ ?_ ?_
  · funext i
    change cfgA σA (relabel e L) i = cfgA (σA ∘ e) L i
    rw [cfgA, Finset.sum_apply, relabel, Finset.sum_image hinj, cfgA, Finset.sum_apply]
    exact Finset.sum_congr rfl fun r _ => by simp only [uA, isA_relabel]
  · funext j
    change cfgB σB (relabel e L) j = cfgB (σB ∘ e) L j
    rw [cfgB, Finset.sum_apply, relabel, Finset.sum_image hinj, cfgB, Finset.sum_apply]
    exact Finset.sum_congr rfl fun r _ => by simp only [uB, isB_relabel]
  · funext i j
    change cfgC σA σB (relabel e L) i j = cfgC (σA ∘ e) (σB ∘ e) L i j
    rw [cfgC, Finset.sum_apply, Finset.sum_apply, relabel, Finset.sum_image hinj, cfgC,
      Finset.sum_apply, Finset.sum_apply]
    exact Finset.sum_congr rfl fun r _ => by simp only [uC, isC_relabel]

theorem hitProb_relabel (hθA : 0 < θA) (hθB : 0 < θB) (hρ : 0 ≤ ρ) (hπA : ∀ i, 0 ≤ πA i)
    (hsA : ∑ i, πA i = 1) (hπB : ∀ j, 0 ≤ πB j) (hsB : ∑ j, πB j = 1)
    (e : Equiv.Perm (Fin n)) {L : Finset (Lin n)} (hw : WF L)
    (hcl : Clean (σA ∘ e) (σB ∘ e) L) :
    hitProb σA σB θA θB ρ πA πB (relabel e L)
      = hitProb (σA ∘ e) (σB ∘ e) θA θB ρ πA πB L := by
  rw [hitProb_eq_q hθA hθB hρ hπA hsA hπB hsB (wf_relabel e hw) (clean_relabel e hcl),
    hitProb_eq_q hθA hθB hρ hπA hsA hπB hsB hw hcl, cfg_relabel]

end Rhone.Coalescent.TwoLocusGenealogy
