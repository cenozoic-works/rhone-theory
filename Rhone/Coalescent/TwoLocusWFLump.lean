/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.TwoLocusWFActive
public import Rhone.LinearAlgebra.Recursion.Config

/-!
# Relabelling invariance and lumping of the two-locus Wright-Fisher dual

Source: griffiths1991_two_locus_graph, pp. 106–107; ewens2004, sec. 3.1. -/

@[expose] public section
noncomputable section
namespace Rhone.Coalescent.WFTwoLocusDual
open Finset MarkovChain MarkovChain.WFAllocationLD

def relabelChoice {M : ℕ} (τ : Equiv.Perm (Fin M)) (ch : Choice M) : Choice M :=
  (τ ch.1, τ ch.2.1, ch.2.2)

theorem parentA_relabelChoice {M : ℕ} (τ : Equiv.Perm (Fin M)) (ch : Choice M) :
    parentA (relabelChoice τ ch) = τ (parentA ch) := rfl

theorem parentB_relabelChoice {M : ℕ} (τ : Equiv.Perm (Fin M)) (ch : Choice M) :
    parentB (relabelChoice τ ch) = τ (parentB ch) := by
  unfold parentB relabelChoice
  split_ifs <;> rfl

theorem lineFactor_relabelChoice {M : ℕ} (c u : ℝ) (r : Req) (τ : Equiv.Perm (Fin M))
    (ch : Choice M) : lineFactor c u r (relabelChoice τ ch) = lineFactor c u r ch := rfl

def relabelAnc {M : ℕ} (σ : Equiv.Perm (Fin M)) (ω : Fin M → Choice M) : Fin M → Choice M :=
  fun t => relabelChoice σ.symm (ω (σ t))

def relabelAncEquiv {M : ℕ} (σ : Equiv.Perm (Fin M)) :
    (Fin M → Choice M) ≃ (Fin M → Choice M) where
  toFun := relabelAnc σ
  invFun := fun ω t => relabelChoice σ (ω (σ.symm t))
  left_inv ω := by
    funext t
    simp [relabelAnc, relabelChoice]
  right_inv ω := by
    funext t
    simp [relabelAnc, relabelChoice]

theorem inf_filter_perm {M : ℕ} (σ : Equiv.Perm (Fin M)) (p : Fin M → Prop) [DecidablePred p]
    (f : Fin M → Finset (Fin 2)) :
    (univ.filter fun t => p (σ t)).inf (fun t => f (σ t)) = (univ.filter p).inf f := by
  have hs : (univ.filter p) = (univ.filter fun t => p (σ t)).map σ.toEmbedding := by
    ext x
    simp
  rw [hs, Finset.inf_map]
  rfl

theorem ancStep_perm {M : ℕ} (σ : Equiv.Perm (Fin M)) (ζ : DualState M)
    (ω : Fin M → Choice M) :
    ancStep (fun s => ζ (σ s)) (relabelAnc σ ω) = fun s => ancStep ζ ω (σ s) := by
  funext s
  simp only [ancStep, relabelAnc, parentA_relabelChoice, parentB_relabelChoice,
    Equiv.symm_apply_eq]
  ext1
  · exact inf_filter_perm σ (fun t => parentA (ω t) = σ s) fun t => mutReq (ω t).2.2.1 (ζ t).1
  · exact inf_filter_perm σ (fun t => parentB (ω t) = σ s) fun t =>
      mutReq (ω t).2.2.2.1 (ζ t).2

theorem ancWeight_perm {M : ℕ} (c u : ℝ) (σ : Equiv.Perm (Fin M)) (ζ : DualState M)
    (ω : Fin M → Choice M) :
    ancWeight M c u (fun s => ζ (σ s)) (relabelAnc σ ω) = ancWeight M c u ζ ω := by
  unfold ancWeight relabelAnc
  simp only [lineFactor_relabelChoice]
  exact Equiv.prod_comp σ fun t => lineFactor c u (ζ t) (ω t)

def permState {M : ℕ} (σ : Equiv.Perm (Fin M)) : DualState M ≃ DualState M where
  toFun ζ := fun s => ζ (σ s)
  invFun ζ := fun s => ζ (σ.symm s)
  left_inv ζ := by funext s; simp
  right_inv ζ := by funext s; simp

theorem ancKernel_perm {M : ℕ} (c u : ℝ) (σ : Equiv.Perm (Fin M)) (ζ ζ' : DualState M) :
    ancKernel M c u (permState σ ζ) (permState σ ζ') = ancKernel M c u ζ ζ' := by
  unfold ancKernel
  rw [← (relabelAncEquiv σ).sum_comp]
  refine Finset.sum_congr rfl fun ω _ => ?_
  change (if ancStep (fun s => ζ (σ s)) (relabelAnc σ ω) = permState σ ζ' then
      ancWeight M c u (fun s => ζ (σ s)) (relabelAnc σ ω) else 0) = _
  rw [ancStep_perm, ancWeight_perm]
  have : permState σ (ancStep ζ ω) = permState σ ζ' ↔ ancStep ζ ω = ζ' :=
    (permState σ).injective.eq_iff
  change (if permState σ (ancStep ζ ω) = permState σ ζ' then _ else _) = _
  simp only [this]

theorem ancMatrix_pow_perm {M : ℕ} (c u : ℝ) (σ : Equiv.Perm (Fin M)) (t : ℕ)
    (ζ ζ' : DualState M) :
    (ancMatrix M c u ^ t) (permState σ ζ) (permState σ ζ') = (ancMatrix M c u ^ t) ζ ζ' := by
  induction t generalizing ζ' with
  | zero =>
    simp only [pow_zero, Matrix.one_apply]
    have : permState σ ζ = permState σ ζ' ↔ ζ = ζ' := (permState σ).injective.eq_iff
    simp only [this]
  | succ t ih =>
    simp only [pow_succ, Matrix.mul_apply]
    rw [← (permState σ).sum_comp]
    refine Finset.sum_congr rfl fun ζ'' _ => ?_
    rw [ih, ancMatrix, Matrix.of_apply, Matrix.of_apply, ancKernel_perm]

theorem permState_fullState {M : ℕ} (σ : Equiv.Perm (Fin M)) :
    permState σ (fullState M) = fullState M := rfl

theorem ancAbsorb_perm {M : ℕ} (c u : ℝ) (σ : Equiv.Perm (Fin M)) (ζ : DualState M) :
    ancAbsorb M c u (permState σ ζ) = ancAbsorb M c u ζ := by
  unfold ancAbsorb
  congr 1
  funext t
  conv_lhs => rw [← permState_fullState σ]
  exact ancMatrix_pow_perm c u σ t ζ (fullState M)

def cnt {M : ℕ} (ζ : DualState M) (r : Req) : ℕ := (univ.filter fun s => ζ s = r).card

theorem exists_perm_of_cnt_eq {M : ℕ} {ζ ξ : DualState M} (h : ∀ r, cnt ζ r = cnt ξ r) :
    ∃ σ : Equiv.Perm (Fin M), permState σ ζ = ξ := by
  classical
  have hc : ∀ r, Fintype.card {a // ξ a = r} = Fintype.card {b // ζ b = r} := by
    intro r
    rw [Fintype.card_subtype, Fintype.card_subtype]
    exact (h r).symm
  let e : ∀ r, {a // ξ a = r} ≃ {b // ζ b = r} := fun r => Fintype.equivOfCardEq (hc r)
  refine ⟨Equiv.ofFiberEquiv e, ?_⟩
  funext s
  exact Equiv.ofFiberEquiv_map e s

theorem ancAbsorb_eq_of_cnt_eq {M : ℕ} (c u : ℝ) {ζ ξ : DualState M}
    (h : ∀ r, cnt ζ r = cnt ξ r) : ancAbsorb M c u ζ = ancAbsorb M c u ξ := by
  obtain ⟨σ, rfl⟩ := exists_perm_of_cnt_eq h
  exact (ancAbsorb_perm c u σ ζ).symm

theorem sum_cnt {M : ℕ} (ζ : DualState M) : ∑ r, cnt ζ r = M := by
  unfold cnt
  rw [← Finset.card_eq_sum_card_fiberwise (fun s _ => Finset.mem_univ (ζ s)),
    Finset.card_univ, Fintype.card_fin]

theorem cnt_eq_of_cnt_ne_eq {M : ℕ} {ζ ξ : DualState M}
    (h : ∀ r, r ≠ (univ, univ) → cnt ζ r = cnt ξ r) : ∀ r, cnt ζ r = cnt ξ r := by
  intro r
  by_cases hr : r = (univ, univ)
  · subst hr
    have h1 := sum_cnt ζ
    have h2 := sum_cnt ξ
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (univ, univ))] at h1 h2
    have h3 : ∑ r ∈ univ.erase (univ, univ), cnt ζ r = ∑ r ∈ univ.erase (univ, univ), cnt ξ r :=
      Finset.sum_congr rfl fun r hr => h r (Finset.ne_of_mem_erase hr)
    omega
  · exact h r hr

theorem finset_fin_two_cases (S : Finset (Fin 2)) :
    S = ∅ ∨ S = {0} ∨ S = {1} ∨ S = univ := by
  revert S
  decide

def cfgOf {M : ℕ} (ζ : DualState M) : Rhone.LinearAlgebra.Recursion.Config 2 2 where
  a i := cnt ζ ({i}, univ)
  b j := cnt ζ (univ, {j})
  c i j := cnt ζ ({i}, {j})

theorem cnt_empty_left {M : ℕ} {ζ : DualState M} (hζ : ¬ Dead ζ) (T : Finset (Fin 2)) :
    cnt ζ (∅, T) = 0 := by
  unfold cnt
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro s _ hs
  exact hζ ⟨s, Or.inl (by rw [hs])⟩

theorem cnt_empty_right {M : ℕ} {ζ : DualState M} (hζ : ¬ Dead ζ) (S : Finset (Fin 2)) :
    cnt ζ (S, ∅) = 0 := by
  unfold cnt
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro s _ hs
  exact hζ ⟨s, Or.inr (by rw [hs])⟩

theorem cnt_eq_of_cfgOf_eq {M : ℕ} {ζ ξ : DualState M} (hζ : ¬ Dead ζ) (hξ : ¬ Dead ξ)
    (h : cfgOf ζ = cfgOf ξ) : ∀ r, cnt ζ r = cnt ξ r := by
  have ha : ∀ i, cnt ζ ({i}, univ) = cnt ξ ({i}, univ) := fun i =>
    congrFun (congrArg Rhone.LinearAlgebra.Recursion.Config.a h) i
  have hb : ∀ j, cnt ζ (univ, {j}) = cnt ξ (univ, {j}) := fun j =>
    congrFun (congrArg Rhone.LinearAlgebra.Recursion.Config.b h) j
  have hc : ∀ i j, cnt ζ ({i}, {j}) = cnt ξ ({i}, {j}) := fun i j =>
    congrFun (congrFun (congrArg Rhone.LinearAlgebra.Recursion.Config.c h) i) j
  refine cnt_eq_of_cnt_ne_eq fun r hr => ?_
  obtain ⟨S, T⟩ := r
  rcases finset_fin_two_cases S with rfl | rfl | rfl | rfl
  · rw [cnt_empty_left hζ, cnt_empty_left hξ]
  all_goals rcases finset_fin_two_cases T with rfl | rfl | rfl | rfl
  all_goals first
    | rw [cnt_empty_right hζ, cnt_empty_right hξ]
    | exact ha _
    | exact hb _
    | exact hc _ _
    | exact absurd rfl hr

theorem ancAbsorb_eq_of_cfgOf_eq {M : ℕ} (c u : ℝ) {ζ ξ : DualState M} (hζ : ¬ Dead ζ)
    (hξ : ¬ Dead ξ) (h : cfgOf ζ = cfgOf ξ) : ancAbsorb M c u ζ = ancAbsorb M c u ξ :=
  ancAbsorb_eq_of_cnt_eq c u (cnt_eq_of_cfgOf_eq hζ hξ h)

open Classical in
def cfgState (M : ℕ) (K : Rhone.LinearAlgebra.Recursion.Config 2 2) : DualState M :=
  if h : ∃ ζ : DualState M, ¬ Dead ζ ∧ cfgOf ζ = K then Classical.choose h else fullState M

theorem cfgState_spec {M : ℕ} {K : Rhone.LinearAlgebra.Recursion.Config 2 2}
    (h : ∃ ζ : DualState M, ¬ Dead ζ ∧ cfgOf ζ = K) :
    ¬ Dead (cfgState M K) ∧ cfgOf (cfgState M K) = K := by
  unfold cfgState
  rw [dite_eq_left h]
  exact Classical.choose_spec h

def lumpAbsorb (M : ℕ) (c u : ℝ) (K : Rhone.LinearAlgebra.Recursion.Config 2 2) : ℝ :=
  ancAbsorb M c u (cfgState M K)

theorem ancAbsorb_eq_lumpAbsorb {M : ℕ} (c u : ℝ) {ζ : DualState M} (hζ : ¬ Dead ζ) :
    ancAbsorb M c u ζ = lumpAbsorb M c u (cfgOf ζ) := by
  have h : ∃ ξ : DualState M, ¬ Dead ξ ∧ cfgOf ξ = cfgOf ζ := ⟨ζ, hζ, rfl⟩
  obtain ⟨h1, h2⟩ := cfgState_spec h
  exact ancAbsorb_eq_of_cfgOf_eq c u hζ h1 h2.symm

def cfgCount (M : ℕ) (K : Rhone.LinearAlgebra.Recursion.Config 2 2) (r : Req) : ℕ :=
  (∑ i, if r = ({i}, univ) then K.a i else 0) + (∑ j, if r = (univ, {j}) then K.b j else 0) +
    (∑ i, ∑ j, if r = ({i}, {j}) then K.c i j else 0) +
    (if r = (univ, univ) then M - K.n else 0)

theorem sum_cfgCount {M : ℕ} {K : Rhone.LinearAlgebra.Recursion.Config 2 2} (hK : K.n ≤ M) :
    ∑ r, cfgCount M K r = M := by
  unfold cfgCount
  simp only [Finset.sum_add_distrib]
  have h1 : ∑ r : Req, ∑ i, (if r = ({i}, univ) then K.a i else 0) = K.sumA := by
    rw [Finset.sum_comm]; simp [Rhone.LinearAlgebra.Recursion.Config.sumA]
  have h2 : ∑ r : Req, ∑ j, (if r = (univ, {j}) then K.b j else 0) = K.sumB := by
    rw [Finset.sum_comm]; simp [Rhone.LinearAlgebra.Recursion.Config.sumB]
  have h3 : ∑ r : Req, ∑ i, ∑ j, (if r = ({i}, {j}) then K.c i j else 0) = K.t := by
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_comm (γ := Req)]
    simp [Rhone.LinearAlgebra.Recursion.Config.t]
  have h4 : ∑ r : Req, (if r = (univ, univ) then M - K.n else 0) = M - K.n := by simp
  rw [h1, h2, h3, h4]
  have : K.n = K.sumA + K.sumB + K.t := rfl
  omega

theorem singleton_ne_univ_two (i : Fin 2) : ({i} : Finset (Fin 2)) ≠ univ := by
  fin_cases i <;> decide

theorem empty_ne_univ_two : (∅ : Finset (Fin 2)) ≠ univ := by decide

theorem cfgCount_empty_left (M : ℕ) (K : Rhone.LinearAlgebra.Recursion.Config 2 2)
    (T : Finset (Fin 2)) : cfgCount M K (∅, T) = 0 := by
  simp [cfgCount, empty_ne_univ_two]

theorem cfgCount_empty_right (M : ℕ) (K : Rhone.LinearAlgebra.Recursion.Config 2 2)
    (S : Finset (Fin 2)) : cfgCount M K (S, ∅) = 0 := by
  simp [cfgCount, empty_ne_univ_two]

theorem exists_state_of_cfg {M : ℕ} {K : Rhone.LinearAlgebra.Recursion.Config 2 2} (hK : K.n ≤ M) :
    ∃ ζ : DualState M, ¬ Dead ζ ∧ cfgOf ζ = K := by
  classical
  have hcard : Fintype.card (Σ r : Req, Fin (cfgCount M K r)) = M := by
    rw [Fintype.card_sigma]
    simp [sum_cfgCount hK]
  let e : Fin M ≃ Σ r : Req, Fin (cfgCount M K r) := (Fintype.equivFinOfCardEq hcard).symm
  have hcnt : ∀ r, cnt (fun s => (e s).1) r = cfgCount M K r := by
    intro r
    unfold cnt
    have hsig : (univ.filter fun x : (Σ r : Req, Fin (cfgCount M K r)) => x.1 = r) =
        Finset.sigma {r} fun r' => (univ : Finset (Fin (cfgCount M K r'))) := by
      ext x
      simp
    rw [← Fintype.card_subtype,
      Fintype.card_congr (e.subtypeEquiv (p := fun s => (e s).1 = r) (q := fun x => x.1 = r)
        fun s => Iff.rfl),
      Fintype.card_subtype, hsig, Finset.card_sigma]
    simp
  refine ⟨fun s => (e s).1, ?_, ?_⟩
  · rintro ⟨s, hs | hs⟩
    · have h0 : cfgCount M K (e s).1 = 0 := by
        rw [show (e s).1 = (∅, (e s).1.2) from Prod.ext hs rfl]
        exact cfgCount_empty_left M K _
      exact (Fin.elim0 (h0 ▸ (e s).2))
    · have h0 : cfgCount M K (e s).1 = 0 := by
        rw [show (e s).1 = ((e s).1.1, ∅) from Prod.ext rfl hs]
        exact cfgCount_empty_right M K _
      exact (Fin.elim0 (h0 ▸ (e s).2))
  · refine Rhone.LinearAlgebra.Recursion.Config.ext ?_ ?_ ?_
    · funext i
      change cnt _ _ = _
      rw [hcnt]
      simp [cfgCount, Ne.symm (singleton_ne_univ_two _)]
    · funext j
      change cnt _ _ = _
      rw [hcnt]
      simp [cfgCount, Ne.symm (singleton_ne_univ_two _)]
    · funext i j
      change cnt _ _ = _
      rw [hcnt]
      fin_cases i <;> fin_cases j <;> simp [cfgCount]

theorem cfgState_of_le {M : ℕ} {K : Rhone.LinearAlgebra.Recursion.Config 2 2} (hK : K.n ≤ M) :
    ¬ Dead (cfgState M K) ∧ cfgOf (cfgState M K) = K :=
  cfgState_spec (exists_state_of_cfg hK)

def sampleCfg {n : ℕ} (y : Fin n → Fin 4) : Rhone.LinearAlgebra.Recursion.Config 2 2 where
  a _ := 0
  b _ := 0
  c i j := (univ.filter fun k => firstIndex (y k) = i ∧ secondIndex (y k) = j).card

theorem not_dead_sampleState {M n : ℕ} (y : Fin n → Fin 4) : ¬ Dead (sampleState M y) := by
  rintro ⟨s, hs | hs⟩ <;>
  · unfold sampleState at hs
    split_ifs at hs <;> first | exact empty_ne_univ_two hs.symm | simp at hs

theorem cfgOf_sampleState {M n : ℕ} (hn : n ≤ M) (y : Fin n → Fin 4) :
    cfgOf (sampleState M y) = sampleCfg y := by
  refine Rhone.LinearAlgebra.Recursion.Config.ext ?_ ?_ ?_
  · funext i
    change cnt _ _ = 0
    unfold cnt
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro s _ hs
    unfold sampleState at hs
    split_ifs at hs with h
    · exact singleton_ne_univ_two _ (congrArg Prod.snd hs)
    · exact singleton_ne_univ_two _ (congrArg Prod.fst hs).symm
  · funext j
    change cnt _ _ = 0
    unfold cnt
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro s _ hs
    unfold sampleState at hs
    split_ifs at hs with h
    · exact singleton_ne_univ_two _ (congrArg Prod.fst hs)
    · exact singleton_ne_univ_two _ (congrArg Prod.snd hs).symm
  · funext i j
    change cnt _ _ = (univ.filter fun k => firstIndex (y k) = i ∧ secondIndex (y k) = j).card
    unfold cnt
    symm
    refine Finset.card_bij (fun k _ => Fin.castLE hn k) ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      unfold sampleState
      rw [dite_eq_left (show (Fin.castLE hn k).val < n from k.isLt)]
      simp [hk.1, hk.2]
    · intro k₁ _ k₂ _ h
      exact Fin.castLE_injective hn h
    · intro s hs
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
      unfold sampleState at hs
      split_ifs at hs with h
      · refine ⟨⟨s.val, h⟩, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          obtain ⟨h1, h2⟩ := Prod.mk.inj hs
          exact ⟨Finset.singleton_inj.mp h1, Finset.singleton_inj.mp h2⟩
        · ext; rfl
      · exact absurd (congrArg Prod.fst hs) (singleton_ne_univ_two i).symm

theorem ancAbsorb_sampleState_eq_lumpAbsorb {M n : ℕ} (hn : n ≤ M) (c u : ℝ)
    (y : Fin n → Fin 4) :
    ancAbsorb M c u (sampleState M y) = lumpAbsorb M c u (sampleCfg y) := by
  rw [ancAbsorb_eq_lumpAbsorb c u (not_dead_sampleState y), cfgOf_sampleState hn]

end Rhone.Coalescent.WFTwoLocusDual
