/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.TwoLocusWFClosure

/-!
# Scaling limit of the two-locus Wright-Fisher dual

Source: griffiths1991_two_locus_graph, p. 101. -/

@[expose] public section
noncomputable section
namespace Rhone.Coalescent.WFTwoLocusDual
open Finset Polynomial Filter Topology LinearAlgebra.Recursion WFTwoLocusLimit
  MarkovChain.WFAllocationLD

theorem sum_vecZ_one (K : Config 2 2) : ∑ q, ((vecZ K q : ℤ) : ℝ) = (K.n : ℝ) := by
  have h := sum_vecZ_mul K fun _ => 1
  simp only [mul_one] at h
  rw [h]
  simp [Config.n, Config.sumA, Config.sumB, Config.t]

theorem levA_cast (κ : Req → ℕ) : (levA κ : ℝ) = ∑ q, (κ q : ℝ) * (nf q.1 : ℝ) := by
  unfold levA nf
  push_cast
  exact Finset.sum_congr rfl fun q _ => by split_ifs <;> simp

theorem levB_cast (κ : Req → ℕ) : (levB κ : ℝ) = ∑ q, (κ q : ℝ) * (nf q.2 : ℝ) := by
  unfold levB nf
  push_cast
  exact Finset.sum_congr rfl fun q _ => by split_ifs <;> simp

theorem lev_of_vecZ {κ : Req → ℕ} {K : Config 2 2}
    (h : ∀ q, q ≠ full → (κ q : ℤ) = vecZ K q) : levA κ = K.nA ∧ levB κ = K.nB := by
  have hq : ∀ (w : Req → ℝ), w full = 0 →
      ∑ q, (κ q : ℝ) * w q = ∑ q, ((vecZ K q : ℤ) : ℝ) * w q := by
    intro w hw
    refine Finset.sum_congr rfl fun q _ => ?_
    by_cases hf : q = full
    · subst hf; simp [hw]
    · rw [← h q hf]; simp
  constructor
  · have := levA_cast κ
    rw [hq _ (by simp [nf]), sum_vecZ_mul] at this
    have e : ((levA κ : ℕ) : ℝ) = ((K.nA : ℕ) : ℝ) := by
      rw [this]
      simp [nf, reqA, reqB, reqC, Config.nA, Config.sumA, Config.t]
    exact_mod_cast e
  · have := levB_cast κ
    rw [hq _ (by simp [nf]), sum_vecZ_mul] at this
    have e : ((levB κ : ℕ) : ℝ) = ((K.nB : ℕ) : ℝ) := by
      rw [this]
      simp [nf, reqA, reqB, reqC, Config.nB, Config.sumB, Config.t]
    exact_mod_cast e

def lamK (K : Config 2 2) : DualState K.n := cfgState K.n K

theorem lamK_spec (K : Config 2 2) : ¬ Dead (lamK K) ∧ cfgOf (lamK K) = K :=
  cfgState_of_le le_rfl

theorem lamK_ne_full (K : Config 2 2) (k : Fin K.n) : lamK K k ≠ full := by
  obtain ⟨hd, hc⟩ := lamK_spec K
  have h1 : ∑ q, (cnt (lamK K) q : ℝ) = K.n := by exact_mod_cast sum_cnt (lamK K)
  have h2 : ∀ q, (cnt (lamK K) q : ℝ) =
      (if q = full then (cnt (lamK K) full : ℝ) else 0) + ((vecZ K q : ℤ) : ℝ) := by
    intro q
    by_cases hq : q = full
    · subst hq; simp
    · have h := cnt_eq_vecZ hd hq
      rw [hc] at h
      rw [ite_eq_right hq, zero_add, ← h, Int.cast_natCast]
  rw [Finset.sum_congr rfl fun q _ => h2 q, Finset.sum_add_distrib, Finset.sum_ite_eq',
    sum_vecZ_one] at h1
  simp only [Finset.mem_univ, ↓reduceIte] at h1
  have h0 : cnt (lamK K) full = 0 := by
    have : (cnt (lamK K) full : ℝ) = 0 := by linarith
    exact_mod_cast this
  intro hk
  unfold cnt at h0
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h0
  exact h0 (Finset.mem_univ k) hk

theorem insAll_lamK (K : Config 2 2) (q : Req) (hq : q ≠ full) :
    insAll (lamK K) 0 q = vecZ K q := by
  obtain ⟨hd, hc⟩ := lamK_spec K
  have h := cnt_eq_vecZ hd hq
  rw [hc] at h
  rw [← h, cnt_eq_sum]
  simp [insAll, eR, Pi.single_apply, hq, eq_comm]

theorem gam_congr (θ ρ : ℝ) {G : (Req → ℤ) → ℝ} (hG : FullFree G) {v w : Req → ℤ}
    (h : ∀ q, q ≠ full → v q = w q) : gam θ ρ G v = gam θ ρ G w := by
  have hs : sCnt v = sCnt w := by
    funext q
    unfold sCnt
    split_ifs with hq
    · rfl
    · rw [h q hq]
  have key : ∀ t : Req → ℤ, G (v + t) = G (w + t) := fun t => hG _ _ (agree_add h t)
  have key0 : G v = G w := hG _ _ h
  unfold gam lin0 pairV
  rw [hs]
  simp only [sub_eq_add_neg, add_assoc, key, key0]

def polyM (θ ρ : ℝ) (g : Config 2 2 → ℝ) (K : Config 2 2) : ℝ[X] :=
  chainP θ ρ (lamK K) (fun v => C (liftZ g v)) 0

theorem polyM_eval_zero (θ ρ : ℝ) (g : Config 2 2 → ℝ) (K : Config 2 2) :
    (polyM θ ρ g K).eval 0 = g K := by
  rw [polyM, (chainP_first_order θ ρ (lamK K) (lamK_ne_full K) _ 0).1, eval_C,
    fullFree_liftZ g _ (vecZ K) (insAll_lamK K), liftZ_vecZ]

theorem polyM_deriv (θ ρ : ℝ) (g : Config 2 2 → ℝ) (K : Config 2 2) :
    (derivative (polyM θ ρ g K)).eval 0 =
      (1 / 2) * (rhs θ θ ρ (fun _ => (1 / 2 : ℝ)) (fun _ => (1 / 2 : ℝ)) g K -
        Rhone.LinearAlgebra.Recursion.diag θ θ ρ K * g K) := by
  rw [polyM, (chainP_first_order θ ρ (lamK K) (lamK_ne_full K) _ 0).2, derivative_C,
    eval_zero, gam_zero]
  simp only [eval_C, zero_add, sub_zero]
  rw [gam_congr θ ρ (fullFree_liftZ g) (insAll_lamK K), gam_liftZ_vecZ]

theorem tendsto_nat_mul_sub_eval (p : ℝ[X]) :
    Tendsto (fun M : ℕ => (M : ℝ) * (p.eval (1 / M : ℝ) - p.eval 0)) atTop
      (𝓝 ((derivative p).eval 0)) := by
  have hd := Polynomial.hasDerivAt p 0
  rw [hasDerivAt_iff_tendsto_slope] at hd
  have h1 : Tendsto (fun M : ℕ => (1 / (M : ℝ))) atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_atTop_nhds_zero_nat, ?_⟩
    filter_upwards [eventually_ge_atTop 1] with M hM
    have : (0 : ℝ) < M := by exact_mod_cast hM
    exact (one_div_pos.mpr this).ne'
  refine (hd.comp h1).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with M hM
  have : (M : ℝ) ≠ 0 := by have : (1 : ℝ) ≤ M := by exact_mod_cast hM
                           linarith
  simp only [Function.comp, slope_def_field, sub_zero]
  field_simp

theorem cnt_fullState_ne (M : ℕ) {q : Req} (hq : q ≠ full) : cnt (fullState M) q = 0 := by
  unfold cnt
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro s _ hs
  exact hq (by rw [← hs]; rfl)

theorem lumpChain_eq_polyM {M : ℕ} (hM : 0 < M) (θ ρ : ℝ) (g : Config 2 2 → ℝ)
    (K : Config 2 2) :
    lumpChain M (ρ / (2 * M)) (θ / (4 * M)) (lamK K) (fun κ => liftZ g (castV κ))
      (cnt (fullState M)) = (polyM θ ρ g K).eval (1 / M : ℝ) := by
  have hfree : FullFree (fun v => C (liftZ g v)) := fun v w h =>
    congrArg C (fullFree_liftZ g v w h)
  rw [← eval_chainP hM θ ρ (lamK K) (H := fun v => C (liftZ g v)) (fun κ' _ => by simp)
    (sum_cnt (fullState M)), polyM]
  congr 1
  refine chainP_congr_full θ ρ (lamK K) hfree _ _ fun q hq => ?_
  simp [castV, cnt_fullState_ne M hq]

def placeState (M : ℕ) {n : ℕ} (lam : Fin n → Req) : DualState M := fun s =>
  if h : s.val < n then lam ⟨s.val, h⟩ else full

theorem cnt_placeState {M n : ℕ} (hn : n ≤ M) (lam : Fin n → Req) {q : Req} (hq : q ≠ full) :
    cnt (placeState M lam) q = cnt lam q := by
  unfold cnt
  symm
  refine Finset.card_bij (fun k _ => Fin.castLE hn k) ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    simp [placeState, hk]
  · intro k₁ _ k₂ _ h
    exact Fin.castLE_injective hn h
  · intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
    unfold placeState at hs
    split_ifs at hs with h
    · exact ⟨⟨s.val, h⟩, by simpa using hs, by ext; rfl⟩
    · exact absurd hs.symm hq

theorem ancAbsorb_placeState {M : ℕ} (c u : ℝ) {K : Config 2 2} (hK : K.n ≤ M) :
    ancAbsorb M c u (placeState M (lamK K)) = lumpAbsorb M c u K := by
  obtain ⟨hd, hc⟩ := lamK_spec K
  have hnd : ¬ Dead (placeState M (lamK K)) := by
    rintro ⟨s, hs⟩
    unfold placeState at hs
    split_ifs at hs
    · exact hd ⟨_, hs⟩
    · rcases hs with hs | hs <;> exact empty_ne_univ_two hs.symm
  rw [ancAbsorb_eq_lumpAbsorb c u hnd]
  congr 1
  conv_rhs => rw [← hc]
  refine Config.ext ?_ ?_ ?_ <;> funext
  · exact cnt_placeState hK _ (reqA_ne_full _)
  · exact cnt_placeState hK _ (reqB_ne_full _)
  · exact cnt_placeState hK _ (reqC_ne_full _ _)

theorem lumpAbsorb_eq_lumpChain {M : ℕ} (hM : 0 < M) {c u : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2) {K : Config 2 2} (hK : K.n ≤ M) :
    lumpAbsorb M c u K = lumpChain M c u (lamK K) (cntAbsorb M c u) (cnt (fullState M)) := by
  rw [← ancAbsorb_placeState c u hK]
  set A : Finset (Fin M) := univ.filter fun s => s.val < K.n with hA
  have hbij : Function.Bijective (fun k : Fin K.n =>
      (⟨Fin.castLE hK k, by simp [hA]⟩ : A)) := by
    constructor
    · intro k₁ k₂ h
      exact Fin.castLE_injective hK (congrArg Subtype.val h)
    · rintro ⟨s, hs⟩
      simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and] at hs
      exact ⟨⟨s.val, hs⟩, by ext; rfl⟩
  have hout : ∀ t, t ∉ A → placeState M (lamK K) t = (univ, univ) := by
    intro t ht
    simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and] at ht
    simp [placeState, ht]
  rw [ancAbsorb_eq_lumpChain hM hc0 hc1 hu0 hu1 hout (Equiv.ofBijective _ hbij)]
  congr 1
  funext k
  simp [placeState]

theorem exists_state_of_cnt {M : ℕ} {κ : Req → ℕ} (hκ : ∑ q, κ q = M) :
    ∃ ξ : DualState M, cnt ξ = κ := by
  classical
  have hcard : Fintype.card (Σ r : Req, Fin (κ r)) = M := by
    rw [Fintype.card_sigma]; simp [hκ]
  let e : Fin M ≃ Σ r : Req, Fin (κ r) := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨fun s => (e s).1, ?_⟩
  funext r
  unfold cnt
  have hsig : (univ.filter fun x : (Σ r : Req, Fin (κ r)) => x.1 = r) =
      Finset.sigma {r} fun r' => (univ : Finset (Fin (κ r'))) := by
    ext x; simp
  rw [← Fintype.card_subtype,
    Fintype.card_congr (e.subtypeEquiv (p := fun s => (e s).1 = r) (q := fun x => x.1 = r)
      fun s => Iff.rfl),
    Fintype.card_subtype, hsig, Finset.card_sigma]
  simp

theorem cntAbsorb_eq_liftZ {M : ℕ} (hM : 0 < M) {c u : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2) {N : ℕ} {K : Config 2 2} (hKN : K.nA + K.nB ≤ N)
    {κ : Req → ℕ} (hκ : LevSet M K.nA K.nB κ) :
    cntAbsorb M c u κ = liftZ (fun η => extend (fun ξ : Idx 2 2 N => lumpAbsorb M c u ξ.1) η +
      indCfg 0 η) (castV κ) := by
  obtain ⟨ξ, rfl⟩ := exists_state_of_cnt hκ.1
  rw [← ancAbsorb_eq_cntAbsorb]
  by_cases hd : Dead ξ
  · rw [ancAbsorb_of_dead hM hc0 hc1 hu0 hu1 hd]
    obtain ⟨s, hs⟩ := hd
    refine (liftZ_dead (q := ξ s) hs ?_).symm
    have : 1 ≤ cnt ξ (ξ s) := Finset.card_pos.mpr ⟨s, by simp⟩
    simp only [castV]; omega
  have hv : ∀ q, q ≠ full → (cnt ξ q : ℤ) = vecZ (cfgOf ξ) q := fun q hq => cnt_eq_vecZ hd hq
  have hcfg : cfgZ (castV (cnt ξ)) = cfgOf ξ := by
    refine Config.ext ?_ ?_ ?_ <;> funext <;> simp [cfgZ, castV, cfgOf] <;> rfl
  rw [liftZ_of fun q hq => by
    have := hv q hq.ne.2.2.2
    simp only [castV, this, (dead_zero _ hq).1], hcfg]
  set K'' := cfgOf ξ with hK''
  obtain ⟨hlA, hlB⟩ := lev_of_vecZ hv
  by_cases hn : K''.n = 0
  · have h0 : K'' = 0 := Config.eq_zero_of_n_eq_zero K'' hn
    have hnm : (0 : Config 2 2) ∉ levelSet 2 2 N := fun h => by
      have := (mem_levelSet.mp h).2; simp [Config.n] at this
    rw [h0, extend_apply, dite_eq_right hnm]
    simp only [indCfg, ↓reduceIte, zero_add]
    have hall : ∀ r, cnt ξ r = cnt (fullState M) r := by
      refine cnt_eq_of_cnt_ne_eq fun r hr => ?_
      rw [cnt_fullState_ne M hr]
      have := hv r hr
      have hz : vecZ 0 r = 0 := by
        simp [vecZ]
      rw [h0, hz] at this
      omega
    rw [ancAbsorb_eq_of_cnt_eq c u hall, ancAbsorb_fullState hM hc0 hc1 hu0 hu1]
  · have hmem : K'' ∈ levelSet 2 2 N := by
      refine mem_levelSet.mpr ⟨?_, by omega⟩
      have := hκ.2.1; have := hκ.2.2; omega
    have hne : K'' ≠ 0 := fun h => hn (by rw [h]; rfl)
    rw [extend_apply, dite_eq_left hmem]
    simp only [indCfg, hne, ↓reduceIte, add_zero]
    exact ancAbsorb_eq_lumpAbsorb c u hd

theorem liftZ_extend {N : ℕ} (h : Idx 2 2 N → ℝ) (v : Req → ℤ) :
    liftZ (fun η => extend h η + indCfg 0 η) v =
      ∑ K', h K' * liftZ (indCfg K'.1) v + liftZ (indCfg 0) v := by
  unfold liftZ
  split_ifs
  · simp [extend]
  · simp

def stepMat (θ ρ : ℝ) (N M : ℕ) : Matrix (Idx 2 2 N) (Idx 2 2 N) ℝ :=
  fun K K' => (polyM θ ρ (indCfg K'.1) K.1).eval (1 / M : ℝ)

def stepVec (θ ρ : ℝ) (N M : ℕ) : Idx 2 2 N → ℝ :=
  fun K => (polyM θ ρ (indCfg 0) K.1).eval (1 / M : ℝ)

theorem n_le_of_mem_levelSet {N : ℕ} (K : Idx 2 2 N) : K.1.n ≤ N := by
  have h := (mem_levelSet.mp K.2).1
  have := K.1.n_add_t
  omega

theorem lumpAbsorb_fixed {θ ρ : ℝ} (hθ : 0 ≤ θ) (hρ : 0 ≤ ρ) {N M : ℕ} (hM : 0 < M)
    (hNM : N ≤ M) (hρM : ρ ≤ 2 * M) (hθM : θ ≤ 2 * M) :
    (fun K : Idx 2 2 N => lumpAbsorb M (ρ / (2 * M)) (θ / (4 * M)) K.1) =
      (stepMat θ ρ N M).mulVec (fun K : Idx 2 2 N => lumpAbsorb M (ρ / (2 * M)) (θ / (4 * M)) K.1) +
        stepVec θ ρ N M := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hc0 : 0 ≤ ρ / (2 * M) := by positivity
  have hc1 : ρ / (2 * M) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  have hu0 : 0 ≤ θ / (4 * M) := by positivity
  have hu1 : θ / (4 * M) ≤ 1 / 2 := by rw [div_le_iff₀ (by positivity)]; linarith
  funext K
  have hK : K.1.n ≤ M := (n_le_of_mem_levelSet K).trans hNM
  have hKN := (mem_levelSet.mp K.2).1
  rw [lumpAbsorb_eq_lumpChain hM hc0 hc1 hu0 hu1 hK]
  have hlev : lamLevA (lamK K.1) = K.1.nA ∧ lamLevB (lamK K.1) = K.1.nB := by
    obtain ⟨hd, hc⟩ := lamK_spec K.1
    have hv : ∀ q, q ≠ full → (cnt (lamK K.1) q : ℤ) = vecZ K.1 q := fun q hq => by
      have h := cnt_eq_vecZ hd hq
      rwa [hc] at h
    obtain ⟨h1, h2⟩ := lev_of_vecZ hv
    have eA : lamLevA (lamK K.1) = levA (cnt (lamK K.1)) := by
      have : ((lamLevA (lamK K.1) : ℕ) : ℝ) = ((levA (cnt (lamK K.1)) : ℕ) : ℝ) := by
        rw [levA_cast, lamLevA]; push_cast
        rw [sum_comp_cnt (lamK K.1) fun q => (nf q.1 : ℝ)]
      exact_mod_cast this
    have eB : lamLevB (lamK K.1) = levB (cnt (lamK K.1)) := by
      have : ((lamLevB (lamK K.1) : ℕ) : ℝ) = ((levB (cnt (lamK K.1)) : ℕ) : ℝ) := by
        rw [levB_cast, lamLevB]; push_cast
        rw [sum_comp_cnt (lamK K.1) fun q => (nf q.2 : ℝ)]
      exact_mod_cast this
    exact ⟨eA.trans h1, eB.trans h2⟩
  have hlev0 : levA (cnt (fullState M)) = 0 ∧ levB (cnt (fullState M)) = 0 := by
    constructor <;>
    · refine Finset.sum_eq_zero fun q _ => ?_
      split_ifs with h
      · rfl
      · exact cnt_fullState_ne M fun e => h (by rw [e])
  rw [lumpChain_congr M _ _ (lamK K.1) (G' := fun κ =>
      ∑ K' : Idx 2 2 N, lumpAbsorb M (ρ / (2 * M)) (θ / (4 * M)) K'.1 *
        liftZ (indCfg K'.1) (castV κ) +
        liftZ (indCfg 0) (castV κ)) (sum_cnt _) fun κ hκ => by
      rw [← liftZ_extend]
      refine cntAbsorb_eq_liftZ hM hc0 hc1 hu0 hu1 hKN ⟨hκ.1, ?_, ?_⟩
      · have := hκ.2.1; rw [hlev0.1, hlev.1] at this; omega
      · have := hκ.2.2; rw [hlev0.2, hlev.2] at this; omega]
  rw [lumpChain_sum]
  simp only [lumpChain_eq_polyM hM θ ρ, Pi.add_apply, Matrix.mulVec, dotProduct, stepMat,
    stepVec]
  congr 1
  exact Finset.sum_congr rfl fun K' _ => mul_comm _ _

theorem one_le_sampleCfg_n {n : ℕ} (hn : 0 < n) (y : Fin n → Fin 4) : 1 ≤ (sampleCfg y).n := by
  have h1 : 1 ≤ (sampleCfg y).c (firstIndex (y ⟨0, hn⟩)) (secondIndex (y ⟨0, hn⟩)) := by
    simp only [sampleCfg]
    exact Finset.one_le_card.mpr ⟨⟨0, hn⟩, by simp⟩
  have h2 : (sampleCfg y).c (firstIndex (y ⟨0, hn⟩)) (secondIndex (y ⟨0, hn⟩)) ≤
      (sampleCfg y).t := by
    unfold Config.t
    refine le_trans ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ (firstIndex (y ⟨0, hn⟩))))
    exact Finset.single_le_sum (f := fun j => (sampleCfg y).c _ j) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ _)
  unfold Config.n
  omega

theorem tendsto_ancAbsorb_sampleState {θ ρ : ℝ} (hθ : 0 < θ) (hρ : 0 ≤ ρ) {n : ℕ}
    (y : Fin n → Fin 4) :
    Tendsto (fun M : ℕ => ancAbsorb M (ρ / (2 * M)) (θ / (4 * M)) (sampleState M y)) atTop
      (𝓝 (Rhone.Coalescent.TwoLocusGenealogy.qProb θ θ ρ (fun _ => (1 / 2 : ℝ))
          (fun _ => (1 / 2 : ℝ))
        (sampleCfg y))) := by
  have hev : ∀ᶠ M : ℕ in atTop, 0 < M ∧ n ≤ M ∧ ρ ≤ 2 * M ∧ θ ≤ 2 * M := by
    have h1 := tendsto_natCast_atTop_atTop (R := ℝ)
    filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop n,
      h1.eventually_ge_atTop (ρ / 2), h1.eventually_ge_atTop (θ / 2)] with M h1 h2 h3 h4
    exact ⟨h1, h2, by linarith, by linarith⟩
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hcfg : sampleCfg y = 0 := by
      refine Config.ext ?_ ?_ ?_ <;> funext <;> simp [sampleCfg]
    rw [hcfg, Rhone.Coalescent.TwoLocusGenealogy.qProb_zero]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with M ⟨hM, _, hρM, hθM⟩
    have hMr : (0 : ℝ) < M := by exact_mod_cast hM
    have hs : sampleState M y = fullState M := by
      funext s; simp [sampleState, fullState]
    rw [hs, ancAbsorb_fullState hM (by positivity)
      (by rw [div_le_one (by positivity)]; linarith) (by positivity)
      (by rw [div_le_iff₀ (by positivity)]; linarith)]
  set N := (sampleCfg y).nA + (sampleCfg y).nB with hN
  have hmem : sampleCfg y ∈ levelSet 2 2 N :=
    mem_levelSet.mpr ⟨le_rfl, one_le_sampleCfg_n hn y⟩
  have hlim := tendsto_qProb_of_expansion (N := N) (P := stepMat θ ρ N) (p := stepVec θ ρ N)
    (h := fun M K => lumpAbsorb M (ρ / (2 * M)) (θ / (4 * M)) K.1)
    (πA := fun _ : Fin 2 => (1 / 2 : ℝ)) (πB := fun _ : Fin 2 => (1 / 2 : ℝ))
    hθ hθ hρ (fun _ => by norm_num) (by simp) (fun _ => by norm_num)
    (by simp) ?hP ?hp ?hfix
  · have h1 := (continuous_apply (⟨sampleCfg y, hmem⟩ : Idx 2 2 N)).continuousAt.tendsto.comp
      hlim
    refine h1.congr' ?_
    filter_upwards [hev] with M ⟨_, hnM, _, _⟩
    exact (ancAbsorb_sampleState_eq_lumpAbsorb hnM _ _ y).symm
  case hP =>
    refine tendsto_pi_nhds.mpr fun K => tendsto_pi_nhds.mpr fun K' => ?_
    have h := tendsto_nat_mul_sub_eval (polyM θ ρ (indCfg K'.1) K.1)
    rw [polyM_deriv, polyM_eval_zero] at h
    convert h using 1
    · funext M
      simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply, stepMat, smul_eq_mul]
      by_cases hKK : K = K'
      · subst hKK; simp [indCfg]
      · have hne : K.1 ≠ K'.1 := fun e => hKK (Subtype.ext e)
        simp [indCfg, hKK, hne]
    · simp only [Matrix.smul_apply, genMat, smul_eq_mul]
      by_cases hKK : K = K'
      · subst hKK; simp [indCfg]
      · have hne : K.1 ≠ K'.1 := fun e => hKK (Subtype.ext e)
        simp [indCfg, hKK, hne]
  case hp =>
    refine tendsto_pi_nhds.mpr fun K => ?_
    have h := tendsto_nat_mul_sub_eval (polyM θ ρ (indCfg 0) K.1)
    rw [polyM_deriv, polyM_eval_zero] at h
    have hK0 : indCfg (0 : Config 2 2) K.1 = 0 := by
      have : K.1 ≠ 0 := fun e => by
        have := (mem_levelSet.mp K.2).2; rw [e] at this; simp [Config.n] at this
      simp [indCfg, this]
    rw [hK0] at h
    convert h using 1
    · funext M; simp [stepVec]
    · simp [genRhs]
  case hfix =>
    filter_upwards [hev, eventually_ge_atTop N] with M ⟨hM, _, hρM, hθM⟩ hNn
    exact lumpAbsorb_fixed hθ.le hρ hM hNn hρM hθM

end Rhone.Coalescent.WFTwoLocusDual
