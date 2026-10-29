/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.TwoLocusArgBridge

/-!
# The MRCA times of the general ancestral recombination graph at finitely many probes

Source: griffiths_marjoram1997, sec. 1, sec. 3; griffiths1991_two_locus_graph, pp. 103, 107;
hudson1983, p. 185, sec. 5, pp. 195–200. -/

@[expose] public section
noncomputable section

namespace Rhone.Coalescent.MultiLocus

open MeasureTheory Finset Rhone.LinearAlgebra MarkovChain IntervalProcess
open MarkovChain.IntervalProcess
  Analysis.ExpNegMoment Probability.ExpNegMoment
open scoped ENNReal

abbrev MCounts (m : ℕ) := Finset (Fin m) → ℕ

variable {m N : ℕ}

def types (m : ℕ) : Finset (Finset (Fin m)) := univ.filter fun S => S.Nonempty

def unitVec (S : Finset (Fin m)) : MCounts m := fun T => if T = S ∧ S.Nonempty then 1 else 0

def carriers (n : MCounts m) (k : Fin m) : ℕ := ∑ S ∈ univ.filter (fun S => k ∈ S), n S

def mergeVec (n : MCounts m) (S T : Finset (Fin m)) : MCounts m :=
  n - unitVec S - unitVec T + unitVec (S ∪ T)

def cutL (S : Finset (Fin m)) (j : Fin m) : Finset (Fin m) := S.filter fun k => k ≤ j

def cutR (S : Finset (Fin m)) (j : Fin m) : Finset (Fin m) := S.filter fun k => j < k

def splitVec (n : MCounts m) (S : Finset (Fin m)) (j : Fin m) : MCounts m :=
  n - unitVec S + unitVec (cutL S j) + unitVec (cutR S j)

def multiGen (d : Fin m → ℝ) (g : MCounts m → ℝ) (n : MCounts m) : ℝ :=
  (∑ S ∈ types m, ∑ T ∈ types m,
      (n S : ℝ) * ((n T : ℝ) - if S = T then 1 else 0) / 2 * (g (mergeVec n S T) - g n)) +
    ∑ S ∈ types m, ∑ j : Fin m,
      (if (cutL S j).Nonempty ∧ (cutR S j).Nonempty then (n S : ℝ) * (d j / 2) else 0) *
        (g (splitVec n S j) - g n)

abbrev MBox (m N : ℕ) := Finset (Fin m) → Fin (N + 1)

def mboxVal (b : MBox m N) : MCounts m := fun S => (b S : ℕ)

theorem mboxVal_injective : Function.Injective (mboxVal (m := m) (N := N)) := by
  intro b b' h
  funext S
  exact Fin.ext (congrFun h S)

def mboxExt (f : MBox m N → ℝ) (n : MCounts m) : ℝ :=
  if h : ∀ S, n S < N + 1 then f fun S => ⟨n S, h S⟩ else 0

theorem mboxExt_mboxVal (f : MBox m N → ℝ) (b : MBox m N) : mboxExt f (mboxVal b) = f b := by
  have h : ∀ S, mboxVal b S < N + 1 := fun S => (b S).isLt
  unfold mboxExt
  rw [dite_eq_left h]
  rfl

def multiRate (d : Fin m → ℝ) (b b' : MBox m N) : ℝ :=
  multiGen d (fun n => if n = mboxVal b' then 1 else 0) (mboxVal b)

theorem nat_mul_sub_ite_nonneg (a c : ℕ) (hS : Prop) [Decidable hS] (h : hS → a = c) :
    0 ≤ (a : ℝ) * ((c : ℝ) - if hS then 1 else 0) / 2 := by
  split_ifs with hs
  · rw [← h hs]
    exact IntervalCounts.nat_mul_pred_div_two_nonneg a
  · rw [sub_zero]
    positivity

theorem multiRate_nonneg {d : Fin m → ℝ} (hd : ∀ j, 0 ≤ d j) {b b' : MBox m N} (h : b ≠ b') :
    0 ≤ multiRate d b b' := by
  unfold multiRate multiGen
  have h0 : (if mboxVal b = mboxVal b' then (1 : ℝ) else 0) = 0 :=
    ite_eq_right fun e => h (mboxVal_injective e)
  simp only [h0, sub_zero]
  refine add_nonneg (Finset.sum_nonneg fun S _ => Finset.sum_nonneg fun T _ => ?_)
    (Finset.sum_nonneg fun S _ => Finset.sum_nonneg fun j _ => ?_)
  · refine mul_nonneg (nat_mul_sub_ite_nonneg _ _ _ fun e => by rw [e]) ?_
    split_ifs <;> norm_num
  · refine mul_nonneg ?_ (by split_ifs <;> norm_num)
    split_ifs
    · exact mul_nonneg (Nat.cast_nonneg _) (div_nonneg (hd j) (by norm_num))
    · exact le_rfl

def multiChain (d : Fin m → ℝ) (hd : ∀ j, 0 ≤ d j) (N : ℕ) : RateChain (MBox m N) where
  Q b b' := if b = b' then -∑ b'' ∈ univ.erase b, multiRate d b b'' else multiRate d b b'
  off_diag_nonneg b b' h := by
    rw [ite_eq_right h]
    exact multiRate_nonneg hd h
  row_sum b := by
    rw [← Finset.add_sum_erase univ _ (mem_univ b), ite_eq_left rfl]
    rw [Finset.sum_congr rfl fun b' hb' => ite_eq_right (Ne.symm (Finset.ne_of_mem_erase hb'))]
    ring

def startBox (m N : ℕ) : MBox m N := fun S =>
  if S = univ ∧ (univ : Finset (Fin m)).Nonempty then Fin.last N else 0

def lowSet (m N : ℕ) (k : Fin m) : Finset (MBox m N) :=
  univ.filter fun b => carriers (mboxVal b) k ≤ 1

def gapLen (x : Fin m → ℝ) (j : Fin m) : ℝ :=
  if h : j.val + 1 < m then x ⟨j.val + 1, h⟩ - x j else 0

theorem gapLen_nonneg {x : Fin m → ℝ} (hx : Monotone x) (j : Fin m) : 0 ≤ gapLen x j := by
  unfold gapLen
  split_ifs with h
  · exact sub_nonneg.2 (hx (Fin.mk_le_mk.2 (Nat.le_succ _)))
  · exact le_rfl

def probeReal (q : Fin m → GenomicProbe) : Fin m → ℝ := fun k => ((q k : ℚ) : ℝ)

theorem probeReal_monotone {q : Fin m → GenomicProbe} (hq : StrictMono q) :
    Monotone (probeReal q) := fun _ _ h => Rat.cast_le.2 (hq.monotone h)

theorem probeReal_nonneg (q : Fin m → GenomicProbe) (k : Fin m) : 0 ≤ probeReal q k := by
  unfold probeReal
  exact_mod_cast (q k).property.1

theorem probeReal_lt_one (q : Fin m → GenomicProbe) (k : Fin m) : probeReal q k < 1 := by
  unfold probeReal
  exact_mod_cast (q k).property.2

def gapRate (R : ℝ) (q : Fin m → GenomicProbe) : Fin m → ℝ :=
  fun j => R * gapLen (probeReal q) j

theorem gapRate_nonneg {R : ℝ} (hR : 0 ≤ R) {q : Fin m → GenomicProbe} (hq : StrictMono q)
    (j : Fin m) : 0 ≤ gapRate R q j :=
  mul_nonneg hR (gapLen_nonneg (probeReal_monotone hq) j)

open scoped Classical in
def carrierSet (x : Fin m → ℝ) (a : Material) : Finset (Fin m) :=
  univ.filter fun k => materialContains a (x k)

open scoped Classical in
def typeVec (x : Fin m → ℝ) (s : State) : MCounts m := fun S =>
  if S.Nonempty then materialCount (fun a => carrierSet x a = S) s else 0

theorem carrierSet_merge (x : Fin m → ℝ) (a b : Material) :
    carrierSet x (mergeMaterial a b) = carrierSet x a ∪ carrierSet x b := by
  classical
  ext k
  simp [carrierSet, materialContains_merge]

theorem carrierSet_split_left (x : Fin m → ℝ) (c : ℝ) (a : Material) :
    carrierSet x (splitMaterial a c).1 = (carrierSet x a).filter fun k => x k < c := by
  classical
  ext k
  simp [carrierSet, materialContains_split_left]

theorem carrierSet_split_right (x : Fin m → ℝ) (c : ℝ) (a : Material) :
    carrierSet x (splitMaterial a c).2 = (carrierSet x a).filter fun k => c ≤ x k := by
  classical
  ext k
  simp [carrierSet, materialContains_split_right]

theorem carriers_typeVec (x : Fin m → ℝ) (s : State) (k : Fin m) :
    carriers (typeVec x s) k = carrierCount (x k) s := by
  classical
  unfold carriers carrierCount materialCount
  rw [Finset.card_eq_sum_card_fiberwise (f := fun i : Fin s.2.2.1 => carrierSet x (s.2.2.2 i).2)
    (t := univ.filter fun S : Finset (Fin m) => k ∈ S)]
  · refine Finset.sum_congr rfl fun S hS => ?_
    have hkS : k ∈ S := (Finset.mem_filter.1 hS).2
    have hSne : S.Nonempty := ⟨k, hkS⟩
    simp only [typeVec, hSne, ↓reduceIte, materialCount]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      refine ⟨?_, h⟩
      have : k ∈ carrierSet x (s.2.2.2 i).2 := h ▸ hkS
      simpa [carrierSet] using this
    · exact fun h => h.2
  · intro i hi
    simp only at hi ⊢
    simpa [carrierSet] using hi

theorem typeVec_measurable (x : Fin m → ℝ) : Measurable (typeVec x) := by
  classical
  refine measurable_pi_iff.mpr fun S => ?_
  unfold typeVec
  split_ifs
  · refine materialCount_measurable _ ?_
    have hset : {a : Material | carrierSet x a = S} =
        ⋂ k : Fin m, {a | (materialContains a (x k) ↔ k ∈ S)} := by
      ext a
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, Finset.ext_iff, carrierSet,
        Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hset]
    refine MeasurableSet.iInter fun k => ?_
    by_cases hk : k ∈ S
    · simpa [hk] using materialContains_measurable (x k)
    · have h' : {a : Material | (materialContains a (x k) ↔ k ∈ S)} =
          {a | materialContains a (x k)}ᶜ := by
        ext a
        simp [hk]
      rw [h']
      exact (materialContains_measurable (x k)).compl
  · exact measurable_const

theorem unitVec_apply_of_nonempty {U V : Finset (Fin m)} (hU : U.Nonempty) :
    unitVec V U = if V = U then 1 else 0 := by
  by_cases h : V = U
  · subst h
    simp [unitVec, hU]
  · have h' : ¬ (U = V ∧ V.Nonempty) := fun h' => h h'.1.symm
    simp [unitVec, h', h]

theorem unitVec_apply_empty (V : Finset (Fin m)) : unitVec V ∅ = 0 := by
  have h : ¬ ((∅ : Finset (Fin m)) = V ∧ V.Nonempty) := fun h => by
    obtain ⟨e, hne⟩ := h
    rw [← e] at hne
    exact Finset.not_nonempty_empty hne
  simp [unitVec, h]

open scoped Classical in
theorem materialCount_ge_ite (P : Material → Prop) (s : State) (i : Fin s.2.2.1) :
    (if P (s.2.2.2 i).2 then 1 else 0) ≤ materialCount P s := by
  rw [materialCount_eq_sum]
  exact Finset.single_le_sum (f := fun k : Fin s.2.2.1 => if P (s.2.2.2 k).2 then 1 else 0)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

open scoped Classical in
theorem materialCount_ge_ite_two (P : Material → Prop) (s : State) (i j : Fin s.2.2.1)
    (hij : i ≠ j) :
    (if P (s.2.2.2 i).2 then 1 else 0) + (if P (s.2.2.2 j).2 then 1 else 0) ≤
      materialCount P s := by
  rw [materialCount_eq_sum]
  have h := Finset.sum_le_sum_of_subset
    (f := fun k : Fin s.2.2.1 => if P (s.2.2.2 k).2 then 1 else 0) (Finset.subset_univ {i, j})
  rw [Finset.sum_pair hij] at h
  exact h

theorem typeVec_coalSuccessor (x : Fin m → ℝ) (s : State) (i j : Fin s.2.2.1)
    (hij : i.val < j.val) :
    typeVec x (coalSuccessor s i j) =
      mergeVec (typeVec x s) (carrierSet x (s.2.2.2 i).2) (carrierSet x (s.2.2.2 j).2) := by
  classical
  funext U
  by_cases hU : U.Nonempty
  · have h := materialCount_coalSuccessor (fun a => carrierSet x a = U) s i j hij
    have hb := materialCount_ge_ite_two (fun a => carrierSet x a = U) s i j
      (fun e => by rw [e] at hij; exact lt_irrefl _ hij)
    simp only [carrierSet_merge] at h
    simp only [typeVec, mergeVec, Pi.add_apply, Pi.sub_apply, ite_eq_left hU,
      unitVec_apply_of_nonempty hU]
    split_ifs at h hb ⊢ <;> omega
  · simp only [typeVec, mergeVec, Pi.add_apply, Pi.sub_apply, ite_eq_right hU]
    rw [Finset.not_nonempty_iff_eq_empty.1 hU]
    simp only [unitVec_apply_empty]

theorem typeVec_splitSuccessor (x : Fin m → ℝ) (s : State) (i : Fin s.2.2.1) (c : ℝ) :
    typeVec x (splitSuccessor s i c) =
      typeVec x s - unitVec (carrierSet x (s.2.2.2 i).2) +
        unitVec ((carrierSet x (s.2.2.2 i).2).filter fun k => x k < c) +
        unitVec ((carrierSet x (s.2.2.2 i).2).filter fun k => c ≤ x k) := by
  classical
  funext U
  by_cases hU : U.Nonempty
  · have h := materialCount_splitSuccessor (fun a => carrierSet x a = U) s i c
    have hb := materialCount_ge_ite (fun a => carrierSet x a = U) s i
    simp only [carrierSet_split_left, carrierSet_split_right] at h
    simp only [typeVec, Pi.add_apply, Pi.sub_apply, ite_eq_left hU, unitVec_apply_of_nonempty hU]
    split_ifs at h hb ⊢ <;> omega
  · simp only [typeVec, Pi.add_apply, Pi.sub_apply, ite_eq_right hU]
    rw [Finset.not_nonempty_iff_eq_empty.1 hU]
    simp only [unitVec_apply_empty]

theorem typeVec_initialState (x : Fin m → ℝ) (hx0 : ∀ k, 0 ≤ x k) (hx1 : ∀ k, x k < 1) :
    typeVec x (initialState N) = mboxVal (startBox m N) := by
  classical
  have hall : ∀ i : Fin (initialState N).2.2.1,
      carrierSet x ((initialState N).2.2.2 i).2 = univ := by
    intro i
    ext k
    simp only [carrierSet, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact ⟨0, hx0 k, hx1 k⟩
  funext S
  unfold typeVec mboxVal startBox
  simp only [materialCount, hall]
  by_cases h2 : S = univ ∧ (univ : Finset (Fin m)).Nonempty
  · obtain ⟨rfl, hne⟩ := h2
    rw [ite_eq_left hne, ite_eq_left ⟨rfl, hne⟩, Finset.filter_true_of_mem fun _ _ => rfl,
      Finset.card_univ, Fintype.card_fin, Fin.val_last]
    rfl
  · rw [ite_eq_right h2, Fin.val_zero]
    split_ifs with h1
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro i _ hi
      exact h2 ⟨hi.symm, by rw [hi]; exact h1⟩
    · rfl

theorem typeVec_atTime (x : Fin m → ℝ) (t : ℝ) (s : State) :
    typeVec x (atTime t s) = typeVec x s := rfl

open SmcSupport in
theorem multi_pairPart (R : ℝ) (x : Fin m → ℝ) (z : AugmentedState) (g : MCounts m → ℝ) :
    ∑ p : Fin z.1.2.2.1 × Fin z.1.2.2.1,
        (candidateRate false R z.1 (.inl p) : ℝ) *
          (∫ v, g (typeVec x (argActionStep R z (.inl p) v).1) ∂(unitUniform.prod unitUniform) -
            g (typeVec x z.1)) =
      ∑ S ∈ types m, ∑ T ∈ types m,
        (typeVec x z.1 S : ℝ) * ((typeVec x z.1 T : ℝ) - if S = T then 1 else 0) / 2 *
          (g (mergeVec (typeVec x z.1) S T) - g (typeVec x z.1)) := by
  classical
  set n := typeVec x z.1 with hn
  set τ : Fin z.1.2.2.1 → Finset (Fin m) := fun i => carrierSet x (z.1.2.2.2 i).2 with hτ
  set Ψ : Finset (Fin m) → Finset (Fin m) → ℝ := fun S T =>
    if S.Nonempty ∧ T.Nonempty then g (mergeVec n S T) - g n else 0 with hΨ
  have hmergeComm : ∀ S T, mergeVec n S T = mergeVec n T S := by
    intro S T
    funext U
    simp only [mergeVec, Pi.add_apply, Pi.sub_apply, Finset.union_comm S T]
    omega
  have hΨ1 : ∀ t t', t.Nonempty → t'.Nonempty → Ψ t t' = g (mergeVec n t t') - g n := by
    intro t t' h1 h2
    rw [hΨ]
    exact ite_eq_left ⟨h1, h2⟩
  have hΨ0 : ∀ t t', ¬ (t.Nonempty ∧ t'.Nonempty) → Ψ t t' = 0 := by
    intro t t' h
    rw [hΨ]
    exact ite_eq_right h
  have hΨsymm : ∀ t t', Ψ t t' = Ψ t' t := by
    intro t t'
    by_cases h : t.Nonempty ∧ t'.Nonempty
    · rw [hΨ1 t t' h.1 h.2, hΨ1 t' t h.2 h.1, hmergeComm]
    · rw [hΨ0 t t' h, hΨ0 t' t fun h' => h ⟨h'.2, h'.1⟩]
  have hcount_ge : ∀ i, (τ i).Nonempty → 1 ≤ n (τ i) := by
    intro i hne
    simp only [hn, typeVec, hne, ↓reduceIte, materialCount]
    exact Finset.card_pos.2 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩⟩
  have hT : ∀ i, ¬ (τ i).Nonempty ∨ 1 ≤ n (τ i) := fun i =>
    (em (τ i).Nonempty).elim (fun h => Or.inr (hcount_ge i h)) Or.inl
  have hme : ∀ S T : Finset (Fin m), S = ∅ → (¬ T.Nonempty ∨ 1 ≤ n T) →
      mergeVec n S T = n := by
    intro S T hS hT'
    subst hS
    funext U
    simp only [mergeVec, Pi.add_apply, Pi.sub_apply, Finset.empty_union]
    have h0 : unitVec (∅ : Finset (Fin m)) U = 0 := by simp [unitVec]
    have hle : unitVec T U ≤ n U := by
      unfold unitVec
      split_ifs with hU
      · rcases hT' with hT' | hT'
        · exact absurd hU.2 hT'
        · rw [hU.1]
          exact hT'
      · exact Nat.zero_le _
    omega
  have hterm : ∀ p : Fin z.1.2.2.1 × Fin z.1.2.2.1,
      (candidateRate false R z.1 (.inl p) : ℝ) *
          (∫ v, g (typeVec x (argActionStep R z (.inl p) v).1) ∂(unitUniform.prod unitUniform) -
            g n) =
        if p.1.val < p.2.val then Ψ (τ p.1) (τ p.2) else 0 := by
    intro p
    rw [candidateRate_unrestricted_pair]
    by_cases hlt : p.1.val < p.2.val
    · rw [ite_eq_left hlt, ite_eq_left hlt, one_mul]
      have hconst : ∀ v, g (typeVec x (argActionStep R z (.inl p) v).1) =
          g (mergeVec n (τ p.1) (τ p.2)) := by
        intro v
        change g (typeVec x (atTime _ (coalSuccessor z.1 p.1 p.2))) = _
        rw [typeVec_atTime, typeVec_coalSuccessor x z.1 p.1 p.2 hlt]
      rw [integral_congr_ae (Filter.Eventually.of_forall hconst), integral_const,
        probReal_univ, one_smul]
      by_cases hne : (τ p.1).Nonempty ∧ (τ p.2).Nonempty
      · rw [hΨ1 _ _ hne.1 hne.2]
      · rw [hΨ0 _ _ hne]
        rcases not_and_or.1 hne with h1 | h1
        · rw [hme _ _ (Finset.not_nonempty_iff_eq_empty.1 h1) (hT p.2), sub_self]
        · rw [hmergeComm, hme _ _ (Finset.not_nonempty_iff_eq_empty.1 h1) (hT p.1), sub_self]
    · rw [ite_eq_right hlt, ite_eq_right hlt, zero_mul]
  have hc : ∀ t : Finset (Fin m), t.Nonempty →
      ((Finset.univ.filter fun i => τ i = t).card : ℝ) = (n t : ℝ) := by
    intro t ht
    simp only [hn, hτ, typeVec, ht, ↓reduceIte, materialCount]
    try congr
  have hdiag : ∑ t, ((Finset.univ.filter fun i => τ i = t).card : ℝ) * Ψ t t =
      ∑ t, ∑ t', (if t = t' then ((Finset.univ.filter fun i => τ i = t).card : ℝ) * Ψ t t'
        else 0) := by
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ _)]
  rw [Finset.sum_congr rfl (fun p _ => hterm p), sum_lt_pair_eq τ Ψ hΨsymm, hdiag,
    ← Finset.sum_sub_distrib, Finset.sum_div]
  simp only [types, Finset.sum_filter]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← Finset.sum_sub_distrib, Finset.sum_div]
  by_cases ht : t.Nonempty
  · rw [ite_eq_left ht]
    refine Finset.sum_congr rfl fun t' _ => ?_
    by_cases ht' : t'.Nonempty
    · rw [ite_eq_left ht', hc t ht, hc t' ht', hΨ1 t t' ht ht']
      split_ifs <;> ring
    · rw [ite_eq_right ht', hΨ0 t t' fun h => ht' h.2]
      split_ifs <;> ring
  · rw [ite_eq_right ht]
    refine Finset.sum_eq_zero fun t' _ => ?_
    rw [hΨ0 t t' fun h => ht h.1]
    split_ifs <;> ring

def gapUp (x : Fin m → ℝ) (j : Fin m) : ℝ :=
  if h : j.val + 1 < m then x ⟨j.val + 1, h⟩ else x j

theorem gapLen_eq_gapUp_sub (x : Fin m → ℝ) (j : Fin m) : gapLen x j = gapUp x j - x j := by
  unfold gapLen gapUp
  split_ifs <;> ring

theorem le_gapUp_of_lt {x : Fin m → ℝ} (hx : StrictMono x) {j k : Fin m} (hjk : j < k) :
    gapUp x j ≤ x k := by
  have hlt := Fin.lt_def.1 hjk
  have hj1 : j.val + 1 < m := by have := k.isLt; omega
  rw [gapUp, dite_eq_left hj1]
  exact hx.monotone (Fin.le_iff_val_le_val.2 (by change j.val + 1 ≤ k.val; omega))

theorem lt_iff_le_of_mem_gap {x : Fin m → ℝ} (hx : StrictMono x) {c : ℝ} {j : Fin m}
    (h : x j < c ∧ c ≤ gapUp x j) (k : Fin m) : x k < c ↔ k ≤ j := by
  constructor
  · intro hk
    by_contra hkj
    push Not at hkj
    have := le_gapUp_of_lt hx hkj
    linarith [h.2]
  · intro hk
    exact lt_of_le_of_lt (hx.monotone hk) h.1

theorem gap_unique {x : Fin m → ℝ} (hx : StrictMono x) {c : ℝ} {j j' : Fin m}
    (h : x j < c ∧ c ≤ gapUp x j) (h' : x j' < c ∧ c ≤ gapUp x j') : j = j' :=
  le_antisymm ((lt_iff_le_of_mem_gap hx h' j).1 h.1) ((lt_iff_le_of_mem_gap hx h j').1 h'.1)

theorem exists_gap_or_trivial {x : Fin m → ℝ} (hx : StrictMono x) (c : ℝ) :
    (∃ j, x j < c ∧ c ≤ gapUp x j) ∨ (∀ k, c ≤ x k) ∨ (∀ k, x k < c) := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨hno, ⟨k1, hk1⟩, ⟨k2, hk2⟩⟩ := hcon
  have hs : (univ.filter fun k => x k < c).Nonempty := ⟨k1, by simp [hk1]⟩
  obtain ⟨j, hjs, hjmax⟩ : ∃ j ∈ univ.filter (fun k => x k < c),
      ∀ k ∈ univ.filter (fun k => x k < c), k ≤ j :=
    ⟨_, Finset.max'_mem _ hs, fun k hk => Finset.le_max' _ k hk⟩
  have hj : x j < c := (Finset.mem_filter.1 hjs).2
  have hjk2 : j < k2 := by
    by_contra hle
    push Not at hle
    have := hx.monotone hle
    linarith
  have hgap := hno j hj
  have hj1 : j.val + 1 < m := by
    have := Fin.lt_def.1 hjk2
    have := k2.isLt
    omega
  rw [gapUp, dite_eq_left hj1] at hgap
  have hmem : (⟨j.val + 1, hj1⟩ : Fin m) ∈ univ.filter (fun k => x k < c) :=
    Finset.mem_filter.2 ⟨Finset.mem_univ _, hgap⟩
  have h2 : j.val + 1 ≤ j.val := Fin.le_iff_val_le_val.1 (hjmax _ hmem)
  omega

theorem filter_lt_eq_cutL {x : Fin m → ℝ} (hx : StrictMono x) {c : ℝ} {j : Fin m}
    (h : x j < c ∧ c ≤ gapUp x j) (S : Finset (Fin m)) :
    S.filter (fun k => x k < c) = cutL S j := by
  unfold cutL
  exact Finset.filter_congr fun k _ => lt_iff_le_of_mem_gap hx h k

theorem filter_le_eq_cutR {x : Fin m → ℝ} (hx : StrictMono x) {c : ℝ} {j : Fin m}
    (h : x j < c ∧ c ≤ gapUp x j) (S : Finset (Fin m)) :
    S.filter (fun k => c ≤ x k) = cutR S j := by
  unfold cutR
  refine Finset.filter_congr fun k _ => ?_
  rw [← not_lt, lt_iff_le_of_mem_gap hx h k, not_le]

theorem splitVec_eq_self {n : MCounts m} {S : Finset (Fin m)} {j : Fin m}
    (hS : ∀ U, unitVec S U ≤ n U) (h : ¬ ((cutL S j).Nonempty ∧ (cutR S j).Nonempty)) :
    splitVec n S j = n := by
  have h0 : ∀ U, unitVec (∅ : Finset (Fin m)) U = 0 := fun U => by simp [unitVec]
  rcases not_and_or.1 h with h1 | h1
  · rw [Finset.not_nonempty_iff_eq_empty] at h1
    have hR : cutR S j = S := by
      unfold cutR
      refine Finset.filter_true_of_mem fun k hk => ?_
      by_contra hjk
      have : k ∈ cutL S j := Finset.mem_filter.2 ⟨hk, not_lt.1 hjk⟩
      rw [h1] at this
      simp at this
    funext U
    simp only [splitVec, Pi.add_apply, Pi.sub_apply, h1, hR, h0]
    have := hS U
    omega
  · rw [Finset.not_nonempty_iff_eq_empty] at h1
    have hL : cutL S j = S := by
      unfold cutL
      refine Finset.filter_true_of_mem fun k hk => ?_
      by_contra hkj
      have : k ∈ cutR S j := Finset.mem_filter.2 ⟨hk, not_le.1 hkj⟩
      rw [h1] at this
      simp at this
    funext U
    simp only [splitVec, Pi.add_apply, Pi.sub_apply, h1, hL, h0]
    have := hS U
    omega

open SmcSupport in
theorem multi_splitPart (R : ℝ) (hR : 0 ≤ R) (x : Fin m → ℝ) (hx : StrictMono x)
    (z : AugmentedState) (g : MCounts m → ℝ) :
    ∑ i : Fin z.1.2.2.1,
        (candidateRate false R z.1 (.inr i) : ℝ) *
          (∫ v, g (typeVec x (argActionStep R z (.inr i) v).1) ∂(unitUniform.prod unitUniform) -
            g (typeVec x z.1)) =
      ∑ S ∈ types m, ∑ j : Fin m,
        (if (cutL S j).Nonempty ∧ (cutR S j).Nonempty then
            (typeVec x z.1 S : ℝ) * ((R * gapLen x j) / 2) else 0) *
          (g (splitVec (typeVec x z.1) S j) - g (typeVec x z.1)) := by
  classical
  set n := typeVec x z.1 with hn
  set τ : Fin z.1.2.2.1 → Finset (Fin m) := fun i => carrierSet x (z.1.2.2.2 i).2 with hτ
  set F : Finset (Fin m) → ℝ := fun S => ∑ j : Fin m,
    (if (cutL S j).Nonempty ∧ (cutR S j).Nonempty then R * gapLen x j / 2 else 0) *
      (g (splitVec n S j) - g n) with hF
  have hcount_ge : ∀ i, (τ i).Nonempty → 1 ≤ n (τ i) := by
    intro i hne
    simp only [hn, typeVec, hne, ↓reduceIte, materialCount]
    exact Finset.card_pos.2 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩⟩
  have huS : ∀ i U, unitVec (τ i) U ≤ n U := by
    intro i U
    unfold unitVec
    split_ifs with hU
    · rw [hU.1]
      exact hcount_ge i hU.2
    · exact Nat.zero_le _
  have h0 : ∀ U, unitVec (∅ : Finset (Fin m)) U = 0 := fun U => by simp [unitVec]
  have hsnd : (unitUniform.prod unitUniform).map Prod.snd = unitUniform := by
    rw [Measure.map_snd_prod, measure_univ, one_smul]
  have hterm : ∀ i, (candidateRate false R z.1 (.inr i) : ℝ) *
      (∫ v, g (typeVec x (argActionStep R z (.inr i) v).1) ∂(unitUniform.prod unitUniform) -
        g n) = F (τ i) := by
    intro i
    set lo := hullLo (z.1.2.2.2 i).2 with hlo
    set len := hullLength (z.1.2.2.2 i).2 with hlen
    set T : Fin m → Set ℝ := fun j => {u : ℝ | x j < lo + len * u ∧ lo + len * u ≤ gapUp x j}
      with hT
    set Δ : Fin m → ℝ := fun j => g (splitVec n (τ i) j) - g n with hΔ
    have hTm : ∀ j, MeasurableSet (T j) := fun j => by
      have hf : Measurable fun u : ℝ => lo + len * u :=
        measurable_const.add (measurable_const.mul measurable_id)
      have h1 : MeasurableSet {u : ℝ | x j < lo + len * u} := measurableSet_lt measurable_const hf
      have h2 : MeasurableSet {u : ℝ | lo + len * u ≤ gapUp x j} :=
        measurableSet_le hf measurable_const
      exact h1.inter h2
    have hpt : ∀ v : ℝ × ℝ, g (typeVec x (argActionStep R z (.inr i) v).1) =
        g n + ∑ j, (Prod.snd ⁻¹' T j).indicator (fun _ => Δ j) v := by
      intro v
      change g (typeVec x (atTime _ (splitSuccessor z.1 i (lo + len * v.2)))) = _
      rw [typeVec_atTime, typeVec_splitSuccessor x z.1 i (lo + len * v.2)]
      have h0' : ∀ U, unitVec (∅ : Finset (Fin m)) U = 0 := h0
      rcases exists_gap_or_trivial hx (lo + len * v.2) with ⟨j0, hj0⟩ | hall | hall
      · have hrest : ∀ j ∈ (univ : Finset (Fin m)), j ≠ j0 →
            (Prod.snd ⁻¹' T j).indicator (fun _ => Δ j) v = 0 := by
          intro j _ hj
          refine Set.indicator_of_notMem ?_ _
          intro hv
          have hv' : x j < lo + len * v.2 ∧ lo + len * v.2 ≤ gapUp x j := hv
          exact hj (gap_unique hx hv' hj0)
        have hin : v ∈ Prod.snd ⁻¹' T j0 := hj0
        rw [Finset.sum_eq_single j0 hrest (fun h => absurd (Finset.mem_univ j0) h),
          Set.indicator_of_mem hin, filter_lt_eq_cutL hx hj0, filter_le_eq_cutR hx hj0]
        change g (splitVec n (τ i) j0) = g n + (g (splitVec n (τ i) j0) - g n)
        ring
      · have hz : ∑ j, (Prod.snd ⁻¹' T j).indicator (fun _ => Δ j) v = 0 := by
          refine Finset.sum_eq_zero fun j _ => Set.indicator_of_notMem ?_ _
          intro hv
          have hv' : x j < lo + len * v.2 ∧ lo + len * v.2 ≤ gapUp x j := hv
          exact (not_le.2 hv'.1) (hall j)
        have hL : (carrierSet x (z.1.2.2.2 i).2).filter (fun k => x k < lo + len * v.2) = ∅ :=
          Finset.filter_false_of_mem fun k _ => not_lt.2 (hall k)
        have hR' : (carrierSet x (z.1.2.2.2 i).2).filter (fun k => lo + len * v.2 ≤ x k) =
            carrierSet x (z.1.2.2.2 i).2 :=
          Finset.filter_true_of_mem fun k _ => hall k
        rw [hz, add_zero, hL, hR']
        change g (n - unitVec (τ i) + unitVec ∅ + unitVec (τ i)) = g n
        congr 1
        funext U
        simp only [Pi.add_apply, Pi.sub_apply, h0']
        have := huS i U
        omega
      · have hup : ∀ j, gapUp x j < lo + len * v.2 := fun j => by
          unfold gapUp
          split_ifs <;> exact hall _
        have hz : ∑ j, (Prod.snd ⁻¹' T j).indicator (fun _ => Δ j) v = 0 := by
          refine Finset.sum_eq_zero fun j _ => Set.indicator_of_notMem ?_ _
          intro hv
          have hv' : x j < lo + len * v.2 ∧ lo + len * v.2 ≤ gapUp x j := hv
          exact (not_le.2 (hup j)) hv'.2
        have hL : (carrierSet x (z.1.2.2.2 i).2).filter (fun k => x k < lo + len * v.2) =
            carrierSet x (z.1.2.2.2 i).2 :=
          Finset.filter_true_of_mem fun k _ => hall k
        have hR' : (carrierSet x (z.1.2.2.2 i).2).filter (fun k => lo + len * v.2 ≤ x k) = ∅ :=
          Finset.filter_false_of_mem fun k _ => not_le.2 (hall k)
        rw [hz, add_zero, hL, hR']
        change g (n - unitVec (τ i) + unitVec (τ i) + unitVec ∅) = g n
        congr 1
        funext U
        simp only [Pi.add_apply, Pi.sub_apply, h0']
        have := huS i U
        omega
    have hint : ∀ j, Integrable ((Prod.snd ⁻¹' T j).indicator (fun _ : ℝ × ℝ => Δ j))
        (unitUniform.prod unitUniform) :=
      fun j => (integrable_const _).indicator ((hTm j).preimage measurable_snd)
    have hreal : ∀ j, (unitUniform.prod unitUniform).real (Prod.snd ⁻¹' T j) =
        unitUniform.real (T j) := by
      intro j
      rw [measureReal_def, measureReal_def, ← Measure.map_apply measurable_snd (hTm j), hsnd]
    have hI : ∫ v, g (typeVec x (argActionStep R z (.inr i) v).1) ∂(unitUniform.prod unitUniform) =
        g n + ∑ j, Δ j * unitUniform.real (T j) := by
      rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_add (integrable_const _)
        (integrable_finsetSum _ fun j _ => hint j), integral_const, probReal_univ, one_smul,
        integral_finsetSum _ fun j _ => hint j]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_indicator_const _ ((hTm j).preimage measurable_snd), hreal, smul_eq_mul,
        mul_comm]
    rw [hI, show ∀ a b : ℝ, a + b - a = b from fun a b => by ring,
      candidateRate_split_eq false R hR, ← hlen, Finset.mul_sum]
    simp only [hF]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hC : (cutL (τ i) j).Nonempty ∧ (cutR (τ i) j).Nonempty
    · rw [ite_eq_left hC]
      obtain ⟨⟨k1, hk1⟩, ⟨k2, hk2⟩⟩ := hC
      rw [cutL, Finset.mem_filter] at hk1
      rw [cutR, Finset.mem_filter] at hk2
      have hc1 : materialContains (z.1.2.2.2 i).2 (x k1) := by
        have := hk1.1
        simpa [hτ, carrierSet] using this
      have hc2 : materialContains (z.1.2.2.2 i).2 (x k2) := by
        have := hk2.1
        simpa [hτ, carrierSet] using this
      have hlo1 : lo ≤ x k1 := hullLo_le_of_materialContains _ _ hc1
      have hhi2 : x k2 < hullHi (z.1.2.2.2 i).2 := lt_hullHi_of_materialContains _ _ hc2
      have hxj : x k1 ≤ x j := hx.monotone hk1.2
      have hup : gapUp x j ≤ x k2 := le_gapUp_of_lt hx hk2.2
      have hjup : x j ≤ gapUp x j := by
        have := gapLen_nonneg hx.monotone j
        rw [gapLen_eq_gapUp_sub] at this
        linarith
      have hpos : 0 < hullHi (z.1.2.2.2 i).2 - lo := by linarith
      have hlenpos : 0 < len := by
        rw [hlen, hullLength]
        exact lt_max_of_lt_right hpos
      have hleneq : len = hullHi (z.1.2.2.2 i).2 - lo := by
        rw [hlen, hullLength]
        exact max_eq_right hpos.le
      have hmass : unitUniform.real (T j) = (gapUp x j - x j) / len :=
        unitUniform_real_affine_cut lo len (x j) (gapUp x j) hlenpos (by linarith) hjup
          (by linarith)
      have hlen0 : len ≠ 0 := hlenpos.ne'
      have key : len * ((gapUp x j - x j) / len) = gapUp x j - x j := by
        rw [← mul_div_assoc, mul_div_cancel_left₀ _ hlen0]
      rw [hmass, gapLen_eq_gapUp_sub]
      simp only [hΔ]
      linear_combination (R / 2 * (g (splitVec n (τ i) j) - g n)) * key
    · rw [ite_eq_right hC, zero_mul]
      have hΔ0 : Δ j = 0 := by
        simp only [hΔ]
        rw [splitVec_eq_self (huS i) hC, sub_self]
      rw [hΔ0, zero_mul, mul_zero]
  have hc : ∀ t : Finset (Fin m), t.Nonempty →
      ((Finset.univ.filter fun i => τ i = t).card : ℝ) = (n t : ℝ) := by
    intro t ht
    simp only [hn, hτ, typeVec, ht, ↓reduceIte, materialCount]
    try congr
  rw [Finset.sum_congr rfl fun i _ => hterm i, sum_comp_type_eq τ F]
  simp only [types, Finset.sum_filter]
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases ht : t.Nonempty
  · rw [ite_eq_left ht, hc t ht]
    simp only [hF, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> ring
  · rw [ite_eq_right ht, Finset.not_nonempty_iff_eq_empty.1 ht]
    have hne : ∀ j : Fin m, ¬ ((cutL (∅ : Finset (Fin m)) j).Nonempty ∧
        (cutR (∅ : Finset (Fin m)) j).Nonempty) := fun j h => by simp [cutL] at h
    simp only [hF]
    refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun j _ => ?_)
    rw [ite_eq_right (hne j), zero_mul]

open SmcSupport in
theorem totalRate_mul_eventKernel_sub_eq_multiGen (R : ℝ) (hR : 0 ≤ R) (x : Fin m → ℝ)
    (hx : StrictMono x) (z : AugmentedState) (hm : 2 ≤ z.1.2.2.1) (g : MCounts m → ℝ)
    (hg : ∃ C, ∀ n, |g n| ≤ C) :
    (totalRate false R z.1 : ℝ) *
        (∫ w, g (typeVec x w.1) ∂eventKernel false R z - g (typeVec x z.1)) =
      multiGen (fun j => R * gapLen x j) g (typeVec x z.1) := by
  classical
  obtain ⟨C, hC⟩ := hg
  have htpos := unrestricted_totalRate_positive R z.1 hm
  have ht : 0 < (totalRate false R z.1 : ℝ) := by exact_mod_cast htpos
  have hΦ : Measurable fun w : AugmentedState => g (typeVec x w.1) :=
    (measurable_of_countable g).comp ((typeVec_measurable x).comp measurable_fst)
  have hbound : ∀ (μ : Measure AugmentedState) [IsFiniteMeasure μ],
      Integrable (fun w : AugmentedState => g (typeVec x w.1)) μ := fun μ _ =>
    Integrable.of_bound hΦ.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun w => by
        rw [Real.norm_eq_abs]
        exact hC _)
  have hmix : ∫ w, g (typeVec x w.1) ∂eventKernel false R z =
      ∑ a : ActionIndex z.1,
        (candidateRate false R z.1 a : ℝ) / (totalRate false R z.1 : ℝ) *
          ∫ v, g (typeVec x (argActionStep R z a v).1) ∂(unitUniform.prod unitUniform) := by
    rw [eventKernel_ARG_action_mixture R z (by omega), integral_finsetSum_measure]
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [integral_smul_measure,
        integral_map (argActionStep_measurable R z a).aemeasurable hΦ.aestronglyMeasurable,
        ENNReal.toReal_ofReal (div_nonneg (NNReal.coe_nonneg _) ht.le), smul_eq_mul]
    · intro a _
      exact (hbound _).smul_measure ENNReal.ofReal_ne_top
  have hsumrate : ∑ a : ActionIndex z.1, (candidateRate false R z.1 a : ℝ) =
      (totalRate false R z.1 : ℝ) := by
    simp [totalRate]
  have hkey : ∑ a : ActionIndex z.1, (candidateRate false R z.1 a : ℝ) *
      (∫ v, g (typeVec x (argActionStep R z a v).1) ∂(unitUniform.prod unitUniform) -
        g (typeVec x z.1)) = multiGen (fun j => R * gapLen x j) g (typeVec x z.1) := by
    rw [Fintype.sum_sum_type, multiGen]
    exact congrArg₂ (· + ·) (multi_pairPart R x z g) (multi_splitPart R hR x hx z g)
  rw [hmix, ← hkey]
  have hexp : ∑ a : ActionIndex z.1,
      (candidateRate false R z.1 a : ℝ) / (totalRate false R z.1 : ℝ) *
        ∫ v, g (typeVec x (argActionStep R z a v).1) ∂(unitUniform.prod unitUniform) =
      (∑ a : ActionIndex z.1, (candidateRate false R z.1 a : ℝ) *
          (∫ v, g (typeVec x (argActionStep R z a v).1) ∂(unitUniform.prod unitUniform) -
            g (typeVec x z.1))) / (totalRate false R z.1 : ℝ) +
        g (typeVec x z.1) * ((∑ a : ActionIndex z.1, (candidateRate false R z.1 a : ℝ)) /
          (totalRate false R z.1 : ℝ)) := by
    rw [Finset.sum_div, Finset.sum_div, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  rw [hexp, hsumrate, div_self ht.ne', mul_one, add_sub_cancel_right]
  field_simp

def mcost (lam : Fin m → ℕ) (n : MCounts m) : ℕ :=
  ∑ k, if 2 ≤ carriers n k then lam k else 0

def multiPsi (d : Fin m → ℝ) (hd : ∀ j, 0 ≤ d j) (N : ℕ) (lam : Fin m → ℕ) : MBox m N → ℝ :=
  (multiChain d hd N).laplace fun b => (mcost lam (mboxVal b) : ℝ)

theorem carriers_add (a c : MCounts m) (k : Fin m) :
    carriers (a + c) k = carriers a k + carriers c k := by
  unfold carriers
  simp only [Pi.add_apply]
  exact Finset.sum_add_distrib

theorem carriers_unitVec (S : Finset (Fin m)) (k : Fin m) :
    carriers (unitVec S) k = if k ∈ S then 1 else 0 := by
  unfold carriers unitVec
  by_cases hk : k ∈ S
  · rw [Finset.sum_eq_single_of_mem S (Finset.mem_filter.2 ⟨Finset.mem_univ _, hk⟩)]
    · rw [ite_eq_left ⟨rfl, ⟨k, hk⟩⟩, ite_eq_left hk]
    · intro U _ hU
      exact ite_eq_right fun h => hU h.1
  · rw [ite_eq_right hk]
    refine Finset.sum_eq_zero fun U hU => ?_
    have hkU : k ∈ U := (Finset.mem_filter.1 hU).2
    exact ite_eq_right fun h : U = S ∧ S.Nonempty => hk (h.1 ▸ hkU)

theorem unitVec_le {n : MCounts m} {S : Finset (Fin m)} (h : 1 ≤ n S) (U : Finset (Fin m)) :
    unitVec S U ≤ n U := by
  unfold unitVec
  split_ifs with hU
  · rw [hU.1]
    exact h
  · exact Nat.zero_le _

theorem carriers_sub_unitVec_add {n : MCounts m} {S : Finset (Fin m)}
    (h : ∀ U, unitVec S U ≤ n U) (k : Fin m) :
    carriers (n - unitVec S) k + (if k ∈ S then 1 else 0) = carriers n k := by
  rw [← carriers_unitVec, ← carriers_add]
  congr 1
  funext U
  simp only [Pi.add_apply, Pi.sub_apply]
  exact Nat.sub_add_cancel (h U)

theorem carriers_mergeVec_le {n : MCounts m} {S T : Finset (Fin m)} (hS : 1 ≤ n S)
    (hT : 1 + (if S = T then 1 else 0) ≤ n T) (k : Fin m) :
    carriers (mergeVec n S T) k ≤ carriers n k := by
  have h1 := carriers_sub_unitVec_add (unitVec_le hS) k
  have hT' : 1 ≤ (n - unitVec S) T := by
    change 1 ≤ n T - unitVec S T
    by_cases e : S = T
    · subst e
      rw [ite_eq_left rfl] at hT
      have : unitVec S S ≤ 1 := by
        unfold unitVec
        split_ifs <;> omega
      omega
    · rw [ite_eq_right e] at hT
      have : unitVec S T = 0 := by
        unfold unitVec
        rw [ite_eq_right fun h => e h.1.symm]
      omega
  have h2 := carriers_sub_unitVec_add (unitVec_le hT') k
  have h3 : carriers (mergeVec n S T) k = carriers (n - unitVec S - unitVec T) k +
      (if k ∈ S ∪ T then 1 else 0) := by
    rw [mergeVec, carriers_add, carriers_unitVec]
  have hu : (if k ∈ S ∪ T then 1 else 0) ≤
      (if k ∈ S then 1 else 0) + (if k ∈ T then 1 else 0) := by
    by_cases hkS : k ∈ S <;> by_cases hkT : k ∈ T <;> simp [hkS, hkT]
  omega

theorem carriers_splitVec {n : MCounts m} {S : Finset (Fin m)} (hS : 1 ≤ n S) (j k : Fin m) :
    carriers (splitVec n S j) k = carriers n k := by
  have h1 := carriers_sub_unitVec_add (unitVec_le hS) k
  rw [splitVec, carriers_add, carriers_add, carriers_unitVec, carriers_unitVec]
  have hc : (if k ∈ cutL S j then 1 else 0) + (if k ∈ cutR S j then 1 else 0) =
      (if k ∈ S then 1 else 0) := by
    unfold cutL cutR
    simp only [Finset.mem_filter]
    by_cases hkS : k ∈ S
    · by_cases hkj : k ≤ j
      · rw [ite_eq_left ⟨hkS, hkj⟩, ite_eq_right fun h => absurd h.2 (not_lt.2 hkj),
          ite_eq_left hkS]
      · rw [ite_eq_right fun h => hkj h.2, ite_eq_left ⟨hkS, not_le.1 hkj⟩, ite_eq_left hkS]
    · rw [ite_eq_right fun h => hkS h.1, ite_eq_right fun h => hkS h.1, ite_eq_right hkS]
  omega

theorem carriers_le_of_multiRate_ne_zero {d : Fin m → ℝ} {b b' : MBox m N}
    (h : multiRate d b b' ≠ 0) (hbb' : b ≠ b') (k : Fin m) :
    carriers (mboxVal b') k ≤ carriers (mboxVal b) k := by
  unfold multiRate multiGen at h
  have h0 : (if mboxVal b = mboxVal b' then (1 : ℝ) else 0) = 0 :=
    ite_eq_right fun e => hbb' (mboxVal_injective e)
  simp only [h0, sub_zero] at h
  have hor : ∀ a c : ℝ, a + c ≠ 0 → a ≠ 0 ∨ c ≠ 0 := fun a c hac => by
    by_contra hh
    push Not at hh
    exact hac (by rw [hh.1, hh.2, add_zero])
  rcases hor _ _ h with hA | hB
  · obtain ⟨S, -, hS'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hA
    obtain ⟨T, -, hT⟩ := Finset.exists_ne_zero_of_sum_ne_zero hS'
    have he : mergeVec (mboxVal b) S T = mboxVal b' := by
      by_contra he
      rw [ite_eq_right he, mul_zero] at hT
      exact hT rfl
    rw [ite_eq_left he, mul_one] at hT
    have hS0 : (mboxVal b S : ℝ) ≠ 0 := fun e => hT (by rw [e]; ring)
    have hT0 : (mboxVal b T : ℝ) - (if S = T then 1 else 0) ≠ 0 := fun e => hT (by rw [e]; ring)
    have hS1 : 1 ≤ mboxVal b S := by
      have : mboxVal b S ≠ 0 := fun e => hS0 (by rw [e]; simp)
      omega
    have hT1 : 1 + (if S = T then 1 else 0) ≤ mboxVal b T := by
      by_cases e : S = T
      · subst e
        rw [ite_eq_left rfl] at hT0 ⊢
        have h1 : (mboxVal b S : ℝ) ≠ 1 := fun e' => hT0 (by rw [e']; norm_num)
        have h2 : mboxVal b S ≠ 1 := fun e' => h1 (by rw [e']; simp)
        omega
      · rw [ite_eq_right e] at hT0 ⊢
        have : mboxVal b T ≠ 0 := fun e' => hT0 (by rw [e']; simp)
        omega
    rw [← he]
    exact carriers_mergeVec_le hS1 hT1 k
  · obtain ⟨S, -, hS'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hB
    obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hS'
    have he : splitVec (mboxVal b) S j = mboxVal b' := by
      by_contra he
      rw [ite_eq_right he, mul_zero] at hj
      exact hj rfl
    have hS1 : 1 ≤ mboxVal b S := by
      by_contra hlt
      have e : mboxVal b S = 0 := by omega
      apply hj
      rw [e]
      simp
    rw [← he]
    exact (carriers_splitVec hS1 j k).le

abbrev Mv (m : ℕ) := (Finset (Fin m) × Finset (Fin m)) ⊕ (Finset (Fin m) × Fin m)

def moves (m : ℕ) : Finset (Mv m) := (types m ×ˢ types m).disjSum (types m ×ˢ univ)

def mcoef (d : Fin m → ℝ) (n : MCounts m) : Mv m → ℝ :=
  Sum.elim (fun p => (n p.1 : ℝ) * ((n p.2 : ℝ) - if p.1 = p.2 then 1 else 0) / 2)
    (fun p => if (cutL p.1 p.2).Nonempty ∧ (cutR p.1 p.2).Nonempty then
      (n p.1 : ℝ) * (d p.2 / 2) else 0)

def mtgt (n : MCounts m) : Mv m → MCounts m :=
  Sum.elim (fun p => mergeVec n p.1 p.2) (fun p => splitVec n p.1 p.2)

theorem multiGen_eq_sum (d : Fin m → ℝ) (g : MCounts m → ℝ) (n : MCounts m) :
    multiGen d g n = ∑ μ ∈ moves m, mcoef d n μ * (g (mtgt n μ) - g n) := by
  rw [moves, Finset.sum_disjSum, Finset.sum_product, Finset.sum_product]
  all_goals rfl

theorem sum_multiChain_Q_mul_eq (d : Fin m → ℝ) (hd : ∀ j, 0 ≤ d j) (b : MBox m N)
    (f : MBox m N → ℝ) :
    ∑ b', (multiChain d hd N).Q b b' * f b' = ∑ b', multiRate d b b' * (f b' - f b) := by
  have hdiag : (multiChain d hd N).Q b b = -∑ b'' ∈ univ.erase b, multiRate d b b'' :=
    ite_eq_left rfl
  have hoff : ∀ b' ∈ univ.erase b, (multiChain d hd N).Q b b' = multiRate d b b' :=
    fun b' hb' => ite_eq_right (Ne.symm (Finset.ne_of_mem_erase hb'))
  have hL : ∑ b', (multiChain d hd N).Q b b' * f b' = (multiChain d hd N).Q b b * f b +
      ∑ b' ∈ univ.erase b, (multiChain d hd N).Q b b' * f b' :=
    (Finset.add_sum_erase univ (fun b' => (multiChain d hd N).Q b b' * f b') (mem_univ b)).symm
  have hR : ∑ b', multiRate d b b' * (f b' - f b) = multiRate d b b * (f b - f b) +
      ∑ b' ∈ univ.erase b, multiRate d b b' * (f b' - f b) :=
    (Finset.add_sum_erase univ (fun b' => multiRate d b b' * (f b' - f b)) (mem_univ b)).symm
  have hE : ∑ b' ∈ univ.erase b, (multiChain d hd N).Q b b' * f b' =
      ∑ b' ∈ univ.erase b, multiRate d b b' * f b' :=
    Finset.sum_congr rfl fun b' hb' => by rw [hoff b' hb']
  rw [hL, hR, hE, hdiag, sub_self, mul_zero, zero_add]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  ring

theorem exists_mboxVal_of_carriers_le {t : MCounts m} (hc : ∀ k, carriers t k ≤ N)
    (h0 : t ∅ ≤ N) : ∃ b0 : MBox m N, mboxVal b0 = t := by
  have hlt : ∀ S, t S < N + 1 := by
    intro S
    rcases S.eq_empty_or_nonempty with hS | ⟨k, hk⟩
    · rw [hS]
      omega
    · have h1 : t S ≤ carriers t k := by
        unfold carriers
        exact Finset.single_le_sum (f := fun U => t U) (fun _ _ => Nat.zero_le _)
          (Finset.mem_filter.2 ⟨Finset.mem_univ _, hk⟩)
      have h2 := hc k
      omega
  exact ⟨fun S => ⟨t S, hlt S⟩, rfl⟩

theorem mergeVec_empty (n : MCounts m) (S T : Finset (Fin m)) : mergeVec n S T ∅ = n ∅ := by
  simp only [mergeVec, Pi.add_apply, Pi.sub_apply, unitVec_apply_empty, Nat.sub_zero, add_zero]

theorem splitVec_empty (n : MCounts m) (S : Finset (Fin m)) (j : Fin m) :
    splitVec n S j ∅ = n ∅ := by
  simp only [splitVec, Pi.add_apply, Pi.sub_apply, unitVec_apply_empty, Nat.sub_zero, add_zero]

theorem merge_counts_of_ne_zero {n : MCounts m} {S T : Finset (Fin m)}
    (hT : (n S : ℝ) * ((n T : ℝ) - if S = T then 1 else 0) / 2 ≠ 0) :
    1 ≤ n S ∧ 1 + (if S = T then 1 else 0) ≤ n T := by
  have hS0 : (n S : ℝ) ≠ 0 := fun e => hT (by rw [e]; ring)
  have hT0 : (n T : ℝ) - (if S = T then 1 else 0) ≠ 0 := fun e => hT (by rw [e]; ring)
  have hS1 : 1 ≤ n S := by
    have : n S ≠ 0 := fun e => hS0 (by rw [e]; simp)
    omega
  refine ⟨hS1, ?_⟩
  by_cases e : S = T
  · subst e
    rw [ite_eq_left rfl] at hT0 ⊢
    have h1 : (n S : ℝ) ≠ 1 := fun e' => hT0 (by rw [e']; norm_num)
    have h2 : n S ≠ 1 := fun e' => h1 (by rw [e']; simp)
    omega
  · rw [ite_eq_right e] at hT0 ⊢
    have : n T ≠ 0 := fun e' => hT0 (by rw [e']; simp)
    omega

theorem split_count_of_ne_zero {n : MCounts m} {d : Fin m → ℝ} {S : Finset (Fin m)} {j : Fin m}
    (h : (if (cutL S j).Nonempty ∧ (cutR S j).Nonempty then (n S : ℝ) * (d j / 2) else 0) ≠ 0) :
    1 ≤ n S := by
  by_contra hlt
  have e : n S = 0 := by omega
  apply h
  rw [e]
  simp

theorem mtgt_mem_box {d : Fin m → ℝ} {b : MBox m N} (hb : ∀ k, carriers (mboxVal b) k ≤ N)
    (μ : Mv m) (hc : mcoef d (mboxVal b) μ ≠ 0) :
    ∃ b0 : MBox m N, mboxVal b0 = mtgt (mboxVal b) μ := by
  have h0 : mboxVal b ∅ ≤ N := Nat.lt_succ_iff.1 (b ∅).isLt
  rcases μ with ⟨S, T⟩ | ⟨S, j⟩
  · change (mboxVal b S : ℝ) * ((mboxVal b T : ℝ) - if S = T then 1 else 0) / 2 ≠ 0 at hc
    obtain ⟨hS1, hT1⟩ := merge_counts_of_ne_zero hc
    change ∃ b0 : MBox m N, mboxVal b0 = mergeVec (mboxVal b) S T
    refine exists_mboxVal_of_carriers_le
      (fun k => (carriers_mergeVec_le hS1 hT1 k).trans (hb k)) ?_
    rw [mergeVec_empty]
    exact h0
  · change (if (cutL S j).Nonempty ∧ (cutR S j).Nonempty then (mboxVal b S : ℝ) * (d j / 2)
      else 0) ≠ 0 at hc
    have hS1 := split_count_of_ne_zero hc
    change ∃ b0 : MBox m N, mboxVal b0 = splitVec (mboxVal b) S j
    refine exists_mboxVal_of_carriers_le
      (fun k => (carriers_splitVec hS1 j k).le.trans (hb k)) ?_
    rw [splitVec_empty]
    exact h0

theorem sum_multiChain_Q_mul (d : Fin m → ℝ) (hd : ∀ j, 0 ≤ d j) {b : MBox m N}
    (hb : ∀ k, carriers (mboxVal b) k ≤ N) (g : MCounts m → ℝ) :
    ∑ b', (multiChain d hd N).Q b b' * g (mboxVal b') = multiGen d g (mboxVal b) := by
  classical
  rw [sum_multiChain_Q_mul_eq d hd b (fun b' => g (mboxVal b')), multiGen_eq_sum]
  have hrate : ∀ b', multiRate d b b' = ∑ μ ∈ moves m, mcoef d (mboxVal b) μ *
      ((if mtgt (mboxVal b) μ = mboxVal b' then 1 else 0) -
        (if mboxVal b = mboxVal b' then 1 else 0)) := fun b' => by
    rw [multiRate, multiGen_eq_sum]
  simp only [hrate, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have hdrop : ∀ b' : MBox m N, mcoef d (mboxVal b) μ *
      ((if mtgt (mboxVal b) μ = mboxVal b' then (1 : ℝ) else 0) -
        (if mboxVal b = mboxVal b' then 1 else 0)) * (g (mboxVal b') - g (mboxVal b)) =
      mcoef d (mboxVal b) μ * ((if mtgt (mboxVal b) μ = mboxVal b' then (1 : ℝ) else 0) *
        (g (mboxVal b') - g (mboxVal b))) := fun b' => by
    by_cases h : mboxVal b = mboxVal b'
    · rw [← h]
      ring
    · rw [ite_eq_right h]
      ring
  simp only [hdrop, ← Finset.mul_sum]
  by_cases hc : mcoef d (mboxVal b) μ = 0
  · rw [hc, zero_mul, zero_mul]
  · obtain ⟨b0, hb0⟩ := mtgt_mem_box hb μ hc
    congr 1
    have hiff : ∀ b', (mtgt (mboxVal b) μ = mboxVal b') ↔ b0 = b' := fun b' => by
      rw [← hb0]
      exact mboxVal_injective.eq_iff
    simp only [hiff, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
      ↓reduceIte, hb0]

theorem multiGen_eq_zero_of_rate_eq_zero (d : Fin m → ℝ) (hd : ∀ j, 0 ≤ d j) {b : MBox m N}
    (hb : ∀ k, carriers (mboxVal b) k ≤ N) (h0 : (multiChain d hd N).rate b = 0)
    (g : MCounts m → ℝ) : multiGen d g (mboxVal b) = 0 := by
  have hQ : ∀ b', (multiChain d hd N).Q b b' = 0 := by
    have hsum := (multiChain d hd N).rate_eq_sum b
    rw [h0] at hsum
    have hz := (Finset.sum_eq_zero_iff_of_nonneg fun b' hb' =>
      (multiChain d hd N).off_diag_nonneg b b' (Finset.ne_of_mem_erase hb').symm).1 hsum.symm
    intro b'
    by_cases hbb : b = b'
    · subst hbb
      have : (multiChain d hd N).Q b b = -(multiChain d hd N).rate b := by
        simp [RateChain.rate]
      rw [this, h0, neg_zero]
    · exact hz b' (Finset.mem_erase.2 ⟨Ne.symm hbb, mem_univ _⟩)
  rw [← sum_multiChain_Q_mul d hd hb g]
  simp [hQ]

theorem exists_two_carriers {n : MCounts m} {k : Fin m} (hk : 2 ≤ carriers n k) :
    ∃ S T : Finset (Fin m), k ∈ S ∧ k ∈ T ∧ 1 ≤ n S ∧ 1 + (if S = T then 1 else 0) ≤ n T := by
  unfold carriers at hk
  have hne : ∑ S ∈ univ.filter (fun S : Finset (Fin m) => k ∈ S), n S ≠ 0 := by omega
  obtain ⟨S, hS, hS0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have hkS : k ∈ S := (Finset.mem_filter.1 hS).2
  have hS0' : n S ≠ 0 := hS0
  by_cases h2 : 2 ≤ n S
  · refine ⟨S, S, hkS, hkS, by omega, ?_⟩
    rw [ite_eq_left rfl]
    omega
  · have hsplit : n S + ∑ x ∈ (univ.filter (fun S : Finset (Fin m) => k ∈ S)).erase S, n x =
        ∑ x ∈ univ.filter (fun S : Finset (Fin m) => k ∈ S), n x :=
      Finset.add_sum_erase _ (fun x => n x) hS
    have hne' : ∑ x ∈ (univ.filter (fun S : Finset (Fin m) => k ∈ S)).erase S, n x ≠ 0 := by
      omega
    obtain ⟨T, hT, hT0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne'
    have hT0' : n T ≠ 0 := hT0
    have hTS : T ≠ S := Finset.ne_of_mem_erase hT
    have hkT : k ∈ T := (Finset.mem_filter.1 (Finset.mem_of_mem_erase hT)).2
    refine ⟨S, T, hkS, hkT, by omega, ?_⟩
    rw [ite_eq_right (Ne.symm hTS)]
    omega

theorem one_le_sub_unitVec {n : MCounts m} {S T : Finset (Fin m)}
    (hT : 1 + (if S = T then 1 else 0) ≤ n T) : 1 ≤ (n - unitVec S) T := by
  change 1 ≤ n T - unitVec S T
  by_cases e : S = T
  · subst e
    rw [ite_eq_left rfl] at hT
    have : unitVec S S ≤ 1 := by
      unfold unitVec
      split_ifs <;> omega
    omega
  · rw [ite_eq_right e] at hT
    have : unitVec S T = 0 := by
      unfold unitVec
      rw [ite_eq_right fun h => e h.1.symm]
    omega

theorem carriers_mergeVec_lt {n : MCounts m} {S T : Finset (Fin m)} (hS : 1 ≤ n S)
    (hT : 1 + (if S = T then 1 else 0) ≤ n T) {k : Fin m} (hkS : k ∈ S) (hkT : k ∈ T) :
    carriers (mergeVec n S T) k < carriers n k := by
  have h1 := carriers_sub_unitVec_add (unitVec_le hS) k
  have h2 := carriers_sub_unitVec_add (unitVec_le (one_le_sub_unitVec hT)) k
  have h3 : carriers (mergeVec n S T) k = carriers (n - unitVec S - unitVec T) k +
      (if k ∈ S ∪ T then 1 else 0) := by
    rw [mergeVec, carriers_add, carriers_unitVec]
  rw [ite_eq_left hkS] at h1
  rw [ite_eq_left hkT] at h2
  rw [ite_eq_left (Finset.mem_union_left T hkS)] at h3
  omega

theorem carriers_le_one_of_rate_eq_zero (d : Fin m → ℝ) (hd : ∀ j, 0 ≤ d j) {b : MBox m N}
    (hb : ∀ k, carriers (mboxVal b) k ≤ N) (h0 : (multiChain d hd N).rate b = 0) (k : Fin m) :
    carriers (mboxVal b) k ≤ 1 := by
  by_contra hk
  obtain ⟨S, T, hkS, hkT, hS1, hT1⟩ := exists_two_carriers (n := mboxVal b) (k := k) (by omega)
  have hne : mergeVec (mboxVal b) S T ≠ mboxVal b := fun e => by
    have := carriers_mergeVec_lt hS1 hT1 hkS hkT
    rw [e] at this
    exact lt_irrefl _ this
  have hSt : S ∈ types m := Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨k, hkS⟩⟩
  have hTt : T ∈ types m := Finset.mem_filter.2 ⟨Finset.mem_univ _, ⟨k, hkT⟩⟩
  have hcoef : 0 < (mboxVal b S : ℝ) * ((mboxVal b T : ℝ) - if S = T then 1 else 0) / 2 := by
    by_cases e : S = T
    · subst e
      rw [ite_eq_left rfl] at hT1 ⊢
      have h2 : (2 : ℝ) ≤ (mboxVal b S : ℝ) := by exact_mod_cast hT1
      refine div_pos ?_ two_pos
      refine mul_pos ?_ ?_ <;> linarith
    · rw [ite_eq_right e] at hT1 ⊢
      have h1 : (1 : ℝ) ≤ (mboxVal b S : ℝ) := by exact_mod_cast hS1
      have h2 : (1 : ℝ) ≤ (mboxVal b T : ℝ) := by exact_mod_cast hT1
      refine div_pos ?_ two_pos
      refine mul_pos ?_ ?_ <;> linarith
  have hpos : 0 < multiGen d (fun t => if t = mboxVal b then (0 : ℝ) else 1) (mboxVal b) := by
    unfold multiGen
    simp only [↓reduceIte, sub_zero]
    refine add_pos_of_pos_of_nonneg ?_ ?_
    · refine Finset.sum_pos' (fun S' _ => Finset.sum_nonneg fun T' _ => ?_) ⟨S, hSt, ?_⟩
      · exact mul_nonneg (nat_mul_sub_ite_nonneg _ _ _ fun e => by rw [e])
          (by split_ifs <;> norm_num)
      · refine Finset.sum_pos' (fun T' _ => mul_nonneg
          (nat_mul_sub_ite_nonneg _ _ _ fun e => by rw [e]) (by split_ifs <;> norm_num))
          ⟨T, hTt, ?_⟩
        rw [ite_eq_right hne, mul_one]
        exact hcoef
    · refine Finset.sum_nonneg fun S' _ => Finset.sum_nonneg fun j _ => mul_nonneg ?_
        (by split_ifs <;> norm_num)
      split_ifs
      · exact mul_nonneg (Nat.cast_nonneg _) (div_nonneg (hd j) (by norm_num))
      · exact le_rfl
  rw [multiGen_eq_zero_of_rate_eq_zero d hd hb h0] at hpos
  exact lt_irrefl _ hpos

theorem mcost_mul_multiPsi_eq_multiGen (d : Fin m → ℝ) (hd : ∀ j, 0 ≤ d j) (lam : Fin m → ℕ)
    {b : MBox m N} (hb : ∀ k, carriers (mboxVal b) k ≤ N) :
    (mcost lam (mboxVal b) : ℝ) * multiPsi d hd N lam b =
      multiGen d (mboxExt (multiPsi d hd N lam)) (mboxVal b) := by
  by_cases h0 : (multiChain d hd N).rate b = 0
  · have hc : mcost lam (mboxVal b) = 0 := by
      unfold mcost
      exact Finset.sum_eq_zero fun k _ =>
        ite_eq_right (by have := carriers_le_one_of_rate_eq_zero d hd hb h0 k; omega)
    rw [hc, Nat.cast_zero, zero_mul, multiGen_eq_zero_of_rate_eq_zero d hd hb h0]
  · have h := (multiChain d hd N).mul_laplace_eq_generator
      (c := fun b' => (mcost lam (mboxVal b') : ℝ)) (fun b' => Nat.cast_nonneg _) h0
    rw [← sum_multiChain_Q_mul d hd hb]
    simp only [mboxExt_mboxVal]
    exact h

theorem multiPsi_eq_one (d : Fin m → ℝ) (hd : ∀ j, 0 ≤ d j) (lam : Fin m → ℕ) {b : MBox m N}
    (hb : ∀ k, carriers (mboxVal b) k ≤ 1) : multiPsi d hd N lam b = 1 := by
  classical
  set Z : Finset (MBox m N) := univ.filter fun b => ∀ k, carriers (mboxVal b) k ≤ 1 with hZ
  have hc : ∀ y : MBox m N, 0 ≤ (mcost lam (mboxVal y) : ℝ) := fun y => Nat.cast_nonneg _
  refine (multiChain d hd N).laplace_eq_one_of_isClosedSet hc (Z := Z) ?_ ?_
    (by simpa [hZ] using hb)
  · refine (multiChain d hd N).isClosedSet_jumpChain fun y hy y' hy' => ?_
    have hyy' : y ≠ y' := fun e => hy' (e ▸ hy)
    change (if y = y' then _ else multiRate d y y') = 0
    rw [ite_eq_right hyy']
    by_contra hne
    apply hy'
    simp only [hZ, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    exact fun k => (carriers_le_of_multiRate_ne_zero hne hyy' k).trans (hy k)
  · intro y hy
    simp only [hZ, Finset.mem_filter, Finset.mem_univ, true_and] at hy
    simp only [mcost, Nat.cast_eq_zero]
    exact Finset.sum_eq_zero fun k _ => ite_eq_right (by have := hy k; omega)

def multiSamplerCost (x : Fin m → ℝ) (lam : Fin m → ℕ) (s : State) : ℕ :=
  ∑ k, if 2 ≤ carrierCount (x k) s then lam k else 0

theorem multiSamplerCost_eq (x : Fin m → ℝ) (lam : Fin m → ℕ) (s : State) :
    multiSamplerCost x lam s = mcost lam (typeVec x s) := by
  unfold multiSamplerCost mcost
  simp only [carriers_typeVec]

def multiSamplerPsi (d : Fin m → ℝ) (hd : ∀ j, 0 ≤ d j) (N : ℕ) (x : Fin m → ℝ)
    (lam : Fin m → ℕ) (s : State) : ℝ :=
  mboxExt (multiPsi d hd N lam) (typeVec x s)

theorem multiSamplerCost_le (x : Fin m → ℝ) (lam : Fin m → ℕ) (s : State) :
    multiSamplerCost x lam s ≤ ∑ k, lam k := by
  unfold multiSamplerCost
  exact Finset.sum_le_sum fun k _ => by split_ifs <;> omega

theorem multiSamplerCost_measurable (x : Fin m → ℝ) (lam : Fin m → ℕ) :
    Measurable (multiSamplerCost x lam) := by
  have h : multiSamplerCost x lam = fun s => mcost lam (typeVec x s) :=
    funext (multiSamplerCost_eq x lam)
  rw [h]
  exact (measurable_of_countable (mcost lam)).comp (typeVec_measurable x)

theorem multiSamplerPsi_measurable (d : Fin m → ℝ) (hd : ∀ j, 0 ≤ d j) (N : ℕ)
    (x : Fin m → ℝ) (lam : Fin m → ℕ) : Measurable (multiSamplerPsi d hd N x lam) :=
  (measurable_of_countable (mboxExt (multiPsi d hd N lam))).comp (typeVec_measurable x)

theorem typeVec_empty (x : Fin m → ℝ) (s : State) : typeVec x s ∅ = 0 := by
  unfold typeVec
  simp

theorem probeReal_strictMono {q : Fin m → GenomicProbe} (hq : StrictMono q) :
    StrictMono (probeReal q) := fun _ _ h => Rat.cast_lt.2 (hq h)

theorem mboxExt_multiPsi_mem_Icc (d : Fin m → ℝ) (hd : ∀ j, 0 ≤ d j) (N : ℕ) (lam : Fin m → ℕ)
    (t : MCounts m) :
    0 ≤ mboxExt (multiPsi d hd N lam) t ∧ mboxExt (multiPsi d hd N lam) t ≤ 1 := by
  unfold mboxExt
  split_ifs
  · exact (multiChain d hd N).laplace_mem _ _
  · exact ⟨le_rfl, zero_le_one⟩

theorem eventKernel_discount_multiSamplerPsi (R : ℝ) (hR : 0 ≤ R) (q : Fin m → GenomicProbe)
    (hq : StrictMono q) (N : ℕ) (lam : Fin m → ℕ) (z : AugmentedState)
    (hz : ∀ k, carrierCount (probeReal q k) z.1 ≤ N) :
    ∫⁻ w, ENNReal.ofReal (Real.exp (-((multiSamplerCost (probeReal q) lam z.1 : ℝ) *
          (w.1.1 - z.1.1)))) *
        ENNReal.ofReal (multiSamplerPsi (gapRate R q) (gapRate_nonneg hR hq) N (probeReal q) lam
          w.1) ∂eventKernel false R z =
      ENNReal.ofReal (multiSamplerPsi (gapRate R q) (gapRate_nonneg hR hq) N (probeReal q) lam
        z.1) := by
  classical
  set ψ := multiSamplerPsi (gapRate R q) (gapRate_nonneg hR hq) N (probeReal q) lam with hψ
  set c : ℝ := (multiSamplerCost (probeReal q) lam z.1 : ℝ) with hcdef
  have hc : 0 ≤ c := Nat.cast_nonneg _
  have hψm : Measurable ψ := multiSamplerPsi_measurable _ _ N _ lam
  have hbd : ∀ s, 0 ≤ ψ s ∧ ψ s ≤ 1 := fun s =>
    mboxExt_multiPsi_mem_Icc _ _ N lam (typeVec (probeReal q) s)
  have hf : Measurable fun t : ℝ => ENNReal.ofReal (Real.exp (-(c * (t - z.1.1)))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      ((measurable_id.sub_const _).const_mul c).neg)
  have hg : Measurable fun s : State => ENNReal.ofReal (ψ s) := ENNReal.measurable_ofReal.comp hψm
  by_cases hm : 2 ≤ z.1.2.2.1
  · have ht : 0 < (totalRate false R z.1 : ℝ) := by
      exact_mod_cast Rhone.Coalescent.SmcSupport.unrestricted_totalRate_positive R z.1 hm
    rw [IntervalCounts.eventKernel_lintegral_time_mul R z hm hf hg (fun t s => rfl),
      IntervalCounts.lintegral_clockDiscount z.1.1 _ c ht hc]
    have hint : Integrable (fun w : AugmentedState => ψ w.1) (eventKernel false R z) :=
      (integrable_const (1 : ℝ)).mono' (hψm.comp measurable_fst).aestronglyMeasurable
        (ae_of_all _ fun w => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hbd _).1]
          exact (hbd _).2)
    rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun w => (hbd w.1).1),
      ← ENNReal.ofReal_mul (div_nonneg ht.le (by linarith))]
    congr 1
    have hgen := totalRate_mul_eventKernel_sub_eq_multiGen R hR (probeReal q)
      (probeReal_strictMono hq) z hm (mboxExt (multiPsi (gapRate R q) (gapRate_nonneg hR hq) N lam))
      ⟨1, fun t => by
        rw [abs_of_nonneg (mboxExt_multiPsi_mem_Icc _ _ N lam t).1]
        exact (mboxExt_multiPsi_mem_Icc _ _ N lam t).2⟩
    obtain ⟨b0, hb0⟩ := exists_mboxVal_of_carriers_le (N := N) (t := typeVec (probeReal q) z.1)
      (fun k => by rw [carriers_typeVec]; exact hz k)
      (by rw [typeVec_empty]; exact Nat.zero_le _)
    have heq := mcost_mul_multiPsi_eq_multiGen (gapRate R q) (gapRate_nonneg hR hq) lam (b := b0)
      (fun k => by rw [hb0, carriers_typeVec]; exact hz k)
    have hψz : ψ z.1 = multiPsi (gapRate R q) (gapRate_nonneg hR hq) N lam b0 := by
      rw [hψ, multiSamplerPsi, ← hb0, mboxExt_mboxVal]
    rw [hb0, ← multiSamplerCost_eq, ← hψz] at heq
    have hgen' : (totalRate false R z.1 : ℝ) * (∫ w, ψ w.1 ∂eventKernel false R z - ψ z.1) =
        c * ψ z.1 := by
      rw [hcdef, heq]
      exact hgen
    rw [div_mul_eq_mul_div, div_eq_iff (by linarith)]
    linear_combination hgen'
  · have hstep : ∀ u, sampleStep false R z.1 u = (z.1, (z.1.1, .inl ())) := fun u => by
      unfold sampleStep
      rw [ite_eq_left (Or.inl (by omega))]
    have hF : Measurable fun w : AugmentedState =>
        ENNReal.ofReal (Real.exp (-(c * (w.1.1 - z.1.1)))) * ENNReal.ofReal (ψ w.1) :=
      (hf.comp measurable_fst.fst).mul (hg.comp measurable_fst)
    have hs : Measurable fun u : Noise => sampleStep false R z.1 u :=
      (sampleStep_measurable false R).comp (measurable_const.prodMk measurable_id)
    rw [eventKernel_apply, lintegral_map hF hs]
    simp only [hstep, sub_self, mul_zero, neg_zero, Real.exp_zero, ENNReal.ofReal_one, one_mul,
      lintegral_const, measure_univ, mul_one]

def multiSamplerDiscount (x : Fin m → ℝ) (lam : Fin m → ℕ) (ω : EventPath) (n : ℕ) : ℝ≥0∞ :=
  ∏ l ∈ range n, ENNReal.ofReal (Real.exp
    (-((multiSamplerCost x lam (ω l).1 : ℝ) * ((ω (l + 1)).1.1 - (ω l).1.1))))

theorem multiSamplerDiscount_measurable (x : Fin m → ℝ) (lam : Fin m → ℕ) (n : ℕ) :
    Measurable[Filtration.piLE (X := fun _ : ℕ => AugmentedState) n]
      fun ω => multiSamplerDiscount x lam ω n := by
  have hev : ∀ k ≤ n, Measurable[Filtration.piLE (X := fun _ : ℕ => AugmentedState) n]
      fun ω : EventPath => ω k := fun k hk =>
    (DiscreteProcess.measurable_eval_piLE k).mono
      ((Filtration.piLE (X := fun _ : ℕ => AugmentedState)).mono hk) le_rfl
  have hc : Measurable fun s : State => (multiSamplerCost x lam s : ℝ) :=
    (measurable_of_countable (fun j : ℕ => (j : ℝ))).comp (multiSamplerCost_measurable x lam)
  unfold multiSamplerDiscount
  refine Finset.measurable_prod _ fun k hk => ?_
  have hk' : k + 1 ≤ n := Finset.mem_range.1 hk
  exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    ((hc.comp (measurable_fst.comp (hev k (by omega)))).mul
      ((measurable_fst.fst.comp (hev (k + 1) hk')).sub
        (measurable_fst.fst.comp (hev k (by omega))))).neg)

theorem multiDiscountFactor_eq_sum (x : Fin m → ℝ) (lam : Fin m → ℕ) (z w : AugmentedState)
    (p : ℝ) :
    ENNReal.ofReal (Real.exp (-((multiSamplerCost x lam z.1 : ℝ) * (w.1.1 - z.1.1)))) *
        ENNReal.ofReal p =
      ∑ j ∈ range (∑ k, lam k + 1),
        (if multiSamplerCost x lam z.1 = j then ENNReal.ofReal (Real.exp (j * z.1.1)) else 0) *
          (ENNReal.ofReal (Real.exp (-(j * w.1.1))) * ENNReal.ofReal p) := by
  rw [Finset.sum_eq_single (multiSamplerCost x lam z.1)]
  · rw [ite_eq_left rfl, ← mul_assoc]
    congr 1
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    ring
  · intro j _ hj
    rw [ite_eq_right_iff.2 fun h => absurd h.symm hj, zero_mul]
  · intro h
    exact absurd (Finset.mem_range.2 (Nat.lt_succ_of_le (multiSamplerCost_le x lam _))) h

theorem lintegral_multiSamplerDiscount_mul_multiSamplerPsi (R : ℝ) (hR : 0 ≤ R)
    (q : Fin m → GenomicProbe) (hq : StrictMono q) (N : ℕ) (lam : Fin m → ℕ) (n : ℕ) :
    ∫⁻ ω, multiSamplerDiscount (probeReal q) lam ω n *
        ENNReal.ofReal (multiSamplerPsi (gapRate R q) (gapRate_nonneg hR hq) N (probeReal q) lam
          (ω n).1) ∂(eventProcess false R).pathLaw (initialState N, (0, .inl ())) =
      ENNReal.ofReal (multiPsi (gapRate R q) (gapRate_nonneg hR hq) N lam (startBox m N)) := by
  classical
  set ψ := multiSamplerPsi (gapRate R q) (gapRate_nonneg hR hq) N (probeReal q) lam with hψ
  have hψm : Measurable fun s => ENNReal.ofReal (ψ s) :=
    ENNReal.measurable_ofReal.comp (multiSamplerPsi_measurable _ _ N _ lam)
  have hstart : ψ (initialState N) = multiPsi (gapRate R q) (gapRate_nonneg hR hq) N lam
      (startBox m N) := by
    rw [hψ, multiSamplerPsi, typeVec_initialState (probeReal q)
      (probeReal_nonneg q) (probeReal_lt_one q), mboxExt_mboxVal]
  rw [← hstart]
  have hbound : ∀ᵐ ω ∂(eventProcess false R).pathLaw (initialState N, (0, .inl ())),
      ∀ k, ∀ l, carrierCount (probeReal q k) (ω l).1 ≤ N := by
    rw [ae_all_iff]
    intro k
    filter_upwards [eventProcess_chronologicalAncestryPath N false R,
      eventProcess_twoSampleTransition R (initialState N, (0, .inl ())) (q k)] with ω h hqk l
    induction l with
    | zero =>
      rw [h.1]
      exact (carrierCount_initialState N _ (probeReal_nonneg q k) (probeReal_lt_one q k)).le
    | succ l ih => exact (hqk l).2.1.trans ih
  set a : ℕ → AugmentedState → ℝ≥0∞ := fun j z =>
    if multiSamplerCost (probeReal q) lam z.1 = j then
      ENNReal.ofReal (Real.exp (j * z.1.1)) else 0 with ha_def
  set b : ℕ → AugmentedState → ℝ≥0∞ := fun j w =>
    ENNReal.ofReal (Real.exp (-(j * w.1.1))) * ENNReal.ofReal (ψ w.1) with hb_def
  have ha : ∀ j, Measurable (a j) := fun j =>
    Measurable.ite ((multiSamplerCost_measurable _ lam).comp measurable_fst
      (measurableSet_singleton j))
      (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
        (measurable_fst.fst.const_mul _))) measurable_const
  have hb : ∀ j, Measurable (b j) := fun j =>
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (measurable_fst.fst.const_mul _).neg)).mul (hψm.comp measurable_fst)
  have hinner : ∀ z : AugmentedState,
      ∑ j ∈ range (∑ k, lam k + 1), a j z * ∫⁻ v, b j v ∂eventKernel false R z =
        ∫⁻ v, ENNReal.ofReal (Real.exp
          (-((multiSamplerCost (probeReal q) lam z.1 : ℝ) * (v.1.1 - z.1.1)))) *
            ENNReal.ofReal (ψ v.1) ∂eventKernel false R z := by
    intro z
    calc ∑ j ∈ range (∑ k, lam k + 1), a j z * ∫⁻ v, b j v ∂eventKernel false R z
        = ∑ j ∈ range (∑ k, lam k + 1), ∫⁻ v, a j z * b j v ∂eventKernel false R z :=
          Finset.sum_congr rfl fun j _ => (lintegral_const_mul _ (hb j)).symm
      _ = ∫⁻ v, ∑ j ∈ range (∑ k, lam k + 1), a j z * b j v ∂eventKernel false R z :=
          (lintegral_finsetSum _ fun j _ => measurable_const.mul (hb j)).symm
      _ = _ := lintegral_congr fun v => (multiDiscountFactor_eq_sum _ lam z v (ψ v.1)).symm
  induction n with
  | zero =>
    simp only [multiSamplerDiscount, Finset.range_zero, Finset.prod_empty, one_mul]
    have e := lintegral_map (μ := (eventProcess false R).pathLaw (initialState N, (0, .inl ())))
      (hψm.comp measurable_fst) (measurable_pi_apply 0)
    rw [(eventProcess false R).map_eval_zero, lintegral_dirac] at e
    exact e.symm
  | succ n ih =>
    have hsplit : ∀ ω : EventPath,
        multiSamplerDiscount (probeReal q) lam ω (n + 1) * ENNReal.ofReal (ψ (ω (n + 1)).1) =
          multiSamplerDiscount (probeReal q) lam ω n *
            ∑ j ∈ range (∑ k, lam k + 1), a j (ω n) * b j (ω (n + 1)) := fun ω => by
      simp only [multiSamplerDiscount, Finset.prod_range_succ]
      rw [mul_assoc]
      exact congrArg _ (multiDiscountFactor_eq_sum _ lam (ω n) (ω (n + 1)) _)
    rw [lintegral_congr hsplit, IntervalCounts.pathLaw_lintegral_mul_sum_eval_succ _ _ n _ ha hb
      (multiSamplerDiscount_measurable _ lam n)]
    refine (lintegral_congr_ae ?_).trans ih
    filter_upwards [hbound] with ω h1
    exact congrArg (multiSamplerDiscount (probeReal q) lam ω n * ·)
      ((hinner (ω n)).trans (eventKernel_discount_multiSamplerPsi R hR q hq N lam (ω n)
        fun k => h1 k n))

theorem multiSamplerPsi_eq_one (d : Fin m → ℝ) (hd : ∀ j, 0 ≤ d j) (N : ℕ) (x : Fin m → ℝ)
    (lam : Fin m → ℕ) {s : State} (hN : ∀ k, carrierCount (x k) s ≤ N)
    (h1 : ∀ k, carrierCount (x k) s ≤ 1) : multiSamplerPsi d hd N x lam s = 1 := by
  obtain ⟨b0, hb0⟩ := exists_mboxVal_of_carriers_le (N := N) (t := typeVec x s)
    (fun k => by rw [carriers_typeVec]; exact hN k) (by rw [typeVec_empty]; exact Nat.zero_le _)
  unfold multiSamplerPsi
  rw [← hb0, mboxExt_mboxVal]
  exact multiPsi_eq_one d hd lam fun k => by rw [hb0, carriers_typeVec]; exact h1 k

theorem multiSamplerPsi_le_one (d : Fin m → ℝ) (hd : ∀ j, 0 ≤ d j) (N : ℕ) (x : Fin m → ℝ)
    (lam : Fin m → ℕ) (s : State) : multiSamplerPsi d hd N x lam s ≤ 1 := by
  unfold multiSamplerPsi mboxExt
  split_ifs
  · exact ((multiChain d hd N).laplace_mem _ _).2
  · exact zero_le_one

theorem multiSamplerDiscount_eq_of_le (x : Fin m → ℝ) (lam : Fin m → ℕ) (ω : EventPath)
    (K : Fin m → ℕ) {n : ℕ} (hK : ∀ k l, 2 ≤ carrierCount (x k) (ω l).1 ↔ l < K k)
    (hn : ∀ k, K k ≤ n) :
    multiSamplerDiscount x lam ω n = ENNReal.ofReal (Real.exp
      (-(∑ k, (lam k : ℝ) * ((ω (K k)).1.1 - (ω 0).1.1)))) := by
  have hc : ∀ l, (multiSamplerCost x lam (ω l).1 : ℝ) =
      ∑ k, (if l < K k then (lam k : ℝ) else 0) := by
    intro l
    simp only [multiSamplerCost, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, hK]
  have hs : ∀ k, ∑ l ∈ range n, (if l < K k then (lam k : ℝ) else 0) *
      ((ω (l + 1)).1.1 - (ω l).1.1) = (lam k : ℝ) * ((ω (K k)).1.1 - (ω 0).1.1) := fun k =>
    IntervalCounts.sum_ite_lt_mul_sub (fun l => (ω l).1.1) _ (hn k)
  unfold multiSamplerDiscount
  rw [← ENNReal.ofReal_prod_of_nonneg fun l _ => (Real.exp_pos _).le, ← Real.exp_sum,
    Finset.sum_neg_distrib]
  simp_rw [hc, Finset.sum_mul]
  rw [Finset.sum_comm, Finset.sum_congr rfl fun k _ => hs k]

theorem lintegral_prod_expNeg_mrca (R : ℝ) (hR : 0 ≤ R) (q : Fin m → GenomicProbe)
    (hq : StrictMono q) (N : ℕ) (lam : Fin m → ℕ) :
    ∫⁻ ω, ∏ k, expNeg (⨆ i, ⨆ j, genealogyObservation N ω (q k) i j) ^ lam k
        ∂(eventProcess false R).pathLaw (initialState N, (0, .inl ())) =
      ENNReal.ofReal (multiPsi (gapRate R q) (gapRate_nonneg hR hq) N lam (startBox m N)) := by
  classical
  set ψ := multiSamplerPsi (gapRate R q) (gapRate_nonneg hR hq) N (probeReal q) lam with hψ
  have hψ0 : ψ (initialState N) = multiPsi (gapRate R q) (gapRate_nonneg hR hq) N lam
      (startBox m N) := by
    rw [hψ, multiSamplerPsi, typeVec_initialState (probeReal q)
      (probeReal_nonneg q) (probeReal_lt_one q), mboxExt_mboxVal]
  rw [← hψ0]
  set F : ℕ → EventPath → ℝ≥0∞ := fun n ω =>
    multiSamplerDiscount (probeReal q) lam ω n * ENNReal.ofReal (ψ (ω n).1) with hF
  have hmart : ∀ n, ∫⁻ ω, F n ω ∂(eventProcess false R).pathLaw (initialState N, (0, .inl ())) =
      ENNReal.ofReal (ψ (initialState N)) := fun n => by
    rw [hψ0]
    exact lintegral_multiSamplerDiscount_mul_multiSamplerPsi R hR q hq N lam n
  have hFm : ∀ n, Measurable (F n) := fun n =>
    ((multiSamplerDiscount_measurable (probeReal q) lam n).mono
      ((Filtration.piLE (X := fun _ : ℕ => AugmentedState)).le n) le_rfl).mul
      ((ENNReal.measurable_ofReal.comp (multiSamplerPsi_measurable _ _ N _ lam)).comp
        (measurable_fst.comp (measurable_pi_apply n)))
  have hgood := (eventProcess_chronologicalAncestryPath N false R).and
    ((ae_all_iff.2 fun k => eventProcess_twoSampleTransition R (initialState N, (0, .inl ()))
      (q k)).and
    ((ae_all_iff.2 fun k => eventProcess_labelMergeTransition R (initialState N, (0, .inl ()))
      (q k)).and
      (eventProcess_liveCount_reaches_one N R hR)))
  have hmono : ∀ ω : EventPath, ChronologicalAncestryPath N ω → Monotone fun k => (ω k).1.1 :=
    fun ω h => monotone_nat_of_le_succ fun k => (h.2 k).1
  have htime0 : ∀ ω : EventPath, ChronologicalAncestryPath N ω → (ω 0).1.1 = 0 := by
    intro ω h
    rw [h.1]
    rfl
  have hccN : ∀ ω : EventPath, ChronologicalAncestryPath N ω → ∀ k,
      (∀ l, twoSampleTransition (q k) (ω l, ω (l + 1))) →
        ∀ l, carrierCount (probeReal q k) (ω l).1 ≤ N := by
    intro ω h k hqk l
    induction l with
    | zero =>
      rw [h.1]
      exact (carrierCount_initialState N _ (probeReal_nonneg q k) (probeReal_lt_one q k)).le
    | succ l ih => exact (hqk l).2.1.trans ih
  have hbound : ∀ n, ∀ᵐ ω ∂(eventProcess false R).pathLaw (initialState N, (0, .inl ())),
      F n ω ≤ 1 := by
    intro n
    filter_upwards [hgood] with ω hω
    have h := hω.1
    refine mul_le_one' (Finset.prod_le_one fun l _ => ?_) (ENNReal.ofReal_le_one.2
      (multiSamplerPsi_le_one _ _ N _ lam _))
    refine ENNReal.ofReal_le_one.2 (Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg
      (Nat.cast_nonneg _) (sub_nonneg.2 ((h.2 l).1)))))
  have hlim : ∀ᵐ ω ∂(eventProcess false R).pathLaw (initialState N, (0, .inl ())),
      Filter.Tendsto (fun n => F n ω) Filter.atTop
        (nhds (∏ k, expNeg (⨆ i, ⨆ j, genealogyObservation N ω (q k) i j) ^ lam k)) := by
    filter_upwards [hgood] with ω hω
    obtain ⟨h, hts, hlm, hterm⟩ := hω
    choose K hbK hK1 hM using fun k => iSup_genealogyObservation_eq_time h (q k) (hts k)
      (hlm k) hterm
    have hanti : ∀ k, Antitone fun l => carrierCount (probeReal q k) (ω l).1 :=
      fun k => antitone_nat_of_succ_le fun l => (hts k l).2.1
    have hiff : ∀ k l, 2 ≤ carrierCount (probeReal q k) (ω l).1 ↔ l < K k := fun k l =>
      ⟨fun h2 => not_le.1 fun hl => by
        have : carrierCount (probeReal q k) (ω l).1 ≤ 1 := (hanti k hl).trans (hK1 k)
        omega,
        fun hl => hbK k l hl⟩
    have ht0 := htime0 ω h
    have htK : ∀ k, 0 ≤ (ω (K k)).1.1 := fun k => ht0 ▸ hmono ω h (Nat.zero_le (K k))
    refine tendsto_const_nhds.congr' (Filter.eventually_atTop.2 ⟨∑ k, K k, fun n hn => ?_⟩)
    have hnK : ∀ k, K k ≤ n := fun k =>
      (Finset.single_le_sum (f := K) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)).trans hn
    change _ = multiSamplerDiscount (probeReal q) lam ω n * ENNReal.ofReal (ψ (ω n).1)
    rw [multiSamplerDiscount_eq_of_le (probeReal q) lam ω K hiff hnK, hψ,
      multiSamplerPsi_eq_one _ _ N _ lam (fun k => hccN ω h k (hts k) n)
        (fun k => (hanti k (hnK k)).trans (hK1 k)),
      ENNReal.ofReal_one, mul_one, ← Finset.sum_neg_distrib, Real.exp_sum,
      ENNReal.ofReal_prod_of_nonneg fun k _ => (Real.exp_pos _).le]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [hM k, expNeg_ofReal (htK k), ht0, sub_zero, ← ENNReal.ofReal_pow (Real.exp_pos _).le,
      ← Real.exp_nat_mul]
    congr 2
    ring
  have hT := tendsto_lintegral_of_dominated_convergence (fun _ => (1 : ℝ≥0∞)) hFm hbound
    (by simp) hlim
  simp only [hmart] at hT
  exact (tendsto_nhds_unique hT tendsto_const_nhds)

theorem mcost_eq (lam : Fin m → ℕ) (b : MBox m N) :
    (mcost lam (mboxVal b) : ℝ) = ∑ k, (lam k : ℝ) * (if b ∈ lowSet m N k then 0 else 1) := by
  rw [mcost, Nat.cast_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hmem : b ∈ lowSet m N k ↔ carriers (mboxVal b) k ≤ 1 := by
    simp [lowSet]
  by_cases h : 2 ≤ carriers (mboxVal b) k
  · rw [ite_eq_left h, ite_eq_right (fun h' => by have := hmem.1 h'; omega)]
    simp
  · rw [ite_eq_right h, ite_eq_left (hmem.2 (by omega))]
    simp

theorem multi_discount_eq (C : RateChain (MBox m N)) (lam : Fin m → ℕ)
    (p : (ℕ → MBox m N) × (ℕ → ℝ)) (l : ℕ) (hp : 0 ≤ C.holdTime p l) :
    C.discount (fun b => (mcost lam (mboxVal b) : ℝ)) p l =
      ∏ k, expNeg (if p.1 l ∈ lowSet m N k then 0 else
        ENNReal.ofReal (1 * C.holdTime p l)) ^ lam k := by
  have key : ∀ k, (if p.1 l ∈ lowSet m N k then (0 : ℝ≥0∞) else
      ENNReal.ofReal (1 * C.holdTime p l)) =
        ENNReal.ofReal ((if p.1 l ∈ lowSet m N k then 0 else 1) * C.holdTime p l) := by
    intro k
    split_ifs <;> simp
  have hi : ∀ k, (0 : ℝ) ≤ if p.1 l ∈ lowSet m N k then 0 else 1 := by
    intro k
    split_ifs <;> norm_num
  have hreal : Real.exp (-max 0 ((mcost lam (mboxVal (p.1 l)) : ℝ) * C.holdTime p l)) =
      ∏ k, Real.exp (-((if p.1 l ∈ lowSet m N k then 0 else 1) * C.holdTime p l)) ^ lam k := by
    rw [mcost_eq, max_eq_right (mul_nonneg (Finset.sum_nonneg fun k _ =>
      mul_nonneg (Nat.cast_nonneg _) (hi k)) hp)]
    simp_rw [← Real.exp_nat_mul]
    rw [← Real.exp_sum]
    congr 1
    rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  change ENNReal.ofReal (Real.exp (-max 0 ((mcost lam (mboxVal (p.1 l)) : ℝ) *
    C.holdTime p l))) = _
  rw [hreal, ENNReal.ofReal_prod_of_nonneg (fun k _ => pow_nonneg (Real.exp_pos _).le _)]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [ENNReal.ofReal_pow (Real.exp_pos _).le, key k, expNeg_ofReal (mul_nonneg (hi k) hp)]

theorem multi_laplaceCost_eq (C : RateChain (MBox m N)) (lam : Fin m → ℕ)
    (p : (ℕ → MBox m N) × (ℕ → ℝ)) (hp : ∀ l, 0 ≤ p.2 l) :
    C.laplaceCost (fun b => (mcost lam (mboxVal b) : ℝ)) p =
      ∏ k, expNeg (C.timeBefore (lowSet m N k) p) ^ lam k := by
  have ha : ∀ l, 0 ≤ C.holdTime p l := fun l => div_nonneg (hp l) (C.rate_nonneg _)
  have hfin : ∀ n, C.discountUpTo (fun b => (mcost lam (mboxVal b) : ℝ)) p n =
      ∏ k, expNeg (∑ l ∈ range n, if p.1 l ∈ lowSet m N k then 0 else
        ENNReal.ofReal (1 * C.holdTime p l)) ^ lam k := by
    intro n
    induction n with
    | zero => simp [RateChain.discountUpTo, expNeg_zero]
    | succ n ih =>
      have hs : C.discountUpTo (fun b => (mcost lam (mboxVal b) : ℝ)) p (n + 1) =
          C.discountUpTo (fun b => (mcost lam (mboxVal b) : ℝ)) p n *
            C.discount (fun b => (mcost lam (mboxVal b) : ℝ)) p n :=
        prod_range_succ _ _
      rw [hs, ih, multi_discount_eq C lam p n (ha n), ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [sum_range_succ, expNeg_add, mul_pow]
  have hlimL : Filter.Tendsto (fun n => C.discountUpTo (fun b => (mcost lam (mboxVal b) : ℝ)) p n)
      Filter.atTop (nhds (C.laplaceCost (fun b => (mcost lam (mboxVal b) : ℝ)) p)) :=
    tendsto_atTop_iInf (C.discountUpTo_antitone _ p)
  have hk : ∀ k ∈ (univ : Finset (Fin m)), Filter.Tendsto (fun n => expNeg (∑ l ∈ range n,
      if p.1 l ∈ lowSet m N k then 0 else ENNReal.ofReal (1 * C.holdTime p l)) ^ lam k)
      Filter.atTop (nhds (expNeg (C.timeBefore (lowSet m N k) p) ^ lam k)) := by
    intro k _
    have hA : Filter.Tendsto (fun n => ∑ l ∈ range n,
        if p.1 l ∈ lowSet m N k then 0 else ENNReal.ofReal (1 * C.holdTime p l)) Filter.atTop
        (nhds (C.timeBefore (lowSet m N k) p)) :=
      ENNReal.tendsto_nat_tsum _
    exact ((ENNReal.continuous_pow (lam k)).tendsto _).comp
      ((continuous_expNeg.tendsto _).comp hA)
  have hR := ENNReal.tendsto_finsetProd_of_ne_top univ hk
    (fun k _ => ENNReal.pow_ne_top (expNeg_ne_top _))
  exact tendsto_nhds_unique hlimL (hR.congr fun n => (hfin n).symm)

theorem lintegral_prod_expNeg_timeBefore (d : Fin m → ℝ) (hd : ∀ j, 0 ≤ d j) (N : ℕ)
    (lam : Fin m → ℕ) :
    ∫⁻ p, ∏ k, expNeg ((multiChain d hd N).timeBefore (lowSet m N k) p) ^ lam k
        ∂(multiChain d hd N).jumpHoldLaw (startBox m N) =
      ENNReal.ofReal (multiPsi d hd N lam (startBox m N)) := by
  set C := multiChain d hd N with hC
  have hclock : ∀ᵐ p ∂(C.jumpHoldLaw (startBox m N)), ∀ k, 0 ≤ p.2 k :=
    Measure.quasiMeasurePreserving_snd.ae Rhone.Coalescent.ae_clockLaw_nonneg
  have hint : ∫⁻ p, ∏ k, expNeg (C.timeBefore (lowSet m N k) p) ^ lam k
      ∂(C.jumpHoldLaw (startBox m N)) =
      ∫⁻ p, C.laplaceCost (fun b => (mcost lam (mboxVal b) : ℝ)) p
        ∂(C.jumpHoldLaw (startBox m N)) :=
    lintegral_congr_ae (hclock.mono fun p hp => (multi_laplaceCost_eq C lam p hp).symm)
  have hle : ∫⁻ p, C.laplaceCost (fun b => (mcost lam (mboxVal b) : ℝ)) p
      ∂(C.jumpHoldLaw (startBox m N)) ≤ 1 :=
    (lintegral_mono fun p => iInf_le _ 0).trans (C.lintegral_discountUpTo_le_one _ _ 0)
  rw [hint, multiPsi, RateChain.laplace,
    ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top hle)]

theorem eq_of_setLIntegral_expNeg_pow_eq {Y : Type*} [MeasurableSpace Y]
    {μ ν : Measure (ℝ≥0∞ × Y)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ (n : ℕ) (B : Set Y), MeasurableSet B →
      ∫⁻ p in Prod.snd ⁻¹' B, expNeg p.1 ^ n ∂μ = ∫⁻ p in Prod.snd ⁻¹' B, expNeg p.1 ^ n ∂ν) :
    μ = ν := by
  have he := measurableEmbedding_expNegReal
  have hm1 : Measurable fun p : ℝ≥0∞ × Y => expNegReal p.1 := he.measurable.comp measurable_fst
  have hAB : ∀ {A : Set ℝ} {B : Set Y}, MeasurableSet A → MeasurableSet B →
      μ ((fun p : ℝ≥0∞ × Y => expNegReal p.1) ⁻¹' A ∩ Prod.snd ⁻¹' B) =
        ν ((fun p : ℝ≥0∞ × Y => expNegReal p.1) ⁻¹' A ∩ Prod.snd ⁻¹' B) := by
    intro A B hA hB
    set S : Set (ℝ≥0∞ × Y) := Prod.snd ⁻¹' B with hS
    have hSm : MeasurableSet S := measurable_snd hB
    have hmom : ∀ (ρ : Measure (ℝ≥0∞ × Y)) (n : ℕ),
        ∫⁻ x, ENNReal.ofReal (x ^ n) ∂(ρ.restrict S).map (fun p => expNegReal p.1) =
          ∫⁻ p in S, expNeg p.1 ^ n ∂ρ := by
      intro ρ n
      have hpm : Measurable fun x : ℝ => ENNReal.ofReal (x ^ n) :=
        ENNReal.measurable_ofReal.comp (measurable_id.pow_const n)
      rw [lintegral_map hpm hm1]
      exact lintegral_congr fun p => ofReal_expNegReal_pow _ n
    have heq : (μ.restrict S).map (fun p => expNegReal p.1) =
        (ν.restrict S).map (fun p => expNegReal p.1) :=
      eq_of_lintegral_pow_eq (map_expNegReal_compl_Icc _ measurable_fst)
        (map_expNegReal_compl_Icc _ measurable_fst) fun n => by
          rw [hmom μ n, hmom ν n, h n B hB]
    have : ((μ.restrict S).map fun p => expNegReal p.1) A =
        ((ν.restrict S).map fun p => expNegReal p.1) A := by
      rw [heq]
    rwa [Measure.map_apply hm1 hA, Measure.map_apply hm1 hA,
      Measure.restrict_apply (hm1 hA), Measure.restrict_apply (hm1 hA)] at this
  have huniv : μ Set.univ = ν Set.univ := by
    have := h 0 Set.univ MeasurableSet.univ
    simpa using this
  refine ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod ?_ huniv
  rintro _ ⟨s, hs, t, ht, rfl⟩
  have hst : s ×ˢ t = (fun p : ℝ≥0∞ × Y => expNegReal p.1) ⁻¹' (expNegReal '' s) ∩
      Prod.snd ⁻¹' t := by
    ext p
    simp only [Set.mem_prod, Set.mem_inter_iff, Set.mem_preimage, he.injective.mem_set_image]
  change μ (s ×ˢ t) = ν (s ×ˢ t)
  rw [hst]
  exact hAB (he.measurableSet_image.2 hs) ht

theorem eq_of_lintegral_prod_expNeg_pow_eq :
    ∀ (m : ℕ) {μ ν : Measure (Fin m → ℝ≥0∞)} [IsFiniteMeasure μ],
      (∀ a : Fin m → ℕ, ∫⁻ p, ∏ k, expNeg (p k) ^ a k ∂μ = ∫⁻ p, ∏ k, expNeg (p k) ^ a k ∂ν) →
        μ = ν
  | 0, μ, ν, _, h => by
    have h0 : μ Set.univ = ν Set.univ := by simpa using h fun k => k.elim0
    ext s _
    rcases s.eq_empty_or_nonempty with rfl | hne
    · simp
    · rw [hne.eq_univ]
      exact h0
  | m + 1, μ, ν, _, h => by
    have huniv : μ Set.univ = ν Set.univ := by simpa using h 0
    have : IsFiniteMeasure ν := ⟨by rw [← huniv]; exact measure_lt_top μ _⟩
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ≥0∞) 0
    have hfst : ∀ x : Fin (m + 1) → ℝ≥0∞, (e x).1 = x 0 := fun x => rfl
    have hsnd : ∀ x : Fin (m + 1) → ℝ≥0∞, (e x).2 = fun j => x j.succ := fun x => rfl
    suffices hmap : μ.map e = ν.map e by
      rw [← e.map_symm_map (μ := μ), ← e.map_symm_map (μ := ν), hmap]
    refine eq_of_setLIntegral_expNeg_pow_eq fun n B hB => ?_
    have hw : Measurable fun p : ℝ≥0∞ × (Fin m → ℝ≥0∞) => expNeg p.1 ^ n :=
      (measurable_expNeg.comp measurable_fst).pow_const n
    have hfinw : ∀ (ρ : Measure (Fin (m + 1) → ℝ≥0∞)) [IsFiniteMeasure ρ],
        IsFiniteMeasure (((ρ.map e).withDensity fun p => expNeg p.1 ^ n).map Prod.snd) := by
      intro ρ _
      have hne : ∫⁻ p, expNeg p.1 ^ n ∂(ρ.map e) ≠ ∞ := by
        refine (lt_of_le_of_lt (lintegral_mono fun p => pow_le_one₀ zero_le (expNeg_le_one _))
          ?_).ne
        rw [lintegral_one]
        exact measure_lt_top _ _
      have := isFiniteMeasure_withDensity hne
      infer_instance
    have hset : ∀ ρ : Measure (Fin (m + 1) → ℝ≥0∞),
        ∫⁻ p in Prod.snd ⁻¹' B, expNeg p.1 ^ n ∂(ρ.map e) =
          (((ρ.map e).withDensity fun p => expNeg p.1 ^ n).map Prod.snd) B := by
      intro ρ
      rw [Measure.map_apply measurable_snd hB, withDensity_apply _ (measurable_snd hB)]
    have hmom : ∀ (ρ : Measure (Fin (m + 1) → ℝ≥0∞)) (a : Fin m → ℕ),
        ∫⁻ y, ∏ k, expNeg (y k) ^ a k
            ∂(((ρ.map e).withDensity fun p => expNeg p.1 ^ n).map Prod.snd) =
          ∫⁻ x, ∏ k, expNeg (x k) ^ (Fin.cons n a : Fin (m + 1) → ℕ) k ∂ρ := by
      intro ρ a
      have hG : Measurable fun y : Fin m → ℝ≥0∞ => ∏ k, expNeg (y k) ^ a k :=
        Finset.measurable_prod _ fun k _ =>
          (measurable_expNeg.comp (measurable_pi_apply k)).pow_const _
      calc ∫⁻ y, ∏ k, expNeg (y k) ^ a k
              ∂(((ρ.map e).withDensity fun p => expNeg p.1 ^ n).map Prod.snd)
          = ∫⁻ p, ∏ k, expNeg (p.2 k) ^ a k
              ∂((ρ.map e).withDensity fun p => expNeg p.1 ^ n) :=
            lintegral_map hG measurable_snd
        _ = ∫⁻ p, expNeg p.1 ^ n * ∏ k, expNeg (p.2 k) ^ a k ∂(ρ.map e) :=
            lintegral_withDensity_eq_lintegral_mul _ hw (hG.comp measurable_snd)
        _ = ∫⁻ x, expNeg (e x).1 ^ n * ∏ k, expNeg ((e x).2 k) ^ a k ∂ρ :=
            lintegral_map_equiv _ e
        _ = ∫⁻ x, ∏ k, expNeg (x k) ^ (Fin.cons n a : Fin (m + 1) → ℕ) k ∂ρ := by
            refine lintegral_congr fun x => ?_
            rw [Fin.prod_univ_succ, hfst, hsnd, Fin.cons_zero]
            simp only [Fin.cons_succ]
    have := hfinw μ
    have := hfinw ν
    have heq : ((μ.map e).withDensity fun p => expNeg p.1 ^ n).map Prod.snd =
        ((ν.map e).withDensity fun p => expNeg p.1 ^ n).map Prod.snd :=
      eq_of_lintegral_prod_expNeg_pow_eq m fun a => by
        rw [hmom μ a, hmom ν a, h]
    rw [hset μ, hset ν, heq]

/-- Source: griffiths_marjoram1997, sec. 1, sec. 3; griffiths1991_two_locus_graph, pp. 103, 107;
hudson1983, p. 185, sec. 5, pp. 195–200. -/
theorem fullARG_mrcaTimes_law_eq_multiChain (N : ℕ) (R : ℝ) (hR : 0 ≤ R)
    (q : Fin m → GenomicProbe) (hq : StrictMono q) :
    (fullARGGenealogyLaw N R).map (fun g k => (⨆ i, ⨆ j, g (q k) i j : ℝ≥0∞)) =
      ((multiChain (gapRate R q) (gapRate_nonneg hR hq) N).jumpHoldLaw (startBox m N)).map
        (fun p k => (multiChain (gapRate R q) (gapRate_nonneg hR hq) N).timeBefore
          (lowSet m N k) p) := by
  have hM : Measurable fun g : Genealogy N => fun k => (⨆ i, ⨆ j, g (q k) i j : ℝ≥0∞) :=
    measurable_pi_iff.mpr fun k => Measurable.iSup fun i => Measurable.iSup fun j =>
      (measurable_pi_apply j).comp ((measurable_pi_apply i).comp (measurable_pi_apply (q k)))
  set C := multiChain (gapRate R q) (gapRate_nonneg hR hq) N with hC
  have hT : Measurable fun p : (ℕ → MBox m N) × (ℕ → ℝ) =>
      fun k => C.timeBefore (lowSet m N k) p :=
    measurable_pi_iff.mpr fun k => measurable_timeBefore C _
  have : IsProbabilityMeasure ((fullARGGenealogyLaw N R).map
      (fun g k => (⨆ i, ⨆ j, g (q k) i j : ℝ≥0∞))) := by
    have := fullARGGenealogyLaw_probability N R
    exact (Measure.isProbabilityMeasure_map_iff hM.aemeasurable).mpr this
  refine eq_of_lintegral_prod_expNeg_pow_eq m fun a => ?_
  have hF : Measurable fun p : Fin m → ℝ≥0∞ => ∏ k, expNeg (p k) ^ a k :=
    Finset.measurable_prod _ fun k _ =>
      (measurable_expNeg.comp (measurable_pi_apply k)).pow_const (a k)
  rw [lintegral_map hF hM, fullARGGenealogyLaw, lintegral_map hF hT]
  refine (lintegral_map (hF.comp hM) (genealogyObservation_measurable N)).trans ?_
  exact (lintegral_prod_expNeg_mrca R hR q hq N a).trans
    (lintegral_prod_expNeg_timeBefore _ _ N a).symm

end Rhone.Coalescent.MultiLocus
