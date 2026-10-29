/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.TwoLocusWFFirstOrder
public import Rhone.Coalescent.TwoLocusWFLimitSystem

/-!
# The generator of the lumped two-locus dual is half the corpus generator

Source: griffiths1991_two_locus_graph, p. 101. -/

@[expose] public section
noncomputable section
namespace Rhone.Coalescent.WFTwoLocusDual
open Finset LinearAlgebra.Recursion

def reqA (i : Fin 2) : Req := ({i}, univ)

def reqB (j : Fin 2) : Req := (univ, {j})

def reqC (i j : Fin 2) : Req := ({i}, {j})

def DeadReq (q : Req) : Prop := q.1 = ∅ ∨ q.2 = ∅

theorem univ_ne_singleton_two (i : Fin 2) : (univ : Finset (Fin 2)) ≠ {i} :=
  (singleton_ne_univ_two i).symm

@[simp] theorem reqA_inj {i i' : Fin 2} : reqA i = reqA i' ↔ i = i' := by
  simp [reqA]

@[simp] theorem reqB_inj {j j' : Fin 2} : reqB j = reqB j' ↔ j = j' := by
  simp [reqB]

@[simp] theorem reqC_inj {i j i' j' : Fin 2} : reqC i j = reqC i' j' ↔ i = i' ∧ j = j' := by
  simp [reqC]

@[simp] theorem reqA_ne_reqB (i j : Fin 2) : reqA i ≠ reqB j := by
  simp [reqA, reqB]

@[simp] theorem reqB_ne_reqA (i j : Fin 2) : reqB j ≠ reqA i := (reqA_ne_reqB i j).symm

@[simp] theorem reqA_ne_reqC (i i' j : Fin 2) : reqA i ≠ reqC i' j := by
  simp [reqA, reqC, univ_ne_singleton_two]

@[simp] theorem reqC_ne_reqA (i i' j : Fin 2) : reqC i' j ≠ reqA i := (reqA_ne_reqC i i' j).symm

@[simp] theorem reqB_ne_reqC (i j j' : Fin 2) : reqB j ≠ reqC i j' := by
  simp [reqB, reqC, univ_ne_singleton_two]

@[simp] theorem reqC_ne_reqB (i j j' : Fin 2) : reqC i j' ≠ reqB j := (reqB_ne_reqC i j j').symm

@[simp] theorem reqA_ne_full (i : Fin 2) : reqA i ≠ full := by
  simp [reqA]

@[simp] theorem reqB_ne_full (j : Fin 2) : reqB j ≠ full := by
  simp [reqB]

@[simp] theorem reqC_ne_full (i j : Fin 2) : reqC i j ≠ full := by
  simp [reqC]

@[simp] theorem full_ne_reqA (i : Fin 2) : full ≠ reqA i := (reqA_ne_full i).symm

@[simp] theorem full_ne_reqB (j : Fin 2) : full ≠ reqB j := (reqB_ne_full j).symm

@[simp] theorem full_ne_reqC (i j : Fin 2) : full ≠ reqC i j := (reqC_ne_full i j).symm

theorem DeadReq.ne {q : Req} (hq : DeadReq q) :
    (∀ i, q ≠ reqA i) ∧ (∀ j, q ≠ reqB j) ∧ (∀ i j, q ≠ reqC i j) ∧ q ≠ full := by
  rcases hq with h | h <;>
  refine ⟨fun i e => ?_, fun j e => ?_, fun i j e => ?_, fun e => ?_⟩ <;> subst e <;>
  first
  | exact absurd h Finset.univ_nonempty.ne_empty
  | simp [reqA, reqB, reqC] at h

def cfgZ (v : Req → ℤ) : Config 2 2 where
  a i := (v (reqA i)).toNat
  b j := (v (reqB j)).toNat
  c i j := (v (reqC i j)).toNat

open Classical in
def liftZ (g : Config 2 2 → ℝ) (v : Req → ℤ) : ℝ :=
  if ∀ q : Req, DeadReq q → v q = 0 then g (cfgZ v) else 0

def vecZ (K : Config 2 2) : Req → ℤ := fun q =>
  (∑ i, if q = reqA i then (K.a i : ℤ) else 0) + (∑ j, if q = reqB j then (K.b j : ℤ) else 0) +
    ∑ i, ∑ j, if q = reqC i j then (K.c i j : ℤ) else 0

@[simp] theorem vecZ_reqA (K : Config 2 2) (i : Fin 2) : vecZ K (reqA i) = K.a i := by
  simp [vecZ]

@[simp] theorem vecZ_reqB (K : Config 2 2) (j : Fin 2) : vecZ K (reqB j) = K.b j := by
  simp [vecZ]

@[simp] theorem vecZ_reqC (K : Config 2 2) (i j : Fin 2) : vecZ K (reqC i j) = K.c i j := by
  fin_cases i <;> fin_cases j <;> simp [vecZ]

theorem vecZ_of_ne (K : Config 2 2) {q : Req} (hA : ∀ i, q ≠ reqA i) (hB : ∀ j, q ≠ reqB j)
    (hC : ∀ i j, q ≠ reqC i j) : vecZ K q = 0 := by
  simp [vecZ, hA, hB, hC]

@[simp] theorem vecZ_full (K : Config 2 2) : vecZ K full = 0 :=
  vecZ_of_ne K (fun i => (reqA_ne_full i).symm) (fun j => (reqB_ne_full j).symm)
    (fun i j => (reqC_ne_full i j).symm)

theorem sum_vecZ_mul (K : Config 2 2) (F : Req → ℝ) :
    ∑ q, ((vecZ K q : ℤ) : ℝ) * F q = (∑ i, (K.a i : ℝ) * F (reqA i)) +
      (∑ j, (K.b j : ℝ) * F (reqB j)) + ∑ i, ∑ j, (K.c i j : ℝ) * F (reqC i j) := by
  have hq : ∀ q, ((vecZ K q : ℤ) : ℝ) * F q =
      (∑ i, if q = reqA i then (K.a i : ℝ) * F q else 0) +
        (∑ j, if q = reqB j then (K.b j : ℝ) * F q else 0) +
        ∑ i, ∑ j, if q = reqC i j then (K.c i j : ℝ) * F q else 0 := by
    intro q
    simp only [vecZ, Int.cast_add, Int.cast_sum, apply_ite (Int.cast : ℤ → ℝ),
      Int.cast_natCast, Int.cast_zero, add_mul, Finset.sum_mul, ite_mul, zero_mul]
  have hA : ∑ q, ∑ i, (if q = reqA i then (K.a i : ℝ) * F q else 0) =
      ∑ i, (K.a i : ℝ) * F (reqA i) := by
    rw [Finset.sum_comm]
    simp
  have hB : ∑ q, ∑ j, (if q = reqB j then (K.b j : ℝ) * F q else 0) =
      ∑ j, (K.b j : ℝ) * F (reqB j) := by
    rw [Finset.sum_comm]
    simp
  have hC : ∑ q, ∑ i, ∑ j, (if q = reqC i j then (K.c i j : ℝ) * F q else 0) =
      ∑ i, ∑ j, (K.c i j : ℝ) * F (reqC i j) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    simp
  rw [Finset.sum_congr rfl fun q _ => hq q, Finset.sum_add_distrib, Finset.sum_add_distrib, hA,
    hB, hC]

theorem sCnt_vecZ (K : Config 2 2) (q : Req) : sCnt (vecZ K) q = ((vecZ K q : ℤ) : ℝ) := by
  unfold sCnt
  split_ifs with h
  · subst h; simp
  · rfl

theorem liftZ_of {g : Config 2 2 → ℝ} {w : Req → ℤ} (hw : ∀ q, DeadReq q → w q = 0) :
    liftZ g w = g (cfgZ w) := by
  unfold liftZ
  exact ite_eq_left hw

theorem liftZ_dead {g : Config 2 2 → ℝ} {w : Req → ℤ} {q : Req} (hq : DeadReq q)
    (hw : w q ≠ 0) : liftZ g w = 0 := by
  unfold liftZ
  exact ite_eq_right fun h => hw (h q hq)

theorem fullFree_liftZ (g : Config 2 2 → ℝ) : FullFree (liftZ g) := by
  intro v w h
  have hc : cfgZ v = cfgZ w := by
    unfold cfgZ
    simp only [h _ (reqA_ne_full _), h _ (reqB_ne_full _), h _ (reqC_ne_full _ _)]
  have hd : (∀ q : Req, DeadReq q → v q = 0) ↔ (∀ q : Req, DeadReq q → w q = 0) :=
    forall_congr' fun q => imp_congr_right fun hq => by rw [h q hq.ne.2.2.2]
  unfold liftZ
  rw [hc]
  by_cases hv : ∀ q : Req, DeadReq q → v q = 0
  · rw [ite_eq_left hv, ite_eq_left (hd.mp hv)]
  · rw [ite_eq_right hv, ite_eq_right (fun h' => hv (hd.mpr h'))]

theorem dead_zero (K : Config 2 2) {q : Req} (hq : DeadReq q) :
    vecZ K q = 0 ∧ (∀ i, eR (reqA i) q = 0) ∧ (∀ j, eR (reqB j) q = 0) ∧
      (∀ i j, eR (reqC i j) q = 0) ∧ eR full q = 0 := by
  obtain ⟨hA, hB, hC, hF⟩ := hq.ne
  exact ⟨vecZ_of_ne K hA hB hC, fun i => by simp [eR, hA i], fun j => by simp [eR, hB j],
    fun i j => by simp [eR, hC i j], by simp [eR, hF]⟩

theorem liftZ_vecZ (g : Config 2 2 → ℝ) (K : Config 2 2) : liftZ g (vecZ K) = g K := by
  rw [liftZ_of fun q hq => (dead_zero K hq).1]
  congr 1
  refine Config.ext ?_ ?_ ?_ <;> funext <;> simp [cfgZ]

section moves
variable (g : Config 2 2 → ℝ) (K : Config 2 2)

theorem liftZ_dropA (i : Fin 2) :
    liftZ g (vecZ K - eR (reqA i) + eR full) = g (K.dropA i) := by
  rw [liftZ_of fun q hq => by
    obtain ⟨h0, hA, -, -, hF⟩ := dead_zero K hq; simp [h0, hA, hF]]
  congr 1
  refine Config.ext ?_ ?_ ?_ <;> funext
  · rename_i i'
    by_cases h1 : i' = i <;> simp [cfgZ, Config.dropA, decf, eR, h1]
  · simp [cfgZ, Config.dropA, eR, Pi.single_apply]
  · simp [cfgZ, Config.dropA, eR, Pi.single_apply]

theorem liftZ_dropB (j : Fin 2) :
    liftZ g (vecZ K - eR (reqB j) + eR full) = g (K.dropB j) := by
  rw [liftZ_of fun q hq => by
    obtain ⟨h0, -, hB, -, hF⟩ := dead_zero K hq; simp [h0, hB, hF]]
  congr 1
  refine Config.ext ?_ ?_ ?_ <;> funext
  · simp [cfgZ, Config.dropB, eR, Pi.single_apply]
  · rename_i j'
    by_cases h2 : j' = j <;> simp [cfgZ, Config.dropB, decf, eR, h2]
  · simp [cfgZ, Config.dropB, eR, Pi.single_apply]

theorem liftZ_dropC (i j : Fin 2) :
    liftZ g (vecZ K - eR (reqC i j) + eR full) = g (K.dropC i j) := by
  rw [liftZ_of fun q hq => by
    obtain ⟨h0, -, -, hC, hF⟩ := dead_zero K hq; simp [h0, hC, hF]]
  congr 1
  refine Config.ext ?_ ?_ ?_ <;> funext
  · simp [cfgZ, Config.dropC, eR, Pi.single_apply]
  · simp [cfgZ, Config.dropC, eR, Pi.single_apply]
  · rename_i i' j'
    by_cases h1 : i' = i <;> by_cases h2 : j' = j <;>
      simp [cfgZ, Config.dropC, Config.decC, decf, eR, h1, h2]

theorem liftZ_mergeAB (i j : Fin 2) :
    liftZ g (vecZ K - eR (reqA i) - eR (reqB j) + eR full + eR (reqC i j)) =
      g (K.mergeAB i j) := by
  rw [liftZ_of fun q hq => by
    obtain ⟨h0, hA, hB, hC, hF⟩ := dead_zero K hq; simp [h0, hA, hB, hC, hF]]
  congr 1
  refine Config.ext ?_ ?_ ?_ <;> funext
  · rename_i i'
    by_cases h1 : i' = i <;> simp [cfgZ, Config.mergeAB, decf, eR, h1]
  · rename_i j'
    by_cases h2 : j' = j <;> simp [cfgZ, Config.mergeAB, decf, eR, h2]
  · rename_i i' j'
    by_cases h1 : i' = i <;> by_cases h2 : j' = j <;>
      simp [cfgZ, Config.mergeAB, Config.incC, incf, eR, h1, h2]

theorem liftZ_killA (i j : Fin 2) :
    liftZ g (vecZ K - eR (reqC i j) + eR (reqB j)) = g (K.killA i j) := by
  rw [liftZ_of fun q hq => by
    obtain ⟨h0, -, hB, hC, -⟩ := dead_zero K hq; simp [h0, hB, hC]]
  congr 1
  refine Config.ext ?_ ?_ ?_ <;> funext
  · simp [cfgZ, Config.killA, eR, Pi.single_apply]
  · rename_i j'
    by_cases h2 : j' = j <;> simp [cfgZ, Config.killA, incf, eR, h2]
  · rename_i i' j'
    by_cases h1 : i' = i <;> by_cases h2 : j' = j <;>
      simp [cfgZ, Config.killA, Config.decC, decf, eR, h1, h2]

theorem liftZ_killB (i j : Fin 2) :
    liftZ g (vecZ K - eR (reqC i j) + eR (reqA i)) = g (K.killB i j) := by
  rw [liftZ_of fun q hq => by
    obtain ⟨h0, hA, -, hC, -⟩ := dead_zero K hq; simp [h0, hA, hC]]
  congr 1
  refine Config.ext ?_ ?_ ?_ <;> funext
  · rename_i i'
    by_cases h1 : i' = i <;> simp [cfgZ, Config.killB, incf, eR, h1]
  · simp [cfgZ, Config.killB, eR, Pi.single_apply]
  · rename_i i' j'
    by_cases h1 : i' = i <;> by_cases h2 : j' = j <;>
      simp [cfgZ, Config.killB, Config.decC, decf, eR, h1, h2]

theorem liftZ_split (i j : Fin 2) :
    liftZ g (vecZ K - eR (reqC i j) + eR (reqA i) - eR full + eR (reqB j)) =
      g (K.split i j) := by
  rw [liftZ_of fun q hq => by
    obtain ⟨h0, hA, hB, hC, hF⟩ := dead_zero K hq; simp [h0, hA, hB, hC, hF]]
  congr 1
  refine Config.ext ?_ ?_ ?_ <;> funext
  · rename_i i'
    by_cases h1 : i' = i <;> simp [cfgZ, Config.split, incf, eR, h1]
  · rename_i j'
    by_cases h2 : j' = j <;> simp [cfgZ, Config.split, incf, eR, h2]
  · rename_i i' j'
    by_cases h1 : i' = i <;> by_cases h2 : j' = j <;>
      simp [cfgZ, Config.split, Config.decC, decf, eR, h1, h2]

theorem liftZ_pairV_dead {q q' : Req} (hd : DeadReq (meet q q')) (hq : ¬ DeadReq q)
    (hq' : ¬ DeadReq q') : liftZ g (pairV (vecZ K) q q') = 0 := by
  refine liftZ_dead hd ?_
  obtain ⟨h0, -, -, -, hF⟩ := dead_zero K hd
  have h1 : meet q q' ≠ q := fun e => hq (e ▸ hd)
  have h2 : meet q q' ≠ q' := fun e => hq' (e ▸ hd)
  simp [pairV, h0, eR, h1, h2, hd.ne.2.2.2]

end moves

theorem singleton_inter_two (i i' : Fin 2) :
    ({i} ∩ {i'} : Finset (Fin 2)) = if i = i' then {i} else ∅ := by
  fin_cases i <;> fin_cases i' <;> decide

theorem not_deadReq_reqA (i : Fin 2) : ¬ DeadReq (reqA i) := by
  rintro (h | h)
  · simp [reqA] at h
  · exact Finset.univ_nonempty.ne_empty h

theorem not_deadReq_reqB (j : Fin 2) : ¬ DeadReq (reqB j) := by
  rintro (h | h)
  · exact Finset.univ_nonempty.ne_empty h
  · simp [reqB] at h

theorem not_deadReq_reqC (i j : Fin 2) : ¬ DeadReq (reqC i j) := by simp [DeadReq, reqC]

theorem pairV_comm (v : Req → ℤ) (q q' : Req) : pairV v q q' = pairV v q' q := by
  simp only [pairV, meet_comm q q']; abel

section pairs
variable (g : Config 2 2 → ℝ) (K : Config 2 2)

theorem liftZ_pairAA (i i' : Fin 2) :
    liftZ g (pairV (vecZ K) (reqA i) (reqA i')) = if i = i' then g (K.dropA i) else 0 := by
  split_ifs with h
  · subst h
    have hm : meet (reqA i) (reqA i) = reqA i := by simp [meet, reqA]
    rw [pairV, hm, ← liftZ_dropA g K i]
    congr 1; abel
  · refine liftZ_pairV_dead g K ?_ (not_deadReq_reqA i) (not_deadReq_reqA i')
    refine Or.inl ?_; simp [meet, reqA, h]

theorem liftZ_pairAB (i j : Fin 2) :
    liftZ g (pairV (vecZ K) (reqA i) (reqB j)) = g (K.mergeAB i j) := by
  have hm : meet (reqA i) (reqB j) = reqC i j := by simp [meet, reqA, reqB, reqC]
  rw [pairV, hm, ← liftZ_mergeAB g K i j]

theorem liftZ_pairAC (i i' j : Fin 2) :
    liftZ g (pairV (vecZ K) (reqA i) (reqC i' j)) = if i = i' then g (K.dropA i) else 0 := by
  split_ifs with h
  · subst h
    have hm : meet (reqA i) (reqC i j) = reqC i j := by simp [meet, reqA, reqC]
    rw [pairV, hm, ← liftZ_dropA g K i]
    congr 1; abel
  · refine liftZ_pairV_dead g K ?_ (not_deadReq_reqA i) (not_deadReq_reqC i' j)
    refine Or.inl ?_; simp [meet, reqA, reqC, h]

theorem liftZ_pairBB (j j' : Fin 2) :
    liftZ g (pairV (vecZ K) (reqB j) (reqB j')) = if j = j' then g (K.dropB j) else 0 := by
  split_ifs with h
  · subst h
    have hm : meet (reqB j) (reqB j) = reqB j := by simp [meet, reqB]
    rw [pairV, hm, ← liftZ_dropB g K j]
    congr 1; abel
  · refine liftZ_pairV_dead g K ?_ (not_deadReq_reqB j) (not_deadReq_reqB j')
    refine Or.inr ?_; simp [meet, reqB, h]

theorem liftZ_pairBC (j i j' : Fin 2) :
    liftZ g (pairV (vecZ K) (reqB j) (reqC i j')) = if j = j' then g (K.dropB j) else 0 := by
  split_ifs with h
  · subst h
    have hm : meet (reqB j) (reqC i j) = reqC i j := by simp [meet, reqB, reqC]
    rw [pairV, hm, ← liftZ_dropB g K j]
    congr 1; abel
  · refine liftZ_pairV_dead g K ?_ (not_deadReq_reqB j) (not_deadReq_reqC i j')
    refine Or.inr ?_; simp [meet, reqB, reqC, h]

theorem liftZ_pairCC (i j i' j' : Fin 2) :
    liftZ g (pairV (vecZ K) (reqC i j) (reqC i' j')) =
      if i = i' ∧ j = j' then g (K.dropC i j) else 0 := by
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    have hm : meet (reqC i j) (reqC i j) = reqC i j := by simp [meet, reqC]
    rw [pairV, hm, ← liftZ_dropC g K i j]
    congr 1; abel
  · refine liftZ_pairV_dead g K ?_ (not_deadReq_reqC i j) (not_deadReq_reqC i' j')
    by_cases h1 : i = i'
    · have h2 : j ≠ j' := fun h2 => h ⟨h1, h2⟩
      refine Or.inr ?_
      simp [meet, reqC, singleton_inter_two, h2]
    · refine Or.inl ?_
      simp [meet, reqC, singleton_inter_two, h1]

theorem lin0_reqA (θ ρ : ℝ) (i : Fin 2) :
    lin0 θ ρ (reqA i) (liftZ g) (vecZ K) = θ / 2 * (1 / 2 * g (K.dropA i) - g K) := by
  unfold lin0
  have e1 : ((univ : Finset (Fin 2)), (reqA i).2) = full := rfl
  have e2 : ((reqA i).1, (univ : Finset (Fin 2))) = reqA i := rfl
  have e3 : vecZ K - eR (reqA i) + eR (reqA i) - eR full + eR full = vecZ K := by abel
  rw [e1, e2, e3, sub_add_cancel, liftZ_dropA, liftZ_vecZ]
  simp [mutFactor, reqA]

theorem lin0_reqB (θ ρ : ℝ) (j : Fin 2) :
    lin0 θ ρ (reqB j) (liftZ g) (vecZ K) = θ / 2 * (1 / 2 * g (K.dropB j) - g K) := by
  unfold lin0
  have e1 : ((univ : Finset (Fin 2)), (reqB j).2) = reqB j := rfl
  have e2 : ((reqB j).1, (univ : Finset (Fin 2))) = full := rfl
  have e3 : vecZ K - eR (reqB j) + eR full - eR full + eR (reqB j) = vecZ K := by abel
  rw [e1, e2, e3, sub_add_cancel, liftZ_dropB, liftZ_vecZ]
  simp [mutFactor, reqB]

theorem lin0_reqC (θ ρ : ℝ) (i j : Fin 2) :
    lin0 θ ρ (reqC i j) (liftZ g) (vecZ K) =
      θ / 2 * (1 / 2 * g (K.killA i j) - g K) + θ / 2 * (1 / 2 * g (K.killB i j) - g K) +
        ρ / 2 * (g (K.split i j) - g K) := by
  unfold lin0
  have e1 : ((univ : Finset (Fin 2)), (reqC i j).2) = reqB j := rfl
  have e2 : ((reqC i j).1, (univ : Finset (Fin 2))) = reqA i := rfl
  rw [e1, e2, liftZ_killA, liftZ_killB, liftZ_split, liftZ_vecZ]
  simp [mutFactor, reqC]

end pairs

theorem sum_mul_sub_diag (s : Req → ℝ) (X : Req → Req → ℝ) :
    ∑ q, ∑ q', s q * (s q' - if q = q' then 1 else 0) * X q q' =
      ∑ q, s q * ((∑ q', s q' * X q q') - X q q) := by
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [mul_sub, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, mul_ite, mul_one,
    mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  congr 1
  exact Finset.sum_congr rfl fun q' _ => by ring

theorem cast_coalA (K : Config 2 2) (i : Fin 2) :
    ((K.coalA i : ℕ) : ℝ) = (K.a i : ℝ) * ((K.a i : ℝ) - 1) + 2 * (K.a i : ℝ) * (K.cRow i : ℝ) := by
  unfold Config.coalA
  rcases Nat.eq_zero_or_pos (K.a i) with h | h
  · simp [h]
  · rw [Nat.cast_mul, Nat.cast_add, Nat.cast_sub h]; push_cast; ring

theorem cast_coalB (K : Config 2 2) (j : Fin 2) :
    ((K.coalB j : ℕ) : ℝ) = (K.b j : ℝ) * ((K.b j : ℝ) - 1) + 2 * (K.b j : ℝ) * (K.cCol j : ℝ) := by
  unfold Config.coalB
  rcases Nat.eq_zero_or_pos (K.b j) with h | h
  · simp [h]
  · rw [Nat.cast_mul, Nat.cast_add, Nat.cast_sub h]; push_cast; ring

theorem cast_coalC (K : Config 2 2) (i j : Fin 2) :
    ((K.coalC i j : ℕ) : ℝ) = (K.c i j : ℝ) * ((K.c i j : ℝ) - 1) := by
  unfold Config.coalC
  rcases Nat.eq_zero_or_pos (K.c i j) with h | h
  · simp [h]
  · rw [Nat.cast_mul, Nat.cast_sub h]; push_cast; ring

theorem cast_n_mul (K : Config 2 2) :
    ((K.n * (K.n - 1) : ℕ) : ℝ) = (K.n : ℝ) * ((K.n : ℝ) - 1) := by
  rcases Nat.eq_zero_or_pos K.n with h | h
  · simp [h]
  · rw [Nat.cast_mul, Nat.cast_sub h]; push_cast; ring

theorem gam_liftZ_vecZ (θ ρ : ℝ) (g : Config 2 2 → ℝ) (K : Config 2 2) :
    gam θ ρ (liftZ g) (vecZ K) =
      (1 / 2) * (rhs θ θ ρ (fun _ => (1 / 2 : ℝ)) (fun _ => (1 / 2 : ℝ)) g K -
        diag θ θ ρ K * g K) := by
  unfold gam
  rw [sum_mul_sub_diag]
  simp only [sCnt_vecZ, liftZ_vecZ]
  rw [sum_vecZ_mul, sum_vecZ_mul]
  simp only [sum_vecZ_mul, liftZ_pairAA, liftZ_pairAB, liftZ_pairAC, liftZ_pairBB,
    liftZ_pairBC, liftZ_pairCC, lin0_reqA, lin0_reqB, lin0_reqC]
  simp only [pairV_comm (vecZ K) (reqB _) (reqA _), pairV_comm (vecZ K) (reqC _ _) (reqA _),
    pairV_comm (vecZ K) (reqC _ _) (reqB _), liftZ_pairAB, liftZ_pairAC, liftZ_pairBC]
  rw [Rhone.LinearAlgebra.Recursion.diag, cast_n_mul]
  simp only [rhs, cast_coalA, cast_coalB, cast_coalC, Config.coalAB, Config.cRow,
    Config.cCol, Config.n, Config.nA, Config.nB, Config.t, Config.sumA, Config.sumB,
    Fin.sum_univ_two, Fin.isValue]
  simp only [Fin.isValue, zero_ne_one, one_ne_zero, ↓reduceIte,
    and_self, and_false, false_and, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  ring

end Rhone.Coalescent.WFTwoLocusDual
