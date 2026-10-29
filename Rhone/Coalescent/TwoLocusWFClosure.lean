/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.TwoLocusWFGenerator

/-! # Linearity and closure of the lumped step of the two-locus Wright-Fisher dual -/

@[expose] public section
noncomputable section
namespace Rhone.Coalescent.WFTwoLocusDual
open Finset

theorem insOp_lin (M : ℕ) (r : Req) (a : ℝ) (G₁ G₂ : (Req → ℕ) → ℝ) (κ : Req → ℕ) :
    insOp M r (fun κ' => a * G₁ κ' + G₂ κ') κ = a * insOp M r G₁ κ + insOp M r G₂ κ := by
  simp only [insOp, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun q _ => by ring

theorem lineOp_lin (M : ℕ) (c u : ℝ) (r : Req) (a : ℝ) (G₁ G₂ : (Req → ℕ) → ℝ)
    (κ : Req → ℕ) :
    lineOp M c u r (fun κ' => a * G₁ κ' + G₂ κ') κ =
      a * lineOp M c u r G₁ κ + lineOp M c u r G₂ κ := by
  have hin : ∀ r', insOp M r' (fun κ' => a * G₁ κ' + G₂ κ') =
      fun κ' => a * insOp M r' G₁ κ' + insOp M r' G₂ κ' :=
    fun r' => funext fun κ' => insOp_lin M r' a G₁ G₂ κ'
  simp only [lineOp, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun f _ => ?_
  split_ifs
  · rw [hin, insOp_lin]; ring
  · rw [insOp_lin]; ring

theorem lumpChain_lin (M : ℕ) (c u : ℝ) :
    ∀ {n : ℕ} (lam : Fin n → Req) (a : ℝ) (G₁ G₂ : (Req → ℕ) → ℝ) (κ : Req → ℕ),
      lumpChain M c u lam (fun κ' => a * G₁ κ' + G₂ κ') κ =
        a * lumpChain M c u lam G₁ κ + lumpChain M c u lam G₂ κ
  | 0, _, _, _, _, _ => rfl
  | n + 1, lam, a, G₁, G₂, κ => by
    simp only [lumpChain]
    rw [show lineOp M c u (lam 0) (fun κ' => a * G₁ κ' + G₂ κ') =
        fun κ' => a * lineOp M c u (lam 0) G₁ κ' + lineOp M c u (lam 0) G₂ κ' from
      funext fun κ' => lineOp_lin M c u (lam 0) a G₁ G₂ κ']
    exact lumpChain_lin M c u (Fin.tail lam) a _ _ κ

theorem lumpChain_sum (M : ℕ) (c u : ℝ) {n : ℕ} (lam : Fin n → Req) {ι : Type*}
    (s : Finset ι) (a : ι → ℝ) (G : ι → (Req → ℕ) → ℝ) (G₀ : (Req → ℕ) → ℝ) (κ : Req → ℕ) :
    lumpChain M c u lam (fun κ' => ∑ i ∈ s, a i * G i κ' + G₀ κ') κ =
      ∑ i ∈ s, a i * lumpChain M c u lam (G i) κ + lumpChain M c u lam G₀ κ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi, add_assoc]
    rw [lumpChain_lin M c u lam (a i) (G i), ih]

def levA (κ : Req → ℕ) : ℕ := ∑ q, if q.1 = univ then 0 else κ q

def levB (κ : Req → ℕ) : ℕ := ∑ q, if q.2 = univ then 0 else κ q

theorem sum_weight_moveCnt {κ : Req → ℕ} {q : Req} (h : 1 ≤ κ q) (q' : Req) (w : Req → ℕ) :
    (∑ x, w x * moveCnt κ q q' x) + w q = (∑ x, w x * κ x) + w q' := by
  have h1 := congrArg (fun v : Req → ℤ => ∑ x, (w x : ℤ) * v x) (castV_moveCnt h q')
  simp only [castV, eR, Pi.add_apply, Pi.sub_apply, mul_add, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte] at h1
  have h2 : ((∑ x, w x * moveCnt κ q q' x + w q : ℕ) : ℤ) =
      ((∑ x, w x * κ x + w q' : ℕ) : ℤ) := by
    push_cast; linarith
  exact_mod_cast h2

theorem levA_eq (κ : Req → ℕ) : levA κ = ∑ x, (if x.1 = univ then 0 else 1) * κ x := by
  unfold levA; exact Finset.sum_congr rfl fun x _ => by split_ifs <;> simp

theorem levB_eq (κ : Req → ℕ) : levB κ = ∑ x, (if x.2 = univ then 0 else 1) * κ x := by
  unfold levB; exact Finset.sum_congr rfl fun x _ => by split_ifs <;> simp

def nf (S : Finset (Fin 2)) : ℕ := if S = univ then 0 else 1

theorem levA_moveCnt_le {κ : Req → ℕ} {q : Req} (h : 1 ≤ κ q) (r : Req) :
    levA (moveCnt κ q (meet q r)) ≤ levA κ + nf r.1 := by
  have h1 := sum_weight_moveCnt h (meet q r) fun x => if x.1 = univ then 0 else 1
  rw [← levA_eq, ← levA_eq] at h1
  have h2 : (if (meet q r).1 = univ then 0 else 1) ≤
      (if q.1 = univ then 0 else 1) + nf r.1 := by
    unfold nf meet
    by_cases hq : q.1 = univ <;> by_cases hr : r.1 = univ <;> simp [hq, hr]
  omega

theorem levB_moveCnt_le {κ : Req → ℕ} {q : Req} (h : 1 ≤ κ q) (r : Req) :
    levB (moveCnt κ q (meet q r)) ≤ levB κ + nf r.2 := by
  have h1 := sum_weight_moveCnt h (meet q r) fun x => if x.2 = univ then 0 else 1
  rw [← levB_eq, ← levB_eq] at h1
  have h2 : (if (meet q r).2 = univ then 0 else 1) ≤
      (if q.2 = univ then 0 else 1) + nf r.2 := by
    unfold nf meet
    by_cases hq : q.2 = univ <;> by_cases hr : r.2 = univ <;> simp [hq, hr]
  omega

theorem nf_mutReq_le (m : Bool) (S : Finset (Fin 2)) : nf (mutReq m S) ≤ nf S := by
  cases m <;> simp [nf, mutReq]

def LevSet (M LA LB : ℕ) (κ : Req → ℕ) : Prop := ∑ q, κ q = M ∧ levA κ ≤ LA ∧ levB κ ≤ LB

theorem insOp_congr (M : ℕ) (r : Req) {G G' : (Req → ℕ) → ℝ} {κ : Req → ℕ}
    (hκ : ∑ q, κ q = M)
    (hG : ∀ κ', LevSet M (levA κ + nf r.1) (levB κ + nf r.2) κ' → G κ' = G' κ') :
    insOp M r G κ = insOp M r G' κ := by
  unfold insOp
  refine Finset.sum_congr rfl fun q _ => ?_
  by_cases h0 : κ q = 0
  · simp [h0]
  have h1 : 1 ≤ κ q := Nat.one_le_iff_ne_zero.mpr h0
  rw [hG _ ⟨(sum_moveCnt h1 _).trans hκ, levA_moveCnt_le h1 r, levB_moveCnt_le h1 r⟩]

theorem lineOp_congr (M : ℕ) (c u : ℝ) (r : Req) {G G' : (Req → ℕ) → ℝ} {κ : Req → ℕ}
    (hκ : ∑ q, κ q = M)
    (hG : ∀ κ', LevSet M (levA κ + nf r.1) (levB κ + nf r.2) κ' → G κ' = G' κ') :
    lineOp M c u r G κ = lineOp M c u r G' κ := by
  unfold lineOp
  refine Finset.sum_congr rfl fun f _ => ?_
  have hA := nf_mutReq_le f.1 r.1
  have hB := nf_mutReq_le f.2.1 r.2
  congr 1
  split_ifs
  · refine insOp_congr M _ hκ fun κ' hκ' => ?_
    refine insOp_congr M _ hκ'.1 fun κ'' hκ'' => hG κ'' ⟨hκ''.1, ?_, ?_⟩
    · have := hκ''.2.1; have := hκ'.2.1; simp [nf] at *; omega
    · have := hκ''.2.2; have := hκ'.2.2; simp [nf] at *; omega
  · refine insOp_congr M _ hκ fun κ' hκ' => hG κ' ⟨hκ'.1, ?_, ?_⟩
    · have := hκ'.2.1; simp only at this; omega
    · have := hκ'.2.2; simp only at this; omega

def lamLevA {n : ℕ} (lam : Fin n → Req) : ℕ := ∑ k, nf (lam k).1

def lamLevB {n : ℕ} (lam : Fin n → Req) : ℕ := ∑ k, nf (lam k).2

theorem lumpChain_congr (M : ℕ) (c u : ℝ) :
    ∀ {n : ℕ} (lam : Fin n → Req) {G G' : (Req → ℕ) → ℝ} {κ : Req → ℕ},
      ∑ q, κ q = M →
      (∀ κ', LevSet M (levA κ + lamLevA lam) (levB κ + lamLevB lam) κ' → G κ' = G' κ') →
      lumpChain M c u lam G κ = lumpChain M c u lam G' κ
  | 0, _, _, _, _, _, hG => hG _ ⟨by assumption, by simp [lamLevA], by simp [lamLevB]⟩
  | n + 1, lam, G, G', κ, hκ, hG => by
    simp only [lumpChain]
    refine lumpChain_congr M c u (Fin.tail lam) hκ fun κ' hκ' => ?_
    refine lineOp_congr M c u (lam 0) hκ'.1 fun κ'' hκ'' => hG κ'' ⟨hκ''.1, ?_, ?_⟩
    · have h1 := hκ''.2.1; have h2 := hκ'.2.1
      have : lamLevA lam = nf (lam 0).1 + lamLevA (Fin.tail lam) := by
        simp [lamLevA, Fin.sum_univ_succ, Fin.tail]
      omega
    · have h1 := hκ''.2.2; have h2 := hκ'.2.2
      have : lamLevB lam = nf (lam 0).2 + lamLevB (Fin.tail lam) := by
        simp [lamLevB, Fin.sum_univ_succ, Fin.tail]
      omega

theorem cnt_eq_vecZ {M : ℕ} {ζ : DualState M} (hζ : ¬ Dead ζ) {q : Req} (hq : q ≠ full) :
    (cnt ζ q : ℤ) = vecZ (cfgOf ζ) q := by
  obtain ⟨S, T⟩ := q
  rcases finset_fin_two_cases S with rfl | rfl | rfl | rfl
  · rw [cnt_empty_left hζ, (dead_zero _ (Or.inl rfl)).1]; rfl
  all_goals rcases finset_fin_two_cases T with rfl | rfl | rfl | rfl
  all_goals first
    | (rw [cnt_empty_right hζ, (dead_zero _ (Or.inr rfl)).1]; rfl)
    | exact absurd rfl hq
    | (rw [show ((({0} : Finset (Fin 2)), (univ : Finset (Fin 2))) : Req) = reqA 0 from rfl,
          vecZ_reqA]; rfl)
    | (rw [show ((({1} : Finset (Fin 2)), (univ : Finset (Fin 2))) : Req) = reqA 1 from rfl,
          vecZ_reqA]; rfl)
    | (rw [show (((univ : Finset (Fin 2)), ({0} : Finset (Fin 2))) : Req) = reqB 0 from rfl,
          vecZ_reqB]; rfl)
    | (rw [show (((univ : Finset (Fin 2)), ({1} : Finset (Fin 2))) : Req) = reqB 1 from rfl,
          vecZ_reqB]; rfl)
    | (rw [show ((({_} : Finset (Fin 2)), ({_} : Finset (Fin 2))) : Req) = reqC _ _ from rfl,
          vecZ_reqC]; rfl)

theorem sum_vecZ_real (K : Rhone.LinearAlgebra.Recursion.Config 2 2) (w : Req → ℝ)
    (hA : ∀ i, w (reqA i) = 1) (hB : ∀ j, w (reqB j) = 0) (hC : ∀ i j, w (reqC i j) = 1) :
    ∑ q, ((vecZ K q : ℤ) : ℝ) * w q = (K.nA : ℝ) := by
  rw [sum_vecZ_mul]
  simp [hA, hB, hC, Rhone.LinearAlgebra.Recursion.Config.nA,
      Rhone.LinearAlgebra.Recursion.Config.sumA,
    Rhone.LinearAlgebra.Recursion.Config.t]

end Rhone.Coalescent.WFTwoLocusDual
