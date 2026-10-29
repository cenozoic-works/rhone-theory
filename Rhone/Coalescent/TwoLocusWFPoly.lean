/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.TwoLocusWFLumpStep

/-!
# The lumped step of the two-locus Wright-Fisher dual as a polynomial in `1 / M`

Source: griffiths1991_two_locus_graph, p. 101. -/

@[expose] public section
noncomputable section
namespace Rhone.Coalescent.WFTwoLocusDual
open Finset Polynomial

abbrev full : Req := (univ, univ)

def eR (q : Req) : Req → ℤ := Pi.single q 1

def sCnt (v : Req → ℤ) (q : Req) : ℝ := if q = full then 0 else (v q : ℝ)

def insV (r : Req) (v : Req → ℤ) : Req → ℤ := v - eR full + eR r

def insP (r : Req) (H : (Req → ℤ) → ℝ[X]) (v : Req → ℤ) : ℝ[X] :=
  H (insV r v) + X * ∑ q, C (sCnt v q) * (H (v - eR q + eR (meet q r)) - H (insV r v))

def flagP (a : ℝ) (m : Bool) : ℝ[X] := if m then C a * X else 1 - C a * X

def lineP (θ ρ : ℝ) (r : Req) (H : (Req → ℤ) → ℝ[X]) (v : Req → ℤ) : ℝ[X] :=
  ∑ f : Bool × Bool × Bool,
    flagP (θ / 2) f.1 * flagP (θ / 2) f.2.1 * flagP (ρ / 2) f.2.2 *
      C (mutFactor f.1 r.1 * mutFactor f.2.1 r.2) *
      (if f.2.2 then insP (mutReq f.1 r.1, univ) (insP (univ, mutReq f.2.1 r.2) H) v
       else insP (mutReq f.1 r.1, mutReq f.2.1 r.2) H v)

def chainP (θ ρ : ℝ) : {n : ℕ} → (Fin n → Req) → ((Req → ℤ) → ℝ[X]) → (Req → ℤ) → ℝ[X]
  | 0, _, H => H
  | _ + 1, lam, H => chainP θ ρ (Fin.tail lam) (lineP θ ρ (lam 0) H)

def castV (κ : Req → ℕ) : Req → ℤ := fun q => (κ q : ℤ)

theorem castV_moveCnt {κ : Req → ℕ} {q : Req} (h : 1 ≤ κ q) (q' : Req) :
    castV (moveCnt κ q q') = castV κ - eR q + eR q' := by
  funext x
  simp only [castV, moveCnt, eR, Pi.add_apply, Pi.sub_apply, Pi.single_apply]
  by_cases h1 : x = q
  · subst h1
    by_cases h2 : x = q'
    · subst h2; simp; omega
    · simp [h2]; omega
  · by_cases h2 : x = q'
    · subst h2; simp [h1]
    · simp [h1, h2]

theorem meet_full_left (r : Req) : meet full r = r := by
  simp [meet]

theorem sum_moveCnt {κ : Req → ℕ} {q : Req} (h : 1 ≤ κ q) (q' : Req) :
    ∑ x, moveCnt κ q q' x = ∑ x, κ x := by
  have h1 := congrArg (fun v : Req → ℤ => ∑ x, v x) (castV_moveCnt h q')
  simp only [castV, eR, Pi.add_apply, Pi.sub_apply, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.sum_pi_single', Finset.mem_univ, ↓reduceIte] at h1
  have h2 : ((∑ x, moveCnt κ q q' x : ℕ) : ℤ) = ((∑ x, κ x : ℕ) : ℤ) := by
    push_cast; linarith
  exact_mod_cast h2

theorem sum_sCnt (κ : Req → ℕ) :
    ∑ q, sCnt (castV κ) q = ((∑ q, κ q : ℕ) : ℝ) - (κ full : ℝ) := by
  have h : ∀ q, sCnt (castV κ) q = (κ q : ℝ) - if q = full then (κ q : ℝ) else 0 := by
    intro q
    unfold sCnt castV
    split_ifs with hq
    · subst hq; ring
    · simp
  rw [Finset.sum_congr rfl fun q _ => h q, Finset.sum_sub_distrib, Finset.sum_ite_eq']
  simp

theorem eval_insP {M : ℕ} (hM : 0 < M) (r : Req) {H : (Req → ℤ) → ℝ[X]}
    {G : (Req → ℕ) → ℝ}
    (hHG : ∀ κ' : Req → ℕ, ∑ q, κ' q = M → (H (castV κ')).eval (1 / M : ℝ) = G κ')
    {κ : Req → ℕ} (hκ : ∑ q, κ q = M) :
    (insP r H (castV κ)).eval (1 / M : ℝ) = insOp M r G κ := by
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hterm : ∀ q, (κ q : ℝ) * G (moveCnt κ q (meet q r)) =
      (if q = full then (κ q : ℝ) * (H (insV r (castV κ))).eval (1 / M : ℝ) else 0) +
        sCnt (castV κ) q * (H (castV κ - eR q + eR (meet q r))).eval (1 / M : ℝ) := by
    intro q
    by_cases hq0 : κ q = 0
    · have : sCnt (castV κ) q = 0 := by simp [sCnt, castV, hq0]
      rw [this, hq0]; simp
    have hq1 : 1 ≤ κ q := Nat.one_le_iff_ne_zero.mpr hq0
    rw [← hHG _ ((sum_moveCnt hq1 _).trans hκ), castV_moveCnt hq1]
    by_cases hq : q = full
    · subst hq
      simp [sCnt, insV, meet_full_left]
    · simp [sCnt, hq, castV]
  have h1 : ∑ q, (κ q : ℝ) / M * G (moveCnt κ q (meet q r)) =
      (1 / M) * ∑ q, (κ q : ℝ) * G (moveCnt κ q (meet q r)) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun q _ => by ring
  have h2 : ∑ q, (κ q : ℝ) * G (moveCnt κ q (meet q r)) =
      (κ full : ℝ) * (H (insV r (castV κ))).eval (1 / M : ℝ) +
        ∑ q, sCnt (castV κ) q * (H (castV κ - eR q + eR (meet q r))).eval (1 / M : ℝ) := by
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp
  have h3 : ∑ q, sCnt (castV κ) q * ((H (castV κ - eR q + eR (meet q r))).eval (1 / M : ℝ) -
        (H (insV r (castV κ))).eval (1 / M : ℝ)) =
      ∑ q, sCnt (castV κ) q * (H (castV κ - eR q + eR (meet q r))).eval (1 / M : ℝ) -
        (∑ q, sCnt (castV κ) q) * (H (insV r (castV κ))).eval (1 / M : ℝ) := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun q _ => by ring
  have hs := sum_sCnt κ
  rw [hκ] at hs
  unfold insOp insP
  simp only [eval_add, eval_mul, eval_X, eval_finsetSum, eval_C, eval_sub]
  rw [h1, h2, h3, hs]
  field_simp
  ring

theorem eval_flagP (a x : ℝ) (m : Bool) :
    (flagP a m).eval x = if m then a * x else 1 - a * x := by
  cases m <;> simp [flagP]

theorem eval_lineP {M : ℕ} (hM : 0 < M) (θ ρ : ℝ) (r : Req) {H : (Req → ℤ) → ℝ[X]}
    {G : (Req → ℕ) → ℝ}
    (hHG : ∀ κ' : Req → ℕ, ∑ q, κ' q = M → (H (castV κ')).eval (1 / M : ℝ) = G κ')
    {κ : Req → ℕ} (hκ : ∑ q, κ q = M) :
    (lineP θ ρ r H (castV κ)).eval (1 / M : ℝ) =
      lineOp M (ρ / (2 * M)) (θ / (4 * M)) r G κ := by
  have hin : ∀ r', ∀ κ' : Req → ℕ, ∑ q, κ' q = M →
      (insP r' H (castV κ')).eval (1 / M : ℝ) = insOp M r' G κ' :=
    fun r' κ' h => eval_insP hM r' hHG h
  unfold lineP lineOp
  simp only [eval_finsetSum, eval_mul, eval_C, eval_flagP]
  refine Finset.sum_congr rfl fun f _ => ?_
  have hw : ∀ m : Bool, (if m then θ / 2 * (1 / M : ℝ) else 1 - θ / 2 * (1 / M : ℝ)) =
      flagWeight (θ / (4 * M)) m := by
    intro m; cases m <;> simp [flagWeight] <;> ring
  rw [hw, hw]
  rcases f with ⟨m1, m2, m3⟩
  cases m3
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hin _ κ hκ]; ring
  · simp only [↓reduceIte]
    rw [eval_insP hM _ (hin _) hκ]; ring

theorem eval_chainP {M : ℕ} (hM : 0 < M) (θ ρ : ℝ) :
    ∀ {n : ℕ} (lam : Fin n → Req) {H : (Req → ℤ) → ℝ[X]} {G : (Req → ℕ) → ℝ},
      (∀ κ' : Req → ℕ, ∑ q, κ' q = M → (H (castV κ')).eval (1 / M : ℝ) = G κ') →
      ∀ {κ : Req → ℕ}, ∑ q, κ q = M →
        (chainP θ ρ lam H (castV κ)).eval (1 / M : ℝ) =
          lumpChain M (ρ / (2 * M)) (θ / (4 * M)) lam G κ
  | 0, _, _, _, hHG, _, hκ => hHG _ hκ
  | n + 1, lam, H, G, hHG, κ, hκ => by
    rw [chainP, lumpChain]
    exact eval_chainP hM θ ρ (Fin.tail lam)
      (fun κ' h => eval_lineP hM θ ρ (lam 0) hHG h) hκ

def FullFree {α : Type*} (H : (Req → ℤ) → α) : Prop :=
  ∀ v w : Req → ℤ, (∀ q, q ≠ full → v q = w q) → H v = H w

theorem agree_add {v w : Req → ℤ} (h : ∀ q, q ≠ full → v q = w q) (t : Req → ℤ) :
    ∀ q, q ≠ full → (v + t) q = (w + t) q := fun q hq => by simp [h q hq]

theorem fullFree_insP (r : Req) {H : (Req → ℤ) → ℝ[X]} (hH : FullFree H) :
    FullFree (insP r H) := by
  intro v w h
  have hs : sCnt v = sCnt w := by
    funext q
    unfold sCnt
    split_ifs with hq
    · rfl
    · rw [h q hq]
  have hi : H (insV r v) = H (insV r w) := by
    refine hH _ _ fun q hq => ?_
    simp only [insV, Pi.add_apply, Pi.sub_apply, h q hq]
  unfold insP
  rw [hs, hi]
  congr 2
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [hH (v - eR q + eR (meet q r)) (w - eR q + eR (meet q r)) fun x hx => by
    simp only [Pi.add_apply, Pi.sub_apply, h x hx]]

theorem fullFree_lineP (θ ρ : ℝ) (r : Req) {H : (Req → ℤ) → ℝ[X]} (hH : FullFree H) :
    FullFree (lineP θ ρ r H) := by
  intro v w h
  unfold lineP
  refine Finset.sum_congr rfl fun f _ => ?_
  split_ifs
  · rw [fullFree_insP _ (fullFree_insP _ hH) v w h]
  · rw [fullFree_insP _ hH v w h]

theorem chainP_congr_full (θ ρ : ℝ) :
    ∀ {n : ℕ} (lam : Fin n → Req) {H : (Req → ℤ) → ℝ[X]}, FullFree H →
      FullFree (chainP θ ρ lam H)
  | 0, _, _, hH => hH
  | n + 1, lam, _, hH => by
    rw [show (chainP θ ρ lam _) = chainP θ ρ (Fin.tail lam) (lineP θ ρ (lam 0) _) from rfl]
    exact chainP_congr_full θ ρ (Fin.tail lam) (fullFree_lineP θ ρ (lam 0) hH)

end Rhone.Coalescent.WFTwoLocusDual
