/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.TwoLocusWFPoly

/-!
# First-order term of the lumped step of the two-locus Wright-Fisher dual

Source: griffiths1991_two_locus_graph, p. 101. -/

@[expose] public section
noncomputable section
namespace Rhone.Coalescent.WFTwoLocusDual
open Finset Polynomial

@[simp] theorem eval_zero_insP (r : Req) (H : (Req → ℤ) → ℝ[X]) (v : Req → ℤ) :
    (insP r H v).eval 0 = (H (insV r v)).eval 0 := by
  simp [insP]

@[simp] theorem deriv_insP (r : Req) (H : (Req → ℤ) → ℝ[X]) (v : Req → ℤ) :
    (derivative (insP r H v)).eval 0 = (derivative (H (insV r v))).eval 0 +
      ∑ q, sCnt v q * ((H (v - eR q + eR (meet q r))).eval 0 - (H (insV r v)).eval 0) := by
  simp [insP, derivative_mul, eval_finsetSum]

def lin1 (θ ρ : ℝ) (r : Req) (G : (Req → ℤ) → ℝ) (v : Req → ℤ) : ℝ :=
  ∑ q, sCnt v q * (G (v - eR q + eR (meet q r)) - G (insV r v)) +
    θ / 2 * (mutFactor true r.1 * G (insV (univ, r.2) v) - G (insV r v)) +
    θ / 2 * (mutFactor true r.2 * G (insV (r.1, univ) v) - G (insV r v)) +
    ρ / 2 * (G (insV (univ, r.2) (insV (r.1, univ) v)) - G (insV r v))

@[simp] theorem eval_zero_lineP (θ ρ : ℝ) (r : Req) (H : (Req → ℤ) → ℝ[X]) (v : Req → ℤ) :
    (lineP θ ρ r H v).eval 0 = (H (insV r v)).eval 0 := by
  simp [lineP, Fintype.sum_prod_type, flagP, mutReq, mutFactor]

theorem deriv_lineP (θ ρ : ℝ) (r : Req) (H : (Req → ℤ) → ℝ[X]) (v : Req → ℤ) :
    (derivative (lineP θ ρ r H v)).eval 0 = (derivative (H (insV r v))).eval 0 +
      lin1 θ ρ r (fun w => (H w).eval 0) v := by
  simp only [lineP, Fintype.sum_prod_type, Fintype.sum_bool, flagP, mutReq, ↓reduceIte,
    Bool.false_eq_true, derivative_add, derivative_mul, derivative_sub, derivative_one,
    derivative_C, derivative_X, eval_add, eval_mul, eval_sub, eval_one, eval_C, eval_X,
    eval_zero, deriv_insP, eval_zero_insP, Prod.mk.eta, lin1]
  simp only [mutFactor, Bool.false_eq_true, ↓reduceIte]
  ring

def pairV (v : Req → ℤ) (q q' : Req) : Req → ℤ := v - eR q - eR q' + eR full + eR (meet q q')

def lin0 (θ ρ : ℝ) (q : Req) (G : (Req → ℤ) → ℝ) (v : Req → ℤ) : ℝ :=
  θ / 2 * (mutFactor true q.1 * G (v - eR q + eR (univ, q.2)) - G v) +
    θ / 2 * (mutFactor true q.2 * G (v - eR q + eR (q.1, univ)) - G v) +
    ρ / 2 * (G (v - eR q + eR (q.1, univ) - eR full + eR (univ, q.2)) - G v)

def gam (θ ρ : ℝ) (G : (Req → ℤ) → ℝ) (v : Req → ℤ) : ℝ :=
  (1 / 2) * ∑ q, ∑ q', sCnt v q * (sCnt v q' - if q = q' then 1 else 0) *
      (G (pairV v q q') - G v) +
    ∑ q, sCnt v q * lin0 θ ρ q G v

theorem meet_comm (q q' : Req) : meet q q' = meet q' q := by
  simp [meet, Finset.inter_comm]

theorem sCnt_insV {r : Req} (hr : r ≠ full) (v : Req → ℤ) (q : Req) :
    sCnt (insV r v) q = sCnt v q + if q = r then 1 else 0 := by
  unfold sCnt
  by_cases hq : q = full
  · subst hq; simp [Ne.symm hr]
  · by_cases hqr : q = r
    · subst hqr; simp [hq, insV, eR]
    · simp [hq, hqr, insV, eR]

theorem pair_sum_shift (s : Req → ℝ) (r : Req) (F : Req → Req → ℝ)
    (hF : ∀ q q', F q q' = F q' q) :
    (1 / 2) * ∑ q, ∑ q', (s q + if q = r then 1 else 0) *
        ((s q' + if q' = r then 1 else 0) - if q = q' then 1 else 0) * F q q' -
      (1 / 2) * ∑ q, ∑ q', s q * (s q' - if q = q' then 1 else 0) * F q q' =
      ∑ q, s q * F q r := by
  have hsplit : ∀ q q', (s q + if q = r then 1 else 0) *
      ((s q' + if q' = r then 1 else 0) - if q = q' then 1 else 0) * F q q' -
      s q * (s q' - if q = q' then 1 else 0) * F q q' =
      (if q' = r then s q * F q q' else 0) +
        (if q = r then (s q' + (if q' = r then 1 else 0) - if q = q' then 1 else 0) * F q q'
          else 0) := by
    intro q q'
    split_ifs <;> ring
  have hA : ∑ q, ∑ q', (if q' = r then s q * F q q' else 0) = ∑ q, s q * F q r := by
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_ite_eq']
    simp
  have hB : ∑ q, ∑ q', (if q = r then
        (s q' + (if q' = r then 1 else 0) - if q = q' then 1 else 0) * F q q' else 0) =
      ∑ q', (s q' + (if q' = r then 1 else 0) - if r = q' then 1 else 0) * F r q' := by
    rw [Finset.sum_eq_single r (fun b _ hb => by simp [hb]) (by simp)]
    simp only [ite_true]
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib, hsplit, Finset.sum_add_distrib]
  rw [hA, hB]
  have h2 : ∑ q', (s q' + (if q' = r then 1 else 0) - if r = q' then 1 else 0) * F r q' =
      ∑ q, s q * F q r := by
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hF r q]
    by_cases h : q = r
    · subst h; simp
    · simp [h, Ne.symm h]
  rw [h2]
  ring

theorem lin1_eq_gam_sub (θ ρ : ℝ) {r : Req} (hr : r ≠ full) (G : (Req → ℤ) → ℝ)
    (v : Req → ℤ) :
    lin1 θ ρ r G v = gam θ ρ G (insV r v) - gam θ ρ (fun w => G (insV r w)) v := by
  have hpair : ∀ q q', pairV (insV r v) q q' = insV r (pairV v q q') := by
    intro q q'; simp only [pairV, insV]; abel
  have hlin0 : ∀ q, lin0 θ ρ q G (insV r v) = lin0 θ ρ q (fun w => G (insV r w)) v := by
    intro q
    unfold lin0
    have e1 : insV r v - eR q + eR (univ, q.2) = insV r (v - eR q + eR (univ, q.2)) := by
      simp only [insV]; abel
    have e2 : insV r v - eR q + eR (q.1, univ) = insV r (v - eR q + eR (q.1, univ)) := by
      simp only [insV]; abel
    have e3 : insV r v - eR q + eR (q.1, univ) - eR full + eR (univ, q.2) =
        insV r (v - eR q + eR (q.1, univ) - eR full + eR (univ, q.2)) := by
      simp only [insV]; abel
    rw [e3, e1, e2]
  set F : Req → Req → ℝ := fun q q' => G (pairV (insV r v) q q') - G (insV r v) with hFdef
  have hF : ∀ q q', F q q' = F q' q := by
    intro q q'
    simp only [hFdef, pairV, meet_comm q q']
    congr 2
    abel
  have hshift := pair_sum_shift (sCnt v) r F hF
  have hF0 : ∀ q q', G (pairV (insV r v) q q') - G (insV r v) = F q q' := fun _ _ => rfl
  have hF' : ∀ q q', G (insV r (pairV v q q')) - G (insV r v) = F q q' := by
    intro q q'; simp only [hFdef, hpair]
  have hL : ∑ q, (sCnt v q + if q = r then 1 else 0) * lin0 θ ρ q (fun w => G (insV r w)) v =
      ∑ q, sCnt v q * lin0 θ ρ q (fun w => G (insV r w)) v +
        lin0 θ ρ r (fun w => G (insV r w)) v := by
    simp only [add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hgam1 : gam θ ρ G (insV r v) =
      (1 / 2) * ∑ q, ∑ q', (sCnt v q + if q = r then 1 else 0) *
        ((sCnt v q' + if q' = r then 1 else 0) - if q = q' then 1 else 0) * F q q' +
      ∑ q, (sCnt v q + if q = r then 1 else 0) * lin0 θ ρ q (fun w => G (insV r w)) v := by
    unfold gam
    simp only [sCnt_insV hr, hlin0, hF0]
  have hgam2 : gam θ ρ (fun w => G (insV r w)) v =
      (1 / 2) * ∑ q, ∑ q', sCnt v q * (sCnt v q' - if q = q' then 1 else 0) * F q q' +
      ∑ q, sCnt v q * lin0 θ ρ q (fun w => G (insV r w)) v := by
    unfold gam
    simp only [hF']
  have hFr : ∀ q, F q r = G (v - eR q + eR (meet q r)) - G (insV r v) := by
    intro q
    simp only [hFdef]
    congr 2
    simp only [pairV, insV]; abel
  have hlin0r : lin0 θ ρ r (fun w => G (insV r w)) v =
      θ / 2 * (mutFactor true r.1 * G (insV (univ, r.2) v) - G (insV r v)) +
      θ / 2 * (mutFactor true r.2 * G (insV (r.1, univ) v) - G (insV r v)) +
      ρ / 2 * (G (insV (univ, r.2) (insV (r.1, univ) v)) - G (insV r v)) := by
    unfold lin0
    have e1 : insV r (v - eR r + eR (univ, r.2)) = insV (univ, r.2) v := by
      simp only [insV]; abel
    have e2 : insV r (v - eR r + eR (r.1, univ)) = insV (r.1, univ) v := by
      simp only [insV]; abel
    have e3 : insV r (v - eR r + eR (r.1, univ) - eR full + eR (univ, r.2)) =
        insV (univ, r.2) (insV (r.1, univ) v) := by
      simp only [insV]; abel
    beta_reduce
    rw [e1, e2, e3]
  have hC : ∑ q, sCnt v q * (G (v - eR q + eR (meet q r)) - G (insV r v)) =
      ∑ q, sCnt v q * F q r := by
    simp only [hFr]
  rw [hgam1, hgam2, hL]
  unfold lin1
  rw [hC, hlin0r]
  linarith [hshift]

def insAll {n : ℕ} (lam : Fin n → Req) (v : Req → ℤ) : Req → ℤ :=
  v + ∑ k, (eR (lam k) - eR full)

theorem insV_insAll_tail {n : ℕ} (lam : Fin (n + 1) → Req) (v : Req → ℤ) :
    insV (lam 0) (insAll (Fin.tail lam) v) = insAll lam v := by
  simp only [insV, insAll, Fin.sum_univ_succ, Fin.tail]
  abel

theorem gam_zero (θ ρ : ℝ) (G : (Req → ℤ) → ℝ) : gam θ ρ G 0 = 0 := by
  simp [gam, sCnt]

theorem chainP_first_order (θ ρ : ℝ) :
    ∀ {n : ℕ} (lam : Fin n → Req), (∀ k, lam k ≠ full) → ∀ (H : (Req → ℤ) → ℝ[X])
      (v : Req → ℤ),
      (chainP θ ρ lam H v).eval 0 = (H (insAll lam v)).eval 0 ∧
      (derivative (chainP θ ρ lam H v)).eval 0 =
        (derivative (H (insAll lam v))).eval 0 +
          gam θ ρ (fun w => (H w).eval 0) (insAll lam v) -
          gam θ ρ (fun w => (H (insAll lam w)).eval 0) v
  | 0, lam, _, H, v => by
    have h : ∀ w, insAll lam w = w := fun w => by simp [insAll]
    simp only [h]
    exact ⟨rfl, by rw [chainP]; ring⟩
  | n + 1, lam, hlam, H, v => by
    obtain ⟨ih1, ih2⟩ := chainP_first_order θ ρ (Fin.tail lam) (fun k => hlam k.succ)
      (lineP θ ρ (lam 0) H) v
    have hfun : (fun w => (lineP θ ρ (lam 0) H w).eval 0) =
        fun w => (H (insV (lam 0) w)).eval 0 := by
      funext w; exact eval_zero_lineP θ ρ _ H w
    have hfun' : (fun w => (lineP θ ρ (lam 0) H (insAll (Fin.tail lam) w)).eval 0) =
        fun w => (H (insAll lam w)).eval 0 := by
      funext w; rw [eval_zero_lineP, insV_insAll_tail]
    rw [show chainP θ ρ lam H v = chainP θ ρ (Fin.tail lam) (lineP θ ρ (lam 0) H) v from rfl]
    refine ⟨by rw [ih1, eval_zero_lineP, insV_insAll_tail], ?_⟩
    rw [ih2, hfun, hfun', deriv_lineP, lin1_eq_gam_sub θ ρ (hlam 0), insV_insAll_tail]
    ring

end Rhone.Coalescent.WFTwoLocusDual
