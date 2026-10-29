/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.TwoLocusWFLump

/-!
# One ancestral step of the two-locus Wright-Fisher dual on counts

Source: griffiths1991_two_locus_graph, p. 101. -/

@[expose] public section
noncomputable section
namespace Rhone.Coalescent.WFTwoLocusDual
open Finset

def meet (q r : Req) : Req := (q.1 ∩ r.1, q.2 ∩ r.2)

def ins {M : ℕ} (S : DualState M) (p : Fin M) (r : Req) : DualState M :=
  fun s => if s = p then meet (S s) r else S s

def moveCnt (κ : Req → ℕ) (q q' : Req) : Req → ℕ :=
  fun x => κ x - (if x = q then 1 else 0) + (if x = q' then 1 else 0)

theorem cnt_eq_sum {M : ℕ} (S : DualState M) (x : Req) :
    cnt S x = ∑ s, if S s = x then 1 else 0 := by
  unfold cnt
  rw [Finset.card_filter]

theorem cnt_ins {M : ℕ} (S : DualState M) (p : Fin M) (r : Req) :
    cnt (ins S p r) = moveCnt (cnt S) (S p) (meet (S p) r) := by
  funext x
  simp only [moveCnt]
  rw [cnt_eq_sum, cnt_eq_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ p),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ p)]
  have hrest : ∑ s ∈ univ.erase p, (if ins S p r s = x then 1 else 0) =
      ∑ s ∈ univ.erase p, (if S s = x then 1 else 0) :=
    Finset.sum_congr rfl fun s hs => by
      rw [ins, ite_eq_right (Finset.ne_of_mem_erase hs)]
  have hp : ins S p r p = meet (S p) r := by simp [ins]
  rw [hrest, hp]
  generalize (∑ s ∈ univ.erase p, if S s = x then 1 else 0) = A
  by_cases h1 : S p = x
  · subst h1
    by_cases h2 : meet (S p) r = S p
    · rw [h2]; simp; omega
    · simp [h2, Ne.symm h2]
  · by_cases h2 : meet (S p) r = x
    · subst h2; simp [h1, Ne.symm h1]; omega
    · simp [h1, h2, Ne.symm h1, Ne.symm h2]

def insOp (M : ℕ) (r : Req) (G : (Req → ℕ) → ℝ) (κ : Req → ℕ) : ℝ :=
  ∑ q, (κ q : ℝ) / M * G (moveCnt κ q (meet q r))

theorem sum_comp_cnt {M : ℕ} (S : DualState M) (g : Req → ℝ) :
    ∑ s, g (S s) = ∑ q, (cnt S q : ℝ) * g q := by
  rw [← Finset.sum_fiberwise univ S fun s => g (S s)]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_congr rfl fun s hs => by rw [(Finset.mem_filter.mp hs).2], Finset.sum_const,
    nsmul_eq_mul]
  rfl

theorem sum_ins {M : ℕ} (S : DualState M) (r : Req) (G : (Req → ℕ) → ℝ) :
    ∑ p, (1 / M : ℝ) * G (cnt (ins S p r)) = insOp M r G (cnt S) := by
  simp_rw [cnt_ins]
  rw [sum_comp_cnt S fun q => (1 / M : ℝ) * G (moveCnt (cnt S) q (meet q r))]
  unfold insOp
  refine Finset.sum_congr rfl fun q _ => ?_
  ring

def insertReq {M : ℕ} (S : DualState M) (ch : Choice M) (r : Req) : DualState M := fun s =>
  ((S s).1 ∩ (if parentA ch = s then mutReq ch.2.2.1 r.1 else univ),
   (S s).2 ∩ (if parentB ch = s then mutReq ch.2.2.2.1 r.2 else univ))

theorem insertReq_eq {M : ℕ} (S : DualState M) (ch : Choice M) (r : Req) :
    insertReq S ch r = if ch.2.2.2.2 then
      ins (ins S ch.1 (mutReq ch.2.2.1 r.1, univ)) ch.2.1 (univ, mutReq ch.2.2.2.1 r.2)
    else ins S ch.1 (mutReq ch.2.2.1 r.1, mutReq ch.2.2.2.1 r.2) := by
  obtain ⟨p1, p2, mA, mB, rc⟩ := ch
  funext s
  cases rc
  · simp only [insertReq, parentA, parentB, ins, meet, Bool.false_eq_true, ↓reduceIte]
    by_cases h : p1 = s
    · subst h; simp
    · simp [h, Ne.symm h]
  · simp only [insertReq, parentA, parentB, ins, meet, ↓reduceIte]
    by_cases h1 : p1 = s <;> by_cases h2 : p2 = s
    · subst h1; subst h2; simp
    · subst h1; simp [h2, Ne.symm h2]
    · subst h2; simp [h1, Ne.symm h1]
    · simp [h1, h2, Ne.symm h1, Ne.symm h2]

def flagWeight (u : ℝ) (m : Bool) : ℝ := if m then 2 * u else 1 - 2 * u

def lineOp (M : ℕ) (c u : ℝ) (r : Req) (G : (Req → ℕ) → ℝ) (κ : Req → ℕ) : ℝ :=
  ∑ f : Bool × Bool × Bool,
    flagWeight u f.1 * flagWeight u f.2.1 * (if f.2.2 then c else 1 - c) *
      (mutFactor f.1 r.1 * mutFactor f.2.1 r.2) *
      (if f.2.2 then insOp M (mutReq f.1 r.1, univ) (insOp M (univ, mutReq f.2.1 r.2) G) κ
       else insOp M (mutReq f.1 r.1, mutReq f.2.1 r.2) G κ)

def choiceEquiv (M : ℕ) : Choice M ≃ (Bool × Bool × Bool) × (Fin M × Fin M) where
  toFun ch := ((ch.2.2.1, ch.2.2.2.1, ch.2.2.2.2), (ch.1, ch.2.1))
  invFun x := (x.2.1, x.2.2, x.1.1, x.1.2.1, x.1.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem sum_lineFactor_insertReq {M : ℕ} (hM : 0 < M) (c u : ℝ) (S : DualState M) (r : Req)
    (G : (Req → ℕ) → ℝ) :
    ∑ ch : Choice M, lineFactor c u r ch * G (cnt (insertReq S ch r)) =
      lineOp M c u r G (cnt S) := by
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have hone : ∑ _p : Fin M, (1 / M : ℝ) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  rw [← (choiceEquiv M).symm.sum_comp, Fintype.sum_prod_type]
  unfold lineOp
  refine Finset.sum_congr rfl fun f _ => ?_
  obtain ⟨mA, mB, rc⟩ := f
  rw [Fintype.sum_prod_type]
  simp only [choiceEquiv, Equiv.coe_fn_symm_mk, lineFactor, choiceWeight, insertReq_eq]
  cases rc
  · simp only [Bool.false_eq_true, ↓reduceIte, flagWeight]
    calc _ = (∑ p1 : Fin M, (1 / M : ℝ) *
            G (cnt (ins S p1 (mutReq mA r.1, mutReq mB r.2)))) *
          ((if mA = true then 2 * u else 1 - 2 * u) * (if mB = true then 2 * u else 1 - 2 * u) *
            (1 - c) * (mutFactor mA r.1 * mutFactor mB r.2)) * ∑ _p : Fin M, (1 / M : ℝ) := by
          rw [Finset.sum_mul, Finset.sum_mul]
          refine Finset.sum_congr rfl fun p1 _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun p2 _ => ?_
          ring_nf
      _ = _ := by rw [hone, sum_ins]; ring
  · simp only [↓reduceIte, flagWeight]
    calc _ = (∑ p1 : Fin M, (1 / M : ℝ) * ∑ p2 : Fin M, (1 / M : ℝ) *
            G (cnt (ins (ins S p1 (mutReq mA r.1, univ)) p2 (univ, mutReq mB r.2)))) *
          ((if mA = true then 2 * u else 1 - 2 * u) * (if mB = true then 2 * u else 1 - 2 * u) *
            c * (mutFactor mA r.1 * mutFactor mB r.2)) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun p1 _ => ?_
          rw [Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun p2 _ => ?_
          ring_nf
      _ = _ := by
          simp_rw [sum_ins]
          ring

theorem mem_inf_iff {ι : Type*} (s : Finset ι) (f : ι → Finset (Fin 2)) (b : Fin 2) :
    b ∈ s.inf f ↔ ∀ i ∈ s, b ∈ f i :=
  Finset.mem_inf

def stepL {M n : ℕ} (lam : Fin n → Req) (α : Fin n → Choice M) : DualState M := fun s =>
  ((univ.filter fun k => parentA (α k) = s).inf fun k => mutReq (α k).2.2.1 (lam k).1,
   (univ.filter fun k => parentB (α k) = s).inf fun k => mutReq (α k).2.2.2.1 (lam k).2)

theorem stepL_cons {M n : ℕ} (r : Req) (lam : Fin n → Req) (ch : Choice M)
    (α : Fin n → Choice M) :
    stepL (Fin.cons r lam : Fin (n + 1) → Req) (Fin.cons ch α : Fin (n + 1) → Choice M) =
      insertReq (stepL lam α) ch r := by
  funext s
  simp only [stepL, insertReq]
  ext1
  · ext b
    simp only [mem_inf_iff, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter,
      Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ]
    by_cases h : parentA ch = s <;> simp [h, and_comm]
  · ext b
    simp only [mem_inf_iff, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter,
      Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ]
    by_cases h : parentB ch = s <;> simp [h, and_comm]

theorem stepL_zero {M : ℕ} (lam : Fin 0 → Req) (α : Fin 0 → Choice M) :
    stepL lam α = fullState M := by
  funext s
  simp [stepL, fullState]

def lumpChain (M : ℕ) (c u : ℝ) : {n : ℕ} → (Fin n → Req) → ((Req → ℕ) → ℝ) → (Req → ℕ) → ℝ
  | 0, _, G => G
  | _ + 1, lam, G => lumpChain M c u (Fin.tail lam) (lineOp M c u (lam 0) G)

theorem sum_stepL {M : ℕ} (hM : 0 < M) (c u : ℝ) :
    ∀ {n : ℕ} (lam : Fin n → Req) (G : (Req → ℕ) → ℝ),
      ∑ α : Fin n → Choice M, (∏ k, lineFactor c u (lam k) (α k)) * G (cnt (stepL lam α)) =
        lumpChain M c u lam G (cnt (fullState M))
  | 0, lam, G => by
    simp [stepL_zero, lumpChain]
  | n + 1, lam, G => by
    rw [lumpChain, ← sum_stepL hM c u (Fin.tail lam) (lineOp M c u (lam 0) G)]
    rw [← (Fin.consEquiv fun _ : Fin (n + 1) => Choice M).sum_comp, Fintype.sum_prod_type,
      Finset.sum_comm]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [← sum_lineFactor_insertReq hM c u (stepL (Fin.tail lam) α) (lam 0) G, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ch _ => ?_
    have hlam : lam = Fin.cons (lam 0) (Fin.tail lam) := (Fin.cons_self_tail lam).symm
    simp only [Fin.consEquiv, Equiv.coe_fn_mk]
    rw [Fin.prod_univ_succ]
    conv_lhs => rw [hlam]
    rw [stepL_cons]
    simp only [Fin.cons_zero, Fin.cons_succ, Fin.tail]
    ring

end Rhone.Coalescent.WFTwoLocusDual
