/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.MarkovChain.WFMutationRecombination
public import Rhone.Dynamics.LDMeasures

/-!
# Ancestral process and duality of the finite two-locus Wright-Fisher chain

Source: griffiths1991_two_locus_graph, p. 101; ewens2004, sec. 3.1. -/

@[expose] public section
noncomputable section
namespace Rhone.Coalescent.WFTwoLocusDual
open Finset MarkovChain Rhone.Dynamics MarkovChain.WFAllocationLD

abbrev Req := Finset (Fin 2) × Finset (Fin 2)

abbrev DualState (M : ℕ) := Fin M → Req

def ind (S : Finset (Fin 2)) (b : Fin 2) : ℝ := if b ∈ S then 1 else 0

def reqInd (r : Req) (i : Fin 4) : ℝ := ind r.1 (firstIndex i) * ind r.2 (secondIndex i)

def hit {M : ℕ} (x : Fin M → Fin 4) (ζ : DualState M) : ℝ := ∏ s, reqInd (ζ s) (x s)

def sampleProb (M : ℕ) (a : AlleleCounts M 4) (ζ : DualState M) : ℝ :=
  (∑ x : Fin M → Fin 4, if wfAlleleAllocationCounts M 4 x = a then hit x ζ else 0) /
    ((univ.filter fun x : Fin M → Fin 4 => wfAlleleAllocationCounts M 4 x = a).card : ℝ)

abbrev Choice (M : ℕ) := Fin M × Fin M × Bool × Bool × Bool

def choiceWeight (M : ℕ) (c u : ℝ) (ch : Choice M) : ℝ :=
  (1 / M) * (1 / M) * (if ch.2.2.1 then 2 * u else 1 - 2 * u) *
    (if ch.2.2.2.1 then 2 * u else 1 - 2 * u) * (if ch.2.2.2.2 then c else 1 - c)

def mutReq (m : Bool) (S : Finset (Fin 2)) : Finset (Fin 2) := if m then univ else S

def mutFactor (m : Bool) (S : Finset (Fin 2)) : ℝ := if m then (S.card : ℝ) / 2 else 1

def parentA {M : ℕ} (ch : Choice M) : Fin M := ch.1

def parentB {M : ℕ} (ch : Choice M) : Fin M := if ch.2.2.2.2 then ch.2.1 else ch.1

def lineFactor {M : ℕ} (c u : ℝ) (r : Req) (ch : Choice M) : ℝ :=
  choiceWeight M c u ch * (mutFactor ch.2.2.1 r.1 * mutFactor ch.2.2.2.1 r.2)

def ancStep {M : ℕ} (ζ : DualState M) (ω : Fin M → Choice M) : DualState M := fun s =>
  ((univ.filter fun t => parentA (ω t) = s).inf fun t => mutReq (ω t).2.2.1 (ζ t).1,
   (univ.filter fun t => parentB (ω t) = s).inf fun t => mutReq (ω t).2.2.2.1 (ζ t).2)

def ancWeight (M : ℕ) (c u : ℝ) (ζ : DualState M) (ω : Fin M → Choice M) : ℝ :=
  ∏ t, lineFactor c u (ζ t) (ω t)

def ancKernel (M : ℕ) (c u : ℝ) (ζ ζ' : DualState M) : ℝ :=
  ∑ ω : Fin M → Choice M, if ancStep ζ ω = ζ' then ancWeight M c u ζ ω else 0

theorem ind_univ (b : Fin 2) : ind univ b = 1 := by simp [ind]

theorem card_eq_ind (S : Finset (Fin 2)) : (S.card : ℝ) = ind S 0 + ind S 1 := by
  have h : (S.card : ℝ) = ∑ b : Fin 2, ind S b := by
    simp only [ind]
    rw [Finset.sum_boole]
    congr 2
    ext b; simp
  rw [h, Fin.sum_univ_two]

theorem vector_countGametes (M : ℕ) (a : AlleleCounts M 4) (i : Fin 4) :
    TwoLocusSelection.vector (countGametes M a) i = (a.val i : ℝ) / M := by
  fin_cases i <;> rfl

theorem sum_countGametes (M : ℕ) (x : Fin M → Fin 4) (f : Fin 4 → ℝ) :
    ∑ i, TwoLocusSelection.vector (countGametes M (wfAlleleAllocationCounts M 4 x)) i * f i =
      (1 / M) * ∑ s, f (x s) := by
  simp_rw [vector_countGametes, wfAlleleAllocationCounts_apply]
  rw [← Finset.sum_fiberwise univ x (fun s => f (x s)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => f i) (fun s hs => by rw [(Finset.mem_filter.mp hs).2]),
    Finset.sum_const, nsmul_eq_mul]
  ring

theorem forced_req (c u : ℝ) (g : Gametes ℝ) (fa fb : Fin 2 → ℝ) :
    ∑ j, TwoLocusSelection.vector (forcedGametes c u g) j *
        (fa (firstIndex j) * fb (secondIndex j)) =
      (1 - c) * ∑ i, TwoLocusSelection.vector g i *
          (((1 - 2 * u) * fa (firstIndex i) + u * (fa 0 + fa 1)) *
            ((1 - 2 * u) * fb (secondIndex i) + u * (fb 0 + fb 1))) +
        c * (∑ i, TwoLocusSelection.vector g i *
            ((1 - 2 * u) * fa (firstIndex i) + u * (fa 0 + fa 1))) *
          (∑ i, TwoLocusSelection.vector g i *
            ((1 - 2 * u) * fb (secondIndex i) + u * (fb 0 + fb 1))) := by
  simp [Fin.sum_univ_four, forcedGametes, independentMutation, TwoLocusSelection.fromVector,
    TwoLocusSelection.vector, Rhone.Dynamics.MutationModels.pimTransition, firstIndex, secondIndex,
    Gametes.recombine, Gametes.pA, Gametes.pB, Gametes.pA', Gametes.pB']
  ring

theorem split_pq {M : ℕ} (hM : 0 < M) (c : ℝ) (F G H : Fin M → ℝ) :
    (1 - c) * ((1 / M) * ∑ s, F s) + c * ((1 / M) * ∑ p, G p) * ((1 / M) * ∑ q, H q) =
      ∑ p : Fin M, ∑ q : Fin M,
        ((1 - c) * (1 / M) * (1 / M) * F p + c * (1 / M) * (1 / M) * (G p * H q)) := by
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.mul_sum]
  rw [← Finset.sum_mul]
  field_simp

theorem sum_choice {M : ℕ} (F : Choice M → ℝ) :
    ∑ ch : Choice M, F ch = ∑ p : Fin M, ∑ q : Fin M, ∑ mA : Bool, ∑ mB : Bool, ∑ r : Bool,
      F (p, q, mA, mB, r) := by
  simp only [Fintype.sum_prod_type]

/-- Source: ewens2004, sec. 3.1. -/
theorem offspring_req {M : ℕ} (hM : 0 < M) (c u : ℝ) (x : Fin M → Fin 4) (r : Req) :
    ∑ i, TwoLocusSelection.vector
        (forcedGametes c u (countGametes M (wfAlleleAllocationCounts M 4 x))) i * reqInd r i =
      ∑ ch : Choice M, lineFactor c u r ch *
        (ind (mutReq ch.2.2.1 r.1) (firstIndex (x (parentA ch))) *
          ind (mutReq ch.2.2.2.1 r.2) (secondIndex (x (parentB ch)))) := by
  simp only [reqInd]
  rw [forced_req, sum_countGametes, sum_countGametes, sum_countGametes, split_pq hM, sum_choice]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  simp only [Fintype.sum_bool, lineFactor, choiceWeight, mutFactor, mutReq, parentA, parentB,
    ite_true, Bool.false_eq_true, ite_false, ind_univ, card_eq_ind]
  ring

theorem prod_ind_inf {ι : Type*} (A : ι → Finset (Fin 2)) (b : Fin 2)
    (T : Finset ι) : ∏ t ∈ T, ind (A t) b = ind (T.inf A) b := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [ind]
  | insert a T ha ih =>
    rw [Finset.prod_insert ha, ih, Finset.inf_insert, Finset.inf_eq_inter]
    simp only [ind, Finset.mem_inter]
    split_ifs <;> simp_all

theorem prod_ind_fiber {M : ℕ} (A : Fin M → Finset (Fin 2)) (π : Fin M → Fin M)
    (y : Fin M → Fin 2) :
    ∏ t, ind (A t) (y (π t)) = ∏ s, ind ((univ.filter fun t => π t = s).inf A) (y s) := by
  rw [← Finset.prod_fiberwise univ π (fun t => ind (A t) (y (π t)))]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [Finset.prod_congr rfl (g := fun t => ind (A t) (y s))
    (fun t ht => by rw [(Finset.mem_filter.mp ht).2]), prod_ind_inf]

/-- Source: ewens2004, sec. 3.1. -/
theorem prod_offspring {M : ℕ} (hM : 0 < M) (c u : ℝ) (x : Fin M → Fin 4) (ζ : DualState M) :
    ∏ t, ∑ i, TwoLocusSelection.vector
        (forcedGametes c u (countGametes M (wfAlleleAllocationCounts M 4 x))) i *
          reqInd (ζ t) i =
      ∑ ω : Fin M → Choice M, ancWeight M c u ζ ω * hit x (ancStep ζ ω) := by
  simp_rw [offspring_req hM]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  have hA := prod_ind_fiber (fun t => mutReq (ω t).2.2.1 (ζ t).1) (fun t => parentA (ω t))
    (fun s => firstIndex (x s))
  have hB := prod_ind_fiber (fun t => mutReq (ω t).2.2.2.1 (ζ t).2) (fun t => parentB (ω t))
    (fun s => secondIndex (x s))
  rw [hA, hB, hit, ancWeight, ← Finset.prod_mul_distrib]
  rfl

theorem sum_ancKernel_mul {M : ℕ} (c u : ℝ) (ζ : DualState M) (f : DualState M → ℝ) :
    ∑ ζ', ancKernel M c u ζ ζ' * f ζ' =
      ∑ ω : Fin M → Choice M, ancWeight M c u ζ ω * f (ancStep ζ ω) := by
  unfold ancKernel
  simp_rw [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp

/-- Source: ewens2004, sec. 3.1. -/
theorem fiber_card_pos (M : ℕ) (a : AlleleCounts M 4) :
    0 < (univ.filter fun x : Fin M → Fin 4 => wfAlleleAllocationCounts M 4 x = a).card := by
  rw [Finset.card_pos]
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  have hlaw := wfMultiallele_allocation_law M 4 a a
  have hzero : (∑ ω : Fin M → Fin 4,
      if wfAlleleAllocationCounts M 4 ω = a
      then wfMultialleleAllocationWeight M 4 a ω else 0) = 0 := by
    rw [← Finset.sum_filter, h, Finset.sum_empty]
  have hpos : 0 < wfMultiallele M 4 a a := by
    unfold wfMultiallele
    apply mul_pos
    · exact_mod_cast Nat.multinomial_pos _ _
    · apply Finset.prod_pos
      intro l _
      rcases Nat.eq_zero_or_pos (a.val l) with h0 | h0
      · rw [h0, pow_zero]; exact one_pos
      · have hle : a.val l ≤ M := by
          calc a.val l ≤ ∑ l', a.val l' :=
                Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
            _ = M := a.sum
        have : (0 : ℝ) < a.val l := by exact_mod_cast h0
        have : (0 : ℝ) < M := by exact_mod_cast lt_of_lt_of_le h0 hle
        positivity
  linarith

theorem sampleProb_eq (M : ℕ) (a : AlleleCounts M 4) (ζ : DualState M) :
    sampleProb M a ζ =
      (∑ x ∈ univ.filter (fun x : Fin M → Fin 4 => wfAlleleAllocationCounts M 4 x = a),
        hit x ζ) /
      ((univ.filter fun x : Fin M → Fin 4 => wfAlleleAllocationCounts M 4 x = a).card : ℝ) := by
  rw [sampleProb, Finset.sum_filter]

def offspringReq (M : ℕ) (c u : ℝ) (a : AlleleCounts M 4) (r : Req) : ℝ :=
  ∑ i, TwoLocusSelection.vector (forcedGametes c u (countGametes M a)) i * reqInd r i

/-- Source: ewens2004, sec. 3.1. -/
theorem ancKernel_sampleProb {M : ℕ} (hM : 0 < M) (c u : ℝ) (a : AlleleCounts M 4)
    (ζ : DualState M) :
    ∑ ζ', ancKernel M c u ζ ζ' * sampleProb M a ζ' = ∏ t, offspringReq M c u a (ζ t) := by
  rw [sum_ancKernel_mul]
  simp_rw [sampleProb_eq, mul_div_assoc', ← Finset.sum_div, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hc : ((univ.filter fun x : Fin M → Fin 4 =>
      wfAlleleAllocationCounts M 4 x = a).card : ℝ) ≠ 0 := by
    exact_mod_cast (fiber_card_pos M a).ne'
  rw [div_eq_iff hc]
  rw [Finset.sum_congr rfl (g := fun _ => ∏ t, offspringReq M c u a (ζ t)) (fun x hx => by
    rw [← (Finset.mem_filter.mp hx).2]
    exact (prod_offspring hM c u x ζ).symm)]
  rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

theorem allocationWeight_eq {M : ℕ} (v : Fin 4 → ℝ) (ω : Fin M → Fin 4) :
    ∏ t, v (ω t) = ∏ i, v i ^ (wfAlleleAllocationCounts M 4 ω).val i := by
  rw [← Finset.prod_fiberwise univ ω (fun t => v (ω t))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finset.prod_congr rfl (g := fun _ => v i) (fun s hs => by rw [(Finset.mem_filter.mp hs).2]),
    Finset.prod_const, wfAlleleAllocationCounts_apply]

/-- Source: ewens2004, sec. 3.1. -/
theorem forcedCountKernel_sampleProb {M : ℕ} (c u : ℝ) (a : AlleleCounts M 4)
    (ζ : DualState M) :
    ∑ b, forcedCountKernel M c u a b * sampleProb M b ζ = ∏ t, offspringReq M c u a (ζ t) := by
  set h := forcedGametes c u (countGametes M a)
  set v := TwoLocusSelection.vector h
  have h1 : ∑ b, forcedCountKernel M c u a b * sampleProb M b ζ =
      ∑ ω : Fin M → Fin 4, allocationWeight M h ω *
        sampleProb M (wfAlleleAllocationCounts M 4 ω) ζ :=
    sampling_expectation_allocation M h _
  rw [h1]
  have hw : ∀ ω : Fin M → Fin 4, allocationWeight M h ω =
      ∏ i, v i ^ (wfAlleleAllocationCounts M 4 ω).val i := fun ω => allocationWeight_eq v ω
  simp_rw [hw, sampleProb_eq, mul_div_assoc', Finset.mul_sum]
  have key : ∀ ω : Fin M → Fin 4,
      (∑ x ∈ univ.filter (fun x : Fin M → Fin 4 =>
          wfAlleleAllocationCounts M 4 x = wfAlleleAllocationCounts M 4 ω),
          (∏ i, v i ^ (wfAlleleAllocationCounts M 4 ω).val i) * hit x ζ) /
        ((univ.filter fun x : Fin M → Fin 4 =>
          wfAlleleAllocationCounts M 4 x = wfAlleleAllocationCounts M 4 ω).card : ℝ) =
      ∑ x : Fin M → Fin 4,
        if wfAlleleAllocationCounts M 4 ω = wfAlleleAllocationCounts M 4 x then
          ((∏ t, v (x t)) * hit x ζ) /
            ((univ.filter fun y : Fin M → Fin 4 =>
              wfAlleleAllocationCounts M 4 y = wfAlleleAllocationCounts M 4 x).card : ℝ)
        else 0 := by
    intro ω
    rw [Finset.sum_div, Finset.sum_filter]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : wfAlleleAllocationCounts M 4 x = wfAlleleAllocationCounts M 4 ω
    · rw [ite_eq_left hx, ite_eq_left hx.symm, allocationWeight_eq v x, hx]
    · rw [ite_eq_right hx, ite_eq_right (Ne.symm hx)]
  simp_rw [key]
  rw [Finset.sum_comm]
  have key2 : ∀ x : Fin M → Fin 4,
      (∑ ω : Fin M → Fin 4,
        if wfAlleleAllocationCounts M 4 ω = wfAlleleAllocationCounts M 4 x then
          ((∏ t, v (x t)) * hit x ζ) /
            ((univ.filter fun y : Fin M → Fin 4 =>
              wfAlleleAllocationCounts M 4 y = wfAlleleAllocationCounts M 4 x).card : ℝ)
        else 0) = (∏ t, v (x t)) * hit x ζ := by
    intro x
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hc : ((univ.filter fun y : Fin M → Fin 4 =>
        wfAlleleAllocationCounts M 4 y = wfAlleleAllocationCounts M 4 x).card : ℝ) ≠ 0 := by
      exact_mod_cast (fiber_card_pos M _).ne'
    field_simp
  simp_rw [key2]
  simp only [hit, ← Finset.prod_mul_distrib, offspringReq]
  rw [Fintype.prod_sum]

/-- Source: ewens2004, sec. 3.1. -/
theorem forcedCountKernel_duality {M : ℕ} (hM : 0 < M) (c u : ℝ) (a : AlleleCounts M 4)
    (ζ : DualState M) :
    ∑ b, forcedCountKernel M c u a b * sampleProb M b ζ =
      ∑ ζ', ancKernel M c u ζ ζ' * sampleProb M a ζ' := by
  rw [forcedCountKernel_sampleProb, ancKernel_sampleProb hM]

theorem choiceWeight_nonneg {M : ℕ} {c u : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 2) (ch : Choice M) : 0 ≤ choiceWeight M c u ch := by
  unfold choiceWeight
  have : 0 ≤ 1 - 2 * u := by linarith
  have : 0 ≤ 1 - c := by linarith
  have : (0 : ℝ) ≤ 1 / M := by positivity
  split_ifs <;> positivity

theorem sum_choiceWeight {M : ℕ} (hM : 0 < M) (c u : ℝ) :
    ∑ ch : Choice M, choiceWeight M c u ch = 1 := by
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  rw [sum_choice]
  simp only [choiceWeight, Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

theorem mutFactor_nonneg (m : Bool) (S : Finset (Fin 2)) : 0 ≤ mutFactor m S := by
  unfold mutFactor; split_ifs <;> positivity

theorem mutFactor_le_one (m : Bool) (S : Finset (Fin 2)) : mutFactor m S ≤ 1 := by
  unfold mutFactor
  split_ifs
  · have : S.card ≤ 2 := by simpa using Finset.card_le_univ S
    have : (S.card : ℝ) ≤ 2 := by exact_mod_cast this
    linarith
  · exact le_rfl

theorem lineFactor_nonneg {M : ℕ} {c u : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 2) (r : Req) (ch : Choice M) : 0 ≤ lineFactor c u r ch :=
  mul_nonneg (choiceWeight_nonneg hc0 hc1 hu0 hu1 ch)
    (mul_nonneg (mutFactor_nonneg _ _) (mutFactor_nonneg _ _))

theorem lineFactor_le {M : ℕ} {c u : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 2) (r : Req) (ch : Choice M) :
    lineFactor c u r ch ≤ choiceWeight M c u ch := by
  unfold lineFactor
  have h1 := choiceWeight_nonneg hc0 hc1 hu0 hu1 ch
  have h2 : mutFactor ch.2.2.1 r.1 * mutFactor ch.2.2.2.1 r.2 ≤ 1 := by
    have := mutFactor_le_one ch.2.2.1 r.1
    have := mutFactor_le_one ch.2.2.2.1 r.2
    have := mutFactor_nonneg ch.2.2.1 r.1
    have := mutFactor_nonneg ch.2.2.2.1 r.2
    nlinarith
  nlinarith

theorem ancWeight_nonneg {M : ℕ} {c u : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 2) (ζ : DualState M) (ω : Fin M → Choice M) : 0 ≤ ancWeight M c u ζ ω :=
  Finset.prod_nonneg fun _t _ => lineFactor_nonneg hc0 hc1 hu0 hu1 _ _

theorem ancWeight_le {M : ℕ} {c u : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 2) (ζ : DualState M) (ω : Fin M → Choice M) :
    ancWeight M c u ζ ω ≤ ∏ t, choiceWeight M c u (ω t) :=
  Finset.prod_le_prod₀ (fun _t _ => lineFactor_nonneg hc0 hc1 hu0 hu1 _ _)
    (fun _t _ => lineFactor_le hc0 hc1 hu0 hu1 _ _)

theorem sum_prod_choiceWeight {M : ℕ} (hM : 0 < M) (c u : ℝ) :
    ∑ ω : Fin M → Choice M, ∏ t, choiceWeight M c u (ω t) = 1 := by
  rw [← Fintype.prod_sum (fun (_ : Fin M) (ch : Choice M) => choiceWeight M c u ch)]
  simp [sum_choiceWeight hM]

theorem ancKernel_nonneg {M : ℕ} {c u : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 2) (ζ ζ' : DualState M) : 0 ≤ ancKernel M c u ζ ζ' :=
  Finset.sum_nonneg fun ω _ => by
    split_ifs
    · exact ancWeight_nonneg hc0 hc1 hu0 hu1 ζ ω
    · exact le_rfl

theorem sum_ancKernel_le_one {M : ℕ} (hM : 0 < M) {c u : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2) (ζ : DualState M) :
    ∑ ζ', ancKernel M c u ζ ζ' ≤ 1 := by
  have h := sum_ancKernel_mul (M := M) c u ζ (fun _ => 1)
  simp only [mul_one] at h
  rw [h, ← sum_prod_choiceWeight hM c u]
  exact Finset.sum_le_sum fun ω _ => ancWeight_le hc0 hc1 hu0 hu1 ζ ω

def countMatrix (M : ℕ) (c u : ℝ) :
    Matrix (AlleleCounts M 4) (AlleleCounts M 4) ℝ := Matrix.of (forcedCountKernel M c u)

def ancMatrix (M : ℕ) (c u : ℝ) : Matrix (DualState M) (DualState M) ℝ :=
  Matrix.of (ancKernel M c u)

def dualMatrix (M : ℕ) : Matrix (AlleleCounts M 4) (DualState M) ℝ := Matrix.of (sampleProb M)

/-- Source: ewens2004, sec. 3.1. -/
theorem duality_matrix {M : ℕ} (hM : 0 < M) (c u : ℝ) :
    countMatrix M c u * dualMatrix M = dualMatrix M * (ancMatrix M c u).transpose := by
  ext a ζ
  simp only [Matrix.mul_apply, countMatrix, dualMatrix, ancMatrix, Matrix.of_apply,
    Matrix.transpose_apply]
  rw [forcedCountKernel_duality hM]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

/-- Source: ewens2004, sec. 3.1. -/
theorem duality_matrix_pow {M : ℕ} (hM : 0 < M) (c u : ℝ) (t : ℕ) :
    countMatrix M c u ^ t * dualMatrix M = dualMatrix M * ((ancMatrix M c u) ^ t).transpose := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ, Matrix.mul_assoc, duality_matrix hM, ← Matrix.mul_assoc, ih, Matrix.mul_assoc,
      ← Matrix.transpose_mul, ← pow_succ']

/-- Source: ewens2004, sec. 3.1. -/
theorem forcedCountKernel_pow_duality {M : ℕ} (hM : 0 < M) (c u : ℝ) (t : ℕ)
    (a : AlleleCounts M 4) (ζ : DualState M) :
    ∑ b, (countMatrix M c u ^ t) a b * sampleProb M b ζ =
      ∑ ζ', (ancMatrix M c u ^ t) ζ ζ' * sampleProb M a ζ' := by
  have h := congrFun (congrFun (duality_matrix_pow hM c u t) a) ζ
  simp only [Matrix.mul_apply, dualMatrix, Matrix.of_apply, Matrix.transpose_apply] at h
  rw [h]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

def fullState (M : ℕ) : DualState M := fun _ => (univ, univ)

theorem hit_fullState {M : ℕ} (x : Fin M → Fin 4) : hit x (fullState M) = 1 := by
  simp [hit, fullState, reqInd, ind_univ]

theorem sampleProb_fullState (M : ℕ) (a : AlleleCounts M 4) :
    sampleProb M a (fullState M) = 1 := by
  rw [sampleProb_eq]
  simp only [hit_fullState, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hc : ((univ.filter fun x : Fin M → Fin 4 =>
      wfAlleleAllocationCounts M 4 x = a).card : ℝ) ≠ 0 := by
    exact_mod_cast (fiber_card_pos M a).ne'
  exact div_self hc

theorem hit_nonneg {M : ℕ} (x : Fin M → Fin 4) (ζ : DualState M) : 0 ≤ hit x ζ :=
  Finset.prod_nonneg fun _ _ => by unfold reqInd ind; split_ifs <;> norm_num

theorem hit_le_one {M : ℕ} (x : Fin M → Fin 4) (ζ : DualState M) : hit x ζ ≤ 1 :=
  Finset.prod_le_one₀ (fun _ _ => by unfold reqInd ind; split_ifs <;> norm_num)
    (fun _ _ => by unfold reqInd ind; split_ifs <;> norm_num)

theorem sampleProb_nonneg (M : ℕ) (a : AlleleCounts M 4) (ζ : DualState M) :
    0 ≤ sampleProb M a ζ := by
  rw [sampleProb_eq]
  exact div_nonneg (Finset.sum_nonneg fun x _ => hit_nonneg x ζ) (Nat.cast_nonneg _)

theorem sampleProb_le_one (M : ℕ) (a : AlleleCounts M 4) (ζ : DualState M) :
    sampleProb M a ζ ≤ 1 := by
  rw [sampleProb_eq, div_le_one (by exact_mod_cast fiber_card_pos M a)]
  calc _ ≤ ∑ x ∈ univ.filter (fun x : Fin M → Fin 4 => wfAlleleAllocationCounts M 4 x = a),
        (1 : ℝ) := Finset.sum_le_sum fun x _ => hit_le_one x ζ
    _ = _ := by simp

theorem ancStep_fullState {M : ℕ} (ω : Fin M → Choice M) :
    ancStep (fullState M) ω = fullState M := by
  funext s
  simp only [ancStep, fullState, mutReq]
  ext1
  · simp only
    refine le_antisymm (by simp) (Finset.le_inf fun t _ => ?_)
    split_ifs <;> exact le_rfl
  · simp only
    refine le_antisymm (by simp) (Finset.le_inf fun t _ => ?_)
    split_ifs <;> exact le_rfl

theorem ancWeight_fullState {M : ℕ} (c u : ℝ) (ω : Fin M → Choice M) :
    ancWeight M c u (fullState M) ω = ∏ t, choiceWeight M c u (ω t) := by
  unfold ancWeight lineFactor
  refine Finset.prod_congr rfl fun t _ => ?_
  simp [fullState, mutFactor]

theorem ancKernel_fullState {M : ℕ} (hM : 0 < M) (c u : ℝ) (ζ' : DualState M) :
    ancKernel M c u (fullState M) ζ' = if fullState M = ζ' then 1 else 0 := by
  unfold ancKernel
  simp_rw [ancStep_fullState, ancWeight_fullState]
  split_ifs
  · exact sum_prod_choiceWeight hM c u
  · simp

def allRedraw {M : ℕ} (ω : Fin M → Choice M) : Prop :=
  ∀ t, (ω t).2.2.1 = true ∧ (ω t).2.2.2.1 = true

instance {M : ℕ} : DecidablePred (allRedraw (M := M)) := fun ω => by
  unfold allRedraw; infer_instance

theorem ancStep_allRedraw {M : ℕ} (ζ : DualState M) (ω : Fin M → Choice M)
    (h : allRedraw ω) : ancStep ζ ω = fullState M := by
  funext s
  simp only [ancStep, fullState, mutReq]
  ext1
  · simp only
    refine le_antisymm (by simp) (Finset.le_inf fun t _ => ?_)
    rw [ite_eq_left (h t).1]
  · simp only
    refine le_antisymm (by simp) (Finset.le_inf fun t _ => ?_)
    rw [ite_eq_left (h t).2]

theorem sum_allRedraw {M : ℕ} (hM : 0 < M) (c u : ℝ) :
    ∑ ω : Fin M → Choice M, (if allRedraw ω then ∏ t, choiceWeight M c u (ω t) else 0) =
      (4 * u ^ 2) ^ M := by
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  have h1 : ∀ ω : Fin M → Choice M,
      (if allRedraw ω then ∏ t, choiceWeight M c u (ω t) else 0) =
        ∏ t, (if (ω t).2.2.1 = true ∧ (ω t).2.2.2.1 = true then
          choiceWeight M c u (ω t) else 0) := by
    intro ω
    unfold allRedraw
    split_ifs with h
    · exact Finset.prod_congr rfl fun t _ => by rw [ite_eq_left (h t)]
    · push Not at h
      obtain ⟨t, ht⟩ := h
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ t)
      rw [ite_eq_right]
      intro h'
      exact ht h'.1 h'.2
  simp_rw [h1]
  rw [← Fintype.prod_sum (fun (_ : Fin M) (ch : Choice M) =>
    if ch.2.2.1 = true ∧ ch.2.2.2.1 = true then choiceWeight M c u ch else 0)]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  rw [sum_choice]
  simp only [choiceWeight, Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false,
    and_true, and_false, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, add_zero]
  field_simp
  ring

theorem sum_ancKernel_ne_full_le {M : ℕ} (hM : 0 < M) {c u : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2) (ζ : DualState M) :
    ∑ ζ' ∈ univ.filter (· ≠ fullState M), ancKernel M c u ζ ζ' ≤ 1 - (4 * u ^ 2) ^ M := by
  have h := sum_ancKernel_mul (M := M) c u ζ (fun ζ' => if ζ' ≠ fullState M then 1 else 0)
  simp only [mul_ite, mul_one, mul_zero] at h
  rw [← Finset.sum_filter] at h
  rw [h, ← sum_allRedraw hM c u, ← sum_prod_choiceWeight hM c u, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun ω _ => ?_
  have hw0 := ancWeight_nonneg hc0 hc1 hu0 hu1 ζ ω
  have hw1 := ancWeight_le hc0 hc1 hu0 hu1 ζ ω
  by_cases hr : allRedraw ω
  · rw [ite_eq_left hr,
      ite_eq_right (by rw [ancStep_allRedraw ζ ω hr]; exact not_not.mpr rfl), sub_self]
  · rw [ite_eq_right hr, sub_zero]
    split_ifs
    · exact hw1
    · exact le_trans le_rfl (Finset.prod_nonneg fun t _ =>
        choiceWeight_nonneg hc0 hc1 hu0 hu1 _)

theorem ancMatrix_pow_nonneg {M : ℕ} {c u : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 2) (t : ℕ) (ζ ζ' : DualState M) : 0 ≤ (ancMatrix M c u ^ t) ζ ζ' := by
  induction t generalizing ζ' with
  | zero =>
    rw [pow_zero, Matrix.one_apply]
    split_ifs <;> norm_num
  | succ t ih =>
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg fun _ _ =>
      mul_nonneg (ih _) (ancKernel_nonneg hc0 hc1 hu0 hu1 _ _)

theorem sum_ancMatrix_pow_ne_full_le {M : ℕ} (hM : 0 < M) {c u : ℝ} (hc0 : 0 ≤ c)
    (hc1 : c ≤ 1) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2) (t : ℕ) (ζ : DualState M) :
    ∑ ζ' ∈ univ.filter (· ≠ fullState M), (ancMatrix M c u ^ t) ζ ζ' ≤
      (1 - (4 * u ^ 2) ^ M) ^ t := by
  induction t with
  | zero =>
    rw [pow_zero, pow_zero]
    calc _ ≤ ∑ ζ' : DualState M, (1 : Matrix (DualState M) (DualState M) ℝ) ζ ζ' :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun ζ' _ _ => by
            rw [Matrix.one_apply]; split_ifs <;> norm_num)
      _ = 1 := by simp [Matrix.one_apply]
  | succ t ih =>
    have hδ : 0 ≤ 1 - (4 * u ^ 2) ^ M := by
      have : 4 * u ^ 2 ≤ 1 := by nlinarith
      have : (4 * u ^ 2) ^ M ≤ 1 := pow_le_one₀ (by positivity) this
      linarith
    simp only [pow_succ, Matrix.mul_apply]
    rw [Finset.sum_comm]
    calc _ = ∑ ζ'' ∈ univ.filter (· ≠ fullState M), (ancMatrix M c u ^ t) ζ ζ'' *
          ∑ ζ' ∈ univ.filter (· ≠ fullState M), ancKernel M c u ζ'' ζ' := by
          rw [← Finset.sum_filter_add_sum_filter_not univ (· ≠ fullState M)]
          have hz : ∑ ζ'' ∈ univ.filter (fun ζ'' => ¬ ζ'' ≠ fullState M),
              ∑ ζ' ∈ univ.filter (· ≠ fullState M),
                (ancMatrix M c u ^ t) ζ ζ'' * ancMatrix M c u ζ'' ζ' = 0 := by
            refine Finset.sum_eq_zero fun ζ'' hζ'' => Finset.sum_eq_zero fun ζ' hζ' => ?_
            have h1 : ζ'' = fullState M := not_not.mp (Finset.mem_filter.mp hζ'').2
            have h2 := (Finset.mem_filter.mp hζ').2
            rw [h1, ancMatrix, Matrix.of_apply, ancKernel_fullState hM, ite_eq_right (Ne.symm h2),
              mul_zero]
          rw [hz, add_zero]
          refine Finset.sum_congr rfl fun ζ'' _ => ?_
          rw [Finset.mul_sum]
          rfl
      _ ≤ ∑ ζ'' ∈ univ.filter (· ≠ fullState M), (ancMatrix M c u ^ t) ζ ζ'' *
          (1 - (4 * u ^ 2) ^ M) :=
          Finset.sum_le_sum fun ζ'' _ => mul_le_mul_of_nonneg_left
            (sum_ancKernel_ne_full_le hM hc0 hc1 hu0 hu1 ζ'')
            (ancMatrix_pow_nonneg hc0 hc1 hu0 hu1 t ζ ζ'')
      _ = (∑ ζ'' ∈ univ.filter (· ≠ fullState M), (ancMatrix M c u ^ t) ζ ζ'') *
          (1 - (4 * u ^ 2) ^ M) := by rw [Finset.sum_mul]
      _ ≤ (1 - (4 * u ^ 2) ^ M) ^ t * (1 - (4 * u ^ 2) ^ M) :=
          mul_le_mul_of_nonneg_right ih hδ

def ancAbsorb (M : ℕ) (c u : ℝ) (ζ : DualState M) : ℝ :=
  Filter.limUnder Filter.atTop fun t => (ancMatrix M c u ^ t) ζ (fullState M)

open Filter Topology in
/-- Source: ewens2004, sec. 3.1. -/
theorem tendsto_ancMatrix_pow_full {M : ℕ} (hM : 0 < M) {c u : ℝ} (hc0 : 0 ≤ c)
    (hc1 : c ≤ 1) (hu0 : 0 < u) (hu1 : u ≤ 1 / 2) (π : AlleleCounts M 4 → ℝ)
    (hπ0 : ∀ a, 0 ≤ π a) (hπ1 : ∑ a, π a = 1)
    (hstat : ∀ b, ∑ a, π a * forcedCountKernel M c u a b = π b) (ζ : DualState M) :
    Tendsto (fun t => (ancMatrix M c u ^ t) ζ (fullState M)) atTop
      (𝓝 (∑ a, π a * sampleProb M a ζ)) := by
  set m : DualState M → ℝ := fun ζ' => ∑ a, π a * sampleProb M a ζ' with hm
  have hstatPow : ∀ t b, ∑ a, π a * (countMatrix M c u ^ t) a b = π b := by
    intro t
    induction t with
    | zero => intro b; simp [Matrix.one_apply]
    | succ t ih =>
      intro b
      simp only [pow_succ, Matrix.mul_apply, Finset.mul_sum]
      rw [Finset.sum_comm]
      rw [← hstat b]
      refine Finset.sum_congr rfl fun b' _ => ?_
      rw [← ih b', Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp [countMatrix, mul_assoc]
  have hfix : ∀ t, m ζ = ∑ ζ', (ancMatrix M c u ^ t) ζ ζ' * m ζ' := by
    intro t
    simp only [hm, Finset.mul_sum]
    rw [Finset.sum_comm]
    have : ∀ a, ∑ ζ', (ancMatrix M c u ^ t) ζ ζ' * (π a * sampleProb M a ζ') =
        π a * ∑ b, (countMatrix M c u ^ t) a b * sampleProb M b ζ := by
      intro a
      rw [forcedCountKernel_pow_duality hM, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    simp_rw [this]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← hstatPow t b, Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have hm0 : ∀ ζ', 0 ≤ m ζ' := fun ζ' =>
    Finset.sum_nonneg fun a _ => mul_nonneg (hπ0 a) (sampleProb_nonneg M a ζ')
  have hm1 : ∀ ζ', m ζ' ≤ 1 := fun ζ' => by
    calc m ζ' ≤ ∑ a, π a * 1 :=
          Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (sampleProb_le_one M a ζ') (hπ0 a)
      _ = 1 := by simp only [mul_one]; exact hπ1
  have hmfull : m (fullState M) = 1 := by
    change ∑ a, π a * sampleProb M a (fullState M) = 1
    simp only [sampleProb_fullState, mul_one]
    exact hπ1
  set δ := 1 - (4 * u ^ 2) ^ M
  have hδ0 : 0 ≤ δ := by
    have : 4 * u ^ 2 ≤ 1 := by nlinarith
    have : (4 * u ^ 2) ^ M ≤ 1 := pow_le_one₀ (by positivity) this
    simp only [δ]; linarith
  have hδ1 : δ < 1 := by
    simp only [δ]
    have : 0 < (4 * u ^ 2) ^ M := by positivity
    linarith
  have hbound : ∀ t, |(ancMatrix M c u ^ t) ζ (fullState M) - m ζ| ≤ δ ^ t := by
    intro t
    rw [hfix t, ← Finset.sum_filter_add_sum_filter_not univ (· ≠ fullState M)]
    have hone : ∑ ζ' ∈ univ.filter (fun ζ' => ¬ ζ' ≠ fullState M),
        (ancMatrix M c u ^ t) ζ ζ' * m ζ' = (ancMatrix M c u ^ t) ζ (fullState M) := by
      have : univ.filter (fun ζ' : DualState M => ¬ ζ' ≠ fullState M) = {fullState M} := by
        ext ζ'; simp
      rw [this, Finset.sum_singleton, hmfull, mul_one]
    rw [hone]
    have hS0 : 0 ≤ ∑ ζ' ∈ univ.filter (· ≠ fullState M), (ancMatrix M c u ^ t) ζ ζ' * m ζ' :=
      Finset.sum_nonneg fun ζ' _ => mul_nonneg (ancMatrix_pow_nonneg hc0 hc1 hu0.le hu1 t ζ ζ')
        (hm0 ζ')
    have hS1 : ∑ ζ' ∈ univ.filter (· ≠ fullState M), (ancMatrix M c u ^ t) ζ ζ' * m ζ' ≤ δ ^ t :=
      le_trans (Finset.sum_le_sum fun ζ' _ => mul_le_of_le_one_right
        (ancMatrix_pow_nonneg hc0 hc1 hu0.le hu1 t ζ ζ') (hm1 ζ'))
        (sum_ancMatrix_pow_ne_full_le hM hc0 hc1 hu0.le hu1 t ζ)
    rw [abs_le]
    constructor <;> linarith
  have hlim : Tendsto (fun t : ℕ => δ ^ t) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hδ0 hδ1
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun t => norm_nonneg _) (fun t => by
    rw [Real.norm_eq_abs]; exact hbound t) hlim

/-- Source: ewens2004, sec. 3.1. -/
theorem stationary_sampleProb_eq_ancAbsorb {M : ℕ} (hM : 0 < M) {c u : ℝ} (hc0 : 0 ≤ c)
    (hc1 : c ≤ 1) (hu0 : 0 < u) (hu1 : u ≤ 1 / 2) (π : AlleleCounts M 4 → ℝ)
    (hπ0 : ∀ a, 0 ≤ π a) (hπ1 : ∑ a, π a = 1)
    (hstat : ∀ b, ∑ a, π a * forcedCountKernel M c u a b = π b) (ζ : DualState M) :
    ∑ a, π a * sampleProb M a ζ = ancAbsorb M c u ζ :=
  ((tendsto_ancMatrix_pow_full hM hc0 hc1 hu0 hu1 π hπ0 hπ1 hstat ζ).limUnder_eq).symm

def sampleState (M : ℕ) {n : ℕ} (y : Fin n → Fin 4) : DualState M := fun s =>
  if h : s.val < n then ({firstIndex (y ⟨s.val, h⟩)}, {secondIndex (y ⟨s.val, h⟩)})
  else (univ, univ)

def sampleGametes {n : ℕ} (y : Fin n → Fin 4) : Gametes ℝ :=
  countGametes n (wfAlleleAllocationCounts n 4 y)

def sampleD {n : ℕ} (y : Fin n → Fin 4) : ℝ := (sampleGametes y).D

def sampleDPrime {n : ℕ} (y : Fin n → Fin 4) : ℝ :=
  Gametes.lewontinD' (sampleGametes y).pA (sampleGametes y).pB (sampleGametes y).D

def sampleRSq {n : ℕ} (y : Fin n → Fin 4) : ℝ :=
  Gametes.rSq (sampleGametes y).pA (sampleGametes y).pB (sampleGametes y).D

theorem type_eq_of_index {i j : Fin 4} (h1 : firstIndex i = firstIndex j)
    (h2 : secondIndex i = secondIndex j) : i = j := by
  revert h1 h2
  fin_cases i <;> fin_cases j <;> decide

theorem reqInd_singleton (i j : Fin 4) :
    reqInd ({firstIndex j}, {secondIndex j}) i = if i = j then 1 else 0 := by
  simp only [reqInd, ind, Finset.mem_singleton]
  by_cases h : i = j
  · subst h; simp
  · rw [ite_eq_right h]
    by_cases h1 : firstIndex i = firstIndex j
    · rw [ite_eq_left h1, ite_eq_right (fun h2 => h (type_eq_of_index h1 h2))]; ring
    · rw [ite_eq_right h1]; ring

theorem hit_sampleState {M n : ℕ} (hn : n ≤ M) (x : Fin M → Fin 4) (y : Fin n → Fin 4) :
    hit x (sampleState M y) = if y = (fun k => x (Fin.castLE hn k)) then 1 else 0 := by
  have hs : ∀ s : Fin M, reqInd (sampleState M y s) (x s) =
      if h : s.val < n then (if x s = y ⟨s.val, h⟩ then 1 else 0) else 1 := by
    intro s
    unfold sampleState
    by_cases h : s.val < n
    · rw [dite_eq_left h, dite_eq_left h, reqInd_singleton]
    · rw [dite_eq_right h, dite_eq_right h]
      change ind univ _ * ind univ _ = 1
      rw [ind_univ, ind_univ, one_mul]
  unfold hit
  simp_rw [hs]
  split_ifs with hy
  · refine Finset.prod_eq_one fun s _ => ?_
    split_ifs with h h'
    · rfl
    · exact absurd (by rw [hy]; rfl) h'
    · rfl
  · obtain ⟨k, hk⟩ : ∃ k, y k ≠ x (Fin.castLE hn k) := by
      by_contra hc
      push Not at hc
      exact hy (funext hc)
    refine Finset.prod_eq_zero (Finset.mem_univ (Fin.castLE hn k)) ?_
    have hlt : (Fin.castLE hn k).val < n := k.isLt
    rw [dite_eq_left hlt, ite_eq_right]
    intro h
    apply hk
    rw [h]
    rfl

theorem sum_sampleProb_sampleState {M n : ℕ} (hn : n ≤ M) (a : AlleleCounts M 4) :
    ∑ y : Fin n → Fin 4, sampleProb M a (sampleState M y) = 1 := by
  simp_rw [sampleProb_eq]
  rw [← Finset.sum_div, Finset.sum_comm]
  simp_rw [hit_sampleState hn, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Finset.sum_const, nsmul_eq_mul, mul_one]
  exact div_self (by exact_mod_cast (fiber_card_pos M a).ne')

/-- Source: ewens2004, sec. 3.1. -/
theorem expect_sample_pow {M : ℕ} (hM : 0 < M) (c u : ℝ) (t : ℕ) (a : AlleleCounts M 4)
    {n : ℕ} (f : (Fin n → Fin 4) → ℝ) :
    ∑ b, (countMatrix M c u ^ t) a b * ∑ y, sampleProb M b (sampleState M y) * f y =
      ∑ y, (∑ ζ', (ancMatrix M c u ^ t) (sampleState M y) ζ' * sampleProb M a ζ') * f y := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← forcedCountKernel_pow_duality hM, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- Source: ewens2004, sec. 3.1. -/
theorem stationary_expect_sample {M : ℕ} (hM : 0 < M) {c u : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hu0 : 0 < u) (hu1 : u ≤ 1 / 2) (π : AlleleCounts M 4 → ℝ) (hπ0 : ∀ a, 0 ≤ π a)
    (hπ1 : ∑ a, π a = 1) (hstat : ∀ b, ∑ a, π a * forcedCountKernel M c u a b = π b)
    {n : ℕ} (f : (Fin n → Fin 4) → ℝ) :
    ∑ a, π a * ∑ y, sampleProb M a (sampleState M y) * f y =
      ∑ y, ancAbsorb M c u (sampleState M y) * f y := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← stationary_sampleProb_eq_ancAbsorb hM hc0 hc1 hu0 hu1 π hπ0 hπ1 hstat, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => by ring

def swapA : Fin 4 → Fin 4 := ![2, 3, 0, 1]

theorem swapA_swapA (i : Fin 4) : swapA (swapA i) = i := by fin_cases i <;> rfl

theorem firstIndex_swapA (i : Fin 4) :
    firstIndex (swapA i) = Equiv.swap (0 : Fin 2) 1 (firstIndex i) := by
  fin_cases i <;> decide

theorem secondIndex_swapA (i : Fin 4) : secondIndex (swapA i) = secondIndex i := by
  fin_cases i <;> rfl

def flipSet (S : Finset (Fin 2)) : Finset (Fin 2) :=
  S.map (Equiv.swap (0 : Fin 2) 1).toEmbedding

theorem flipSet_flipSet (S : Finset (Fin 2)) : flipSet (flipSet S) = S := by
  ext b; simp [flipSet]

theorem flipSet_univ : flipSet univ = univ := Finset.map_univ_equiv _

theorem flipSet_inf {ι : Type*} (A : ι → Finset (Fin 2)) (T : Finset ι) :
    T.inf (fun t => flipSet (A t)) = flipSet (T.inf A) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [flipSet_univ]
  | insert a T ha ih =>
    rw [Finset.inf_insert, Finset.inf_insert, ih, Finset.inf_eq_inter, Finset.inf_eq_inter]
    exact (Finset.map_inter _ _).symm

theorem card_flipSet (S : Finset (Fin 2)) : (flipSet S).card = S.card := Finset.card_map _

def flipState {M : ℕ} (ζ : DualState M) : DualState M := fun s => (flipSet (ζ s).1, (ζ s).2)

theorem flipState_flipState {M : ℕ} (ζ : DualState M) : flipState (flipState ζ) = ζ := by
  funext s; simp [flipState, flipSet_flipSet]

theorem flipState_fullState (M : ℕ) : flipState (fullState M) = fullState M := by
  funext s; simp [flipState, fullState, flipSet_univ]

theorem mutReq_flipSet (m : Bool) (S : Finset (Fin 2)) :
    mutReq m (flipSet S) = flipSet (mutReq m S) := by
  cases m <;> simp [mutReq, flipSet_univ]

theorem ancStep_flipState {M : ℕ} (ζ : DualState M) (ω : Fin M → Choice M) :
    ancStep (flipState ζ) ω = flipState (ancStep ζ ω) := by
  funext s
  simp only [ancStep, flipState, mutReq_flipSet]
  rw [flipSet_inf]

theorem ancWeight_flipState {M : ℕ} (c u : ℝ) (ζ : DualState M) (ω : Fin M → Choice M) :
    ancWeight M c u (flipState ζ) ω = ancWeight M c u ζ ω := by
  simp [ancWeight, lineFactor, flipState, mutFactor, card_flipSet]

def flipPerm (M : ℕ) : DualState M ≃ DualState M :=
  Function.Involutive.toPerm flipState flipState_flipState

theorem ancKernel_flipState {M : ℕ} (c u : ℝ) (ζ ζ' : DualState M) :
    ancKernel M c u (flipState ζ) (flipState ζ') = ancKernel M c u ζ ζ' := by
  unfold ancKernel
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [ancStep_flipState, ancWeight_flipState]
  have : flipState (ancStep ζ ω) = flipState ζ' ↔ ancStep ζ ω = ζ' :=
    (flipPerm M).injective.eq_iff
  simp only [this]

theorem ancMatrix_pow_flipState {M : ℕ} (c u : ℝ) (t : ℕ) (ζ ζ' : DualState M) :
    (ancMatrix M c u ^ t) (flipState ζ) (flipState ζ') = (ancMatrix M c u ^ t) ζ ζ' := by
  induction t generalizing ζ' with
  | zero =>
    simp only [pow_zero, Matrix.one_apply]
    have : flipState ζ = flipState ζ' ↔ ζ = ζ' := (flipPerm M).injective.eq_iff
    simp only [this]
  | succ t ih =>
    simp only [pow_succ, Matrix.mul_apply]
    rw [← (flipPerm M).sum_comp]
    refine Finset.sum_congr rfl fun ζ'' _ => ?_
    have h1 : (flipPerm M) ζ'' = flipState ζ'' := rfl
    rw [h1, ih, ancMatrix, Matrix.of_apply, Matrix.of_apply, ancKernel_flipState]

theorem ancAbsorb_flipState {M : ℕ} (c u : ℝ) (ζ : DualState M) :
    ancAbsorb M c u (flipState ζ) = ancAbsorb M c u ζ := by
  unfold ancAbsorb
  congr 1
  funext t
  conv_lhs => rw [← flipState_fullState M]
  exact ancMatrix_pow_flipState c u t ζ (fullState M)

theorem sampleState_swapA {M n : ℕ} (y : Fin n → Fin 4) :
    sampleState M (fun k => swapA (y k)) = flipState (sampleState M y) := by
  funext s
  by_cases h : s.val < n
  · simp [sampleState, flipState, h, flipSet, firstIndex_swapA, secondIndex_swapA]
  · simp [sampleState, flipState, h, flipSet_univ]

theorem card_swapA {n : ℕ} (y : Fin n → Fin 4) (i : Fin 4) :
    (univ.filter fun k => swapA (y k) = i).card = (univ.filter fun k => y k = swapA i).card := by
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h; rw [← h, swapA_swapA]
  · intro h; rw [h, swapA_swapA]

theorem sampleGametes_swapA {n : ℕ} (y : Fin n → Fin 4) :
    sampleGametes (fun k => swapA (y k)) =
      ⟨(sampleGametes y).x21, (sampleGametes y).x22, (sampleGametes y).x11,
        (sampleGametes y).x12⟩ := by
  simp only [sampleGametes, countGametes, TwoLocusSelection.fromVector,
    wfAlleleAllocationCounts_apply, card_swapA]
  rfl

theorem sampleD_swapA {n : ℕ} (y : Fin n → Fin 4) :
    sampleD (fun k => swapA (y k)) = -sampleD y := by
  simp only [sampleD, sampleGametes_swapA, Gametes.D]
  ring

theorem lewontinD'_flip (pA pB D : ℝ) :
    Gametes.lewontinD' (1 - pA) pB (-D) = -Gametes.lewontinD' pA pB D := by
  unfold Gametes.lewontinD' Gametes.dMax
  rcases lt_trichotomy D 0 with h | h | h
  · rw [ite_eq_left (by linarith), ite_eq_right (by linarith), neg_div]
    congr 2
    rw [min_comm]; ring_nf
  · subst h; simp
  · rw [ite_eq_right (by linarith), ite_eq_left h.le, neg_div]
    congr 2
    rw [min_comm]; ring_nf

theorem sampleDPrime_swapA {n : ℕ} (hn : 0 < n) (y : Fin n → Fin 4) :
    sampleDPrime (fun k => swapA (y k)) = -sampleDPrime y := by
  have ht := count_gametes_total n hn (wfAlleleAllocationCounts n 4 y)
  have hpA : (sampleGametes (fun k => swapA (y k))).pA = 1 - (sampleGametes y).pA := by
    rw [sampleGametes_swapA]
    simp only [Gametes.pA]
    have : (sampleGametes y).total = 1 := ht
    unfold Gametes.total at this
    linarith
  have hpB : (sampleGametes (fun k => swapA (y k))).pB = (sampleGametes y).pB := by
    rw [sampleGametes_swapA]
    simp only [Gametes.pB]
    ring
  have hD : (sampleGametes (fun k => swapA (y k))).D = -(sampleGametes y).D := sampleD_swapA y
  rw [sampleDPrime, hpA, hpB, hD, lewontinD'_flip]
  rfl

def swapSamples (n : ℕ) : (Fin n → Fin 4) ≃ (Fin n → Fin 4) :=
  Function.Involutive.toPerm (fun y k => swapA (y k)) (fun y => by funext k; exact swapA_swapA _)

theorem sum_odd_eq_zero {M n : ℕ} (c u : ℝ) (f : (Fin n → Fin 4) → ℝ)
    (hf : ∀ y, f (fun k => swapA (y k)) = -f y) :
    ∑ y, ancAbsorb M c u (sampleState M y) * f y = 0 := by
  have h := (swapSamples n).sum_comp (fun y => ancAbsorb M c u (sampleState M y) * f y)
  have h2 : ∀ y, ancAbsorb M c u (sampleState M (swapSamples n y)) * f (swapSamples n y) =
      -(ancAbsorb M c u (sampleState M y) * f y) := by
    intro y
    change ancAbsorb M c u (sampleState M (fun k => swapA (y k))) *
      f (fun k => swapA (y k)) = _
    rw [sampleState_swapA, ancAbsorb_flipState, hf]
    ring
  simp_rw [h2, Finset.sum_neg_distrib] at h
  linarith

/-- Source: ewens2004, sec. 3.1. -/
theorem stationary_expect_sampleD {M : ℕ} (hM : 0 < M) {c u : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hu0 : 0 < u) (hu1 : u ≤ 1 / 2) (π : AlleleCounts M 4 → ℝ) (hπ0 : ∀ a, 0 ≤ π a)
    (hπ1 : ∑ a, π a = 1) (hstat : ∀ b, ∑ a, π a * forcedCountKernel M c u a b = π b) (n : ℕ) :
    ∑ a, π a * ∑ y : Fin n → Fin 4, sampleProb M a (sampleState M y) * sampleD y = 0 := by
  rw [stationary_expect_sample hM hc0 hc1 hu0 hu1 π hπ0 hπ1 hstat]
  exact sum_odd_eq_zero c u _ sampleD_swapA

/-- Source: ewens2004, sec. 3.1. -/
theorem stationary_expect_sampleDPrime {M : ℕ} (hM : 0 < M) {c u : ℝ} (hc0 : 0 ≤ c)
    (hc1 : c ≤ 1) (hu0 : 0 < u) (hu1 : u ≤ 1 / 2) (π : AlleleCounts M 4 → ℝ)
    (hπ0 : ∀ a, 0 ≤ π a) (hπ1 : ∑ a, π a = 1)
    (hstat : ∀ b, ∑ a, π a * forcedCountKernel M c u a b = π b) {n : ℕ} (hn : 0 < n) :
    ∑ a, π a * ∑ y : Fin n → Fin 4, sampleProb M a (sampleState M y) * sampleDPrime y = 0 := by
  rw [stationary_expect_sample hM hc0 hc1 hu0 hu1 π hπ0 hπ1 hstat]
  exact sum_odd_eq_zero c u _ (sampleDPrime_swapA hn)

/-- Source: ewens2004, sec. 3.1. -/
theorem stationary_expect_sampleD_of_le {M : ℕ} (hM : 0 < M) {c u : ℝ} (hc0 : 0 ≤ c)
    (hc1 : c ≤ 1) (hu0 : 0 < u) (hu1 : u ≤ 1 / 2) (π : AlleleCounts M 4 → ℝ)
    (hπ0 : ∀ a, 0 ≤ π a) (hπ1 : ∑ a, π a = 1)
    (hstat : ∀ b, ∑ a, π a * forcedCountKernel M c u a b = π b) {n : ℕ} (hn : n ≤ M) :
    ∑ a, π a * ∑ y : Fin n → Fin 4, sampleProb M a (sampleState M y) = 1 ∧
      ∑ a, π a * ∑ y : Fin n → Fin 4, sampleProb M a (sampleState M y) * sampleD y = 0 := by
  refine ⟨?_, stationary_expect_sampleD hM hc0 hc1 hu0 hu1 π hπ0 hπ1 hstat n⟩
  simp only [sum_sampleProb_sampleState hn, mul_one]
  exact hπ1

/-- Source: ewens2004, sec. 3.1. -/
theorem stationary_expect_sampleDPrime_of_le {M : ℕ} (hM : 0 < M) {c u : ℝ} (hc0 : 0 ≤ c)
    (hc1 : c ≤ 1) (hu0 : 0 < u) (hu1 : u ≤ 1 / 2) (π : AlleleCounts M 4 → ℝ)
    (hπ0 : ∀ a, 0 ≤ π a) (hπ1 : ∑ a, π a = 1)
    (hstat : ∀ b, ∑ a, π a * forcedCountKernel M c u a b = π b) {n : ℕ} (hn0 : 0 < n)
    (hn : n ≤ M) :
    ∑ a, π a * ∑ y : Fin n → Fin 4, sampleProb M a (sampleState M y) = 1 ∧
      ∑ a, π a * ∑ y : Fin n → Fin 4, sampleProb M a (sampleState M y) * sampleDPrime y =
        0 := by
  refine ⟨?_, stationary_expect_sampleDPrime hM hc0 hc1 hu0 hu1 π hπ0 hπ1 hstat hn0⟩
  simp only [sum_sampleProb_sampleState hn, mul_one]
  exact hπ1

theorem sampleGametes_isDist {n : ℕ} (hn : 0 < n) (y : Fin n → Fin 4) :
    (sampleGametes y).IsDist := by
  have ht := count_gametes_total n hn (wfAlleleAllocationCounts n 4 y)
  refine ⟨?_, ?_, ?_, ?_, ht⟩ <;>
    simp only [sampleGametes, countGametes, TwoLocusSelection.fromVector] <;> positivity

/-- Source: ewens2004, sec. 3.1. -/
theorem stationary_expect_sampleRSq {M : ℕ} (hM : 0 < M) {c u : ℝ} (hc0 : 0 ≤ c)
    (hc1 : c ≤ 1) (hu0 : 0 < u) (hu1 : u ≤ 1 / 2) (π : AlleleCounts M 4 → ℝ)
    (hπ0 : ∀ a, 0 ≤ π a) (hπ1 : ∑ a, π a = 1)
    (hstat : ∀ b, ∑ a, π a * forcedCountKernel M c u a b = π b) {n : ℕ} (hn0 : 0 < n)
    (hn : n ≤ M) :
    ∑ a, π a * ∑ y : Fin n → Fin 4, sampleProb M a (sampleState M y) * sampleRSq y =
        ∑ y : Fin n → Fin 4, ancAbsorb M c u (sampleState M y) * sampleRSq y ∧
      0 ≤ ∑ a, π a * ∑ y : Fin n → Fin 4, sampleProb M a (sampleState M y) * sampleRSq y ∧
      ∑ a, π a * ∑ y : Fin n → Fin 4, sampleProb M a (sampleState M y) * sampleRSq y ≤ 1 := by
  refine ⟨stationary_expect_sample hM hc0 hc1 hu0 hu1 π hπ0 hπ1 hstat _, ?_, ?_⟩
  · exact Finset.sum_nonneg fun a _ => mul_nonneg (hπ0 a) (Finset.sum_nonneg fun y _ =>
      mul_nonneg (sampleProb_nonneg M a _) (Gametes.rSq_nonneg (sampleGametes_isDist hn0 y)))
  · calc _ ≤ ∑ a, π a * ∑ y : Fin n → Fin 4, sampleProb M a (sampleState M y) * 1 :=
          Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ =>
            mul_le_mul_of_nonneg_left (Gametes.rSq_le_one (sampleGametes_isDist hn0 y))
              (sampleProb_nonneg M a _)) (hπ0 a)
      _ = 1 := by simp only [mul_one, sum_sampleProb_sampleState hn]; exact hπ1

theorem sum_ancMatrix_pow_le_one {M : ℕ} (hM : 0 < M) {c u : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2) (t : ℕ) (ζ : DualState M) :
    ∑ ζ', (ancMatrix M c u ^ t) ζ ζ' ≤ 1 := by
  induction t with
  | zero => simp [Matrix.one_apply]
  | succ t ih =>
    simp only [pow_succ, Matrix.mul_apply]
    rw [Finset.sum_comm]
    calc _ = ∑ ζ'', (ancMatrix M c u ^ t) ζ ζ'' * ∑ ζ', ancKernel M c u ζ'' ζ' := by
          refine Finset.sum_congr rfl fun ζ'' _ => ?_
          rw [Finset.mul_sum]
          rfl
      _ ≤ ∑ ζ'', (ancMatrix M c u ^ t) ζ ζ'' * 1 :=
          Finset.sum_le_sum fun ζ'' _ => mul_le_mul_of_nonneg_left
            (sum_ancKernel_le_one hM hc0 hc1 hu0 hu1 ζ'')
            (ancMatrix_pow_nonneg hc0 hc1 hu0 hu1 t ζ ζ'')
      _ ≤ 1 := by simpa only [mul_one] using ih

theorem ancMatrix_pow_full_le_one {M : ℕ} (hM : 0 < M) {c u : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2) (t : ℕ) (ζ : DualState M) :
    (ancMatrix M c u ^ t) ζ (fullState M) ≤ 1 :=
  le_trans (Finset.single_le_sum (fun ζ' _ => ancMatrix_pow_nonneg hc0 hc1 hu0 hu1 t ζ ζ')
    (Finset.mem_univ _)) (sum_ancMatrix_pow_le_one hM hc0 hc1 hu0 hu1 t ζ)

theorem monotone_ancMatrix_pow_full {M : ℕ} (hM : 0 < M) {c u : ℝ} (hc0 : 0 ≤ c)
    (hc1 : c ≤ 1) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2) (ζ : DualState M) :
    Monotone fun t => (ancMatrix M c u ^ t) ζ (fullState M) := by
  refine monotone_nat_of_le_succ fun t => ?_
  simp only [pow_succ, Matrix.mul_apply]
  calc (ancMatrix M c u ^ t) ζ (fullState M) =
        (ancMatrix M c u ^ t) ζ (fullState M) * ancMatrix M c u (fullState M) (fullState M) := by
        have h1 : ancMatrix M c u (fullState M) (fullState M) = 1 := by
          change ancKernel M c u _ _ = 1
          rw [ancKernel_fullState hM, ite_eq_left rfl]
        rw [h1, mul_one]
    _ ≤ _ := Finset.single_le_sum (f := fun ζ'' =>
        (ancMatrix M c u ^ t) ζ ζ'' * ancMatrix M c u ζ'' (fullState M))
        (fun ζ'' _ => mul_nonneg (ancMatrix_pow_nonneg hc0 hc1 hu0 hu1 t ζ ζ'')
          (ancKernel_nonneg hc0 hc1 hu0 hu1 ζ'' _)) (Finset.mem_univ _)

open Filter Topology in
theorem tendsto_ancMatrix_pow_ancAbsorb {M : ℕ} (hM : 0 < M) {c u : ℝ} (hc0 : 0 ≤ c)
    (hc1 : c ≤ 1) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2) (ζ : DualState M) :
    Tendsto (fun t => (ancMatrix M c u ^ t) ζ (fullState M)) atTop (𝓝 (ancAbsorb M c u ζ)) := by
  have h := tendsto_atTop_ciSup (monotone_ancMatrix_pow_full hM hc0 hc1 hu0 hu1 ζ)
    ⟨1, by rintro _ ⟨t, rfl⟩; exact ancMatrix_pow_full_le_one hM hc0 hc1 hu0 hu1 t ζ⟩
  rw [ancAbsorb, h.limUnder_eq]
  exact h

open Filter Topology in
theorem ancAbsorb_eq_sum_ancKernel {M : ℕ} (hM : 0 < M) {c u : ℝ} (hc0 : 0 ≤ c)
    (hc1 : c ≤ 1) (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2) (ζ : DualState M) :
    ancAbsorb M c u ζ = ∑ ζ', ancKernel M c u ζ ζ' * ancAbsorb M c u ζ' := by
  have hs : Tendsto (fun t => (ancMatrix M c u ^ (t + 1)) ζ (fullState M)) atTop
      (𝓝 (ancAbsorb M c u ζ)) :=
    (tendsto_ancMatrix_pow_ancAbsorb hM hc0 hc1 hu0 hu1 ζ).comp (tendsto_add_atTop_nat 1)
  have hr : Tendsto (fun t => ∑ ζ', ancKernel M c u ζ ζ' * (ancMatrix M c u ^ t) ζ' (fullState M))
      atTop (𝓝 (∑ ζ', ancKernel M c u ζ ζ' * ancAbsorb M c u ζ')) :=
    tendsto_finsetSum _ fun ζ' _ =>
      (tendsto_ancMatrix_pow_ancAbsorb hM hc0 hc1 hu0 hu1 ζ').const_mul _
  have heq : ∀ t, (ancMatrix M c u ^ (t + 1)) ζ (fullState M) =
      ∑ ζ', ancKernel M c u ζ ζ' * (ancMatrix M c u ^ t) ζ' (fullState M) := fun t => by
    rw [pow_succ', Matrix.mul_apply]
    rfl
  exact tendsto_nhds_unique hs (hr.congr fun t => (heq t).symm)

theorem ancAbsorb_fullState {M : ℕ} (hM : 0 < M) {c u : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2) : ancAbsorb M c u (fullState M) = 1 := by
  have hpow : ∀ t, (ancMatrix M c u ^ t) (fullState M) (fullState M) = 1 := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      rw [pow_succ', Matrix.mul_apply, Finset.sum_eq_single (fullState M)]
      · rw [ih]
        change ancKernel M c u _ _ * 1 = 1
        rw [ancKernel_fullState hM, ite_eq_left rfl, one_mul]
      · intro ζ' _ hne
        change ancKernel M c u _ _ * _ = 0
        rw [ancKernel_fullState hM, ite_eq_right (Ne.symm hne), zero_mul]
      · intro h
        exact absurd (Finset.mem_univ _) h
  have h := tendsto_ancMatrix_pow_ancAbsorb hM hc0 hc1 hu0 hu1 (fullState M)
  simp only [hpow] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

def Dead {M : ℕ} (ζ : DualState M) : Prop := ∃ s, (ζ s).1 = ∅ ∨ (ζ s).2 = ∅

theorem dead_ancStep {M : ℕ} {c u : ℝ} {ζ : DualState M} (hζ : Dead ζ)
    (ω : Fin M → Choice M) (hw : ancWeight M c u ζ ω ≠ 0) : Dead (ancStep ζ ω) := by
  obtain ⟨s, hs⟩ := hζ
  have hl : lineFactor c u (ζ s) (ω s) ≠ 0 := by
    intro h0
    exact hw (Finset.prod_eq_zero (Finset.mem_univ s) h0)
  rcases hs with hs | hs
  · have hm : (ω s).2.2.1 = false := by
      by_contra hm
      rw [Bool.not_eq_false] at hm
      exact hl (by simp [lineFactor, mutFactor, hm, hs])
    refine ⟨parentA (ω s), Or.inl ?_⟩
    simp only [ancStep]
    exact Finset.subset_empty.mp (le_trans (Finset.inf_le (b := s) (by simp))
      (by simp [mutReq, hm, hs]))
  · have hm : (ω s).2.2.2.1 = false := by
      by_contra hm
      rw [Bool.not_eq_false] at hm
      exact hl (by simp [lineFactor, mutFactor, hm, hs])
    refine ⟨parentB (ω s), Or.inr ?_⟩
    simp only [ancStep]
    exact Finset.subset_empty.mp (le_trans (Finset.inf_le (b := s) (by simp))
      (by simp [mutReq, hm, hs]))

theorem not_dead_fullState (M : ℕ) : ¬ Dead (fullState M) := by
  rintro ⟨s, hs | hs⟩ <;> exact Finset.univ_nonempty.ne_empty hs

theorem ancAbsorb_of_dead {M : ℕ} (hM : 0 < M) {c u : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 2) {ζ : DualState M} (hζ : Dead ζ) :
    ancAbsorb M c u ζ = 0 := by
  have hker : ∀ {ζ₁ ζ' : DualState M}, Dead ζ₁ → ¬ Dead ζ' → ancKernel M c u ζ₁ ζ' = 0 := by
    intro ζ₁ ζ' h1 h2
    refine Finset.sum_eq_zero fun ω _ => ?_
    split_ifs with hstep
    · by_contra hw
      exact h2 (hstep ▸ dead_ancStep h1 ω hw)
    · rfl
  have hpow : ∀ t (ζ₁ : DualState M), Dead ζ₁ →
      (ancMatrix M c u ^ t) ζ₁ (fullState M) = 0 := by
    intro t
    induction t with
    | zero =>
      intro ζ₁ h1
      rw [pow_zero, Matrix.one_apply, ite_eq_right]
      rintro rfl
      exact not_dead_fullState M h1
    | succ t ih =>
      intro ζ₁ h1
      rw [pow_succ', Matrix.mul_apply]
      refine Finset.sum_eq_zero fun ζ' _ => ?_
      by_cases h2 : Dead ζ'
      · rw [ih ζ' h2, mul_zero]
      · change ancKernel M c u _ _ * _ = 0
        rw [hker h1 h2, zero_mul]
  have h := tendsto_ancMatrix_pow_ancAbsorb hM hc0 hc1 hu0 hu1 ζ
  simp only [hpow _ ζ hζ] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

end Rhone.Coalescent.WFTwoLocusDual
