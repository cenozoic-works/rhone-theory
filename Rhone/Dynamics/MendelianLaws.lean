/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Rhone.Dynamics.MendelianIBD
public import Rhone.Dynamics.Inbreeding
/-!
# Finite Mendelian offspring laws and their founder-copy identity moments

Source: wright1931, pp. 107–110. -/
@[expose] public section
namespace Rhone.Dynamics.MendelianIBD
open Finset
noncomputable def offspringPushforwardMass {S T : Type*} [Fintype S] [DecidableEq T]
    (w : S → ℝ) (f : S → T) (t : T) : ℝ :=
  ∑ s, if f s = t then w s else 0
private theorem push_expectation {S T : Type*} [Fintype S] [Fintype T] [DecidableEq T]
    (w : S → ℝ) (f : S → T) (g : T → ℝ) :
    (∑ t, offspringPushforwardMass w f t * g t) = ∑ s, w s * g (f s) := by
  unfold offspringPushforwardMass
  simp only [sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro s hs
  rw [sum_eq_single (f s)]
  · simp
  · intro t ht hne
    simp [Ne.symm hne]
  · simp
private theorem push_total {S T : Type*} [Fintype S] [Fintype T] [DecidableEq T]
    (w : S → ℝ) (f : S → T) : ∑ t, offspringPushforwardMass w f t = ∑ s, w s := by
  simpa only [mul_one] using push_expectation w f (fun _ => 1)
private theorem push_nonnegative {S T : Type*} [Fintype S] [DecidableEq T]
    (w : S → ℝ) (f : S → T) (hw : ∀ s, 0 ≤ w s) (t : T) :
    0 ≤ offspringPushforwardMass w f t := by
  apply sum_nonneg
  intro s hs
  split_ifs
  · exact hw s
  · exact le_rfl
noncomputable def mendelianLaw {O A : Type*} [Fintype O] [Fintype A] [DecidableEq A]
    (w : O → ℝ) (X Y : O → Fin 2 → A) : (Fin 2 → A) → ℝ :=
  offspringPushforwardMass (fun z : O × (Fin 2 × Fin 2) => w z.1 / 4)
    (fun z => mendelianChild (X z.1) (Y z.1) z.2.1 z.2.2)
theorem mendelian_law_total {O A : Type*} [Fintype O] [Fintype A] [DecidableEq A]
    (w : O → ℝ) (X Y : O → Fin 2 → A) (hw : ∑ o, w o = 1) :
    ∑ d, mendelianLaw w X Y d = 1 := by
  rw [mendelianLaw, push_total]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
  have hpoint : ∀ o, w o / 4 + w o / 4 + (w o / 4 + w o / 4) = w o := by
    intro o; ring
  simp_rw [hpoint]
  exact hw
theorem mendelian_law_nonnegative {O A : Type*}
    [Fintype O] [Fintype A] [DecidableEq A]
    (w : O → ℝ) (X Y : O → Fin 2 → A) (hw : ∀ o, 0 ≤ w o) (d : Fin 2 → A) :
    0 ≤ mendelianLaw w X Y d := by
  apply push_nonnegative
  intro z
  exact div_nonneg (hw z.1) (by norm_num)
/-- Source: wright1931, p. 107. -/
theorem mendelian_law_ibd
    {O A : Type*} [Fintype O] [Fintype A] [DecidableEq A]
    (w : O → ℝ) (X Y : O → Fin 2 → A)
    (hw0 : ∀ o, 0 ≤ w o) (hw : ∑ o, w o = 1) :
    founderIbd (mendelianLaw w X Y) id = founderKinship w X Y := by
  unfold founderIbd mendelianLaw
  rw [push_expectation]
  simp only [Fintype.sum_prod_type, id_eq, mendelianChild,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  unfold founderKinship
  simp only [mul_sum, mul_div_assoc, div_mul_eq_mul_div]
  have ht : 0 ≤ ∑ o, w o := sum_nonneg fun o _ => hw0 o
  have htotal : ∑ o, w o = 1 := hw
  rfl
noncomputable def fullSiblingLaw {O A : Type*} [Fintype O] [Fintype A] [DecidableEq A]
    (w : O → ℝ) (X Y : O → Fin 2 → A) : ((Fin 2 → A) × (Fin 2 → A)) → ℝ :=
  offspringPushforwardMass (fun z : O × ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) => w z.1 / 16)
    (fun z => (mendelianChild (X z.1) (Y z.1) z.2.1.1 z.2.1.2,
      mendelianChild (X z.1) (Y z.1) z.2.2.1 z.2.2.2))
/-- Source: wright1931, p. 107. -/
theorem sibling_law_kinship
    {O A : Type*} [Fintype O] [Fintype A] [DecidableEq A]
    (w : O → ℝ) (X Y : O → Fin 2 → A)
    (hw0 : ∀ o, 0 ≤ w o) (hw : ∑ o, w o = 1) :
    founderKinship (fullSiblingLaw w X Y) Prod.fst Prod.snd = siblingKinship w X Y := by
  unfold founderKinship fullSiblingLaw
  rw [push_expectation]
  simp only [Fintype.sum_prod_type]
  have ht : 0 ≤ ∑ o, w o := sum_nonneg fun o _ => hw0 o
  have htotal : ∑ o, w o = 1 := hw
  unfold siblingKinship founderKinship
  simp only [Fintype.sum_unique, one_mul]
theorem sibling_law_nonnegative {O A : Type*}
    [Fintype O] [Fintype A] [DecidableEq A]
    (w : O → ℝ) (X Y : O → Fin 2 → A) (hw : ∀ o, 0 ≤ w o)
    (d : (Fin 2 → A) × (Fin 2 → A)) : 0 ≤ fullSiblingLaw w X Y d := by
  apply push_nonnegative
  intro z
  exact div_nonneg (hw z.1) (by norm_num)
theorem sibling_law_total {O A : Type*} [Fintype O] [Fintype A] [DecidableEq A]
    (w : O → ℝ) (X Y : O → Fin 2 → A) (hw : ∑ o, w o = 1) :
    ∑ d, fullSiblingLaw w X Y d = 1 := by
  rw [fullSiblingLaw, push_total]
  rw [Fintype.sum_prod_type]
  have ht : ∀ o, (∑ z : (Fin 2 × Fin 2) × (Fin 2 × Fin 2), w o / 16) = w o := by
    intro o
    simp only [sum_const, card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
    norm_num
    ring
  simp_rw [ht]
  exact hw
private theorem sibling_law_marginal {O A : Type*}
    [Fintype O] [Fintype A] [DecidableEq A]
    (w : O → ℝ) (X Y : O → Fin 2 → A) (side : Fin 2) :
    founderIbd (fullSiblingLaw w X Y)
      (fun d => if side = 0 then d.1 else d.2) = founderKinship w X Y := by
  unfold founderIbd fullSiblingLaw
  rw [push_expectation]
  simp only [Fintype.sum_prod_type]
  unfold founderKinship
  apply sum_congr rfl
  intro o ho
  fin_cases side
  all_goals simp only [Fin.sum_univ_two]
  all_goals dsimp +instances [mendelianChild]
  all_goals ring
noncomputable def selfingLaw {A : Type*} [Fintype A] [DecidableEq A]
    (p : (Fin 2 → A) → ℝ) : (Fin 2 → A) → ℝ := mendelianLaw p id id
noncomputable def sibLaw {A : Type*} [Fintype A] [DecidableEq A]
    (p : ((Fin 2 → A) × (Fin 2 → A)) → ℝ) : ((Fin 2 → A) × (Fin 2 → A)) → ℝ :=
  fullSiblingLaw p Prod.fst Prod.snd
noncomputable def ibdPair {A : Type*} [Fintype A] [DecidableEq A]
    (p : ((Fin 2 → A) × (Fin 2 → A)) → ℝ) : ℝ × ℝ :=
  (founderIbd p Prod.fst, founderKinship p Prod.fst Prod.snd)
private theorem selfing_law_ibd {A : Type*} [Fintype A] [DecidableEq A]
    (p : (Fin 2 → A) → ℝ) (hp0 : ∀ d, 0 ≤ p d) (hp : ∑ d, p d = 1) :
    founderIbd (selfingLaw p) id = Inbreeding.partialSelfingStep 1 (founderIbd p id) := by
  have hself : founderKinship p id id = selfedIbd p id := by
    unfold founderKinship selfedIbd
    simp only [id_eq, mul_sum]
    dsimp +instances [mendelianChild]
    simp only [div_mul_eq_mul_div, mul_div_assoc]
  rw [selfingLaw, mendelian_law_ibd p id id hp0 hp, hself, selfed_ibd_eq p id hp0 hp]
  simp [Inbreeding.partialSelfingStep]
/-- Source: wright1931, pp. 109–110. -/
theorem selfing_generation_ibd
    {A : Type*} [Fintype A] [DecidableEq A]
    (p : (Fin 2 → A) → ℝ) (hp0 : ∀ d, 0 ≤ p d) (hp : ∑ d, p d = 1) (t : ℕ) :
    founderIbd ((selfingLaw^[t]) p) id = 1 - (1 - founderIbd p id)/(2 : ℝ)^t := by
  have hvalid : ∀ t, (∀ d, 0 ≤ ((selfingLaw^[t]) p) d) ∧
      (∑ d, ((selfingLaw^[t]) p) d) = 1 := by
    intro t
    induction t with
    | zero => exact ⟨hp0, hp⟩
    | succ t ih =>
      rw [Function.iterate_succ_apply']
      exact ⟨mendelian_law_nonnegative _ id id ih.1, mendelian_law_total _ id id ih.2⟩
  have hsem : ∀ t, founderIbd ((selfingLaw^[t]) p) id =
      ((Inbreeding.partialSelfingStep 1)^[t]) (founderIbd p id) := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
      rw [Function.iterate_succ_apply', selfing_law_ibd _ (hvalid t).1 (hvalid t).2,
        ih, Function.iterate_succ_apply']
  rw [hsem, Inbreeding.selfing_iterate]
private theorem sib_marginal_fst {A : Type*} [Fintype A] [DecidableEq A]
    (p : ((Fin 2 → A) × (Fin 2 → A)) → ℝ) :
    founderIbd (sibLaw p) Prod.fst = founderKinship p Prod.fst Prod.snd := by
  simpa only [sibLaw, ite_true] using sibling_law_marginal p Prod.fst Prod.snd 0
private theorem sib_marginal_snd {A : Type*} [Fintype A] [DecidableEq A]
    (p : ((Fin 2 → A) × (Fin 2 → A)) → ℝ) :
    founderIbd (sibLaw p) Prod.snd = founderKinship p Prod.fst Prod.snd := by
  have hne : (1 : Fin 2) ≠ 0 := by norm_num
  simpa only [sibLaw, hne, ite_false] using sibling_law_marginal p Prod.fst Prod.snd 1
private theorem sib_law_pair {A : Type*} [Fintype A] [DecidableEq A]
    (p : ((Fin 2 → A) × (Fin 2 → A)) → ℝ)
    (hp0 : ∀ d, 0 ≤ p d) (hp : ∑ d, p d = 1)
    (hequal : founderIbd p Prod.fst = founderIbd p Prod.snd) :
    ibdPair (sibLaw p) = Inbreeding.fullSibStep (ibdPair p) := by
  apply Prod.ext
  · exact sib_marginal_fst p
  · change founderKinship (fullSiblingLaw p Prod.fst Prod.snd) Prod.fst Prod.snd =
      (1 + 2 * founderKinship p Prod.fst Prod.snd + founderIbd p Prod.fst) / 4
    rw [sibling_law_kinship _ _ _ hp0 hp, sibling_kinship_eq _ _ _ hp0 hp, ← hequal]
    ring
/-- Source: wright1931, pp. 109–110. -/
theorem sibling_generation_ibd
    {A : Type*} [Fintype A] [DecidableEq A]
    (p : ((Fin 2 → A) × (Fin 2 → A)) → ℝ)
    (hp0 : ∀ d, 0 ≤ p d) (hp : ∑ d, p d = 1)
    (hequal : founderIbd p Prod.fst = founderIbd p Prod.snd) (t : ℕ) :
    ibdPair ((sibLaw^[t]) p) = (Rhone.Dynamics.Inbreeding.fullSibStep^[t]) (ibdPair p) := by
  have hvalid : ∀ t, (∀ d, 0 ≤ ((sibLaw^[t]) p) d) ∧
      (∑ d, ((sibLaw^[t]) p) d) = 1 ∧
      founderIbd ((sibLaw^[t]) p) Prod.fst = founderIbd ((sibLaw^[t]) p) Prod.snd := by
    intro t
    induction t with
    | zero => exact ⟨hp0, hp, hequal⟩
    | succ t ih =>
      rw [Function.iterate_succ_apply']
      refine ⟨sibling_law_nonnegative _ Prod.fst Prod.snd ih.1,
        sibling_law_total _ Prod.fst Prod.snd ih.2.1, ?_⟩
      rw [sib_marginal_fst, sib_marginal_snd]
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', sib_law_pair _ (hvalid t).1 (hvalid t).2.1
      (hvalid t).2.2, ih, Function.iterate_succ_apply']
end Rhone.Dynamics.MendelianIBD
