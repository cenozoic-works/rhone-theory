/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Statistics.KillingLevelSum
public import Rhone.Statistics.AllelicPatternLaw

/-! # Pattern sums over block-respecting paths for allelic patterns -/

@[expose] public section
namespace Rhone.Statistics
open Finset MarkovChain Coalescent Rhone.Combinatorics

variable {n : ℕ} {κ : Type*} [DecidableEq κ] {θ : ℝ}

local notation "pp(" θ ", " N ", " z ", " σ ")" =>
  FinChain.pathProduct (RateChain.jumpChain (partitionChain (Fin _))) N
    (fun k τ => killLevelFactor θ τ (z k)) σ

def patternRel {N : ℕ} (z : Fin N → Finset (Finset (Fin n))) (a b : Fin n) : Prop :=
  ∀ k, ∀ B ∈ z k, (a ∈ B ↔ b ∈ B)

instance instDecidablePatternRel {N : ℕ} (z : Fin N → Finset (Finset (Fin n))) (a b : Fin n) :
    Decidable (patternRel z a b) := by
  unfold patternRel
  infer_instance

theorem patternRel_symm {N : ℕ} {z : Fin N → Finset (Finset (Fin n))} {a b : Fin n}
    (h : patternRel z a b) : patternRel z b a :=
  fun k B hB => (h k B hB).symm

theorem patternRel_cons {N : ℕ} (Z0 : Finset (Finset (Fin n)))
    (z' : Fin N → Finset (Finset (Fin n))) (a b : Fin n) :
    patternRel (Fin.cons Z0 z' : Fin (N + 1) → Finset (Finset (Fin n))) a b ↔
      (∀ B ∈ Z0, (a ∈ B ↔ b ∈ B)) ∧ patternRel z' a b := by
  unfold patternRel
  rw [Fin.forall_fin_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

def patternMatches {N : ℕ} (A : Finset (Fin n)) (z : Fin N → Finset (Finset (Fin n)))
    (c : Fin n → κ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, (patternRel z a b ↔ c a = c b)

instance instDecidablePatternMatches {N : ℕ} (A : Finset (Fin n))
    (z : Fin N → Finset (Finset (Fin n))) (c : Fin n → κ) :
    Decidable (patternMatches A z c) := by
  unfold patternMatches
  infer_instance

omit [DecidableEq κ] in
theorem patternMatches_cons_empty {N : ℕ} (A : Finset (Fin n))
    (z' : Fin N → Finset (Finset (Fin n))) (c : Fin n → κ) :
    patternMatches A (Fin.cons ∅ z' : Fin (N + 1) → Finset (Finset (Fin n))) c ↔
      patternMatches A z' c := by
  refine forall₄_congr fun a _ b _ => ?_
  rw [patternRel_cons, and_iff_right]
  exact fun B hB => absurd hB (Finset.notMem_empty B)

def blocksRespect (π : Finpartition (univ : Finset (Fin n))) {N : ℕ}
    (z : Fin N → Finset (Finset (Fin n))) : Prop :=
  ∀ k, ∀ B ∈ z k, ∀ C ∈ π.parts, C ⊆ B ∨ Disjoint C B

theorem blocksRespect_of_le {π σ : Finpartition (univ : Finset (Fin n))} (h : π ≤ σ) {N : ℕ}
    {z : Fin N → Finset (Finset (Fin n))} (hσ : blocksRespect σ z) : blocksRespect π z := by
  intro k B hB C hC
  obtain ⟨C', hC', hCC'⟩ := h hC
  rcases hσ k B hB C' hC' with h1 | h1
  · exact Or.inl (hCC'.trans h1)
  · exact Or.inr (h1.mono_left hCC')

/-- Source: kingman1982, eq. (1.10). -/
theorem partition_jump_of_card_le_one {π : Finpartition (univ : Finset (Fin n))}
    (hk : π.parts.card ≤ 1) (σ : Finpartition (univ : Finset (Fin n))) :
    (partitionChain (Fin n)).jumpChain.P π σ = if π = σ then 1 else 0 := by
  have hr : (partitionChain (Fin n)).rate π = 0 := by
    rw [partitionChain_rate, coalRate_eq_zero hk, Rat.cast_zero]
  by_cases he : π = σ
  · subst he
    simp [RateChain.jumpChain_P, RateChain.jumpMatrix, hr]
  · simp [RateChain.jumpChain_P, RateChain.jumpMatrix, hr, he]

/-- Source: kingman1982, eq. (1.3)–(1.4). -/
theorem le_of_partition_jump_ne_zero {π σ : Finpartition (univ : Finset (Fin n))}
    (h : (partitionChain (Fin n)).jumpChain.P π σ ≠ 0) : π ≤ σ := by
  by_cases hk : 2 ≤ π.parts.card
  · rw [partition_jump_prob hk] at h
    exact le_of_mem_merges (by_contra fun hn => h (ite_eq_right hn))
  · rw [partition_jump_of_card_le_one (by omega)] at h
    have he : π = σ := by_contra fun hn => h (ite_eq_right hn)
    rw [he]

theorem subset_parts_of_killLevelFactor_ne_zero {π : Finpartition (univ : Finset (Fin n))}
    {D : Finset (Finset (Fin n))} (h : killLevelFactor θ π D ≠ 0) : D ⊆ π.parts := by
  by_contra hD
  apply h
  unfold killLevelFactor
  by_cases h1 : 1 < π.parts.card
  · rw [ite_eq_left h1, ite_eq_right hD]
  · rw [ite_eq_right h1]
    exact ite_eq_right fun h0 => hD (by rw [h0]; exact Finset.empty_subset _)

theorem blocksRespect_of_pathProduct_ne_zero (θ : ℝ) :
    ∀ (N : ℕ) (z : Fin N → Finset (Finset (Fin n))) (π : Finpartition (univ : Finset (Fin n))),
      pp(θ, N, z, π) ≠ 0 → blocksRespect π z := by
  intro N
  induction N with
  | zero =>
    intro z π _ k
    exact k.elim0
  | succ N ih =>
    intro z π h
    rw [FinChain.pathProduct_succ] at h
    obtain ⟨h0, hs⟩ := mul_ne_zero_iff.1 h
    obtain ⟨σ, -, hσ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hs
    obtain ⟨hP, hpp⟩ := mul_ne_zero_iff.1 hσ
    have hle := le_of_partition_jump_ne_zero hP
    have hZ : z 0 ⊆ π.parts := subset_parts_of_killLevelFactor_ne_zero h0
    intro k
    refine Fin.cases ?_ (fun k' => ?_) k
    · intro B hB C hC
      by_cases hCB : C = B
      · exact Or.inl (by rw [hCB])
      · exact Or.inr (π.disjoint hC (hZ hB) hCB)
    · exact blocksRespect_of_le hle (ih (fun k => z k.succ) σ hpp) k'

theorem patternMatches_cons {π : Finpartition (univ : Finset (Fin n))}
    {Z0 : Finset (Finset (Fin n))} (hZ : Z0 ⊆ π.parts) {N : ℕ}
    {z' : Fin N → Finset (Finset (Fin n))} (hg : blocksRespect π z') (A : Finset (Fin n))
    (c : Fin n → κ) :
    patternMatches A (Fin.cons Z0 z' : Fin (N + 1) → Finset (Finset (Fin n))) c ↔
      (∀ x ∈ Z0, labelFull π.parts (blockLabels A c) x) ∧
        patternMatches (A \ Z0.sup id) z' c := by
  have hsame : ∀ x ∈ π.parts, ∀ a ∈ x, ∀ b ∈ x,
      patternRel (Fin.cons Z0 z' : Fin (N + 1) → Finset (Finset (Fin n))) a b := by
    intro x hx a ha b hb
    rw [patternRel_cons]
    refine ⟨fun B hB => ?_, fun k B hB => ?_⟩
    · by_cases hBx : B = x
      · rw [hBx]
        exact iff_of_true ha hb
      · have hd : Disjoint x B := π.disjoint hx (hZ hB) (Ne.symm hBx)
        exact iff_of_false (Finset.disjoint_left.1 hd ha) (Finset.disjoint_left.1 hd hb)
    · rcases hg k B hB x hx with h1 | h1
      · exact iff_of_true (h1 ha) (h1 hb)
      · exact iff_of_false (Finset.disjoint_left.1 h1 ha) (Finset.disjoint_left.1 h1 hb)
  have hsep : ∀ x ∈ Z0, ∀ a ∈ x, ∀ b, b ∉ x →
      ¬ patternRel (Fin.cons Z0 z' : Fin (N + 1) → Finset (Finset (Fin n))) a b := by
    intro x hx a ha b hb h
    rw [patternRel_cons] at h
    exact hb ((h.1 x hx).1 ha)
  have hlab : ∀ {a : Fin n} {x : Finset (Fin n)}, a ∈ x → a ∈ A → c a ∈ blockLabels A c x :=
    fun ha haA => mem_image_of_mem c (mem_inter.2 ⟨ha, haA⟩)
  have hout : ∀ a b, a ∉ Z0.sup id → b ∉ Z0.sup id →
      (patternRel (Fin.cons Z0 z' : Fin (N + 1) → Finset (Finset (Fin n))) a b ↔
        patternRel z' a b) := by
    intro a b ha hb
    rw [patternRel_cons, and_iff_right]
    intro B hB
    exact iff_of_false (fun h => ha (Finset.mem_sup.2 ⟨B, hB, h⟩))
      (fun h => hb (Finset.mem_sup.2 ⟨B, hB, h⟩))
  constructor
  · intro hE
    refine ⟨fun x hx => ⟨?_, fun y hy hyx => ?_⟩, fun a ha b hb => ?_⟩
    · rw [Finset.card_le_one]
      intro u hu v hv
      obtain ⟨a, ha, rfl⟩ := mem_image.1 hu
      obtain ⟨b, hb, rfl⟩ := mem_image.1 hv
      rw [mem_inter] at ha hb
      exact (hE a ha.2 b hb.2).1 (hsame x (hZ hx) a ha.1 b hb.1)
    · rw [Finset.disjoint_left]
      intro u hu hv
      obtain ⟨a, ha, rfl⟩ := mem_image.1 hu
      obtain ⟨b, hb, hab⟩ := mem_image.1 hv
      rw [mem_inter] at ha hb
      have hbx : b ∉ x := Finset.disjoint_left.1 (π.disjoint hy (hZ hx) hyx) hb.1
      exact hsep x hx a ha.1 b hbx ((hE a ha.2 b hb.2).2 hab.symm)
    · rw [mem_sdiff] at ha hb
      rw [← hout a b ha.2 hb.2]
      exact hE a ha.1 b hb.1
  · rintro ⟨hF, hE⟩ a ha b hb
    have key : ∀ a ∈ A, ∀ b ∈ A, ∀ x ∈ Z0, a ∈ x →
        (patternRel (Fin.cons Z0 z' : Fin (N + 1) → Finset (Finset (Fin n))) a b ↔
          c a = c b) := by
      intro a ha b hb x hx hax
      by_cases hbx : b ∈ x
      · exact iff_of_true (hsame x (hZ hx) a hax b hbx)
          (Finset.card_le_one.1 (hF x hx).1 _ (hlab hax ha) _ (hlab hbx hb))
      · refine iff_of_false (hsep x hx a hax b hbx) fun hab => ?_
        have hy := π.part_mem.2 (mem_univ b)
        have hby := π.mem_part (mem_univ b)
        have hne : π.part b ≠ x := fun h => hbx (by rw [← h]; exact hby)
        have hd := (hF x hx).2 (π.part b) hy hne
        exact Finset.disjoint_left.1 hd (hlab hax ha) (by rw [hab]; exact hlab hby hb)
    by_cases ha' : a ∈ Z0.sup id
    · obtain ⟨x, hx, hax⟩ := Finset.mem_sup.1 ha'
      exact key a ha b hb x hx hax
    · by_cases hb' : b ∈ Z0.sup id
      · obtain ⟨x, hx, hbx⟩ := Finset.mem_sup.1 hb'
        have h := key b hb a ha x hx hbx
        exact ⟨fun h1 => (h.1 (patternRel_symm h1)).symm,
          fun h1 => patternRel_symm (h.2 h1.symm)⟩
      · rw [hout a b ha' hb']
        exact hE a (mem_sdiff.2 ⟨ha, ha'⟩) b (mem_sdiff.2 ⟨hb, hb'⟩)

noncomputable def patternSum (θ : ℝ) (N : ℕ) (π : Finpartition (univ : Finset (Fin n)))
    (A : Finset (Fin n)) (c : Fin n → κ) : ℝ :=
  ∑ z : Fin N → Finset (Finset (Fin n)), if patternMatches A z c then pp(θ, N, z, π) else 0

theorem patternSum_eq (hθ : 0 < θ) :
    ∀ (N : ℕ) (π : Finpartition (univ : Finset (Fin n))), π.parts.card ≤ N + 1 →
      ∀ (A : Finset (Fin n)) (c : Fin n → κ), patternSum θ N π A c = killingWeight θ π A c := by
  intro N
  induction N with
  | zero =>
    intro π hπ A c
    unfold patternSum
    rw [Fintype.sum_unique, killingWeight_of_card_le_one hθ hπ, FinChain.pathProduct_zero]
    have hiff : ∀ z : Fin 0 → Finset (Finset (Fin n)), patternMatches A z c ↔
        ∀ a ∈ A, ∀ b ∈ A, c a = c b := fun z =>
      forall₄_congr fun a _ b _ => iff_true_left (show patternRel z a b from fun k => k.elim0)
    by_cases h : ∀ a ∈ A, ∀ b ∈ A, c a = c b
    · rw [ite_eq_left h]
      exact ite_eq_left ((hiff _).2 h)
    · rw [ite_eq_right h]
      exact ite_eq_right fun h' => h ((hiff _).1 h')
  | succ N ih =>
    intro π hπ A c
    have hsplit : patternSum θ (N + 1) π A c =
        ∑ Z0 : Finset (Finset (Fin n)), ∑ z' : Fin N → Finset (Finset (Fin n)),
          (if patternMatches A (Fin.cons Z0 z' : Fin (N + 1) → Finset (Finset (Fin n))) c then
            killLevelFactor θ π Z0 *
              ∑ σ, (partitionChain (Fin n)).jumpChain.P π σ * pp(θ, N, z', σ) else 0) := by
      unfold patternSum
      rw [← Fintype.sum_prod_type']
      refine (Fintype.sum_equiv (Fin.consEquiv fun _ => Finset (Finset (Fin n))) _ _
        fun p => ?_).symm
      simp only [Fin.consEquiv_apply, FinChain.pathProduct_succ, Fin.cons_zero, Fin.cons_succ]
      rfl
    by_cases hk : 2 ≤ π.parts.card
    · have hklf : ∀ Z0 : Finset (Finset (Fin n)), killLevelFactor θ π Z0 =
          if Z0 ⊆ π.parts then
            killPatternWeight (θ / ((π.parts.card : ℝ) * ((π.parts.card : ℝ) - 1))) Z0.card
              (π.parts.card - Z0.card) else 0 := by
        intro Z0
        unfold killLevelFactor
        rw [ite_eq_left (show 1 < π.parts.card by omega)]
      have hsumσ : ∀ g : Finpartition (univ : Finset (Fin n)) → ℝ,
          ∑ σ, (partitionChain (Fin n)).jumpChain.P π σ * g σ =
            ((π.parts.card.choose 2 : ℕ) : ℝ)⁻¹ * ∑ σ ∈ merges π, g σ := by
        intro g
        have hterm : ∀ σ, (partitionChain (Fin n)).jumpChain.P π σ * g σ =
            if σ ∈ merges π then ((π.parts.card.choose 2 : ℕ) : ℝ)⁻¹ * g σ else 0 := fun σ => by
          rw [partition_jump_prob hk, ite_mul, zero_mul]
        rw [Finset.sum_congr rfl fun σ _ => hterm σ, ← Finset.sum_filter,
          Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.mul_sum]
      have hB : ∀ Z0 : Finset (Finset (Fin n)), ∑ z' : Fin N → Finset (Finset (Fin n)),
          (if patternMatches A (Fin.cons Z0 z' : Fin (N + 1) → Finset (Finset (Fin n))) c then
            killLevelFactor θ π Z0 *
              ∑ σ, (partitionChain (Fin n)).jumpChain.P π σ * pp(θ, N, z', σ) else 0) =
          if Z0 ∈ (fullBlocks π A c).powerset then
            killPatternWeight (θ / ((π.parts.card : ℝ) * ((π.parts.card : ℝ) - 1))) Z0.card
              (π.parts.card - Z0.card) * avgMerge θ π (A \ Z0.sup id) c else 0 := by
        intro Z0
        by_cases hZ : Z0 ⊆ π.parts
        · have hz : ∀ z' : Fin N → Finset (Finset (Fin n)),
              (if patternMatches A
                  (Fin.cons Z0 z' : Fin (N + 1) → Finset (Finset (Fin n))) c then
                killLevelFactor θ π Z0 *
                  ∑ σ, (partitionChain (Fin n)).jumpChain.P π σ * pp(θ, N, z', σ) else 0) =
              if ∀ x ∈ Z0, labelFull π.parts (blockLabels A c) x then
                killPatternWeight (θ / ((π.parts.card : ℝ) * ((π.parts.card : ℝ) - 1)))
                  Z0.card (π.parts.card - Z0.card) *
                  (((π.parts.card.choose 2 : ℕ) : ℝ)⁻¹ * ∑ σ ∈ merges π,
                    if patternMatches (A \ Z0.sup id) z' c then pp(θ, N, z', σ) else 0)
              else 0 := by
            intro z'
            rw [hklf, ite_eq_left hZ, hsumσ]
            by_cases hall : ∀ σ ∈ merges π, pp(θ, N, z', σ) = 0
            · rw [Finset.sum_eq_zero hall, Finset.sum_eq_zero (fun σ hσ => by
                rw [hall σ hσ]
                exact ite_self 0)]
              simp
            · push Not at hall
              obtain ⟨σ0, hσ0, hne⟩ := hall
              have hg : blocksRespect π z' := blocksRespect_of_le (le_of_mem_merges hσ0)
                (blocksRespect_of_pathProduct_ne_zero θ N z' σ0 hne)
              have hdec := patternMatches_cons hZ hg A c
              by_cases hF : ∀ x ∈ Z0, labelFull π.parts (blockLabels A c) x
              · rw [ite_eq_left hF]
                by_cases hE : patternMatches (A \ Z0.sup id) z' c
                · rw [ite_eq_left (hdec.2 ⟨hF, hE⟩)]
                  congr 2
                  exact Finset.sum_congr rfl fun σ _ => (ite_eq_left hE).symm
                · rw [ite_eq_right (fun h => hE (hdec.1 h).2),
                    Finset.sum_eq_zero fun σ _ => ite_eq_right hE, mul_zero, mul_zero]
              · rw [ite_eq_right hF, ite_eq_right (fun h => hF (hdec.1 h).1)]
          rw [Finset.sum_congr rfl fun z' _ => hz z']
          by_cases hF : ∀ x ∈ Z0, labelFull π.parts (blockLabels A c) x
          · have hmem : Z0 ∈ (fullBlocks π A c).powerset :=
              mem_powerset.2 fun x hx => mem_filter.2 ⟨hZ hx, hF x hx⟩
            rw [ite_eq_left hmem, Finset.sum_congr rfl fun z' _ => ite_eq_left hF,
              ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm]
            unfold avgMerge
            congr 2
            refine Finset.sum_congr rfl fun σ hσ => ?_
            have hcard := card_parts_of_mem_merges hσ
            exact ih σ (by omega) (A \ Z0.sup id) c
          · have hmem : Z0 ∉ (fullBlocks π A c).powerset := fun h =>
              hF fun x hx => (mem_filter.1 (mem_powerset.1 h hx)).2
            rw [ite_eq_right hmem]
            exact Finset.sum_eq_zero fun z' _ => ite_eq_right hF
        · have hmem : Z0 ∉ (fullBlocks π A c).powerset := fun h =>
            hZ fun x hx => (mem_filter.1 (mem_powerset.1 h hx)).1
          rw [ite_eq_right hmem]
          refine Finset.sum_eq_zero fun z' _ => ?_
          rw [hklf, ite_eq_right hZ, zero_mul]
          exact ite_self 0
      rw [hsplit, Finset.sum_congr rfl fun Z0 _ => hB Z0, ← Finset.sum_filter,
        Finset.filter_mem_eq_inter, Finset.univ_inter]
      exact levelSum_eq hθ hk c A
    · have hk1 : π.parts.card ≤ 1 := by omega
      have hsumσ : ∀ g : Finpartition (univ : Finset (Fin n)) → ℝ,
          ∑ σ, (partitionChain (Fin n)).jumpChain.P π σ * g σ = g π := by
        intro g
        rw [Finset.sum_eq_single_of_mem π (mem_univ π) (fun σ _ hσ => by
          rw [partition_jump_of_card_le_one hk1, ite_eq_right hσ.symm, zero_mul]),
          partition_jump_of_card_le_one hk1, ite_eq_left rfl, one_mul]
      have hA : ∀ Z0 : Finset (Finset (Fin n)), ∑ z' : Fin N → Finset (Finset (Fin n)),
          (if patternMatches A (Fin.cons Z0 z' : Fin (N + 1) → Finset (Finset (Fin n))) c then
            killLevelFactor θ π Z0 *
              ∑ σ, (partitionChain (Fin n)).jumpChain.P π σ * pp(θ, N, z', σ) else 0) =
          if Z0 = ∅ then patternSum θ N π A c else 0 := by
        intro Z0
        by_cases hZ0 : Z0 = ∅
        · have hklf : killLevelFactor θ π Z0 = 1 := by
            unfold killLevelFactor
            rw [ite_eq_right (show ¬ 1 < π.parts.card by omega), ite_eq_left hZ0]
          rw [ite_eq_left hZ0]
          unfold patternSum
          refine Finset.sum_congr rfl fun z' _ => ?_
          rw [hklf, one_mul, hsumσ, hZ0]
          exact if_congr (patternMatches_cons_empty A z' c) rfl rfl
        · have hklf : killLevelFactor θ π Z0 = 0 := by
            unfold killLevelFactor
            rw [ite_eq_right (show ¬ 1 < π.parts.card by omega), ite_eq_right hZ0]
          rw [ite_eq_right hZ0]
          refine Finset.sum_eq_zero fun z' _ => ?_
          rw [hklf, zero_mul]
          exact ite_self 0
      rw [hsplit, Finset.sum_congr rfl fun Z0 _ => hA Z0,
        Finset.sum_eq_single_of_mem ∅ (mem_univ _) (fun Z _ hZ => ite_eq_right hZ),
        ite_eq_left rfl]
      exact ih π (by omega) A c

end Rhone.Statistics
