/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Probability.Propagation.Propagate

/-! # The `(ND)` range criterion, and the two obstructions O1 and O2 -/

@[expose] public section

namespace Rhone.Probability.Propagation

open Matrix

def tau (t0 p q i j : ℕ) (b : ℚ) : ℚ := t0 * (i + j * b) / (p + q * b)

theorem tau_base (t0 p q : ℕ) (b : ℚ) (h : (p : ℚ) + q * b ≠ 0) : tau t0 p q p q b = t0 := by
  rw [tau, mul_div_assoc, div_self h, mul_one]

theorem gcd_split (m n : ℕ) (hm : 0 < m) :
    ∃ M N, m = Nat.gcd m n * M ∧ n = Nat.gcd m n * N ∧ Nat.Coprime M N ∧ 0 < M := by
  have hg : 0 < Nat.gcd m n := Nat.pos_of_ne_zero fun h => by
    rw [Nat.gcd_eq_zero_iff] at h; omega
  exact ⟨m / Nat.gcd m n, n / Nat.gcd m n,
    (Nat.mul_div_cancel' (Nat.gcd_dvd_left m n)).symm,
    (Nat.mul_div_cancel' (Nat.gcd_dvd_right m n)).symm,
    Nat.coprime_div_gcd_div_gcd hg,
    Nat.div_pos (Nat.le_of_dvd hm (Nat.gcd_dvd_left m n)) hg⟩

theorem nd_core {p q t0 k g' g P Q G T : ℕ}
    (hP : p = g' * P) (hQ : q = g' * Q) (hcopPQ : Nat.Coprime P Q)
    (hPpos : 0 < P) (hQpos : 0 < Q) (hg'pos : 0 < g')
    (hG : g' = g * G) (hT : t0 = g * T) (hcopGT : Nat.Coprime G T)
    (hgpos : 0 < g) (hGpos : 0 < G) :
    (∃ i j, p ≤ i ∧ i ≤ p + k ∧ q ≤ j ∧ j ≤ q + k ∧ (i, j) ≠ (p, q) ∧
        i * q = j * p ∧ p ∣ t0 * i)
      ↔ max p q ≤ k * g := by
  have hkey : ∀ d : ℕ, g' ∣ t0 * d ↔ G ∣ d := by
    intro d
    constructor
    · intro hd
      rw [hG, hT, mul_assoc] at hd
      exact hcopGT.dvd_of_dvd_mul_left ((Nat.mul_dvd_mul_iff_left hgpos).1 hd)
    · rintro ⟨e, rfl⟩
      rw [hG, hT]
      exact ⟨T * e, by ring⟩
  constructor
  · rintro ⟨i, j, hpi, hik, hqj, hjk, hne, hcol, hdvd⟩
    obtain ⟨a, rfl⟩ : ∃ a, i = p + a := ⟨i - p, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, j = q + b := ⟨j - q, by omega⟩
    have hcomm : p * q = q * p := Nat.mul_comm p q
    have haq : a * q = b * p := by rw [add_mul, add_mul] at hcol; omega
    have haQ : a * Q = b * P := by
      refine Nat.eq_of_mul_eq_mul_left hg'pos ?_
      calc g' * (a * Q) = a * (g' * Q) := by ring
        _ = a * q := by rw [← hQ]
        _ = b * p := haq
        _ = b * (g' * P) := by rw [← hP]
        _ = g' * (b * P) := by ring
    obtain ⟨d, hd⟩ : P ∣ a := hcopPQ.dvd_of_dvd_mul_right ⟨b, by rw [haQ]; ring⟩
    have hb : b = Q * d := by
      refine Nat.eq_of_mul_eq_mul_left hPpos ?_
      calc P * b = b * P := Nat.mul_comm P b
        _ = a * Q := haQ.symm
        _ = P * (Q * d) := by rw [hd]; ring
    have hdpos : 0 < d := by
      rcases Nat.eq_zero_or_pos d with rfl | h
      · exact absurd (by rw [hd, hb]; simp) hne
      · exact h
    have hdvd' : g' ∣ t0 * d := by
      have hi : p + a = P * (g' + d) := by rw [hP, hd]; ring
      rw [hi, hP] at hdvd
      have h1 : g' * P ∣ t0 * (g' + d) * P := dvd_trans hdvd ⟨1, by ring⟩
      have h2 : g' ∣ t0 * (g' + d) := (Nat.mul_dvd_mul_iff_right hPpos).1 h1
      rw [show t0 * (g' + d) = t0 * g' + t0 * d from by ring] at h2
      exact (Nat.dvd_add_right ⟨t0, by ring⟩).1 h2
    have hGle : G ≤ d := Nat.le_of_dvd hdpos ((hkey d).1 hdvd')
    have hPk : P * G ≤ k := by
      have h5 : P * G ≤ P * d := Nat.mul_le_mul (le_refl P) hGle
      omega
    have hQk : Q * G ≤ k := by
      have h5 : Q * G ≤ Q * d := Nat.mul_le_mul (le_refl Q) hGle
      omega
    have hpk : p ≤ k * g := by
      calc p = g * (P * G) := by rw [hP, hG]; ring
        _ ≤ g * k := Nat.mul_le_mul (le_refl g) hPk
        _ = k * g := Nat.mul_comm g k
    have hqk : q ≤ k * g := by
      calc q = g * (Q * G) := by rw [hQ, hG]; ring
        _ ≤ g * k := Nat.mul_le_mul (le_refl g) hQk
        _ = k * g := Nat.mul_comm g k
    omega
  · intro hmax
    have hpk : p ≤ k * g := le_trans (le_max_left p q) hmax
    have hqk : q ≤ k * g := le_trans (le_max_right p q) hmax
    have hPk : P * G ≤ k := by
      refine Nat.le_of_mul_le_mul_left ?_ hgpos
      calc g * (P * G) = p := by rw [hP, hG]; ring
        _ ≤ k * g := hpk
        _ = g * k := Nat.mul_comm k g
    have hQk : Q * G ≤ k := by
      refine Nat.le_of_mul_le_mul_left ?_ hgpos
      calc g * (Q * G) = q := by rw [hQ, hG]; ring
        _ ≤ k * g := hqk
        _ = g * k := Nat.mul_comm k g
    refine ⟨p + P * G, q + Q * G, by omega, by omega, by omega, by omega, ?_, ?_, ?_⟩
    · intro he
      have h6 : q + Q * G = q := congrArg Prod.snd he
      have h7 : 0 < Q * G := Nat.mul_pos hQpos hGpos
      omega
    · calc (p + P * G) * q = p * q + P * G * q := by ring
        _ = q * p + Q * G * p := by rw [hP, hQ]; ring
        _ = (q + Q * G) * p := by ring
    · have h1 : p + P * G = P * (g' + G) := by rw [hP]; ring
      have h3 : g' ∣ t0 * (g' + G) := by
        rw [show t0 * (g' + G) = t0 * g' + t0 * G from by ring]
        exact Nat.dvd_add ⟨t0, by ring⟩ ((hkey G).2 dvd_rfl)
      rw [h1, hP]
      obtain ⟨c, hc⟩ := h3
      exact ⟨c, by
        rw [show t0 * (P * (g' + G)) = t0 * (g' + G) * P from by ring, hc]; ring⟩

theorem nd_exists_iff (p q t0 k : ℕ) (hp : 0 < p) (hq : 0 < q) :
    (∃ i j, p ≤ i ∧ i ≤ p + k ∧ q ≤ j ∧ j ≤ q + k ∧ (i, j) ≠ (p, q) ∧
        i * q = j * p ∧ p ∣ t0 * i)
      ↔ max p q ≤ k * Nat.gcd (Nat.gcd p q) t0 := by
  have hg'pos : 0 < Nat.gcd p q := Nat.pos_of_ne_zero fun h => by
    rw [Nat.gcd_eq_zero_iff] at h; omega
  obtain ⟨P, Q, hP, hQ, hcopPQ, hPpos⟩ := gcd_split p q hp
  have hQpos : 0 < Q := Nat.pos_of_ne_zero fun h => by rw [h, Nat.mul_zero] at hQ; omega
  obtain ⟨G, T, hG, hT, hcopGT, hGpos⟩ := gcd_split (Nat.gcd p q) t0 hg'pos
  have hgpos : 0 < Nat.gcd (Nat.gcd p q) t0 := Nat.pos_of_ne_zero fun h => by
    rw [Nat.gcd_eq_zero_iff] at h; omega
  exact nd_core hP hQ hcopPQ hPpos hQpos hg'pos hG hT hcopGT hgpos hGpos

theorem nd_box_iff (p q t0 k : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) :
    (∀ i j, p ≤ i → i ≤ p + k → q ≤ j → j ≤ q + k → (i, j) ≠ (p, q) →
        ¬(i * q = j * p ∧ p ∣ t0 * i))
      ↔ k * Nat.gcd (Nat.gcd p q) t0 < max p q := by
  constructor
  · intro h
    rcases Nat.lt_or_ge (k * Nat.gcd (Nat.gcd p q) t0) (max p q) with hlt | hge
    · exact hlt
    · obtain ⟨i, j, h1, h2, h3, h4, h5, h6, h7⟩ :=
        (nd_exists_iff p q t0 k (by omega) (by omega)).2 hge
      exact absurd ⟨h6, h7⟩ (h i j h1 h2 h3 h4 h5)
  · intro hlt i j h1 h2 h3 h4 h5 hcon
    have hge : max p q ≤ k * Nat.gcd (Nat.gcd p q) t0 :=
      (nd_exists_iff p q t0 k (by omega) (by omega)).1
        ⟨i, j, h1, h2, h3, h4, h5, hcon.1, hcon.2⟩
    omega

theorem nd_box_one (p q t0 : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) (ht0 : 1 ≤ t0)
    (ht0' : t0 ≤ min p q) (hne : ¬(p = q ∧ q = t0)) :
    ∀ i j, p ≤ i → i ≤ p + 1 → q ≤ j → j ≤ q + 1 → (i, j) ≠ (p, q) →
      ¬(i * q = j * p ∧ p ∣ t0 * i) := by
  rw [nd_box_iff p q t0 1 hp hq, one_mul]
  have h1 : Nat.gcd (Nat.gcd p q) t0 ≤ t0 :=
    Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right _ _)
  rcases Nat.lt_or_ge (Nat.gcd (Nat.gcd p q) t0) (max p q) with h | h
  · exact h
  · exact absurd ⟨by omega, by omega⟩ hne

theorem sign_incoherent :
    0 < tau 1 2 2 3 2 (7 / 5) - 1 ∧ tau 1 2 2 3 3 (7 / 5) - 2 < 0
      ∧ tau 1 2 2 4 3 (7 / 5) - 2 < 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [tau]

theorem sign_paths_opposite :
    0 < (tau 1 2 2 3 3 (7 / 5) - 2) * (tau 1 2 2 4 3 (7 / 5) - 2)
      ∧ (tau 1 2 2 3 2 (7 / 5) - 1) * (tau 1 2 2 4 3 (7 / 5) - 2) < 0 := by
  constructor <;> norm_num [tau]

variable {K : Type*} [Field K]

theorem level_not_formal {m : ℕ} (A : Matrix (Fin (m + 2)) (Fin (m + 2)) K) (hA : IsUnit A.det)
    (t : Fin (m + 2)) : ∃ u : Fin (m + 2) → K, A⁻¹ *ᵥ u ≠ 0 ∧ (A⁻¹ *ᵥ u) t = 0 := by
  obtain ⟨t', ht'⟩ : ∃ t' : Fin (m + 2), t' ≠ t := exists_ne t
  refine ⟨A *ᵥ (Pi.single t' 1), ?_, ?_⟩
  · rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hA, Matrix.one_mulVec]
    intro hz
    have hz' := congrFun hz t'
    rw [Pi.single_eq_same] at hz'
    exact one_ne_zero hz'
  · rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hA, Matrix.one_mulVec]
    exact Pi.single_eq_of_ne (Ne.symm ht') 1

end Rhone.Probability.Propagation
