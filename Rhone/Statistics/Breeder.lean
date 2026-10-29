/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Rhone.Statistics.Price

/-!
# The breeder's equation as a regression identity

Source: lush1943, ch. 12, p. 143; felsenstein_teg2019, eq. (IX-69), p. 443; falconer_mackay1996,
ch. 11. -/

@[expose] public section

namespace Rhone.Statistics

variable {ι : Type*} [Fintype ι] {F : Type*} [Field F]

def selectionDifferential (w m : ι → F) : F := nextMean w m - popMean m

def selectionResponse (w o : ι → F) : F := nextMean w o - popMean o

private theorem card_ne_zero_of_popMean_ne_zero {w : ι → F} (hw : popMean w ≠ 0) :
    (Fintype.card ι : F) ≠ 0 := by
  intro h
  apply hw
  simp [popMean, h]

/-- Source: lush1943, ch. 12, p. 143; felsenstein_teg2019, eq. (IX-69), p. 443; falconer_mackay1996.
-/
theorem breeder_equation (w m o : ι → F) (a h2 : F) (hw : popMean w ≠ 0)
    (hlin : ∀ i, o i = a + h2 * m i) :
    selectionResponse w o = h2 * selectionDifferential w m := by
  have hc := card_ne_zero_of_popMean_ne_zero hw
  have hw' : ∑ i, w i ≠ 0 := fun h => hw (by simp [popMean, h])
  have h1 : ∑ i, w i * o i = a * ∑ i, w i + h2 * ∑ i, w i * m i := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [hlin i]; ring
  have h2' : ∑ i, o i = (Fintype.card ι : F) * a + h2 * ∑ i, m i := by
    rw [Finset.mul_sum, ← nsmul_eq_mul, ← Finset.card_univ, ← Finset.sum_const,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [hlin i]
  simp only [selectionResponse, selectionDifferential, nextMean, popMean]
  rw [h1, h2']
  field_simp
  ring

theorem heritability_eq_regression_slope [NeZero (Fintype.card ι : F)] (m o : ι → F)
    (a h2 : F) (hlin : ∀ i, o i = a + h2 * m i) (hv : popCov m m ≠ 0) :
    h2 = popCov o m / popCov m m := by
  have hc : (Fintype.card ι : F) ≠ 0 := NeZero.ne _
  have ho : o = fun i => a + h2 * m i := funext hlin
  subst ho
  rw [eq_div_iff hv]
  simp only [popCov, popMean, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum, add_mul, mul_assoc]
  field_simp
  ring

theorem breeder_equation_covariance (w m o : ι → F) (a h2 : F) (hw : popMean w ≠ 0)
    (hlin : ∀ i, o i = a + h2 * m i) :
    selectionResponse w o = h2 * (popCov w m / popMean w) := by
  rw [breeder_equation w m o a h2 hw hlin, selectionDifferential, robertson_price w m hw]

end Rhone.Statistics
