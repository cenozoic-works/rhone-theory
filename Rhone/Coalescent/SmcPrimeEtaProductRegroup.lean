/-
Copyright (c) 2026 Cenozoic Works. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cenozoic Works
-/
module

public import Rhone.Coalescent.SmcPrimeEtaFlatCoordinates
public import Rhone.Coalescent.SmcPrimeReferenceFiberFlat

/-!
# Measure-preserving regrouping of product coordinates of the one-split reference measure

Source: marjoram_wall2006, Methods, “The SMC′ algorithm”, steps 1–6. -/

@[expose] public section
namespace Rhone.Coalescent.SmcPrime
open MeasureTheory Probability.MeasureTransport
open scoped ENNReal

private theorem count_product {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [Countable A] [Countable B] [MeasurableSingletonClass A] [MeasurableSingletonClass B] :
    (Measure.count : Measure A).prod (Measure.count : Measure B) = Measure.count := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_prod _ hf.aemeasurable, lintegral_count, lintegral_count,
    ENNReal.tsum_prod']
  exact tsum_congr (fun _ => lintegral_count _)

def etaProductShuffleEquiv {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D] : (A × B) × (C × D) ≃ᵐ (A × C) × (B × D) where
  toEquiv := Equiv.prodProdProdComm A B C D
  measurable_toFun := by
    change Measurable (fun p : (A × B) × (C × D) => ((p.1.1, p.2.1), (p.1.2, p.2.2)))
    fun_prop
  measurable_invFun := by
    change Measurable (fun p : (A × C) × (B × D) => ((p.1.1, p.2.1), (p.1.2, p.2.2)))
    fun_prop

private theorem etaProductShuffleEquiv_preserving {A B C D : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    (a : Measure A) (b : Measure B) (c : Measure C) (d : Measure D)
    [SFinite a] [SFinite b] [SFinite c] [SFinite d] :
    MeasurePreserving (etaProductShuffleEquiv : (A × B) × (C × D) ≃ᵐ (A × C) × (B × D))
      ((a.prod b).prod (c.prod d)) ((a.prod c).prod (b.prod d)) := by
  have h0 := measurePreserving_prodAssoc a b (c.prod d)
  have h1 := (MeasurePreserving.id a).prod
    ((measurePreserving_prodAssoc b c d).symm MeasurableEquiv.prodAssoc)
  have h2 := (MeasurePreserving.id a).prod
    ((Measure.measurePreserving_swap (μ := b) (ν := c)).prod (MeasurePreserving.id d))
  have h3 := (MeasurePreserving.id a).prod (measurePreserving_prodAssoc c b d)
  have h4 := (measurePreserving_prodAssoc a c (b.prod d)).symm MeasurableEquiv.prodAssoc
  exact h4.comp (h3.comp (h2.comp (h1.comp h0)))

def etaLastToFirst {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] : A × (B × C) ≃ᵐ C × (B × A) where
  toEquiv :=
    ((Equiv.prodAssoc A B C).symm.trans (Equiv.prodComm (A × B) C)).trans
      ((Equiv.refl C).prodCongr (Equiv.prodComm A B))
  measurable_toFun := by
    change Measurable (fun p : A × (B × C) => (p.2.2, (p.2.1, p.1)))
    fun_prop
  measurable_invFun := by
    change Measurable (fun p : C × (B × A) => (p.2.2, (p.2.1, p.1)))
    fun_prop

private theorem etaLastToFirst_preserving {A B C : Type*} [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C] (a : Measure A) (b : Measure B) (c : Measure C)
    [SFinite a] [SFinite b] [SFinite c] :
    MeasurePreserving (etaLastToFirst : A × (B × C) ≃ᵐ C × (B × A))
      (a.prod (b.prod c)) (c.prod (b.prod a)) := by
  have h0 := (measurePreserving_prodAssoc a b c).symm MeasurableEquiv.prodAssoc
  have h1 := Measure.measurePreserving_swap (μ := a.prod b) (ν := c)
  have h2 := (MeasurePreserving.id c).prod (Measure.measurePreserving_swap (μ := a) (ν := b))
  exact h2.comp (h1.comp h0)

def etaClockSplit (n : ℕ) : (Fin (n + 2) → ℝ) ≃ᵐ (Fin n → ℝ) × (ℝ × ℝ) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 2) => ℝ) (Fin.last (n + 1))).trans
    (((MeasurableEquiv.refl ℝ).prodCongr
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n))).trans
        etaLastToFirst)

theorem etaClockSplit_preserving (n : ℕ) :
    MeasurePreserving (etaClockSplit n) volume
      ((volume : Measure (Fin n → ℝ)).prod (volume.prod volume)) := by
  have h0 := volume_preserving_piFinSuccAbove (fun _ : Fin (n + 2) => ℝ) (Fin.last (n + 1))
  have h1 := (MeasurePreserving.id (volume : Measure ℝ)).prod
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n))
  have h2 := etaLastToFirst_preserving (volume : Measure ℝ) (volume : Measure ℝ)
    (volume : Measure (Fin n → ℝ))
  exact h2.comp (h1.comp h0)

theorem etaClockSplit_apply (n : ℕ) (τ : Fin (n + 2) → ℝ) :
    etaClockSplit n τ =
      (fun j => τ j.castSucc.castSucc, τ (Fin.last n).castSucc, τ (Fin.last (n + 1))) := by
  simp [etaClockSplit, MeasurableEquiv.prodCongr, MeasurableEquiv.piFinSuccAbove,
    etaLastToFirst, Equiv.prodAssoc, Equiv.prodCongr, Fin.init]
  rfl

abbrev EtaRawCoordinate (N : ℕ) :=
  ((Fin (N - 1) → ℕ × ℕ) × (Fin (N - 1) → ℝ)) × EtaFiberCoordinate N

abbrev EtaRealProduct (N : ℕ) := (Fin (N - 1) → ℝ) × (ℝ × (ℝ × ℝ))

def etaProductShuffle (N : ℕ) :
    EtaRawCoordinate N ≃ᵐ EtaFlatMark N × EtaRealProduct N :=
  ((MeasurableEquiv.refl _).prodCongr
    ((MeasurableEquiv.refl (ℕ × ℝ)).prodCongr
      (etaLastToFirst : ℝ × (ℝ × Finset (Fin N)) ≃ᵐ Finset (Fin N) × (ℝ × ℝ)))).trans
        (((MeasurableEquiv.refl _).prodCongr etaProductShuffleEquiv).trans etaProductShuffleEquiv)

theorem etaProductShuffle_preserving (N : ℕ) :
    MeasurePreserving (etaProductShuffle N)
      (((Measure.count : Measure (Fin (N - 1) → ℕ × ℕ)).prod volume).prod
        (((Measure.count : Measure ℕ).prod volume).prod
          (volume.prod (volume.prod (Measure.count : Measure (Finset (Fin N)))))))
      ((Measure.count : Measure (EtaFlatMark N)).prod
        (volume.prod (volume.prod (volume.prod volume)))) := by
  let w : Measure (Fin (N - 1) → ℕ × ℕ) := Measure.count
  let o : Measure (Fin (N - 1) → ℝ) := volume
  let b : Measure ℕ := Measure.count
  let c : Measure (Finset (Fin N)) := Measure.count
  let v : Measure ℝ := volume
  have h0 := (MeasurePreserving.id (w.prod o)).prod
    ((MeasurePreserving.id (b.prod v)).prod (etaLastToFirst_preserving v v c))
  have h1 := (MeasurePreserving.id (w.prod o)).prod
    (etaProductShuffleEquiv_preserving b v c (v.prod v))
  have h2 := etaProductShuffleEquiv_preserving w o (b.prod c) (v.prod (v.prod v))
  have h := h2.comp (h1.comp h0)
  change MeasurePreserving (etaProductShuffle N) _ ((w.prod (b.prod c)).prod _) at h
  dsimp only [w, b, c] at h
  rw [count_product, count_product] at h
  exact h

def etaMarkedClockSplit (n : ℕ) :
    MarkedClocks (n + 2) ≃ᵐ (Fin n → ℝ) × (ℝ × (ℝ × ℝ)) :=
  ((etaClockSplit n).prodCongr (MeasurableEquiv.refl ℝ)).trans
    (MeasurableEquiv.prodAssoc.trans
      ((MeasurableEquiv.refl _).prodCongr MeasurableEquiv.prodAssoc))

theorem etaMarkedClockSplit_preserving (n : ℕ) :
    MeasurePreserving (etaMarkedClockSplit n) volume
      ((volume : Measure (Fin n → ℝ)).prod
        ((volume : Measure ℝ).prod ((volume : Measure ℝ).prod (volume : Measure ℝ)))) := by
  have h0 := (etaClockSplit_preserving n).prod (MeasurePreserving.id (volume : Measure ℝ))
  have h1 := measurePreserving_prodAssoc (volume : Measure (Fin n → ℝ))
    ((volume : Measure ℝ).prod (volume : Measure ℝ)) (volume : Measure ℝ)
  have h2 := (MeasurePreserving.id (volume : Measure (Fin n → ℝ))).prod
    (measurePreserving_prodAssoc (volume : Measure ℝ) (volume : Measure ℝ) (volume : Measure ℝ))
  exact h2.comp (h1.comp h0)

def etaCoordinateUnpack (n : ℕ) : EtaFlatCoordinate (n + 1) ≃ᵐ EtaRawCoordinate (n + 1) :=
  ((MeasurableEquiv.refl (EtaFlatMark (n + 1))).prodCongr (etaMarkedClockSplit n)).trans
    (etaProductShuffle (n + 1)).symm

theorem etaCoordinateUnpack_preserving (n : ℕ) :
    MeasurePreserving (etaCoordinateUnpack n)
      ((Measure.count : Measure (EtaFlatMark (n + 1))).prod volume)
      (((Measure.count : Measure (Fin n → ℕ × ℕ)).prod volume).prod
        (((Measure.count : Measure ℕ).prod volume).prod
          (volume.prod (volume.prod (Measure.count : Measure (Finset (Fin (n + 1)))))))) := by
  have h0 := (MeasurePreserving.id (Measure.count : Measure (EtaFlatMark (n + 1)))).prod
    (etaMarkedClockSplit_preserving n)
  have h1 := (etaProductShuffle_preserving (n + 1)).symm (etaProductShuffle (n + 1))
  exact h1.comp h0

theorem etaCoordinateUnpack_apply (n : ℕ) (p : EtaFlatCoordinate (n + 1)) :
    etaCoordinateUnpack n p =
      ((p.1.1, etaOldTimes (n + 1) p.2.1),
        ((p.1.2.1, etaCutTime (n + 1) p.2.1),
          (p.2.2, etaAttachmentTime (n + 1) p.2.1, p.1.2.2))) := by
  have he : etaClockSplit n p.2.1 =
      (etaOldTimes (n + 1) p.2.1, etaCutTime (n + 1) p.2.1,
        etaAttachmentTime (n + 1) p.2.1) := by
    rw [etaClockSplit_apply]
    rfl
  have h := congrArg (fun z : (Fin n → ℝ) × (ℝ × ℝ) =>
    ((p.1.1, z.1), ((p.1.2.1, z.2.1), (p.2.2, z.2.2, p.1.2.2)))) he
  simpa [etaCoordinateUnpack, etaProductShuffle, etaProductShuffleEquiv,
    etaMarkedClockSplit, MeasurableEquiv.prodCongr, MeasurableEquiv.prodAssoc,
    etaLastToFirst] using h

end Rhone.Coalescent.SmcPrime
