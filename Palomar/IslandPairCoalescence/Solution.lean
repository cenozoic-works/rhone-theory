module

public import Rhone.Coalescent.IslandPairExpected
public import Rhone.Coalescent.IslandPairFst

@[expose] public section

namespace Rhone.Palomar.IslandPairCoalescence

open Finset MeasureTheory Coalescent.IslandPair

theorem expectedTime_same (d : Nat) (hd : 2 ≤ d) (m c : Real)
    (hm : 0 < m) (hc : 0 < c) (a : Fin d) :
    (chain d m c hm.le hc.le).expectedTime {none} (some (a,a)) = d / c :=
  Rhone.Coalescent.IslandPair.expectedTime_same d hd m c hm hc a

theorem expectedTime_different (d : Nat) (hd : 2 ≤ d) (m c : Real)
    (hm : 0 < m) (hc : 0 < c) (a b : Fin d) (hab : a ≠ b) :
    (chain d m c hm.le hc.le).expectedTime {none} (some (a,b)) =
      d / c + (d - 1 : Nat) / (2 * m) :=
  Rhone.Coalescent.IslandPair.expectedTime_different d hd m c hm hc a b hab

theorem lintegral_timeBefore (d : Nat) (hd : 2 ≤ d) (m c : Real)
    (hm : 0 < m) (hc : 0 < c) (s : State d) :
    ∫⁻ p, (chain d m c hm.le hc.le).timeBefore {none} p
      ∂(chain d m c hm.le hc.le).jumpHoldLaw s = ENNReal.ofReal (meanTime d m c s) :=
  Rhone.Coalescent.IslandPair.lintegral_timeBefore d hd m c hm hc s

end Rhone.Palomar.IslandPairCoalescence

namespace Rhone.Palomar.IslandPairCoalescence

open Finset Filter Topology Coalescent.IslandPair Coalescent.IslandPairFst

theorem fstFromTimes_between (d : ℕ) (hd : 2 ≤ d) (m c : ℝ) (hm : 0 < m) (hc : 0 < c)
    (a b b' : Fin d) (hbb : b ≠ b') :
    fstFromTimes ((chain d m c hm.le hc.le).expectedTime {none} (some (a, a)))
      ((chain d m c hm.le hc.le).expectedTime {none} (some (b, b'))) = fstBetween d m c :=
  Rhone.Coalescent.IslandPairFst.fstFromTimes_between d hd m c hm hc a b b' hbb

theorem fstFromTimes_random (d : ℕ) (hd : 2 ≤ d) (m c : ℝ) (hm : 0 < m) (hc : 0 < c)
    (a : Fin d) :
    fstFromTimes ((chain d m c hm.le hc.le).expectedTime {none} (some (a, a)))
      (randomDemesTime d m c hm.le hc.le) = fstRandom d m c :=
  Rhone.Coalescent.IslandPairFst.fstFromTimes_random d hd m c hm hc a

theorem fstBetween_diploid (d : ℕ) (hd : 2 ≤ d) (m N : ℝ) (hm : 0 < m) (hN : 0 < N) :
    fstBetween d m (1 / (2 * N)) = 1 / (1 + 4 * N * m * ((d : ℝ) / ((d : ℝ) - 1))) :=
  Rhone.Coalescent.IslandPairFst.fstBetween_diploid d hd m N hm hN

theorem fstRandom_diploid (d : ℕ) (hd : 2 ≤ d) (m N : ℝ) (hm : 0 < m) (hN : 0 < N) :
    fstRandom d m (1 / (2 * N)) =
      1 / (1 + 4 * N * m * ((d : ℝ) ^ 2 / ((d : ℝ) - 1) ^ 2)) :=
  Rhone.Coalescent.IslandPairFst.fstRandom_diploid d hd m N hm hN

theorem fstBetween_strictAntiOn (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : 0 < c) :
    StrictAntiOn (fun m : ℝ => fstBetween d m c) (Set.Ioi 0) :=
  Rhone.Coalescent.IslandPairFst.fstBetween_strictAntiOn d hd c hc

theorem fstRandom_strictAntiOn (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : 0 < c) :
    StrictAntiOn (fun m : ℝ => fstRandom d m c) (Set.Ioi 0) :=
  Rhone.Coalescent.IslandPairFst.fstRandom_strictAntiOn d hd c hc

theorem tendsto_fstBetween_zero_right (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : 0 < c) :
    Tendsto (fun m : ℝ => fstBetween d m c) (𝓝[>] 0) (𝓝 1) :=
  Rhone.Coalescent.IslandPairFst.tendsto_fstBetween_zero_right d hd c hc

theorem tendsto_fstRandom_zero_right (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : 0 < c) :
    Tendsto (fun m : ℝ => fstRandom d m c) (𝓝[>] 0) (𝓝 1) :=
  Rhone.Coalescent.IslandPairFst.tendsto_fstRandom_zero_right d hd c hc

theorem tendsto_fstBetween_atTop (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (_hc : 0 < c) :
    Tendsto (fun m : ℝ => fstBetween d m c) atTop (𝓝 0) :=
  Rhone.Coalescent.IslandPairFst.tendsto_fstBetween_atTop d hd c _hc

theorem tendsto_fstRandom_atTop (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (_hc : 0 < c) :
    Tendsto (fun m : ℝ => fstRandom d m c) atTop (𝓝 0) :=
  Rhone.Coalescent.IslandPairFst.tendsto_fstRandom_atTop d hd c _hc

theorem tendsto_fstBetween_demes (m c : ℝ) (hm : 0 < m) (hc : 0 < c) :
    Tendsto (fun d : ℕ => fstBetween d m c) atTop (𝓝 (c / (2 * m + c))) :=
  Rhone.Coalescent.IslandPairFst.tendsto_fstBetween_demes m c hm hc

theorem tendsto_fstRandom_demes (m c : ℝ) (hm : 0 < m) (hc : 0 < c) :
    Tendsto (fun d : ℕ => fstRandom d m c) atTop (𝓝 (c / (2 * m + c))) :=
  Rhone.Coalescent.IslandPairFst.tendsto_fstRandom_demes m c hm hc

theorem tendsto_fstBetween_demes_diploid (m N : ℝ) (hm : 0 < m) (hN : 0 < N) :
    Tendsto (fun d : ℕ => fstBetween d m (1 / (2 * N))) atTop
      (𝓝 (1 / (1 + 4 * N * m))) :=
  Rhone.Coalescent.IslandPairFst.tendsto_fstBetween_demes_diploid m N hm hN

theorem tendsto_fstRandom_demes_diploid (m N : ℝ) (hm : 0 < m) (hN : 0 < N) :
    Tendsto (fun d : ℕ => fstRandom d m (1 / (2 * N))) atTop
      (𝓝 (1 / (1 + 4 * N * m))) :=
  Rhone.Coalescent.IslandPairFst.tendsto_fstRandom_demes_diploid m N hm hN

end Rhone.Palomar.IslandPairCoalescence
