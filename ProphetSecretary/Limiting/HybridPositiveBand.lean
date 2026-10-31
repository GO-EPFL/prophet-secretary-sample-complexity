import ProphetSecretary.Limiting.HybridCandidateGap
import ProphetSecretary.Analysis.BandSlopeVolume

/-!
# Hybrid positive acceptance-band width

Between two band times the later retained state is a subset of the earlier
one. Its actual base optimizer and the proved fixed-policy horizon support
supply the slope. Constants depend on cap, weights and tails above b/4 only;
there is no retained-dimension or total-Poisson-mass factor.
-/
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal Classical
namespace ProphetSecretary.Limiting
variable {n : ℕ}

theorem FiniteIntensityHybridInstance.candidateGap_positiveBand_slope
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal = 0) {H w c b L e : ℝ}
    (hH : 0 ≤ H) (hCap : (B.cap : ℝ) ≤ H) (hw : 0 < w) (hc : 0 < c) (hb : 0 < b)
    (hTail : B.tailCount (b/4) ≤ L) (he : e ≤ w*b/4)
    (candidate : Option (Fin n)) {x : ℝ} (hx : b ≤ x) (u : Fin n → ℝ) :
    ProphetSecretary.Analysis.SlopeLowerBoundOn (B.candidateGap w c candidate x u)
      (c*Model.positiveBandDuration H w c b L)
      (ProphetSecretary.Analysis.thresholdBand (B.candidateGap w c candidate x u) e) := by
  intro t ht s hs hts
  let A := retainedClockState u t candidate
  let D := retainedClockState u s candidate
  let C := B.restrictIndividuals D
  let R := C.remainingHorizon (remainingTime s)
  let π := R.valueThresholdPolicy hw.le (mul_nonneg hc.le (remainingTime s).property)
  have hGap : B.candidateGap w c candidate x u s ≤ e :=
    (le_abs_self _).trans (show |B.candidateGap w c candidate x u s| ≤ e from hs.2)
  have hLevel : 3*w*b/4 ≤ C.continuationValue w c (remainingTime s) := by
    change w*x-C.continuationValue w c (remainingTime s) ≤ e at hGap
    nlinarith [mul_le_mul_of_nonneg_left hx hw.le]
  have hRem1 : remainingTime s ≤ 1 := remainingTime_le_one hs.1.1
  have hTailR : R.tailCount (b/4) ≤ L :=
    (C.remainingHorizon_tailCount_le hRem1 (b/4)).trans
      ((B.restrictIndividuals_tailCount_le D (b/4)).trans hTail)
  have hRemReal : (remainingTime s : ℝ) ≤ 1 := by exact_mod_cast hRem1
  have hWeight : c*(remainingTime s : ℝ) ≤ c := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hRemReal hc.le
  have hOpt : π.scalarObjective R w (c*(remainingTime s : ℝ)) = C.continuationValue w c (remainingTime s) :=
    R.valueThresholdPolicy_optimal ha hw (mul_nonneg hc.le (remainingTime s).property)
  have hObj : 3*w*b/4 ≤ π.scalarObjective R w (c*(remainingTime s : ℝ)) := hLevel.trans_eq hOpt.symm
  have hT : Model.positiveBandDuration H w c b L ≤ π.expectedDuration R :=
    π.duration_ge_positiveValue R ha hH hCap hw hc hb hTailR hWeight hObj
  have hRem : remainingTime s ≤ remainingTime t := by
    have hR : (remainingTime s : ℝ) ≤ (remainingTime t : ℝ) := by
      rw [coe_remainingTime hs.1.2,coe_remainingTime ht.1.2]
      linarith
    exact_mod_cast hR
  have hSupport := C.continuationValue_support ha hw hc.le hRem
  change C.continuationValue w c (remainingTime s)+
      c*((remainingTime t : ℝ)-(remainingTime s : ℝ))*π.expectedDuration R ≤
        C.continuationValue w c (remainingTime t) at hSupport
  have hMono := (B.remainingHorizon (remainingTime t)).optimalScalarValue_restrictIndividuals_mono ha
    (retainedClockState_antitone u candidate hts) hw.le (mul_nonneg hc.le (remainingTime t).property)
  change C.continuationValue w c (remainingTime t) ≤
    (B.restrictIndividuals A).continuationValue w c (remainingTime t) at hMono
  have hMul := mul_le_mul_of_nonneg_left hT (mul_nonneg hc.le
    (sub_nonneg.mpr (show (remainingTime s : ℝ) ≤ (remainingTime t : ℝ) by exact_mod_cast hRem)))
  have hDelta : (remainingTime t : ℝ)-(remainingTime s : ℝ) = s-t := by
    rw [coe_remainingTime ht.1.2,coe_remainingTime hs.1.2]
    ring
  rw [hDelta] at hSupport hMul
  change (c*Model.positiveBandDuration H w c b L)*(s-t) ≤
    (w*x-C.continuationValue w c (remainingTime s))-
      (w*x-(B.restrictIndividuals A).continuationValue w c (remainingTime t))
  nlinarith only [hSupport,hMono,hMul]

/-- This is an outer-measure statement, so no clock-history regularity is
silently supplied as a measurability hypothesis. -/
theorem FiniteIntensityHybridInstance.candidateGap_positiveBand_volume
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal = 0) {H w c b L e : ℝ}
    (hH : 0 ≤ H) (hCap : (B.cap : ℝ) ≤ H) (hw : 0 < w) (hc : 0 < c) (hb : 0 < b)
    (hTail : B.tailCount (b/4) ≤ L) (he : e ≤ w*b/4)
    (candidate : Option (Fin n)) {x : ℝ} (hx : b ≤ x) (u : Fin n → ℝ) :
    volume (ProphetSecretary.Analysis.thresholdBand (B.candidateGap w c candidate x u) e) ≤
      ENNReal.ofReal (2*e/(c*Model.positiveBandDuration H w c b L)) := by
  have hL0 : 0 ≤ L := (B.tailCount_nonnegative _).trans hTail
  exact ProphetSecretary.Analysis.volume_thresholdBand_le_of_bandSlope
    (mul_pos hc (Model.positiveBandDuration_pos hH hw hc hb hL0))
    (B.candidateGap_positiveBand_slope ha hH hCap hw hc hb hTail he candidate hx u)

end ProphetSecretary.Limiting
