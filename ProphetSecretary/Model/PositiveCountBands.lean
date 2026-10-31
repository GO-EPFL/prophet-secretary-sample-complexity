import ProphetSecretary.Model.PositiveCountGrowth
import ProphetSecretary.Model.ScalarBands
import ProphetSecretary.Model.TruncatedReward

/-!
# Acceptance bands controlled by positive tail count

Remaining-horizon growth and unseen-set monotonicity give increasing elapsed-time
gaps. The bound includes jumps caused by observed zero identities and replaces
the finite cardinality constant by the expected number of positive offers.
-/

open MeasureTheory Set

namespace ProphetSecretary.Model

variable {n : ℕ}

lemma Instance.continuationValue_positiveCount_growth (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (A : Finset (Fin n))
    {w c u v : ℝ} (hw : 0 < w) (hc : 0 < c) (hu : 0 ≤ u) (huv : u ≤ v) :
    (c / (4 * (1 + P.positiveCount))) * (v - u) ≤
      P.continuationValue A v w c - P.continuationValue A u w c := by
  have hcount : (P.restrictTo A).positiveCount ≤ P.positiveCount := P.tailCount_restrictTo_le A 0
  have hnonneg : 0 ≤ (P.restrictTo A).positiveCount := (P.restrictTo A).tailCount_nonnegative 0
  have hcoef : c / (4 * (1 + P.positiveCount)) ≤ c / (4 * (1 + (P.restrictTo A).positiveCount)) :=
    div_le_div_of_nonneg_left hc.le (by positivity) (by linarith)
  exact (mul_le_mul_of_nonneg_right hcoef (sub_nonneg.mpr huv)).trans
    (remainingScalarValue_positiveCount_growth (P.restrictTo A) (P.restrictTo_integrable_maximum A hP) hw hc hu huv)

theorem Instance.candidateGap_positiveCount_slope (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 < c)
    (i : Fin n) (x : ℝ) (u : Fin n → ℝ) :
    ProphetSecretary.Analysis.SlopeLowerBoundOn (P.candidateGap w c i x u)
      (c / (4 * (1 + P.positiveCount))) (Icc (0 : ℝ) 1) := by
  intro t ht s hs hts
  have hg := P.continuationValue_positiveCount_growth hP (otherUnseen u i t) hw hc
    (sub_nonneg.mpr hs.2) (sub_le_sub_left hts 1)
  have hm := P.optimalScalarValue_restrictTo_mono hP (otherUnseen_antitone u i hts) hw.le
    (mul_nonneg hc.le (sub_nonneg.mpr hs.2))
  have he : (1 - t) - (1 - s) = s - t := by ring
  rw [he] at hg
  change P.continuationValue (otherUnseen u i s) (1 - s) w c ≤
    P.continuationValue (otherUnseen u i t) (1 - s) w c at hm
  unfold Instance.candidateGap
  rw [max_eq_right (sub_nonneg.mpr ht.2), max_eq_right (sub_nonneg.mpr hs.2)]
  linarith only [hg, hm]

theorem Instance.candidateGap_positiveCount_band_volume (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c e : ℝ} (hw : 0 < w) (hc : 0 < c)
    (he : 0 ≤ e) (i : Fin n) (x : ℝ) (u : Fin n → ℝ) :
    volume.real (ProphetSecretary.Analysis.thresholdBand (P.candidateGap w c i x u) e) ≤
      2 * e / (c / (4 * (1 + P.positiveCount))) := by
  have hL : 0 ≤ P.positiveCount := P.tailCount_nonnegative 0
  exact ProphetSecretary.Analysis.volumeReal_thresholdBand_le (by positivity) he
    (P.candidateGap_positiveCount_slope hP hw hc i x u)

end ProphetSecretary.Model
