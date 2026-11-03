import ProphetSecretary.Model.PositiveArrivalSlope
import ProphetSecretary.Model.ScalarBands
import ProphetSecretary.Model.TruncatedReward

/-!
# Sharp acceptance bands for numerical calibration

The first-positive-arrival duration bound gives slope `c/(1+L)` for the
elapsed-time acceptance gap, including identity-removal jumps. These are
the numerical disagreement bands in `lem:calibration-coupling`.
-/

open MeasureTheory Set

namespace ProphetSecretary.Model

variable {n : ℕ}

lemma Instance.continuationValue_reciprocal_positiveCount_growth (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (A : Finset (Fin n))
    {w c u v : ℝ} (hw : 0 < w) (hc : 0 < c) (hu : 0 ≤ u) (huv : u ≤ v) :
    (c / (1 + P.positiveCount)) * (v - u) ≤
      P.continuationValue A v w c - P.continuationValue A u w c := by
  have hcount : (P.restrictTo A).positiveCount ≤ P.positiveCount := P.tailCount_restrictTo_le A 0
  have hnonneg : 0 ≤ (P.restrictTo A).positiveCount := (P.restrictTo A).tailCount_nonnegative 0
  have hcoef : c / (1 + P.positiveCount) ≤ c / (1 + (P.restrictTo A).positiveCount) :=
    div_le_div_of_nonneg_left hc.le (by positivity) (by linarith)
  exact (mul_le_mul_of_nonneg_right hcoef (sub_nonneg.mpr huv)).trans
    (remainingScalarValue_reciprocal_positiveCount_growth (P.restrictTo A) (P.restrictTo_integrable_maximum A hP) hw hc hu huv)

theorem Instance.candidateGap_reciprocal_positiveCount_slope (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 < c)
    (i : Fin n) (x : ℝ) (u : Fin n → ℝ) :
    ProphetSecretary.Analysis.SlopeLowerBoundOn (P.candidateGap w c i x u)
      (c / (1 + P.positiveCount)) (Icc (0 : ℝ) 1) := by
  intro t ht s hs hts
  have hg := P.continuationValue_reciprocal_positiveCount_growth hP (otherUnseen u i t) hw hc
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

theorem Instance.candidateGap_reciprocal_positiveCount_band_volume (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c e : ℝ} (hw : 0 < w) (hc : 0 < c)
    (he : 0 ≤ e) (i : Fin n) (x : ℝ) (u : Fin n → ℝ) :
    volume.real (ProphetSecretary.Analysis.thresholdBand (P.candidateGap w c i x u) e) ≤
      2 * e / (c / (1 + P.positiveCount)) := by
  have hL : 0 ≤ P.positiveCount := P.tailCount_nonnegative 0
  exact ProphetSecretary.Analysis.volumeReal_thresholdBand_le (by positivity) he
    (P.candidateGap_reciprocal_positiveCount_slope hP hw hc i x u)

/-- A numerical design law and the true evaluation law have separate positive
counts. Candidate-clock integration retains the true probability of positivity. -/
theorem Instance.positiveAcceptanceBandUnder_probability {S : Type*} [MeasurableSpace S]
    (Q P : Instance n) (hQ : Integrable Instance.maximum Q.valuesLaw)
    (ν : Measure S) [IsProbabilityMeasure ν] {w c δ : ℝ}
    (hw : 0 < w) (hc : 0 < c) (hδ : 0 ≤ δ) (i : Fin n) :
    (P.worldLaw ν).real {ω : World n S | 0 < ω.1 i ∧
      |w * ω.1 i - Q.continuationAtArrival w c ω.1 ω.2.1 i| ≤ δ} ≤
      (2 * δ / (c / (1 + Q.positiveCount))) * (P.law i).real (Ioi 0) := by
  let μ := P.worldLaw ν
  let E : Set (World n S) := {ω | 0 < ω.1 i ∧
    |w * ω.1 i - Q.continuationAtArrival w c ω.1 ω.2.1 i| ≤ δ}
  let a := c / (1 + Q.positiveCount)
  let K := 2 * δ / a
  have hL : 0 ≤ Q.positiveCount := Q.tailCount_nonnegative 0
  have ha : 0 < a := by dsimp [a]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hx : Measurable (fun ω : World n S => ω.1 i) :=
    (measurable_pi_apply i).comp measurable_fst
  have hpos : MeasurableSet {ω : World n S | 0 < ω.1 i} :=
    measurableSet_lt measurable_const hx
  have hV : Measurable (fun ω : World n S => Q.continuationAtArrival w c ω.1 ω.2.1 i) :=
    Q.measurable_continuationAtArrival hQ hw hc.le
      (fun j => (measurable_pi_apply j).comp measurable_fst)
      (fun j => (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)) i
  have hE : MeasurableSet E := hpos.inter
    (measurableSet_le (continuous_abs.measurable.comp ((measurable_const.mul hx).sub hV)) measurable_const)
  have hp := P.replaceClock_measurePreserving ν i
  have hpre := hE.preimage hp.measurable
  have hInner (ω : World n S) :
      Instance.uniformClock (Prod.mk ω ⁻¹' ((Instance.replaceClock i) ⁻¹' E)) ≤
        {ω : World n S | 0 < ω.1 i}.indicator (fun _ => ENNReal.ofReal K) ω := by
    by_cases hpositive : 0 < ω.1 i
    · rw [Set.indicator_of_mem (show ω ∈ {ω : World n S | 0 < ω.1 i} from hpositive)]
      let g := Q.candidateGap w c i (ω.1 i) ω.2.1
      have hg := Q.measurable_candidateGap hQ hw.le hc.le i (ω.1 i) ω.2.1
      have hlevel : MeasurableSet {t : ℝ | |g t| ≤ δ} :=
        measurableSet_le (continuous_abs.measurable.comp hg) measurable_const
      have he : Prod.mk ω ⁻¹' ((Instance.replaceClock i) ⁻¹' E) = {t : ℝ | |g t| ≤ δ} := by
        ext t
        change (0 < ω.1 i ∧ |w * ω.1 i - Q.continuationAtArrival w c ω.1
          (Function.update ω.2.1 i t) i| ≤ δ) ↔ |Q.candidateGap w c i (ω.1 i) ω.2.1 t| ≤ δ
        rw [Q.candidateGap_eq_replacedAcceptanceGap]
        exact and_iff_right hpositive
      rw [he, Instance.uniformClock, Measure.restrict_apply hlevel, inter_comm]
      exact ProphetSecretary.Analysis.volume_thresholdBand_le ha
        (Q.candidateGap_reciprocal_positiveCount_slope hQ hw hc i (ω.1 i) ω.2.1)
    · rw [Set.indicator_of_notMem (show ω ∉ {ω : World n S | 0 < ω.1 i} from hpositive)]
      have he : Prod.mk ω ⁻¹' ((Instance.replaceClock i) ⁻¹' E) = ∅ := by
        ext t
        change (0 < ω.1 i ∧ _) ↔ False
        simp [hpositive]
      rw [he, measure_empty]
  have hv : MeasurePreserving (fun ω : World n S => ω.1 i) μ (P.law i) :=
    (measurePreserving_eval P.law i).comp measurePreserving_fst
  have hvalue : μ {ω : World n S | 0 < ω.1 i} = P.law i (Ioi 0) :=
    hv.measure_preimage measurableSet_Ioi.nullMeasurableSet
  have hbound : μ E ≤ ENNReal.ofReal K * P.law i (Ioi 0) := by
    calc
      μ E = (μ.prod Instance.uniformClock) ((Instance.replaceClock i) ⁻¹' E) :=
        (hp.measure_preimage hE.nullMeasurableSet).symm
      _ = ∫⁻ ω, Instance.uniformClock (Prod.mk ω ⁻¹' ((Instance.replaceClock i) ⁻¹' E)) ∂μ :=
        Measure.prod_apply hpre
      _ ≤ ∫⁻ ω, {ω : World n S | 0 < ω.1 i}.indicator (fun _ => ENNReal.ofReal K) ω ∂μ :=
        lintegral_mono hInner
      _ = ENNReal.ofReal K * P.law i (Ioi 0) := by
        rw [lintegral_indicator hpos]
        simp [hvalue]
  have he : ENNReal.ofReal K * P.law i (Ioi 0) =
      ENNReal.ofReal (K * (P.law i).real (Ioi 0)) := by
    rw [ENNReal.ofReal_mul hK, Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rw [he] at hbound
  exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg hK measureReal_nonneg) hbound

end ProphetSecretary.Model
