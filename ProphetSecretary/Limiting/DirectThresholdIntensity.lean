import ProphetSecretary.Limiting.DirectScoreMarginals
import ProphetSecretary.Limiting.ThresholdedOfferLaw

/-!
# Exact positive-band intensity of a fixed-size direct approximation

Summing the actual virtual marginal laws above a nonnegative cutoff recovers
the restricted finite intensity exactly. The number of variables is the
chosen fixed count, not a parameter recomputed after a likelihood tilt.
-/
open MeasureTheory Set
open scoped Classical BigOperators NNReal ENNReal
namespace ProphetSecretary.Limiting

lemma directPoissonMarginal_threshold_sum (μ : FiniteMeasure ℝ) (p : unitInterval) (N : ℕ)
    (hN : 0<N) (hp : (p:ℝ)=(μ.mass:ℝ)/(N:ℝ)) {d : ℝ} (hd : 0≤d) :
    (∑ _i : Fin N, thresholdMarkIntensity (zeroInflatedLaw (normalizedMarkOrZero μ) p) d)=μ.restrict (Ioi d) := by
  let κ := zeroInflatedLaw (normalizedMarkOrZero μ) p
  let ν : FiniteMeasure ℝ := ∑ _i : Fin N, thresholdMarkIntensity κ d
  have hEach (S : Set ℝ) (hS : MeasurableSet S) :
      (thresholdMarkIntensity κ d:Measure ℝ).real S=(μ:Measure ℝ).real (S∩Ioi d)/(N:ℝ) := by
    change (κ.restrict (Ioi d)).real S=_
    rw [Measure.real,Measure.restrict_apply hS]
    exact directPoissonMarginal_band_mass μ p N hp (hS.inter measurableSet_Ioi)
      (fun hx => not_lt.mpr hd hx.2)
  have hReal (S : Set ℝ) (hS : MeasurableSet S) :
      (ν:Measure ℝ).real S=(μ.restrict (Ioi d):Measure ℝ).real S := by
    have hSum : (ν:Measure ℝ).real S=∑ _i : Fin N, (thresholdMarkIntensity κ d:Measure ℝ).real S := by
      simp only [ν,FiniteMeasure.toMeasure_sum,Measure.real,Measure.coe_finsetSum,Finset.sum_apply]
      exact ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _)
    rw [hSum]
    simp_rw [hEach S hS]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    have hNr : (N:ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
    rw [mul_div_cancel₀ _ hNr]
    change (μ:Measure ℝ).real (S∩Ioi d)=((μ:Measure ℝ).restrict (Ioi d)).real S
    rw [Measure.real,Measure.real,Measure.restrict_apply hS]
  apply FiniteMeasure.toMeasure_injective
  apply Measure.ext
  intro S hS
  calc
    _ = ENNReal.ofReal ((ν:Measure ℝ).real S) := (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ = ENNReal.ofReal ((μ.restrict (Ioi d):Measure ℝ).real S) := congrArg ENNReal.ofReal (hReal S hS)
    _ = _ := ENNReal.ofReal_toReal (measure_ne_top _ _)
end ProphetSecretary.Limiting
