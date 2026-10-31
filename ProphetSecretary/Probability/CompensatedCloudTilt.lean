import ProphetSecretary.Probability.CompensatedCloudScore
import ProphetSecretary.Probability.CompensatedBandTilt

/-!
# Controlling the compensating change outside a positive band

For nonidentical residual variables with band masses at most p_max≤1/2, the
sum of compensating mass changes on D\B is at most 2|t|p_max ΣᵢPᵢ(D).
This is the finite estimate used to identify the tilted cloud limit in
`updual:scorelift`; no zero atom is required.
-/

open MeasureTheory Set
open scoped Classical BigOperators

namespace ProphetSecretary.Probability

variable {n : ℕ}

theorem compensatedCloudTilt_outsideBand_mass_le (μ : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] {B D : Set ℝ} (hB : MeasurableSet B) (hD : MeasurableSet D)
    {p θ : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 1 / 2) (hpi : ∀ i, (μ i).real B ≤ p)
    (hθ : |θ| ≤ 1 / 4) :
    (∑ i, |(tiltLaw (μ i) (compensatedBandScore (μ i) B) θ).real (D \ B) - (μ i).real (D \ B)|) ≤
      2 * |θ| * p * ∑ i, (μ i).real D := by
  have hhalf (i : Fin n) : (μ i).real B ≤ 1 / 2 := (hpi i).trans hp
  have hratio (i : Fin n) : (μ i).real B / (1 - (μ i).real B) ≤ 2 * p := by
    have h := compensatedBandScore_secondMoment_le (μ i) hB (hhalf i)
    rw [compensatedBandScore_secondMoment (μ i) hB (by linarith [hhalf i])] at h
    linarith only [h, hpi i]
  calc
    _ = ∑ i, |θ| * ((μ i).real B / (1 - (μ i).real B) * (μ i).real (D \ B)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [compensatedBandScore_tilt_complement_difference (μ i) hB (hhalf i) hθ
        (hD.diff hB) (fun _ hx => hx.2)]
      ring
    _ ≤ ∑ i, |θ| * (2 * p * (μ i).real D) := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg θ)
      exact mul_le_mul (hratio i) (measureReal_mono (μ := μ i) Set.sdiff_subset)
        measureReal_nonneg (by positivity)
    _ = _ := by
      simp_rw [← mul_assoc]
      rw [← Finset.mul_sum]
      ring

end ProphetSecretary.Probability
