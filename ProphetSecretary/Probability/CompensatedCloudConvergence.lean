import ProphetSecretary.Probability.CompensatedCloudTilt

/-!
# Vanishing score-count error for a residual array

When residual band masses vanish uniformly and their sum stays bounded, the
actual squared L² error between the compensated score and centered count tends
to zero. The dimension may vary with the sequence. This proves the error term
in `updual:scorecount`; convergence of the counts themselves is a separate step.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators Topology

namespace ProphetSecretary.Probability

theorem compensatedCloudScore_centeredCount_tendsto_L2
    (N : ℕ → ℕ) (μ : ∀ m : ℕ, Fin (N m) → Measure ℝ)
    [∀ m i, IsProbabilityMeasure (μ m i)] {B : Set ℝ} (hB : MeasurableSet B)
    (pmax : ℕ → ℝ) (hp0 : ∀ m, 0 ≤ pmax m) (hpHalf : ∀ m, pmax m ≤ 1 / 2)
    (hp : ∀ m i, (μ m i).real B ≤ pmax m) {I : ℝ}
    (hI : ∀ m, (∑ i, (μ m i).real B) ≤ I) (hlim : Tendsto pmax atTop (𝓝 0)) :
    Tendsto (fun m => ∫ x : Fin (N m) → ℝ,
      (completeScore (fun i => compensatedBandScore (μ m i) B) x -
        ((∑ i, B.indicator (fun _ => (1 : ℝ)) (x i)) - ∑ i, (μ m i).real B)) ^ 2 ∂Measure.pi (μ m))
      atTop (𝓝 0) := by
  apply squeeze_zero (fun m => integral_nonneg fun x => sq_nonneg _) ?_
    (by simpa only [zero_mul] using hlim.mul_const I)
  intro m
  apply (compensatedCloudScore_centeredCount_L2 (μ m) hB (fun i => (hp m i).trans (hpHalf m))).trans
  calc
    (∑ i, ((μ m i).real B) ^ 2) ≤ ∑ i, pmax m * (μ m i).real B := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [pow_two] using mul_le_mul_of_nonneg_right (hp m i) (measureReal_nonneg : 0 ≤ (μ m i).real B)
    _ = pmax m * ∑ i, (μ m i).real B := (Finset.mul_sum _ _ _).symm
    _ ≤ pmax m * I := mul_le_mul_of_nonneg_left (hI m) (hp0 m)

/-- Compensation outside the target band vanishes uniformly over the permitted
perturbation interval, expressed by allowing any sequence of parameters. -/
theorem compensatedCloudTilt_outsideBand_tendsto
    (N : ℕ → ℕ) (μ : ∀ m : ℕ, Fin (N m) → Measure ℝ)
    [∀ m i, IsProbabilityMeasure (μ m i)] {B D : Set ℝ} (hB : MeasurableSet B) (hD : MeasurableSet D)
    (pmax θ : ℕ → ℝ) (hp0 : ∀ m, 0 ≤ pmax m) (hpHalf : ∀ m, pmax m ≤ 1 / 2)
    (hp : ∀ m i, (μ m i).real B ≤ pmax m) (hθ : ∀ m, |θ m| ≤ 1 / 4) {I : ℝ}
    (hI : ∀ m, (∑ i, (μ m i).real D) ≤ I) (hlim : Tendsto pmax atTop (𝓝 0)) :
    Tendsto (fun m => ∑ i, |(tiltLaw (μ m i) (compensatedBandScore (μ m i) B) (θ m)).real (D \ B) -
      (μ m i).real (D \ B)|) atTop (𝓝 0) := by
  apply squeeze_zero (fun m => Finset.sum_nonneg fun i _ => abs_nonneg _) ?_
    (by simpa only [zero_mul, zero_div] using (hlim.mul_const I).div_const 2)
  intro m
  apply (compensatedCloudTilt_outsideBand_mass_le (μ m) hB hD (hp0 m) (hpHalf m) (hp m) (hθ m)).trans
  have hm := mul_le_mul_of_nonneg_left (hI m) (hp0 m)
  have hs : 0 ≤ pmax m * ∑ i, (μ m i).real D :=
    mul_nonneg (hp0 m) (Finset.sum_nonneg fun i _ => measureReal_nonneg)
  have ht : 2 * |θ m| ≤ 1 / 2 := by linarith only [hθ m]
  have hh := mul_le_mul_of_nonneg_right ht hs
  nlinarith only [hh, hm]

end ProphetSecretary.Probability
