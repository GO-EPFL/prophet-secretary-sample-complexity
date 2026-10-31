import ProphetSecretary.Limiting.BernoulliStateError

/-!
# Actual continuation approximation for every finite Bernoulli child state

The subset S contains the genuinely unseen original and virtual identities.
Its exact relabeling is proved before invoking the Poisson value comparison.
The additional intensity-fraction error is explicit, and the common error
budget depends only on cap, mark intensity and reward weight, not |S| or c.
-/
open MeasureTheory Set Filter
open scoped Topology NNReal Classical
namespace ProphetSecretary.Limiting
variable {n : ℕ}

theorem FiniteIntensityHybridInstance.finiteDesign_value_error_at_horizon
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal = 0) (hμ : B.intensity ≠ 0)
    (j K : ℕ) (hK : K ≤ bernoulliMultiplicity ((B.intensity : Measure ℝ).real univ) j) (u : ℝ≥0)
    {w d : ℝ} (hw : 0 < w) (hd : 0 ≤ d) :
    let rate := (B.intensity : Measure ℝ).real univ
    let q := bernoulliMultiplicity rate j
    let p := bernoulliProbability rate measureReal_nonneg j
    let r : ℝ≥0 := (K : ℝ≥0)/(q : ℝ≥0)
    |Model.optimalScalarValue (finitePoissonDesign B.individuals (B.intensity.normalize : Measure ℝ)
      (B.normalizedMark_nonnegative hμ) p K) w d-(B.remainingHorizon u).optimalScalarValue w d| ≤
      B.bernoulliStateError w j+w * |(r : ℝ)-(u : ℝ)| * (∫ x, x ∂(B.intensity : Measure ℝ)) := by
  dsimp only
  let r : ℝ≥0 := (K : ℝ≥0)/(bernoulliMultiplicity ((B.intensity : Measure ℝ).real univ) j : ℝ≥0)
  have hFinite := B.finiteDesign_remaining_value_error ha hμ j K hK hw hd
  have hIntensity := B.intensityScale_value_abs_sub_le u r hw.le hd
  have hTriangle := abs_sub_le
    (Model.optimalScalarValue (finitePoissonDesign B.individuals (B.intensity.normalize : Measure ℝ)
      (B.normalizedMark_nonnegative hμ) (bernoulliProbability ((B.intensity : Measure ℝ).real univ) measureReal_nonneg j) K) w d)
    ((B.remainingHorizon r).optimalScalarValue w d) ((B.remainingHorizon u).optimalScalarValue w d)
  exact hTriangle.trans (add_le_add hFinite hIntensity)

/-- Full original-plus-virtual state S, with all zero identities retained. -/
theorem FiniteIntensityHybridInstance.bernoulliChild_value_error
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal = 0) (hμ : B.intensity ≠ 0)
    (j : ℕ) (S : Finset (Fin (n+bernoulliMultiplicity ((B.intensity : Measure ℝ).real univ) j))) (u : ℝ≥0)
    {w d : ℝ} (hw : 0 < w) (hd : 0 ≤ d) :
    let rate := (B.intensity : Measure ℝ).real univ
    let q := bernoulliMultiplicity rate j
    let p := bernoulliProbability rate measureReal_nonneg j
    let A := Model.retainedSet q S
    let K := (virtualSet n S).card
    let r : ℝ≥0 := (K : ℝ≥0)/(q : ℝ≥0)
    |Model.optimalScalarValue ((finitePoissonDesign B.individuals (B.intensity.normalize : Measure ℝ)
      (B.normalizedMark_nonnegative hμ) p q).restrictTo S) w d-
      ((B.restrictIndividuals A).remainingHorizon u).optimalScalarValue w d| ≤
      B.bernoulliStateError w j+w * |(r : ℝ)-(u : ℝ)| * (∫ x, x ∂(B.intensity : Measure ℝ)) := by
  dsimp only
  let rate := (B.intensity : Measure ℝ).real univ
  let q := bernoulliMultiplicity rate j
  let p := bernoulliProbability rate measureReal_nonneg j
  let κ : Measure ℝ := B.intensity.normalize
  let hκ := B.normalizedMark_nonnegative hμ
  let A := Model.retainedSet q S
  let K := (virtualSet n S).card
  have hK : K ≤ q := (Finset.card_filter_le _ _).trans_eq (by simp [q,rate])
  have hB := B.individuals.integrable_maximum_of_bounded B.individual_bounded
  have hI := B.normalizedMark_integrable hμ
  have hQ := finitePoissonDesign_integrable_maximum B.individuals κ hκ p q hB hI
  have hRelabel := appendIID_restrictTo_value B.individuals (zeroInflatedLaw κ p)
    (zeroInflatedLaw_nonnegative κ hκ p) q S hQ hw.le hd
  change Model.optimalScalarValue ((finitePoissonDesign B.individuals κ hκ p q).restrictTo S) w d =
    Model.optimalScalarValue (finitePoissonDesign (B.individuals.restrictTo A) κ hκ p K) w d at hRelabel
  rw [hRelabel]
  exact (B.restrictIndividuals A).finiteDesign_value_error_at_horizon ha hμ j K hK u hw hd

end ProphetSecretary.Limiting
