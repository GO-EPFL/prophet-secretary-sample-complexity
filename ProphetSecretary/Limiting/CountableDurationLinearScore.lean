import ProphetSecretary.Limiting.CountableConditionalDurationScore

/-!
# A centered linear value score detects every individual duration response

For the fixed canonical policy, conditional duration is antitone. Any
nonzero bounded centered individual score excludes a constant conditional
duration. Strict covariance then makes the continuous clipped linear score
have strictly negative duration response. On the supported offer interval,
this score is exactly `(x - E[X_i])/H`, as used in the score-lifting argument.
-/
open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Limiting.CountableInstance

theorem canonical_centeredValue_durationScore_negative_of_nonzero_response
    (B : CountableInstance) {w c : ℝ} (hw : 0 < w) (hc : 0 < c)
    (hH : 0 < (B.cap : ℝ)) (i : ℕ) (φ : ℝ → ℝ)
    (hφ : Measurable φ) (hb : ∀ x, |φ x| ≤ 1)
    (hMean : (∫ x, φ x ∂(B.individuals i : Measure ℝ))=0)
    (hResponse : (∫ v : CompleteWorld Unit, φ (v.2.1 i)*(B.valueRule w c).realizedDuration v
      ∂B.completeWorldLaw (Measure.dirac ()))≠0) :
    (∫ v : CompleteWorld Unit, ProphetSecretary.Probability.centeredValueScore
      (B.individuals i : Measure ℝ) B.cap (v.2.1 i)*(B.valueRule w c).realizedDuration v
      ∂B.completeWorldLaw (Measure.dirac ())) < 0 := by
  apply B.canonical_centeredValue_durationScore_negative hw hc hH i
  rintro ⟨d,hd⟩
  apply hResponse
  rw [(B.valueRule w c).integral_duration_value_weight (B.valueRule_isMeasurable hw.le hc.le)
    B (Measure.dirac ()) i φ hφ hb]
  calc
    _ = ∫ x, φ x*d ∂(B.individuals i : Measure ℝ) := by
      apply integral_congr_ae
      filter_upwards [hd] with x hx
      rw [hx]
    _ = 0 := by rw [integral_mul_const,hMean,zero_mul]

end ProphetSecretary.Limiting.CountableInstance
