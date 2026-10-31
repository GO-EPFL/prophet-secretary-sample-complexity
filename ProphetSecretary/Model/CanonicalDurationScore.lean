import ProphetSecretary.Probability.ConditionalDurationValue
import ProphetSecretary.Probability.CenteredValueCovariance
import ProphetSecretary.Probability.NormalizedScoreResponse
import ProphetSecretary.Probability.SingleMarginalTilt

/-!
# A negative individual-value duration score for the canonical policy

Conditional duration is constructed from the actual online execution by
independent candidate replacement. Canonical Markov thresholds make this
response antitone; a nonconstant response therefore has strictly negative
covariance with the bounded continuous centered individual-value score.
-/
open MeasureTheory Set Filter
open scoped NNReal
namespace ProphetSecretary.Model
open ProphetSecretary.Probability
variable {n : ℕ}

/-- Actual single-coordinate product score and conditional-duration identity. -/
theorem RandomizedPolicy.expectedDurationScore_single (π : RandomizedPolicy n) (P : Instance n)
    (i : Fin n) (φ : ℝ → ℝ) (hφ : Measurable φ) (hb : ∀ a, |φ a| ≤ 1) :
    π.expectedDurationScore P (singleScore i φ) =
      ∫ a, φ a * π.rule.conditionalDurationAtValue P π.seedLaw i a ∂P.law i := by
  unfold expectedDurationScore
  simp_rw [singleScore_complete]
  exact π.rule.integral_duration_value_weight π.measurable_rule P π.seedLaw i φ hφ hb

/-- The finite individual-variable direction when the actual canonical
conditional-duration response is not almost surely constant. -/
theorem Instance.canonical_centeredValue_durationScore_negative (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {H : ℝ≥0} (hH : 0 < (H : ℝ))
    (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ (H : ℝ)) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) (i : Fin n)
    (hn : ¬∃ d : ℝ, (P.valuePolicy hP hw.le hc).rule.conditionalDurationAtValue P
      (P.valuePolicy hP hw.le hc).seedLaw i =ᵐ[P.law i] fun _ => d) :
    (P.valuePolicy hP hw.le hc).expectedDurationScore P (singleScore i (centeredValueScore (P.law i) H)) < 0 := by
  let π := P.valuePolicy hP hw.le hc
  let g := π.rule.conditionalDurationAtValue P π.seedLaw i
  have hX : ∀ᵐ a ∂P.law i, a ∈ Icc (0 : ℝ) H := by
    filter_upwards [P.nonnegative i,hbound i] with a ha0 haH
    exact ⟨ha0,haH⟩
  have hgm : Measurable g := π.rule.measurable_conditionalDurationAtValue π.measurable_rule P π.seedLaw i
  have hgB : ∀ᵐ a ∂P.law i, g a ∈ Icc (0 : ℝ) 1 :=
    Eventually.of_forall fun a => π.rule.conditionalDurationAtValue_mem_unit π.measurable_rule P π.seedLaw i a
  have hga : Antitone g :=
    P.canonical_conditionalDurationAtValue_antitone hP hw.le hc P i
  have hneg := centeredValueScore_response_negative (P.law i) hH hX g hgm hgB hga hn
  rw [RandomizedPolicy.expectedDurationScore_single _ P i _
    (continuous_centeredValueScore (P.law i) H).measurable (centeredValueScore_abs_le_one (P.law i) hH)]
  exact hneg

end ProphetSecretary.Model
