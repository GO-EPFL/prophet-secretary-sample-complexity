import ProphetSecretary.Limiting.CountableConditionalDuration
import ProphetSecretary.Limiting.CountableDurationValueMonotonicity
import ProphetSecretary.Probability.CenteredValueCovariance

/-!
# Zero individual duration scores force a constant conditional mean

Actual candidate replacement and Fubini identify the score response with the
conditional-duration kernel. Canonical value monotonicity makes that kernel
antitone. If it were not almost surely constant, the previously proved strict
covariance theorem supplies a bounded continuous centered value score with
negative response. The zero-cap case is handled directly by its supported law.
This is the conditional-mean step of `lem:nonzero`.
-/
open MeasureTheory Set Filter
open scoped Classical NNReal
namespace ProphetSecretary.Limiting.CountableInstance
variable {Seed : Type*} [MeasurableSpace Seed]

theorem countableMarkovRule_conditionalDurationAtValue_antitone
    (accept : Seed → IndividualMask → ℝ → Option ℕ → ℝ → Bool) (hUp : UpwardCountableAcceptance accept)
    (hπ : (countableMarkovRule accept).IsMeasurable) (B : CountableInstance)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (i : ℕ) :
    Antitone ((countableMarkovRule accept).conditionalDurationAtValue B ν i) := by
  intro a b hab
  apply integral_mono ((countableMarkovRule accept).integrable_durationAtValue_fixed hπ B ν i b)
    ((countableMarkovRule accept).integrable_durationAtValue_fixed hπ B ν i a)
  intro v
  exact countableMarkovRule_duration_antitone_candidateValue accept hUp i v hab

theorem canonical_conditionalDurationAtValue_antitone (B : CountableInstance) {w c : ℝ}
    (hw : 0 ≤ w) (hc : 0 ≤ c) (i : ℕ) :
    Antitone ((B.valueRule w c).conditionalDurationAtValue B (Measure.dirac ()) i) := by
  intro a b hab
  apply integral_mono ((B.valueRule w c).integrable_durationAtValue_fixed (B.valueRule_isMeasurable hw hc) B (Measure.dirac ()) i b)
    ((B.valueRule w c).integrable_durationAtValue_fixed (B.valueRule_isMeasurable hw hc) B (Measure.dirac ()) i a)
  intro v
  exact B.canonical_duration_antitone_candidateValue hw i v hab

theorem canonical_centeredValue_durationScore_negative (B : CountableInstance)
    {w c : ℝ} (hw : 0 < w) (hc : 0 < c) (hH : 0 < (B.cap : ℝ)) (i : ℕ)
    (hn : ¬∃ d : ℝ, (B.valueRule w c).conditionalDurationAtValue B (Measure.dirac ()) i =ᵐ[(B.individuals i : Measure ℝ)] fun _ => d) :
    (∫ v : CompleteWorld Unit, ProphetSecretary.Probability.centeredValueScore (B.individuals i : Measure ℝ) B.cap (v.2.1 i)*
      (B.valueRule w c).realizedDuration v ∂B.completeWorldLaw (Measure.dirac ())) < 0 := by
  let π := B.valueRule w c
  let g := π.conditionalDurationAtValue B (Measure.dirac ()) i
  have hπ : π.IsMeasurable := B.valueRule_isMeasurable hw.le hc.le
  have hgm : Measurable g := π.measurable_conditionalDurationAtValue hπ B (Measure.dirac ()) i
  have hBound : ∀ᵐ x ∂(B.individuals i : Measure ℝ), g x ∈ Icc (0 : ℝ) 1 :=
    Eventually.of_forall (π.conditionalDurationAtValue_mem_unit hπ B (Measure.dirac ()) i)
  have hNeg := ProphetSecretary.Probability.centeredValueScore_response_negative (B.individuals i : Measure ℝ)
    hH (B.individual_supported i) g hgm hBound (B.canonical_conditionalDurationAtValue_antitone hw.le hc.le i) hn
  rw [π.integral_duration_value_weight hπ B (Measure.dirac ()) i _
    (ProphetSecretary.Probability.continuous_centeredValueScore (B.individuals i : Measure ℝ) B.cap).measurable
    (ProphetSecretary.Probability.centeredValueScore_abs_le_one (B.individuals i : Measure ℝ) hH)]
  exact hNeg

theorem canonical_conditionalDurationAtValue_ae_constant_of_zero_scores (B : CountableInstance)
    {w c : ℝ} (hw : 0 < w) (hc : 0 < c) (i : ℕ)
    (hZero : ∀ φ : ℝ → ℝ, Measurable φ → (∀ x, |φ x| ≤ 1) →
      (∫ x, φ x ∂(B.individuals i : Measure ℝ))=0 →
      (∫ v : CompleteWorld Unit, φ (v.2.1 i)*(B.valueRule w c).realizedDuration v ∂B.completeWorldLaw (Measure.dirac ()))=0) :
    ∃ d : ℝ, (B.valueRule w c).conditionalDurationAtValue B (Measure.dirac ()) i =ᵐ[(B.individuals i : Measure ℝ)] fun _ => d := by
  by_cases hCap : B.cap=0
  · refine ⟨(B.valueRule w c).conditionalDurationAtValue B (Measure.dirac ()) i 0,?_⟩
    filter_upwards [B.individual_supported i] with x hx
    have hx0 : x=0 := le_antisymm (by simpa only [hCap,NNReal.coe_zero] using hx.2) hx.1
    rw [hx0]
  · have hH : 0 < (B.cap : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hCap : 0 < B.cap)
    by_contra hn
    have hNeg := B.canonical_centeredValue_durationScore_negative hw hc hH i hn
    exact (ne_of_lt hNeg) (hZero _
      (ProphetSecretary.Probability.continuous_centeredValueScore (B.individuals i : Measure ℝ) B.cap).measurable
      (ProphetSecretary.Probability.centeredValueScore_abs_le_one (B.individuals i : Measure ℝ) hH)
      (ProphetSecretary.Probability.centeredValueScore_mean (B.individuals i : Measure ℝ) B.cap))

end ProphetSecretary.Limiting.CountableInstance
