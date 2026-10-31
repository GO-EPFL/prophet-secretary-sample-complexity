import ProphetSecretary.Limiting.CountableNonzeroAlternative
import ProphetSecretary.Limiting.CountableDurationLinearScore

/-!
# A concrete nonzero duration score at criticality

Failure of the explicit all-zero alternative supplies an actual individual
or positive-window score. Conditional duration monotonicity replaces every
individual witness by the globally bounded continuous centered value score,
equal to `(x-E[X_i])/H` on the offer support. Positive-window scores are
nonpositive by the proved insertion comparison, so both alternatives may be
chosen with strictly negative duration response.
-/
open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Limiting.CountableInstance

lemma cap_pos_of_critical (B : CountableInstance) {w c : ℝ} (hCritical : B.IsCritical w c) :
    0<(B.cap : ℝ) := by
  have hBound : B.expectedMaximum≤(B.cap : ℝ) := by
    unfold expectedMaximum
    calc
      _ ≤ ∫ _ : ValueWorld, (B.cap : ℝ) ∂B.valueLaw :=
        integral_mono_ae B.integrable_maximum (integrable_const (B.cap : ℝ))
          (B.maximum_bounded.mono (fun _ hx => hx.2))
      _ = (B.cap : ℝ) := by rw [integral_const,probReal_univ,one_smul]
  exact hCritical.1.trans_le hBound

theorem exists_negative_duration_score_at_critical (B : CountableInstance) {w c : ℝ}
    (hw : 0<w) (hc : 0<c) (hCritical : B.IsCritical w c) :
    (∃ i : ℕ, (∫ v : CompleteWorld Unit,
      ProphetSecretary.Probability.centeredValueScore (B.individuals i : Measure ℝ) B.cap (v.2.1 i)*
        (B.valueRule w c).realizedDuration v ∂B.completeWorldLaw (Measure.dirac ()))<0) ∨
    (∃ S : Set ℝ, MeasurableSet S ∧ ∃ b : ℝ, (B.terminal : ℝ)<b ∧ S ⊆ Ioi b ∧
      (∫ v : CompleteWorld Unit, (B.valueRule w c).realizedDuration v*B.bandScore S v
        ∂B.completeWorldLaw (Measure.dirac ()))<0) := by
  have hNot := B.not_all_duration_scores_zero_at_critical hw hc hCritical
  by_cases hIndividual : B.AllIndividualDurationScoresZero w c
  · have hBand : ¬B.AllPositiveBandDurationScoresZero w c := fun h => hNot ⟨hIndividual,h⟩
    unfold AllPositiveBandDurationScoresZero at hBand
    push Not at hBand
    obtain ⟨S,hS,b,hb,hSub,hResponse⟩ := hBand
    exact Or.inr ⟨S,hS,b,hb,hSub,lt_of_le_of_ne
      (B.valueRule_positiveWindow_durationScore_nonpositive hw hc hS hb hSub).2 hResponse⟩
  · unfold AllIndividualDurationScoresZero at hIndividual
    push Not at hIndividual
    obtain ⟨i,φ,hφ,hBound,hMean,hResponse⟩ := hIndividual
    exact Or.inl ⟨i,B.canonical_centeredValue_durationScore_negative_of_nonzero_response
      hw hc (B.cap_pos_of_critical hCritical) i φ hφ hBound hMean hResponse⟩

end ProphetSecretary.Limiting.CountableInstance
