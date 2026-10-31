import ProphetSecretary.Limiting.CountableInstance

/-!
# Countable individual masks and remaining-horizon states

A zero-masked identity remains an observed individual identity. Equality with
physical deletion is a separate value comparison. Remaining time u scales the
anonymous intensity by u and leaves the terminal reward available at the end.
-/

open MeasureTheory Set
open scoped Classical NNReal ENNReal

namespace ProphetSecretary.Limiting

abbrev IndividualMask := ℕ → Bool

noncomputable def maskedProbabilityLaw (q : ProbabilityMeasure ℝ) (keep : Bool) : ProbabilityMeasure ℝ :=
  if keep = true then q else ⟨Measure.dirac 0,inferInstance⟩

noncomputable def CountableInstance.maskIndividuals (B : CountableInstance) (keep : IndividualMask) : CountableInstance where
  cap := B.cap
  terminal := B.terminal
  terminal_le_cap := B.terminal_le_cap
  individuals i := maskedProbabilityLaw (B.individuals i) (keep i)
  individual_supported i := by
    by_cases hk : keep i = true
    · simpa only [maskedProbabilityLaw,if_pos hk] using B.individual_supported i
    · rw [maskedProbabilityLaw,if_neg hk]
      exact (ae_dirac_iff measurableSet_Icc).mpr ⟨le_rfl,B.cap.property⟩
  intensity := B.intensity
  intensity_supported := B.intensity_supported
  individual_tail_finite b hb := by
    have hb0 : 0 ≤ b := B.terminal.property.trans hb.le
    apply lt_of_le_of_lt _ (B.individual_tail_finite b hb)
    apply ENNReal.tsum_le_tsum
    intro i
    by_cases hk : keep i = true
    · simp only [maskedProbabilityLaw,if_pos hk,le_refl]
    · have he : maskedProbabilityLaw (B.individuals i) (keep i) =
          (⟨Measure.dirac 0,inferInstance⟩ : ProbabilityMeasure ℝ) := if_neg hk
      calc
        _ = (Measure.dirac (0 : ℝ)) (Ioi b) :=
          congrArg (fun q : ProbabilityMeasure ℝ => (q : Measure ℝ) (Ioi b)) he
        _ = 0 := by simp [Measure.dirac_apply',not_lt.mpr hb0]
        _ ≤ _ := bot_le
  intensity_tail_finite := B.intensity_tail_finite

noncomputable def CountableInstance.remainingHorizon (B : CountableInstance) (u : ℝ≥0) : CountableInstance where
  cap := B.cap
  terminal := B.terminal
  terminal_le_cap := B.terminal_le_cap
  individuals := B.individuals
  individual_supported := B.individual_supported
  intensity := u • B.intensity
  intensity_supported := Measure.ae_smul_measure B.intensity_supported u
  individual_tail_finite := B.individual_tail_finite
  intensity_tail_finite b hb := by
    change (u : ℝ≥0∞)*B.intensity (Ioi b) < ⊤
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top (B.intensity_tail_finite b hb)

noncomputable def CountableInstance.remainingState (B : CountableInstance) (keep : IndividualMask) (u : ℝ≥0) : CountableInstance :=
  (B.maskIndividuals keep).remainingHorizon u

lemma CountableInstance.ext_data (B D : CountableInstance) (hCap : B.cap = D.cap)
    (hTerm : B.terminal = D.terminal) (hP : B.individuals = D.individuals) (hμ : B.intensity = D.intensity) : B = D := by
  cases B
  cases D
  cases hCap
  cases hTerm
  cases hP
  cases hμ
  rfl

lemma CountableInstance.maskIndividuals_all (B : CountableInstance) : B.maskIndividuals (fun _ => true) = B := by
  apply CountableInstance.ext_data <;> rfl

lemma CountableInstance.remainingHorizon_one (B : CountableInstance) : B.remainingHorizon 1 = B := by
  apply CountableInstance.ext_data
  · rfl
  · rfl
  · rfl
  · exact one_smul _ _

end ProphetSecretary.Limiting
