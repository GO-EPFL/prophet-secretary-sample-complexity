import ProphetSecretary.Limiting.CountableFirstBandDeletionPath
import ProphetSecretary.Limiting.CountableNoWindowSelection
import ProphetSecretary.Limiting.CountableIntensityOrder
import ProphetSecretary.Limiting.CountableFixedValuePolicy
import ProphetSecretary.Limiting.CountableCanonicalOptimizer

/-!
# Scalar value is preserved by a zero-response finite-band deletion

No deleted anonymous occurrence is selected. The original Markov optimizer
therefore keeps its actual reward and duration under the proved deletion
coupling. Its positive acceptance floor makes it admissible under the new
instance. The reverse value inequality is the actual full-policy intensity
comparison, obtained from finite-hybrid comparisons and truncation limits.
-/
open MeasureTheory Set Filter
open scoped Classical ENNReal
namespace ProphetSecretary.Limiting.CountableInstance

theorem valueRule_outcomes_eraseFirstBandsWorld_ae (B : CountableInstance) {w c : ℝ}
    (hw : 0 < w) (hc : 0 < c) (N : ℕ)
    (hZero : (∫ v : CompleteWorld Unit, (B.valueRule w c).realizedDuration v*B.bandScore (B.firstBandWindow N) v
      ∂B.completeWorldLaw (Measure.dirac ()))=0) :
    ∀ᵐ v : CompleteWorld Unit ∂B.completeWorldLaw (Measure.dirac ()),
      (B.valueRule w c).realizedReward B.terminal (eraseFirstBandsWorld N v)=
          (B.valueRule w c).realizedReward B.terminal v ∧
        (B.valueRule w c).realizedDuration (eraseFirstBandsWorld N v)=
          (B.valueRule w c).realizedDuration v := by
  have hSub : B.firstBandWindow N ⊆ Ioi (B.markCutoff N) := by rw [B.firstBandWindow_eq_tail]
  have hNo (k : ℕ) := B.valueRule_no_selected_poisson_window hw hc (B.measurableSet_firstBandWindow N)
    (B.terminal_lt_markCutoff N) hSub hZero k
  have hAllNo := ae_all_iff.mpr hNo
  have hMarks := (Measure.quasiMeasurePreserving_fst (μ := B.bandConfigurationsLaw)
    (ν := B.individualWorldLaw (Measure.dirac ()))).ae B.bandConfigurations_marks_in_band
  filter_upwards [hAllNo,hMarks,B.valueRule_admissible hw hc] with v hNoV hMarksV hAdm
  have hSurvive (i : ℕ) (hi : FirstAcceptance.Earliest (B.valueRule w c).codeAccepted codeTime v i) :
      SurvivesFirstBandDeletion N (candidateEnumeration.symm i) := by
    cases hCandidate : candidateEnumeration.symm i with
    | inl j => trivial
    | inr kj =>
      obtain ⟨k,j⟩ := kj
      change N<k
      by_contra hk
      have hkN : k≤N := le_of_not_gt hk
      have hPresent := hi.1.1
      change candidatePresent v (candidateEnumeration.symm i) at hPresent
      rw [hCandidate] at hPresent
      change j<(v.1 k).1 at hPresent
      have hMark := B.markBand_subset_firstBandWindow hkN (hMarksV k ⟨j,hPresent⟩)
      have hNot := hNoV k ⟨j,hPresent⟩ hMark
      have hCode : candidateEnumeration (Sum.inr (k,j))=i := by
        rw [← hCandidate,Equiv.apply_symm_apply]
      exact hNot (by rwa [hCode])
  have hPath := countableMarkovRule_outcomes_eraseFirstBandsWorld (B.valueMarkovAcceptance w c) N (B.terminal : ℝ) v
  rw [← B.valueRule_eq_markovAcceptance] at hPath
  exact hPath hAdm hSurvive

noncomputable def fixedCanonicalBandDeletionPolicy (B : CountableInstance) {w c : ℝ}
    (hw : 0 < w) (hc : 0 < c) (N : ℕ) : RandomizedCountablePolicy (B.deleteFirstBands N) :=
  B.fixedValuePolicy (B.deleteFirstBands N) (le_refl _) hw hc

theorem fixedCanonicalBandDeletionPolicy_expected_outcomes (B : CountableInstance) {w c : ℝ}
    (hw : 0 < w) (hc : 0 < c) (N : ℕ)
    (hZero : (∫ v : CompleteWorld Unit, (B.valueRule w c).realizedDuration v*B.bandScore (B.firstBandWindow N) v
      ∂B.completeWorldLaw (Measure.dirac ()))=0) :
    (B.fixedCanonicalBandDeletionPolicy hw hc N).expectedReward=(B.valuePolicy hw hc).expectedReward ∧
      (B.fixedCanonicalBandDeletionPolicy hw hc N).expectedDuration=(B.valuePolicy hw hc).expectedDuration := by
  have hMP := B.eraseFirstBandsWorld_measurePreserving N (Measure.dirac ())
  have hPath := B.valueRule_outcomes_eraseFirstBandsWorld_ae hw hc N hZero
  constructor
  · have hMap := hMP.hasLaw.integral_comp ((B.valueRule w c).measurable_realizedReward
      (B.valueRule_isMeasurable hw.le hc.le) B.terminal).aestronglyMeasurable
    exact hMap.symm.trans (integral_congr_ae (hPath.mono (fun _ h => h.1)))
  · have hMap := hMP.hasLaw.integral_comp ((B.valueRule w c).measurable_realizedDuration
      (B.valueRule_isMeasurable hw.le hc.le)).aestronglyMeasurable
    exact hMap.symm.trans (integral_congr_ae (hPath.mono (fun _ h => h.2)))

lemma deleteFirstBands_intensity_le (B : CountableInstance) (N : ℕ) :
    (B.deleteFirstBands N).intensity≤B.intensity := by
  have hDensity : (fun x => ENNReal.ofReal (bandScaleFactor (B.firstBandWindow N) 0 x)) ≤ᵐ[B.intensity]
      (fun _ => (1 : ℝ≥0∞)) := by
    apply Eventually.of_forall
    intro x
    by_cases hx : x ∈ B.firstBandWindow N <;> simp [bandScaleFactor,hx]
  calc
    _ ≤ B.intensity.withDensity 1 := withDensity_mono hDensity
    _ = _ := withDensity_one

theorem deleteFirstBands_value_eq_of_zero_durationScore (B : CountableInstance)
    (hTerminal : B.terminal=0) {w c : ℝ} (hw : 0 < w) (hc : 0 < c) (N : ℕ)
    (hZero : (∫ v : CompleteWorld Unit, (B.valueRule w c).realizedDuration v*B.bandScore (B.firstBandWindow N) v
      ∂B.completeWorldLaw (Measure.dirac ()))=0) :
    (B.deleteFirstBands N).optimalScalarValue w c=B.optimalScalarValue w c := by
  apply le_antisymm
  · exact (B.deleteFirstBands N).optimalScalarValue_mono_intensity B rfl rfl rfl (B.deleteFirstBands_intensity_le N) hw.le hc.le
  · have hOutcomes := B.fixedCanonicalBandDeletionPolicy_expected_outcomes hw hc N hZero
    have hScalar : (B.fixedCanonicalBandDeletionPolicy hw hc N).scalarObjective w c=
        (B.valuePolicy hw hc).scalarObjective w c := by
      rw [RandomizedCountablePolicy.scalarObjective,RandomizedCountablePolicy.scalarObjective,hOutcomes.1,hOutcomes.2]
    rw [← B.valuePolicy_optimal hTerminal hw hc,← hScalar]
    exact (B.deleteFirstBands N).scalarObjective_le_value (B.fixedCanonicalBandDeletionPolicy hw hc N) w c

end ProphetSecretary.Limiting.CountableInstance
