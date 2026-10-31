import ProphetSecretary.Limiting.CountableMeanCanonicalValue
import ProphetSecretary.Limiting.CountableCanonicalLimit

/-!
# Canonical duration and untouched scores after mean contraction

The fixed original canonical rule remains optimal under mean contraction.
Actual optimal-outcome uniqueness identifies it with the new canonical rule.
Together with the original pathwise constancy, this identifies the two
canonical durations under the proved mean-substitution coupling. Integrable
scores unchanged by that substitution retain their duration covariances.
-/
open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Limiting.CountableInstance

lemma eraseCompleteSeed_unit (v : CompleteWorld Unit) : eraseCompleteSeed v=v := by
  exact Prod.ext rfl (Prod.ext rfl (Prod.ext rfl (Subsingleton.elim _ _)))

theorem canonical_duration_contractIndividual_coupling
    (B : CountableInstance) (hZero : B.terminal=0) {w c : ℝ}
    (hw : 0 < w) (hc : 0 < c) (i : ℕ)
    (hScores : ∀ φ : ℝ → ℝ, Measurable φ → (∀ x, |φ x| ≤ 1) →
      (∫ x, φ x ∂(B.individuals i : Measure ℝ))=0 →
      (∫ v : CompleteWorld Unit, φ (v.2.1 i)*(B.valueRule w c).realizedDuration v
        ∂B.completeWorldLaw (Measure.dirac ()))=0) :
    ∀ᵐ v ∂B.completeWorldLaw (Measure.dirac ()),
      ((B.contractIndividual i).valueRule w c).realizedDuration
          (replaceIndividualValue i (v,B.individualMean i))=
        (B.valueRule w c).realizedDuration v := by
  let Q := B.contractIndividual i
  have hQZero : Q.terminal=0 := (B.contractIndividual_terminal i).trans hZero
  have hOptimal : (B.fixedCanonicalMeanPolicy hw hc i).scalarObjective w c=Q.optimalScalarValue w c := by
    rw [B.fixedCanonicalMeanPolicy_scalarObjective hZero hw hc i hScores,
      B.valuePolicy_optimal hZero hw hc]
    exact (B.contractIndividual_value_eq_of_zero_duration_scores hZero hw hc i hScores).symm
  have hUnique := (B.fixedCanonicalMeanPolicy hw hc i).outcomes_eq_canonical_ae_of_optimal hQZero hw hc hOptimal
  have hDuration : ∀ᵐ z ∂Q.completeWorldLaw (Measure.dirac ()),
      (B.valueRule w c).realizedDuration z=(Q.valueRule w c).realizedDuration z := by
    have hDurationUnique := hUnique.mono (fun z hz => hz.2)
    change ∀ᵐ z : CompleteWorld Unit ∂Q.completeWorldLaw (Measure.dirac ()),
      (B.valueRule w c).realizedDuration z=(Q.valueRule w c).realizedDuration (eraseCompleteSeed z) at hDurationUnique
    filter_upwards [hDurationUnique] with z hz
    rw [eraseCompleteSeed_unit] at hz
    exact hz
  have hMP := B.meanSubstitution_measurePreserving i (Measure.dirac ())
  filter_upwards [hMP.quasiMeasurePreserving.ae hDuration,
    B.canonical_durationAtValue_mean_ae_eq hZero hw hc i hScores] with v hQ hMean
  exact hQ.symm.trans hMean

theorem canonical_durationScore_contractIndividual
    (B : CountableInstance) (hZero : B.terminal=0) {w c : ℝ}
    (hw : 0 < w) (hc : 0 < c) (i : ℕ)
    (hScores : ∀ φ : ℝ → ℝ, Measurable φ → (∀ x, |φ x| ≤ 1) →
      (∫ x, φ x ∂(B.individuals i : Measure ℝ))=0 →
      (∫ v : CompleteWorld Unit, φ (v.2.1 i)*(B.valueRule w c).realizedDuration v
        ∂B.completeWorldLaw (Measure.dirac ()))=0)
    (Z : CompleteWorld Unit → ℝ) (hZ : Measurable Z)
    (hInt : Integrable Z (B.completeWorldLaw (Measure.dirac ())))
    (hInvariant : ∀ᵐ v ∂B.completeWorldLaw (Measure.dirac ()),
      Z (replaceIndividualValue i (v,B.individualMean i))=Z v) :
    Integrable (fun v => Z v*((B.contractIndividual i).valueRule w c).realizedDuration v)
        ((B.contractIndividual i).completeWorldLaw (Measure.dirac ())) ∧
      (∫ v, Z v*((B.contractIndividual i).valueRule w c).realizedDuration v
        ∂(B.contractIndividual i).completeWorldLaw (Measure.dirac ()))=
      ∫ v, Z v*(B.valueRule w c).realizedDuration v ∂B.completeWorldLaw (Measure.dirac ()) := by
  let Q := B.contractIndividual i
  have hMP := B.meanSubstitution_measurePreserving i (Measure.dirac ())
  have hQInt : Integrable Z (Q.completeWorldLaw (Measure.dirac ())) := by
    rw [← hMP.map_eq]
    apply (integrable_map_measure hZ.aestronglyMeasurable hMP.measurable.aemeasurable).mpr
    apply hInt.congr
    filter_upwards [hInvariant] with v hv
    exact hv.symm
  have hTauM := (Q.valueRule w c).measurable_realizedDuration (Q.valueRule_isMeasurable hw.le hc.le)
  refine ⟨hQInt.mul_bdd (c := 1) hTauM.aestronglyMeasurable (Eventually.of_forall (fun v => ?_)),?_⟩
  · rw [Real.norm_eq_abs,abs_of_nonneg ((Q.valueRule w c).duration_bounds v).1]
    exact ((Q.valueRule w c).duration_bounds v).2
  · have hMap := hMP.hasLaw.integral_comp (hZ.mul hTauM).aestronglyMeasurable
    refine hMap.symm.trans (integral_congr_ae ?_)
    filter_upwards [hInvariant,B.canonical_duration_contractIndividual_coupling hZero hw hc i hScores]
      with v hI hT
    change Z (replaceIndividualValue i (v,B.individualMean i))*
      (Q.valueRule w c).realizedDuration (replaceIndividualValue i (v,B.individualMean i))=_
    rw [hI,hT]

end ProphetSecretary.Limiting.CountableInstance
