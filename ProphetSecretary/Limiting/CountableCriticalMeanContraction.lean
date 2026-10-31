import ProphetSecretary.Probability.ConstantLocationCdf
import ProphetSecretary.Limiting.CountableZeroValueSelection
import ProphetSecretary.Limiting.CountableMeanBenchmark
import ProphetSecretary.Limiting.CountableMeanCanonicalValue
import ProphetSecretary.Limiting.CountableIndividualLocation
import ProphetSecretary.Model.HalfGuarantee

/-!
# Criticality under an individual mean contraction

Zero individual duration scores make conditional selection constant. The
actual critical location identity then makes the competing strict CDF
marginally constant. A zero atom is handled using the canonical rejection of
zero and the nonnegative competing law. The proved maximum-kernel affinity
preserves the prophet benchmark, separately from the full scalar-value
preservation. Absence of positive individual/competing ties remains an
explicit prerequisite for the location identity used here.
-/
open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Limiting.CountableInstance
open ProphetSecretary.Model

theorem critical_individual_competingCdf_ae_constant_of_zero_duration_scores
    (B : CountableInstance) {w c : ℝ} (hw : 0 < w) (hc : 0 < c)
    (hCritical : B.IsCritical w c) (i : ℕ)
    (hNoTie : ∀ᵐ v : CompleteWorld Unit ∂B.completeWorldLaw (Measure.dirac ()),
      0<v.2.1 i → v.2.1 i≠B.competingMaximum i v)
    (hScores : ∀ φ : ℝ → ℝ, Measurable φ → (∀ x, |φ x| ≤ 1) →
      (∫ x, φ x ∂(B.individuals i : Measure ℝ))=0 →
      (∫ v : CompleteWorld Unit, φ (v.2.1 i)*(B.valueRule w c).realizedDuration v
        ∂B.completeWorldLaw (Measure.dirac ()))=0) :
    ∃ k : ℝ, (fun x => (B.competingMaximumLaw i : Measure ℝ).real (Iio x))=ᵐ[(B.individuals i : Measure ℝ)] fun _ => k := by
  have hTerminal := B.terminal_eq_zero_of_critical hw hc.le hCritical
  let p := (B.valueRule w c).individualSelectionProbability B (Measure.dirac ()) i
  have hSelection := B.canonical_conditionalSelectionAtValue_eq_on_support_hull hTerminal hw hc i hScores
  have hConst : B.individualLocationSelection w c i =ᵐ[(B.individuals i : Measure ℝ)] fun _ => p := by
    have hSupport : ∀ᵐ x ∂(B.individuals i : Measure ℝ), x ∈ (B.individuals i : Measure ℝ).support :=
      (B.individuals i : Measure ℝ).support_mem_ae
    filter_upwards [hSupport] with x hx
    exact hSelection x (subset_convexHull ℝ _ hx)
  have hZero : B.individualLocationSelection w c i 0=0 := B.valueRule_conditionalSelectionAtValue_zero w c i
  have hC : 0 < optimalCompetitiveRatio := lt_of_lt_of_le (by norm_num : (0 : ℝ)<1/2) half_le_optimalCompetitiveRatio
  have hLocation := B.critical_individual_location_of_no_positive_ties hw hc hCritical i hNoTie
  exact ProphetSecretary.Probability.strictCdf_ae_constant_of_constant_location
    (B.individuals i : Measure ℝ) (B.competingMaximumLaw i : Measure ℝ)
    ((B.individual_supported i).mono (fun _ hx => hx.1))
    ((B.competingMaximumLaw_supported i).mono (fun _ hx => hx.1))
    optimalCompetitiveRatio hC.ne' _ hZero p hConst hLocation

theorem critical_contractIndividual_expectedMaximum_eq_of_zero_duration_scores
    (B : CountableInstance) {w c : ℝ} (hw : 0 < w) (hc : 0 < c)
    (hCritical : B.IsCritical w c) (i : ℕ)
    (hNoTie : ∀ᵐ v : CompleteWorld Unit ∂B.completeWorldLaw (Measure.dirac ()),
      0<v.2.1 i → v.2.1 i≠B.competingMaximum i v)
    (hScores : ∀ φ : ℝ → ℝ, Measurable φ → (∀ x, |φ x| ≤ 1) →
      (∫ x, φ x ∂(B.individuals i : Measure ℝ))=0 →
      (∫ v : CompleteWorld Unit, φ (v.2.1 i)*(B.valueRule w c).realizedDuration v
        ∂B.completeWorldLaw (Measure.dirac ()))=0) :
    (B.contractIndividual i).expectedMaximum=B.expectedMaximum := by
  obtain ⟨k,hCdf⟩ := B.critical_individual_competingCdf_ae_constant_of_zero_duration_scores hw hc hCritical i hNoTie hScores
  exact B.contractIndividual_expectedMaximum_eq_of_constant_competing_Cdf i k hCdf

theorem critical_contractIndividual_isCritical_of_zero_duration_scores
    (B : CountableInstance) {w c : ℝ} (hw : 0 < w) (hc : 0 < c)
    (hCritical : B.IsCritical w c) (i : ℕ)
    (hNoTie : ∀ᵐ v : CompleteWorld Unit ∂B.completeWorldLaw (Measure.dirac ()),
      0<v.2.1 i → v.2.1 i≠B.competingMaximum i v)
    (hScores : ∀ φ : ℝ → ℝ, Measurable φ → (∀ x, |φ x| ≤ 1) →
      (∫ x, φ x ∂(B.individuals i : Measure ℝ))=0 →
      (∫ v : CompleteWorld Unit, φ (v.2.1 i)*(B.valueRule w c).realizedDuration v
        ∂B.completeWorldLaw (Measure.dirac ()))=0) :
    (B.contractIndividual i).IsCritical w c := by
  have hTerminal := B.terminal_eq_zero_of_critical hw hc.le hCritical
  have hM := B.critical_contractIndividual_expectedMaximum_eq_of_zero_duration_scores hw hc hCritical i hNoTie hScores
  have hV := B.contractIndividual_value_eq_of_zero_duration_scores hTerminal hw hc i hScores
  constructor
  · rw [hM]
    exact hCritical.1
  · change (B.contractIndividual i).optimalScalarValue w c-optimalCompetitiveRatio*
      (w*(B.contractIndividual i).expectedMaximum+c)=0
    rw [hV,hM]
    exact hCritical.2

end ProphetSecretary.Limiting.CountableInstance
