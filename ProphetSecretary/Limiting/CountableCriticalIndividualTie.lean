import ProphetSecretary.Limiting.CountableSymmetricLevelMaximum
import ProphetSecretary.Limiting.CountableCriticalMeanContraction
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Critical instances have no positive individual/competing ties

The actual fair-sign perturbation increases the prophet expectation by at
least h/2 times the probability of a tie above the fixed positive level.
Its scalar value change is o(h). The nonnegative scalar gap at the perturbed
valid countable instances forces that tie probability to vanish. A countable
positive-level exhaustion gives the individual no-tie premise, and hence the
individual location and mean-contraction statements used in `lem:nonzero`.
This does not assert exclusion of ties involving only Poisson occurrences.
-/
open MeasureTheory Set Filter
open scoped Classical Topology
namespace ProphetSecretary.Limiting.CountableInstance
open ProphetSecretary.Model

theorem critical_individualCompetingTieAbove_probability_zero (B : CountableInstance)
    {w c : ℝ} (hw : 0<w) (hc : 0<c) (hCritical : B.IsCritical w c)
    (i : ℕ) (b : ℝ) (hb : 0<b) :
    (B.completeWorldLaw (Measure.dirac ())).real (B.individualCompetingTieAbove i b)=0 := by
  let p := (B.completeWorldLaw (Measure.dirac ())).real (B.individualCompetingTieAbove i b)
  let family := B.symmetricLevelIndividualPath i b hb
  have hTerminal := B.terminal_eq_zero_of_critical hw hc.le hCritical
  have hLittleO := B.symmetricLevelIndividualPath_scalar_change_isLittleO hTerminal hw hc i b hb
  have hLimit : Tendsto (fun h : ℝ => ((family h).optimalScalarValue w c-B.optimalScalarValue w c)/h)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    hLittleO.tendsto_div_nhds_zero.mono_left nhdsWithin_le_nhds
  have hRadius := individualValueRadius_pos (by norm_num : (0 : ℝ)≤1) hb
  have hC : 0<optimalCompetitiveRatio := lt_of_lt_of_le (by norm_num : (0 : ℝ)<1/2) half_le_optimalCompetitiveRatio
  have hCw : 0<optimalCompetitiveRatio*w := mul_pos hC hw
  have hBase : B.optimalScalarValue w c=optimalCompetitiveRatio*(w*B.expectedMaximum+c) :=
    sub_eq_zero.mp hCritical.2
  have hLower : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ),
      optimalCompetitiveRatio*w*(p/2) ≤ ((family h).optimalScalarValue w c-B.optimalScalarValue w c)/h := by
    filter_upwards [(self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ)),
      nhdsWithin_le_nhds (Iio_mem_nhds hRadius)] with h hh hSmall
    have hGain := B.symmetricLevelIndividualPath_maximum_gain i b hb h hh.le hSmall.le
    have hRobust := (family h).globalScalar_inequality hw.le hc.le
    have hValue : optimalCompetitiveRatio*w*((family h).expectedMaximum-B.expectedMaximum) ≤
        (family h).optimalScalarValue w c-B.optimalScalarValue w c := by
      nlinarith only [hRobust,hBase]
    have hMax : p*(h/2) ≤ (family h).expectedMaximum-B.expectedMaximum := by
      linarith only [hGain]
    have hScaled := (mul_le_mul_of_nonneg_left hMax hCw.le).trans hValue
    apply (le_div_iff₀ hh).mpr
    convert hScaled using 1
    ring
  have hBound : optimalCompetitiveRatio*w*(p/2)≤0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hLimit hLower
  apply le_antisymm
  · by_contra hp
    exact (not_lt_of_ge hBound) (mul_pos hCw (half_pos (lt_of_not_ge hp)))
  · exact measureReal_nonneg

theorem critical_individual_no_competing_ties (B : CountableInstance)
    {w c : ℝ} (hw : 0<w) (hc : 0<c) (hCritical : B.IsCritical w c) (i : ℕ) :
    ∀ᵐ v : CompleteWorld Unit ∂B.completeWorldLaw (Measure.dirac ()),
      0<v.2.1 i → v.2.1 i≠B.competingMaximum i v := by
  have hNull (k : ℕ) : (B.completeWorldLaw (Measure.dirac ()))
      (B.individualCompetingTieAbove i (1/(k+1 : ℝ)))=0 := by
    have h := B.critical_individualCompetingTieAbove_probability_zero hw hc hCritical i (1/(k+1 : ℝ)) (by positivity)
    exact ((ENNReal.toReal_eq_zero_iff _).mp h).resolve_right (measure_ne_top _ _)
  have hAll := ae_all_iff.mpr (fun k => measure_eq_zero_iff_ae_notMem.mp (hNull k))
  filter_upwards [hAll] with v hv hx hTie
  obtain ⟨k,hk⟩ := exists_nat_one_div_lt hx
  exact hv k ⟨hTie,hk.le⟩

theorem critical_individual_location (B : CountableInstance) {w c : ℝ}
    (hw : 0<w) (hc : 0<c) (hCritical : B.IsCritical w c) (i : ℕ) :
    ∀ᵐ x ∂(B.individuals i : Measure ℝ), 0<x →
      B.individualLocationSelection w c i x=optimalCompetitiveRatio*B.individualLocationProphet i x :=
  B.critical_individual_location_of_no_positive_ties hw hc hCritical i (B.critical_individual_no_competing_ties hw hc hCritical i)

theorem critical_mean_contraction (B : CountableInstance) {w c : ℝ}
    (hw : 0<w) (hc : 0<c) (hCritical : B.IsCritical w c) (i : ℕ)
    (hScores : ∀ φ : ℝ → ℝ, Measurable φ → (∀ x, |φ x|≤1) →
      (∫ x, φ x ∂(B.individuals i : Measure ℝ))=0 →
      (∫ v : CompleteWorld Unit, φ (v.2.1 i)*(B.valueRule w c).realizedDuration v
        ∂B.completeWorldLaw (Measure.dirac ()))=0) :
    (B.contractIndividual i).IsCritical w c ∧
      (B.contractIndividual i).expectedMaximum=B.expectedMaximum ∧
      (B.contractIndividual i).optimalScalarValue w c=B.optimalScalarValue w c := by
  have hNoTie := B.critical_individual_no_competing_ties hw hc hCritical i
  exact ⟨B.critical_contractIndividual_isCritical_of_zero_duration_scores hw hc hCritical i hNoTie hScores,
    B.critical_contractIndividual_expectedMaximum_eq_of_zero_duration_scores hw hc hCritical i hNoTie hScores,
    B.contractIndividual_value_eq_of_zero_duration_scores (B.terminal_eq_zero_of_critical hw hc.le hCritical) hw hc i hScores⟩

end ProphetSecretary.Limiting.CountableInstance
