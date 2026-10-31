import ProphetSecretary.Limiting.CountableCompetingMaximumLaw
import ProphetSecretary.Limiting.CountableIndividualMean
import ProphetSecretary.Probability.MaximumKernelAffinity

/-!
# Prophet expectation under individual mean contraction

The actual competing maximum is independent of the individual. The original
benchmark is the product-law maximum kernel; the contracted benchmark is that
kernel at the individual's mean. A strict competing CDF constant almost
everywhere on all marginal values therefore makes the benchmarks equal.
Criticality and the location identity must establish this CDF premise.
-/
open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Limiting.CountableInstance

lemma contractIndividual_maximum (B : CountableInstance) (i : ℕ) :
    (B.contractIndividual i).maximum=B.maximum := rfl

theorem expectedMaximum_contractIndividual_eq_competing_kernel (B : CountableInstance) (i : ℕ) :
    (B.contractIndividual i).expectedMaximum=
      ∫ y, max (B.individualMean i) y ∂(B.competingMaximumLaw i : Measure ℝ) := by
  let Q := B.contractIndividual i
  let m := B.individualMean i
  have hValue := (Q.value_projection_measurePreserving (Measure.dirac ())).hasLaw.integral_comp Q.measurable_maximum.aestronglyMeasurable
  have hMP := B.meanSubstitution_measurePreserving i (Measure.dirac ())
  have hF : Measurable (fun v : CompleteWorld Unit => Q.maximum (v.1,v.2.1)) :=
    Q.measurable_maximum.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have hMean := hMP.hasLaw.integral_comp hF.aestronglyMeasurable
  have hCompeting := (B.competingMaximum_hasLaw i (Measure.dirac ())).integral_comp
    ((measurable_const : Measurable (fun _ : ℝ => m)).max measurable_id).aestronglyMeasurable
  calc
    _ = ∫ v : CompleteWorld Unit, Q.maximum (v.1,v.2.1) ∂Q.completeWorldLaw (Measure.dirac ()) := hValue.symm
    _ = ∫ v : CompleteWorld Unit, Q.maximum
        ((replaceIndividualValue i (v,m)).1,(replaceIndividualValue i (v,m)).2.1)
          ∂B.completeWorldLaw (Measure.dirac ()) := hMean.symm
    _ = ∫ v : CompleteWorld Unit, max m (B.competingMaximum i v) ∂B.completeWorldLaw (Measure.dirac ()) := by
      apply integral_congr_ae
      filter_upwards [B.maximum_replaceIndividual_eq_max_ae (Measure.dirac ()) i] with v hv
      change (B.contractIndividual i).maximum (v.1,Function.update v.2.1 i m)=_
      rw [B.contractIndividual_maximum]
      exact hv m
    _ = _ := hCompeting

theorem contractIndividual_expectedMaximum_eq_of_constant_competing_Cdf
    (B : CountableInstance) (i : ℕ) (k : ℝ)
    (hCdf : ∀ᵐ x ∂(B.individuals i : Measure ℝ),
      (B.competingMaximumLaw i : Measure ℝ).real (Iio x)=k) :
    (B.contractIndividual i).expectedMaximum=B.expectedMaximum := by
  rw [B.expectedMaximum_contractIndividual_eq_competing_kernel i,
    B.expectedMaximum_eq_individual_competing_kernel i]
  exact (ProphetSecretary.Probability.expected_maximum_mean_contraction_of_constant_strictCdf
    (B.individuals i : Measure ℝ) (B.competingMaximumLaw i : Measure ℝ) B.cap
    (B.individual_supported i) (B.competingMaximumLaw_integrable i) k hCdf).2.symm

end ProphetSecretary.Limiting.CountableInstance
