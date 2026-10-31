import ProphetSecretary.Limiting.Support
import ProphetSecretary.Limiting.ConfigurationMeasurability
import ProphetSecretary.Probability.IndependentNullSections

/-!
# Configuration clocks avoid independent times

The null-section argument uses the actual intensity and independent product
law. In particular it applies when the independent time is selected from a
different finite configuration or from an individual arrival clock.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Limiting

lemma configuration_times_ne (μ : FiniteMeasure ℝ) (t : ℝ) :
    ∀ᵐ ω ∂configurationLaw μ, ∀ j : Fin ω.1, (ω.2 j).1 ≠ t := by
  have ht : ∀ᵐ p : Point ∂intensity μ, p.1 ≠ t :=
    (Measure.quasiMeasurePreserving_fst (μ := Model.Instance.uniformClock) (ν := (μ : Measure ℝ))).ae
      (Model.Instance.uniformClock.ae_ne t)
  exact all_points_in_of_intensity_compl_null μ
    ((measurableSet_singleton t).preimage measurable_fst).compl (ae_iff.mp ht)

lemma measurableSet_configuration_times_ne_joint :
    MeasurableSet {q : Configuration × ℝ | ∀ j : Fin q.1.1, (q.1.2 j).1 ≠ q.2} := by
  apply measurableSet_setOf.mpr
  apply measurable_of_configuration_prod_branches
  intro N
  apply measurableSet_setOf.mp
  change MeasurableSet {q : (Fin N → Point) × ℝ | ∀ j : Fin N, (q.1 j).1 ≠ q.2}
  simp only [setOf_forall]
  apply MeasurableSet.iInter
  intro j
  exact (measurableSet_eq_fun (measurable_fst.comp ((measurable_pi_apply j).comp measurable_fst))
    measurable_snd).compl

theorem independent_configuration_times_ne {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (μ : FiniteMeasure ℝ)
    {X : Ω → Configuration} {T : Ω → ℝ}
    (hI : IndepFun X T P) (hMX : Measurable X) (hMT : Measurable T)
    (hX : HasLaw X (configurationLaw μ) P) :
    ∀ᵐ ω ∂P, ∀ j : Fin (X ω).1, ((X ω).2 j).1 ≠ T ω :=
  ProphetSecretary.Probability.indepFun_ae_of_sections hI hMX hMT hX
    measurableSet_configuration_times_ne_joint (configuration_times_ne μ)

end ProphetSecretary.Limiting
