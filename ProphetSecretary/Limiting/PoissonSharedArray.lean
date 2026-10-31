import ProphetSecretary.Limiting.FiniteIntensityPoisson
import Mathlib.Probability.Independence.InfinitePi

/-!
# Constructing a Poisson configuration from an independent shared array

An infinite iid point array is auxiliary coupling data. Only its finite prefix
of the independently sampled count is mapped to the actual configuration law.
-/
open MeasureTheory ProbabilityTheory Set
open scoped Classical NNReal ENNReal
namespace ProphetSecretary.Limiting

noncomputable def sharedPointArrayLaw (μ : FiniteMeasure ℝ) : Measure (ℕ → Point) :=
  Measure.infinitePi (fun _ => pointLaw μ)
instance sharedPointArrayLaw_probability (μ : FiniteMeasure ℝ) :
    IsProbabilityMeasure (sharedPointArrayLaw μ) := by
  unfold sharedPointArrayLaw
  infer_instance

def sharedArrayConfiguration (z : ℕ × (ℕ → Point)) : Configuration :=
  configurationMk z.1 (fun j => z.2 j)

lemma measurable_sharedArrayConfiguration : Measurable sharedArrayConfiguration := by
  apply measurable_from_prod_countable_right
  intro N
  exact (measurable_configuration_mk N).comp (measurable_pi_lambda _ (fun j => measurable_pi_apply (j:ℕ)))

lemma sharedPointArray_prefix_measurePreserving (μ : FiniteMeasure ℝ) (N : ℕ) :
    MeasurePreserving (fun v : ℕ → Point => fun j : Fin N => v j)
      (sharedPointArrayLaw μ) (arrayLaw μ N) := by
  constructor
  · exact measurable_pi_lambda _ (fun j => measurable_pi_apply (j:ℕ))
  · change (Measure.infinitePi (fun _ : ℕ => pointLaw μ)).map _ = Measure.pi _
    rw [Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective,Measure.infinitePi_eq_pi]

lemma sharedArrayConfiguration_fiber_law (μ : FiniteMeasure ℝ) (N : ℕ) :
    ((Measure.dirac N).prod (sharedPointArrayLaw μ)).map sharedArrayConfiguration = fiberLaw μ N := by
  rw [Measure.dirac_prod,Measure.map_map measurable_sharedArrayConfiguration (by fun_prop)]
  exact ((sharedPointArray_prefix_measurePreserving μ N).map_eq ▸
    (Measure.map_map (measurable_configuration_mk N)
      (sharedPointArray_prefix_measurePreserving μ N).measurable)).symm

theorem sharedArrayConfiguration_measurePreserving (μ : FiniteMeasure ℝ) :
    MeasurePreserving sharedArrayConfiguration
      ((poissonMeasure μ.mass).prod (sharedPointArrayLaw μ)) (configurationLaw μ) := by
  refine ⟨measurable_sharedArrayConfiguration,?_⟩
  rw [poissonMeasure,Measure.prod_sum_left,
    Measure.map_sum measurable_sharedArrayConfiguration.aemeasurable]
  unfold configurationLaw
  congr 1
  funext N
  rw [Measure.prod_smul_left,Measure.map_smul,sharedArrayConfiguration_fiber_law]
  rfl
end ProphetSecretary.Limiting
