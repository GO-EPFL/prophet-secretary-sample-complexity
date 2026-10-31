import ProphetSecretary.Limiting.HybridMixture
import ProphetSecretary.Limiting.PoissonCountMoments

/-!
# Count moments for the hybrid close-pair estimate

The actual configuration count has its constructed Poisson law. Its affine
square moment controls positive close pairs after conditioning analytically on
that count; the count is not an additional policy observation.
-/
open MeasureTheory Set Filter
open scoped Classical NNReal
namespace ProphetSecretary.Limiting
variable {Aux : Type*} [MeasurableSpace Aux]

lemma world_count_second_integrable (μ : FiniteMeasure ℝ) (ν : Measure Aux) [IsProbabilityMeasure ν] :
    Integrable (fun v : World Aux => (v.1.1 : ℝ)^2) (worldLaw μ ν) :=
  ((configuration_count_measurePreserving μ).comp
    (measurePreserving_fst (μ := configurationLaw μ) (ν := ν))).integrable_comp_of_integrable
      (g := fun N : ℕ => (N : ℝ)^2) (poisson_second_integrable μ.mass)

lemma integral_world_count_second (μ : FiniteMeasure ℝ) (ν : Measure Aux) [IsProbabilityMeasure ν] :
    (∫ v : World Aux, (v.1.1 : ℝ)^2 ∂worldLaw μ ν) = (μ.mass : ℝ)^2+(μ.mass : ℝ) :=
  (((configuration_count_measurePreserving μ).comp
    (measurePreserving_fst (μ := configurationLaw μ) (ν := ν))).hasLaw.integral_comp
      (poisson_second_integrable μ.mass).aestronglyMeasurable).trans (integral_poisson_second μ.mass)

lemma world_affineCountSquare_integrable (μ : FiniteMeasure ℝ) (ν : Measure Aux) [IsProbabilityMeasure ν]
    (s p : ℝ) : Integrable (fun v : World Aux => (s+(v.1.1 : ℝ)*p)^2) (worldLaw μ ν) := by
  have hN : Integrable (fun v : World Aux => (v.1.1 : ℝ)) (worldLaw μ ν) :=
    (measurePreserving_fst (μ := configurationLaw μ) (ν := ν)).integrable_comp_of_integrable
      (configuration_count_integrable μ)
  have hSq := world_count_second_integrable μ ν
  have hPol := ((integrable_const (s^2)).add (hN.const_mul (2*s*p))).add (hSq.const_mul (p^2))
  have hEq : (fun v : World Aux => (s+(v.1.1 : ℝ)*p)^2) =
      (fun v => (s^2+(2*s*p)*(v.1.1 : ℝ))+p^2*(v.1.1 : ℝ)^2) := by funext v; ring
  rw [hEq]
  exact hPol

lemma integral_world_affineCountSquare (μ : FiniteMeasure ℝ) (ν : Measure Aux) [IsProbabilityMeasure ν]
    (s p : ℝ) :
    (∫ v : World Aux, (s+(v.1.1 : ℝ)*p)^2 ∂worldLaw μ ν) =
      s^2+2*s*p*(μ.mass : ℝ)+p^2*((μ.mass : ℝ)^2+(μ.mass : ℝ)) := by
  have hN : Integrable (fun v : World Aux => (v.1.1 : ℝ)) (worldLaw μ ν) :=
    (measurePreserving_fst (μ := configurationLaw μ) (ν := ν)).integrable_comp_of_integrable
      (configuration_count_integrable μ)
  have hSq := world_count_second_integrable μ ν
  have hNMean : (∫ v : World Aux, (v.1.1 : ℝ) ∂worldLaw μ ν) = (μ.mass : ℝ) :=
    ((measurePreserving_fst (μ := configurationLaw μ) (ν := ν)).hasLaw.integral_comp
      (configuration_count_integrable μ).aestronglyMeasurable).trans (configuration_count_expectation μ)
  have hEq : (fun v : World Aux => (s+(v.1.1 : ℝ)*p)^2) =
      (fun v => (s^2+(2*s*p)*(v.1.1 : ℝ))+p^2*(v.1.1 : ℝ)^2) := by funext v; ring
  rw [hEq,integral_add (f := fun v : World Aux => s^2+(2*s*p)*(v.1.1 : ℝ))
      (g := fun v : World Aux => p^2*(v.1.1 : ℝ)^2)
      ((integrable_const (s^2)).add (hN.const_mul (2*s*p))) (hSq.const_mul (p^2)),
    integral_add (f := fun _ : World Aux => s^2) (g := fun v : World Aux => (2*s*p)*(v.1.1 : ℝ))
      (integrable_const (s^2)) (hN.const_mul (2*s*p)),integral_const_mul,integral_const_mul,
    hNMean,integral_world_count_second]
  simp only [integral_const,probReal_univ,one_smul]

end ProphetSecretary.Limiting
