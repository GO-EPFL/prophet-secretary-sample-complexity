import ProphetSecretary.Limiting.PoissonCounts

/-!
# Void probabilities of actual Poisson configurations

The event concerns the complete configuration, including points arriving after
stopping. Its probability is derived from the constructed count law.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical NNReal ENNReal

namespace ProphetSecretary.Limiting

lemma pointCount_eq_zero_iff (S : Set Point) (ω : Configuration) :
    pointCount S ω = 0 ↔ ∀ j, ω.2 j ∉ S := by
  simp [pointCount]

lemma configuration_void_probability (μ : FiniteMeasure ℝ) {S : Set Point}
    (hS : MeasurableSet S) :
    configurationLaw μ {ω | ∀ j, ω.2 j ∉ S} =
      ENNReal.ofReal (Real.exp (-(intensity μ).real S)) := by
  have he : {ω : Configuration | ∀ j, ω.2 j ∉ S} = pointCount S ⁻¹' {0} := by
    ext ω
    exact (pointCount_eq_zero_iff S ω).symm
  rw [he, ← Measure.map_apply (measurable_pointCount hS) (measurableSet_singleton 0),
    pointCount_law μ hS, poissonMeasure_singleton]
  simp [countRate_coe_eq_intensity]

lemma configuration_no_marks_above_probability (μ : FiniteMeasure ℝ) (t : ℝ) :
    configurationLaw μ {ω | ∀ j, (ω.2 j).2 ≤ t} =
      ENNReal.ofReal (Real.exp (-(μ : Measure ℝ).real (Ioi t))) := by
  have he : {ω : Configuration | ∀ j, (ω.2 j).2 ≤ t} =
      {ω : Configuration | ∀ j, ω.2 j ∉ univ ×ˢ Ioi t} := by
    ext ω
    simp
  rw [he, configuration_void_probability μ (MeasurableSet.univ.prod measurableSet_Ioi)]
  congr 2
  simp [intensity, Measure.prod_prod, Measure.real]

end ProphetSecretary.Limiting
