import ProphetSecretary.Limiting.FiniteBandNormalization
import ProphetSecretary.Limiting.PoissonCounts
import ProphetSecretary.Probability.InfiniteCoordinateDensity

/-!
# Actual array and fiber likelihoods for a scaled mark band

The product of the normalized mark densities is expressed through the total
array length and the count of band marks. These counts are analytical; they
are not additional observations made available to an online rule.
-/

open MeasureTheory Set
open scoped Classical NNReal ENNReal BigOperators

namespace ProphetSecretary.Limiting

noncomputable def bandNormalizedConfigurationDensity (μ : FiniteMeasure ℝ) (S : Set ℝ)
    (r : ℝ≥0) (ω : Configuration) : ℝ :=
  (((μ.mass/(bandScaledIntensity μ S r).mass : ℝ≥0) : ℝ)^ω.1)*
    (r : ℝ)^(pointCount (univ ×ˢ S) ω)

lemma measurable_bandNormalizedConfigurationDensity (μ : FiniteMeasure ℝ) {S : Set ℝ}
    (hS : MeasurableSet S) (r : ℝ≥0) : Measurable (bandNormalizedConfigurationDensity μ S r) :=
  ((measurable_of_countable (fun N : ℕ =>
    (((μ.mass/(bandScaledIntensity μ S r).mass : ℝ≥0) : ℝ)^N))).comp measurable_configuration_count).mul
      ((measurable_of_countable (fun N : ℕ => (r : ℝ)^N)).comp
        (measurable_pointCount (MeasurableSet.univ.prod hS)))

lemma bandNormalizedDensity_product (μ : FiniteMeasure ℝ) (S : Set ℝ) (r : ℝ≥0)
    (N : ℕ) (v : Fin N → Point) :
    (∏ j : Fin N, bandNormalizedDensity μ S r (v j).2)=
      bandNormalizedConfigurationDensity μ S r (configurationMk N v) := by
  let c : ℝ := ((μ.mass/(bandScaledIntensity μ S r).mass : ℝ≥0) : ℝ)
  change (∏ j : Fin N, c*bandScaleFactor S r (v j).2)=c^N*(r : ℝ)^(pointCount (univ ×ˢ S) (configurationMk N v))
  rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  congr 1
  calc
    _ = ∏ j : Fin N, (r : ℝ)^(if (v j).2 ∈ S then (1 : ℕ) else 0) := by
      apply Finset.prod_congr rfl
      intro j _
      by_cases hx : (v j).2 ∈ S <;> simp [bandScaleFactor,hx]
    _ = _ := by
      rw [Finset.prod_pow_eq_pow_sum]
      congr 1
      simp only [pointCount,configurationMk,Set.mem_prod,Set.mem_univ,true_and]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hx : (v j).2 ∈ S <;> simp [hx]

lemma arrayLaw_bandScale_configurationDensity (μ : FiniteMeasure ℝ) {S : Set ℝ}
    (hS : MeasurableSet S) {r : ℝ≥0} (hr : 0 < r) (hμ : μ ≠ 0) (N : ℕ) :
    arrayLaw (bandScaledIntensity μ S r) N=(arrayLaw μ N).withDensity
      (fun v => ENNReal.ofReal (bandNormalizedConfigurationDensity μ S r (configurationMk N v))) := by
  rw [arrayLaw_bandScale_density μ hS hr hμ N]
  apply congrArg (fun f => (arrayLaw μ N).withDensity f)
  funext v
  exact congrArg ENNReal.ofReal (bandNormalizedDensity_product μ S r N v)

lemma fiberLaw_bandScale_configurationDensity (μ : FiniteMeasure ℝ) {S : Set ℝ}
    (hS : MeasurableSet S) {r : ℝ≥0} (hr : 0 < r) (hμ : μ ≠ 0) (N : ℕ) :
    fiberLaw (bandScaledIntensity μ S r) N=(fiberLaw μ N).withDensity
      (fun ω => ENNReal.ofReal (bandNormalizedConfigurationDensity μ S r ω)) := by
  have hMP : MeasurePreserving (configurationMk N) (arrayLaw μ N) (fiberLaw μ N) :=
    ⟨measurable_configuration_mk N,rfl⟩
  have hDensity : Measurable (fun ω => ENNReal.ofReal (bandNormalizedConfigurationDensity μ S r ω)) :=
    ENNReal.measurable_ofReal.comp (measurable_bandNormalizedConfigurationDensity μ hS r)
  have hWeighted := ProphetSecretary.Probability.measurePreserving_withDensity hMP hDensity
  change (arrayLaw (bandScaledIntensity μ S r) N).map (configurationMk N)=_
  rw [arrayLaw_bandScale_configurationDensity μ hS hr hμ N]
  exact hWeighted.map_eq

end ProphetSecretary.Limiting
