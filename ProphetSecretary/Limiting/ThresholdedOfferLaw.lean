import ProphetSecretary.Limiting.BernoulliCountingMeasure

/-!
# Thresholded ordinary offers as rare marked configurations

Removing a mark at or below a chosen cutoff is an analytical projection.
The online policy still receives identities and values of zero observations
in the original execution; a policy ignoring them is a separate construction.
-/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical NNReal ENNReal
namespace ProphetSecretary.Limiting

noncomputable def thresholdMarkIntensity (ν : Measure ℝ) [IsProbabilityMeasure ν] (b : ℝ) :
    FiniteMeasure ℝ := ⟨ν.restrict (Ioi b),inferInstance⟩

lemma thresholdMarkIntensity_mass_le_one (ν : Measure ℝ) [IsProbabilityMeasure ν] (b : ℝ) :
    (thresholdMarkIntensity ν b).mass ≤ 1 := by
  simp only [FiniteMeasure.mass,thresholdMarkIntensity,FiniteMeasure.mk_apply,Measure.restrict_apply_univ]
  rw [← ENNReal.toNNReal_one]
  exact ENNReal.toNNReal_mono (by simp) (prob_le_one)

noncomputable def thresholdOccurrenceProbability (ν : Measure ℝ) [IsProbabilityMeasure ν] (b : ℝ) :
    unitInterval := ⟨((thresholdMarkIntensity ν b).mass : ℝ),NNReal.coe_nonneg _,
      by exact_mod_cast thresholdMarkIntensity_mass_le_one ν b⟩

lemma thresholdMarkIntensity_rate (ν : Measure ℝ) [IsProbabilityMeasure ν] (b : ℝ) :
    (thresholdMarkIntensity ν b).mass=unitInterval.toNNReal (thresholdOccurrenceProbability ν b) := by
  apply Subtype.ext
  rfl

lemma thresholdPointIntensity (ν : Measure ℝ) [IsProbabilityMeasure ν] (b : ℝ) :
    (Model.Instance.uniformClock.prod ν).restrict (univ ×ˢ Ioi b) =
      intensity (thresholdMarkIntensity ν b) := by
  simpa only [Measure.restrict_univ,intensity,thresholdMarkIntensity,FiniteMeasure.toMeasure_mk] using
    (Measure.prod_restrict (μ := Model.Instance.uniformClock) (ν := ν) univ (Ioi b)).symm

/-- An actual independent uniform clock and original offer have exactly the
rare point-counting law obtained by retaining marks strictly above the cutoff. -/
theorem thresholded_offer_countingMeasure_law (ν : Measure ℝ) [IsProbabilityMeasure ν] (b : ℝ) :
    (Model.Instance.uniformClock.prod ν).map (observedSingleton (univ ×ˢ Ioi b)) =
      (bernoulliConfigurationLaw (thresholdMarkIntensity ν b)
        (thresholdOccurrenceProbability ν b)).map countingMeasure := by
  let μ := thresholdMarkIntensity ν b
  let p := thresholdOccurrenceProbability ν b
  have hS : MeasurableSet (univ ×ˢ Ioi b : Set Point) := MeasurableSet.univ.prod measurableSet_Ioi
  have hMass : (Model.Instance.uniformClock.prod ν) (univ ×ˢ Ioi b) = (μ.mass : ℝ≥0∞) := by
    rw [Measure.prod_prod,measure_univ,one_mul]
    simpa only [μ,thresholdMarkIntensity,FiniteMeasure.toMeasure_mk,Measure.restrict_apply_univ] using
      (FiniteMeasure.ennreal_mass (μ := μ)).symm
  have hComp : (Model.Instance.uniformClock.prod ν) (univ ×ˢ Ioi b)ᶜ =
      ENNReal.ofReal (1-(p:ℝ)) := by
    rw [measure_compl hS (by finiteness),measure_univ,hMass]
    change 1-(μ.mass : ℝ≥0∞) = ENNReal.ofReal (1-(μ.mass:ℝ))
    rw [ENNReal.ofReal_sub 1 (NNReal.coe_nonneg μ.mass),ENNReal.ofReal_one,ENNReal.ofReal_coe_nnreal]
  rw [observedSingleton_law _ _ hS,thresholdPointIntensity,hComp,
    bernoulliConfiguration_countingMeasure_law _ _ (thresholdMarkIntensity_rate ν b)]
  exact add_comm _ _
end ProphetSecretary.Limiting
