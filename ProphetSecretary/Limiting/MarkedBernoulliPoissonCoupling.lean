import ProphetSecretary.Probability.BernoulliPoissonCoupling
import ProphetSecretary.Limiting.PoissonSharedArray

/-!
# Shared-mark coupling for one rare offer

The Bernoulli and Poisson configurations use the same point array. Equal
counts give identical finite configurations, so the whole marked discrepancy
has probability at most the square of the rare-offer probability.
-/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical NNReal ENNReal
namespace ProphetSecretary.Limiting
open ProphetSecretary.Probability

noncomputable def bernoulliConfigurationLaw (μ : FiniteMeasure ℝ) (p : unitInterval) :
    Measure Configuration :=
  ((bernoulliMeasure (1:ℕ) 0 p).prod (sharedPointArrayLaw μ)).map sharedArrayConfiguration

instance bernoulliConfigurationLaw_probability (μ : FiniteMeasure ℝ) (p : unitInterval) :
    IsProbabilityMeasure (bernoulliConfigurationLaw μ p) :=
  Measure.isProbabilityMeasure_map measurable_sharedArrayConfiguration.aemeasurable

lemma bernoulliConfigurationLaw_eq (μ : FiniteMeasure ℝ) (p : unitInterval) :
    bernoulliConfigurationLaw μ p =
      ENNReal.ofReal (p:ℝ) • fiberLaw μ 1 + ENNReal.ofReal (1-(p:ℝ)) • fiberLaw μ 0 := by
  unfold bernoulliConfigurationLaw bernoulliMeasure
  rw [Measure.add_prod,Measure.map_add _ _ measurable_sharedArrayConfiguration,
    ← Measure.coe_nnreal_smul,← Measure.coe_nnreal_smul,
    Measure.prod_smul_left,Measure.prod_smul_left,Measure.map_smul,Measure.map_smul,
    sharedArrayConfiguration_fiber_law,sharedArrayConfiguration_fiber_law]
  congr 1
  · rw [← unitInterval.coe_toNNReal p,ENNReal.ofReal_coe_nnreal]
  · rw [← unitInterval.coe_symm_eq p,← unitInterval.coe_toNNReal (unitInterval.symm p),ENNReal.ofReal_coe_nnreal]

abbrev MarkedCountPair := (ℕ × ℕ) × (ℕ → Point)

noncomputable def markedBernoulliPoissonCoupling (μ : FiniteMeasure ℝ) (p : unitInterval) :
    Measure MarkedCountPair := (bernoulliPoissonCoupling p).prod (sharedPointArrayLaw μ)

instance markedBernoulliPoissonCoupling_probability (μ : FiniteMeasure ℝ) (p : unitInterval) :
    IsProbabilityMeasure (markedBernoulliPoissonCoupling μ p) := by
  unfold markedBernoulliPoissonCoupling
  infer_instance

def markedBernoulliConfiguration (q : MarkedCountPair) : Configuration :=
  sharedArrayConfiguration (q.1.1,q.2)
def markedPoissonConfiguration (q : MarkedCountPair) : Configuration :=
  sharedArrayConfiguration (q.1.2,q.2)

lemma markedBernoulliConfiguration_measurePreserving (μ : FiniteMeasure ℝ) (p : unitInterval) :
    MeasurePreserving markedBernoulliConfiguration (markedBernoulliPoissonCoupling μ p)
      (bernoulliConfigurationLaw μ p) := by
  have hCount : MeasurePreserving (Prod.fst : ℕ × ℕ → ℕ) (bernoulliPoissonCoupling p)
      (bernoulliMeasure (1:ℕ) 0 p) := ⟨measurable_fst,bernoulliPoissonCoupling_fst p⟩
  exact (⟨measurable_sharedArrayConfiguration,rfl⟩ : MeasurePreserving sharedArrayConfiguration
    ((bernoulliMeasure (1:ℕ) 0 p).prod (sharedPointArrayLaw μ))
    (bernoulliConfigurationLaw μ p)).comp (hCount.prod (MeasurePreserving.id _))

lemma markedPoissonConfiguration_measurePreserving (μ : FiniteMeasure ℝ) (p : unitInterval)
    (hRate : μ.mass=unitInterval.toNNReal p) :
    MeasurePreserving markedPoissonConfiguration (markedBernoulliPoissonCoupling μ p)
      (configurationLaw μ) := by
  have hCount : MeasurePreserving (Prod.snd : ℕ × ℕ → ℕ) (bernoulliPoissonCoupling p)
      (poissonMeasure μ.mass) := by
    rw [hRate]
    exact ⟨measurable_snd,bernoulliPoissonCoupling_snd p⟩
  exact (sharedArrayConfiguration_measurePreserving μ).comp (hCount.prod (MeasurePreserving.id _))

lemma markedConfigurations_eq_of_counts_eq (q : MarkedCountPair) (h : q.1.1=q.1.2) :
    markedBernoulliConfiguration q = markedPoissonConfiguration q := by
  unfold markedBernoulliConfiguration markedPoissonConfiguration
  rw [h]

lemma markedBernoulliPoissonCoupling_mismatch_le (μ : FiniteMeasure ℝ) (p : unitInterval) :
    (markedBernoulliPoissonCoupling μ p).real
      {q | markedBernoulliConfiguration q ≠ markedPoissonConfiguration q} ≤ (p:ℝ)^2 := by
  have hsub : {q : MarkedCountPair | markedBernoulliConfiguration q ≠ markedPoissonConfiguration q} ⊆
      {q | q.1.1≠q.1.2} := by
    intro q hq hcount
    exact hq (markedConfigurations_eq_of_counts_eq q hcount)
  apply (measureReal_mono hsub).trans
  have he : MeasurePreserving (Prod.fst : MarkedCountPair → ℕ × ℕ)
      (markedBernoulliPoissonCoupling μ p) (bernoulliPoissonCoupling p) := measurePreserving_fst
  have hMass := map_measureReal_apply (μ := markedBernoulliPoissonCoupling μ p) he.measurable
    (measurableSet_eq_fun measurable_fst measurable_snd).compl
  rw [he.map_eq] at hMass
  change (bernoulliPoissonCoupling p).real {q | q.1≠q.2} =
    (markedBernoulliPoissonCoupling μ p).real {q | q.1.1≠q.1.2} at hMass
  rw [← hMass]
  exact bernoulliPoissonCoupling_mismatch_le p
end ProphetSecretary.Limiting
