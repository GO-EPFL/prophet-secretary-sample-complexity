import ProphetSecretary.Limiting.FinitePoissonSuperposition
import ProphetSecretary.Limiting.MarkedBernoulliPoissonCoupling
import ProphetSecretary.Probability.BoundedCouplingError

/-!
# Poisson approximation of a finite family of rare marked offers

An actual product coupling preserves the Bernoulli and Poisson marginal
configuration laws. The total error is controlled by the sum of squared
occurrence probabilities, independently of the number of offers.
-/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical NNReal ENNReal BigOperators
namespace ProphetSecretary.Limiting
open ProphetSecretary.Probability
variable {ι : Type*} [Fintype ι]

noncomputable def rareOfferCoupling (μ : ι → FiniteMeasure ℝ) (p : ι → unitInterval) :
    Measure (ι → MarkedCountPair) := Measure.pi (fun i => markedBernoulliPoissonCoupling (μ i) (p i))
instance rareOfferCoupling_probability (μ : ι → FiniteMeasure ℝ) (p : ι → unitInterval) :
    IsProbabilityMeasure (rareOfferCoupling μ p) := by
  unfold rareOfferCoupling
  infer_instance

noncomputable def rareCountingMeasureLaw (μ : ι → FiniteMeasure ℝ) (p : ι → unitInterval) :
    Measure (Measure Point) :=
  (Measure.pi (fun i => bernoulliConfigurationLaw (μ i) (p i))).map finiteCountingMeasure
instance rareCountingMeasureLaw_probability (μ : ι → FiniteMeasure ℝ) (p : ι → unitInterval) :
    IsProbabilityMeasure (rareCountingMeasureLaw μ p) :=
  Measure.isProbabilityMeasure_map measurable_finiteCountingMeasure.aemeasurable

noncomputable def coupledRareCountingMeasure (q : ι → MarkedCountPair) : Measure Point :=
  finiteCountingMeasure (fun i => markedBernoulliConfiguration (q i))
noncomputable def coupledPoissonCountingMeasure (q : ι → MarkedCountPair) : Measure Point :=
  finiteCountingMeasure (fun i => markedPoissonConfiguration (q i))

lemma coupledRareCountingMeasure_measurePreserving (μ : ι → FiniteMeasure ℝ) (p : ι → unitInterval) :
    MeasurePreserving coupledRareCountingMeasure (rareOfferCoupling μ p) (rareCountingMeasureLaw μ p) :=
  (⟨measurable_finiteCountingMeasure,rfl⟩ : MeasurePreserving finiteCountingMeasure
    (Measure.pi (fun i => bernoulliConfigurationLaw (μ i) (p i))) (rareCountingMeasureLaw μ p)).comp
    (measurePreserving_pi _ _ (fun i => markedBernoulliConfiguration_measurePreserving (μ i) (p i)))

lemma coupledPoissonCountingMeasure_measurePreserving (μ : ι → FiniteMeasure ℝ) (p : ι → unitInterval)
    (hRate : ∀ i, (μ i).mass=unitInterval.toNNReal (p i)) :
    MeasurePreserving coupledPoissonCountingMeasure (rareOfferCoupling μ p)
      ((configurationLaw (∑ i, μ i)).map countingMeasure) :=
  (⟨measurable_finiteCountingMeasure,finiteCountingMeasure_law μ⟩ :
    MeasurePreserving finiteCountingMeasure (finiteConfigurationsLaw μ)
      ((configurationLaw (∑ i, μ i)).map countingMeasure)).comp
    (measurePreserving_pi _ _ (fun i => markedPoissonConfiguration_measurePreserving (μ i) (p i) (hRate i)))

def rareOfferMismatch : Set (ι → MarkedCountPair) := {q | ∃ i, (q i).1.1≠(q i).1.2}
lemma measurableSet_rareOfferMismatch : MeasurableSet (rareOfferMismatch (ι := ι)) := by
  have hset : rareOfferMismatch = ⋃ i, {q : ι → MarkedCountPair | (q i).1.1≠(q i).1.2} := by
    ext q
    simp [rareOfferMismatch]
  rw [hset]
  exact MeasurableSet.iUnion (fun i =>
    (measurableSet_eq_fun ((measurable_pi_apply i).fst.fst) ((measurable_pi_apply i).fst.snd)).compl)

lemma rareOfferCoupling_mismatch_le (μ : ι → FiniteMeasure ℝ) (p : ι → unitInterval) :
    (rareOfferCoupling μ p).real rareOfferMismatch ≤ ∑ i, (p i:ℝ)^2 := by
  have hset : rareOfferMismatch = ⋃ i, {q : ι → MarkedCountPair | (q i).1.1≠(q i).1.2} := by ext q; simp [rareOfferMismatch]
  rw [hset]
  apply (measureReal_iUnion_fintype_le _).trans
  apply Finset.sum_le_sum
  intro i _
  have he : MeasurePreserving (fun q : ι → MarkedCountPair => (q i).1)
      (rareOfferCoupling μ p) (bernoulliPoissonCoupling (p i)) :=
    (measurePreserving_fst (μ := bernoulliPoissonCoupling (p i)) (ν := sharedPointArrayLaw (μ i))).comp
      (measurePreserving_eval (fun j => markedBernoulliPoissonCoupling (μ j) (p j)) i)
  have hMass := map_measureReal_apply (μ := rareOfferCoupling μ p) he.measurable
    (measurableSet_eq_fun measurable_fst measurable_snd).compl
  rw [he.map_eq] at hMass
  change (bernoulliPoissonCoupling (p i)).real {q | q.1≠q.2} =
    (rareOfferCoupling μ p).real {q | (q i).1.1≠(q i).1.2} at hMass
  rw [← hMass]
  exact bernoulliPoissonCoupling_mismatch_le (p i)

lemma coupledCountingMeasures_eq_off (q : ι → MarkedCountPair) (hq : q∉rareOfferMismatch) :
    coupledRareCountingMeasure q = coupledPoissonCountingMeasure q := by
  unfold coupledRareCountingMeasure coupledPoissonCountingMeasure
  congr 1
  funext i
  have hAll : ∀ i, (q i).1.1=(q i).1.2 := by
    simpa only [rareOfferMismatch,mem_setOf_eq,not_exists,not_not] using hq
  exact markedConfigurations_eq_of_counts_eq (q i) (hAll i)

/-- Quantitative marked Poisson approximation for any bounded measurable
observable and any additional independent auxiliary randomness. -/
theorem rareCountingMeasure_observable_error {Aux : Type*} [MeasurableSpace Aux]
    (ν : Measure Aux) [IsProbabilityMeasure ν]
    (μ : ι → FiniteMeasure ℝ) (p : ι → unitInterval)
    (hRate : ∀ i, (μ i).mass=unitInterval.toNNReal (p i))
    (f : (Measure Point) × Aux → ℝ) (hf : Measurable f) {D : ℝ} (hD : 0≤D)
    (hb : ∀ q, |f q|≤D) :
    |(∫ q, f q ∂(rareCountingMeasureLaw μ p).prod ν)-
      ∫ q, f q ∂((configurationLaw (∑ i, μ i)).map countingMeasure).prod ν| ≤
      2*D*∑ i, (p i:ℝ)^2 := by
  let γ := (rareOfferCoupling μ p).prod ν
  let X := fun q : (ι → MarkedCountPair) × Aux => (coupledRareCountingMeasure q.1,q.2)
  let Y := fun q : (ι → MarkedCountPair) × Aux => (coupledPoissonCountingMeasure q.1,q.2)
  have hX : MeasurePreserving X γ ((rareCountingMeasureLaw μ p).prod ν) :=
    (coupledRareCountingMeasure_measurePreserving μ p).prod (MeasurePreserving.id ν)
  have hY : MeasurePreserving Y γ (((configurationLaw (∑ i, μ i)).map countingMeasure).prod ν) :=
    (coupledPoissonCountingMeasure_measurePreserving μ p hRate).prod (MeasurePreserving.id ν)
  have hE : MeasurableSet (Prod.fst ⁻¹' (rareOfferMismatch (ι := ι)) : Set ((ι → MarkedCountPair) × Aux)) :=
    measurableSet_rareOfferMismatch.preimage measurable_fst
  have hBound := integral_sub_abs_le_of_eq_off γ (f ∘ X) (f ∘ Y)
    (hf.comp hX.measurable) (hf.comp hY.measurable) hD (fun q => hb (X q)) (fun q => hb (Y q))
    _ hE (fun q hq => by
      have he := coupledCountingMeasures_eq_off q.1 hq
      change f (coupledRareCountingMeasure q.1,q.2) = f (coupledPoissonCountingMeasure q.1,q.2)
      rw [he])
  rw [hX.hasLaw.integral_comp hf.aestronglyMeasurable,hY.hasLaw.integral_comp hf.aestronglyMeasurable] at hBound
  apply hBound.trans
  have hFst : MeasurePreserving (Prod.fst : (ι → MarkedCountPair) × Aux → (ι → MarkedCountPair))
      γ (rareOfferCoupling μ p) := measurePreserving_fst
  have hMass := map_measureReal_apply (μ := γ) hFst.measurable measurableSet_rareOfferMismatch
  rw [hFst.map_eq] at hMass
  rw [← hMass]
  exact mul_le_mul_of_nonneg_left (rareOfferCoupling_mismatch_le μ p) (by positivity)
end ProphetSecretary.Limiting
