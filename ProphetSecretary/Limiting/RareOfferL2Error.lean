import ProphetSecretary.Limiting.RareOfferPoissonCoupling
import ProphetSecretary.Probability.L2CouplingError

/-!
# Square-integrable rare-configuration observable error

The actual marked product coupling also handles unbounded analytical scores.
Only their explicit second-moment bounds remain inputs to this estimate;
the coupling and both marginal laws are constructed, not postulated.
-/
open MeasureTheory Set
open scoped Classical BigOperators
namespace ProphetSecretary.Limiting
open ProphetSecretary.Probability
variable {ι : Type*} [Fintype ι] {Aux : Type*} [MeasurableSpace Aux]

lemma rareCountingMeasure_l2_observable_error (ν : Measure Aux) [IsProbabilityMeasure ν]
    (μ : ι → FiniteMeasure ℝ) (p : ι → unitInterval)
    (hRate : ∀ i, (μ i).mass=unitInterval.toNNReal (p i))
    (f : (Measure Point) × Aux → ℝ) (hf : Measurable f)
    (hL : MemLp f 2 ((rareCountingMeasureLaw μ p).prod ν))
    (hR : MemLp f 2 (((configurationLaw (∑ i, μ i)).map countingMeasure).prod ν))
    {IL IR : ℝ}
    (hML : (∫ q, (f q)^2 ∂(rareCountingMeasureLaw μ p).prod ν)≤IL)
    (hMR : (∫ q, (f q)^2 ∂((configurationLaw (∑ i, μ i)).map countingMeasure).prod ν)≤IR) :
    |(∫ q, f q ∂(rareCountingMeasureLaw μ p).prod ν)-
      ∫ q, f q ∂((configurationLaw (∑ i, μ i)).map countingMeasure).prod ν| ≤
      Real.sqrt (2*(IL+IR)*(∑ i, (p i:ℝ)^2)) := by
  let γ := (rareOfferCoupling μ p).prod ν
  let X := fun q : (ι → MarkedCountPair) × Aux => (coupledRareCountingMeasure q.1,q.2)
  let Y := fun q : (ι → MarkedCountPair) × Aux => (coupledPoissonCountingMeasure q.1,q.2)
  have hX : MeasurePreserving X γ ((rareCountingMeasureLaw μ p).prod ν) :=
    (coupledRareCountingMeasure_measurePreserving μ p).prod (MeasurePreserving.id ν)
  have hY : MeasurePreserving Y γ (((configurationLaw (∑ i, μ i)).map countingMeasure).prod ν) :=
    (coupledPoissonCountingMeasure_measurePreserving μ p hRate).prod (MeasurePreserving.id ν)
  have hLeft : (∫ q, ((f ∘ X) q)^2 ∂γ)≤IL := by
    have he := hX.hasLaw.integral_comp (hf.pow_const 2).aestronglyMeasurable
    exact he.trans_le hML
  have hRight : (∫ q, ((f ∘ Y) q)^2 ∂γ)≤IR := by
    have he := hY.hasLaw.integral_comp (hf.pow_const 2).aestronglyMeasurable
    exact he.trans_le hMR
  have hE : MeasurableSet (Prod.fst ⁻¹' (rareOfferMismatch (ι := ι)) : Set ((ι → MarkedCountPair) × Aux)) :=
    measurableSet_rareOfferMismatch.preimage measurable_fst
  have hBound := integral_sub_abs_le_of_eq_off_L2 γ (f ∘ X) (f ∘ Y)
    (hL.comp_measurePreserving hX) (hR.comp_measurePreserving hY) hLeft hRight _ hE
    (fun q hq => by
      have he := coupledCountingMeasures_eq_off q.1 hq
      change f (coupledRareCountingMeasure q.1,q.2)=f (coupledPoissonCountingMeasure q.1,q.2)
      rw [he])
  rw [hX.hasLaw.integral_comp hf.aestronglyMeasurable,hY.hasLaw.integral_comp hf.aestronglyMeasurable] at hBound
  apply hBound.trans
  have hFst : MeasurePreserving (Prod.fst : (ι → MarkedCountPair) × Aux → (ι → MarkedCountPair))
      γ (rareOfferCoupling μ p) := measurePreserving_fst
  have hMass := map_measureReal_apply (μ := γ) hFst.measurable measurableSet_rareOfferMismatch
  rw [hFst.map_eq] at hMass
  rw [← hMass]
  apply Real.sqrt_le_sqrt
  have hIL0 : 0≤IL := (integral_nonneg (fun q => sq_nonneg (f q))).trans hML
  have hIR0 : 0≤IR := (integral_nonneg (fun q => sq_nonneg (f q))).trans hMR
  exact mul_le_mul_of_nonneg_left (rareOfferCoupling_mismatch_le μ p) (by positivity)
end ProphetSecretary.Limiting
