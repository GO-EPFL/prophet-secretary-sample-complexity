import ProphetSecretary.Model.ThresholdExecutionContinuity
import ProphetSecretary.Model.ScalarBands
import ProphetSecretary.Model.ClippedOutcomeObservables

/-!
# Almost-everywhere continuity of actual finite canonical payoffs

For positive reward and duration weights, the proved acceptance-band bound
with width zero removes every actual value-threshold tie. Independent uniform
clocks remove arrival ties and terminal clock 1. The actual canonical reward
and duration are therefore continuous at almost every complete offer/clock
world, without any non-atomic offer assumption. This fixes the design law;
no continuity after reoptimizing a varying design law is asserted.
-/
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Topology Classical NNReal
namespace ProphetSecretary.Model
variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

lemma Instance.acceptance_gap_ne_zero_ae (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (ν : Measure Seed) [IsProbabilityMeasure ν]
    {w c : ℝ} (hw : 0 < w) (hc : 0 < c) :
    ∀ᵐ ω : World n Seed ∂P.worldLaw ν, ∀ i,
      w * ω.1 i - P.continuationAtArrival w c ω.1 ω.2.1 i ≠ 0 := by
  apply ae_all_iff.mpr
  intro i
  have hband := P.acceptanceBand_probability hP ν hw hc (δ := 0) le_rfl i
  have hzero : (P.worldLaw ν).real {ω : World n Seed |
      w * ω.1 i - P.continuationAtArrival w c ω.1 ω.2.1 i = 0} = 0 := by
    apply le_antisymm _ measureReal_nonneg
    simpa only [mul_zero,zero_div,abs_nonpos_iff] using hband
  have hnull := (measureReal_eq_zero_iff (measure_ne_top _ _)).mp hzero
  exact measure_eq_zero_iff_ae_notMem.mp hnull

lemma Instance.canonical_threshold_ties_null (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (ν : Measure Seed) [IsProbabilityMeasure ν]
    {w c : ℝ} (hw : 0 < w) (hc : 0 < c) :
    ∀ᵐ ω : World n Seed ∂P.worldLaw ν, ∀ i,
      ω.1 i ≠ P.valueThreshold w c (unseen (history Finset.univ ω.1 ω.2.1 (ω.2.1 i))) (ω.2.1 i) i := by
  filter_upwards [P.acceptance_gap_ne_zero_ae hP ν hw hc] with ω hω
  intro i hi
  apply hω i
  rw [P.continuationAtArrival_eq_threshold hw,hi,sub_self]

omit [MeasurableSpace Seed] in
lemma Instance.canonical_outcomes_continuousAt_regular (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c)
    (x u : Fin n → ℝ) (hu : Function.Injective u) (hterm : ∀ i, u i ≠ 1)
    (htie : ∀ i, x i ≠ P.valueThreshold w c (unseen (history Finset.univ x u (u i))) (u i) i) :
    ContinuousAt (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
      (P.valuePolicy hP hw hc).rule.reward () Finset.univ z.1 z.2) (x,u) ∧
    ContinuousAt (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
      (P.valuePolicy hP hw hc).rule.stoppingTime () Finset.univ z.1 z.2) (x,u) :=
  thresholdPolicy.outcomes_continuousAt (fun (_ : Unit) A t i => P.valueThreshold w c A t i) ()
    (P.valueThreshold_continuous hP hw hc) Finset.univ x u hu hterm htie

/-- Actual product-law AE continuity, with the optimizer's design law fixed. -/
theorem Instance.canonical_outcomes_continuousAt_ae (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (ν : Measure Seed) [IsProbabilityMeasure ν]
    {w c : ℝ} (hw : 0 < w) (hc : 0 < c) :
    ∀ᵐ ω : World n Seed ∂P.worldLaw ν,
      ContinuousAt (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
        (P.valuePolicy hP hw.le hc.le).rule.reward () Finset.univ z.1 z.2) (ω.1,ω.2.1) ∧
      ContinuousAt (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
        (P.valuePolicy hP hw.le hc.le).rule.stoppingTime () Finset.univ z.1 z.2) (ω.1,ω.2.1) := by
  have hterm : ∀ᵐ ω : World n Seed ∂P.worldLaw ν, ∀ i, ω.2.1 i ≠ 1 :=
    ae_all_iff.mpr fun i => (P.world_clock_measurePreserving ν i).quasiMeasurePreserving.ae (Instance.uniformClock.ae_ne 1)
  filter_upwards [P.world_clocks_distinct ν,hterm,P.canonical_threshold_ties_null hP ν hw hc] with ω hu ht hties
  exact P.canonical_outcomes_continuousAt_regular hP hw.le hc.le ω.1 ω.2.1 hu ht hties

omit [MeasurableSpace Seed] in
/-- Removing the independent unit factor gives the actual offer/clock product
law used for finite configuration convergence. -/
theorem Instance.canonical_outcomes_continuousAt_data_ae (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 < c) :
    ∀ᵐ z : (Fin n → ℝ) × (Fin n → ℝ) ∂P.valuesLaw.prod (Instance.clocksLaw n),
      ContinuousAt (fun y : (Fin n → ℝ) × (Fin n → ℝ) =>
        (P.valuePolicy hP hw.le hc.le).rule.reward () Finset.univ y.1 y.2) z ∧
      ContinuousAt (fun y : (Fin n → ℝ) × (Fin n → ℝ) =>
        (P.valuePolicy hP hw.le hc.le).rule.stoppingTime () Finset.univ y.1 y.2) z := by
  have hunit : MeasurePreserving (fun z : (Fin n → ℝ) × (Fin n → ℝ) => (z, ()))
      (P.valuesLaw.prod (Instance.clocksLaw n))
      ((P.valuesLaw.prod (Instance.clocksLaw n)).prod (Measure.dirac ())) := by
    refine ⟨by fun_prop,?_⟩
    rw [Measure.prod_dirac]
  have hMP := (measurePreserving_prodAssoc P.valuesLaw (Instance.clocksLaw n) (Measure.dirac ())).comp hunit
  exact hMP.quasiMeasurePreserving.ae (P.canonical_outcomes_continuousAt_ae hP (Measure.dirac ()) hw hc)

omit [MeasurableSpace Seed] in
/-- These observables satisfy the global bounds required by weak integral
transfer, and agree with actual payoffs under every cap-supported online law. -/
theorem Instance.canonical_bounded_observables_continuousAt_ae (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 < c) (H : ℝ≥0) :
    ∀ᵐ z : (Fin n → ℝ) × (Fin n → ℝ) ∂P.valuesLaw.prod (Instance.clocksLaw n),
      ContinuousAt ((P.valuePolicy hP hw.le hc.le).rule.boundedRewardObservable H () Finset.univ) z ∧
      ContinuousAt ((P.valuePolicy hP hw.le hc.le).rule.boundedDurationObservable () Finset.univ) z := by
  filter_upwards [P.canonical_outcomes_continuousAt_data_ae hP hw hc] with z hz
  exact ⟨(ProphetSecretary.Probability.boundedOfferValue H).continuous.continuousAt.comp hz.1,
    (ProphetSecretary.Probability.boundedOfferValue 1).continuous.continuousAt.comp hz.2⟩

/-- Lifting to complete worlds does not require continuity of any random seed:
the canonical rule uses its fixed unit seed and the lift ignores this factor. -/
theorem Instance.canonical_outcomes_continuousAt_world_ae [TopologicalSpace Seed] (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (ν : Measure Seed) [IsProbabilityMeasure ν]
    {w c : ℝ} (hw : 0 < w) (hc : 0 < c) :
    ∀ᵐ ω : World n Seed ∂P.worldLaw ν,
      ContinuousAt (fun z : World n Seed =>
        (P.valuePolicy hP hw.le hc.le).rule.reward () Finset.univ z.1 z.2.1) ω ∧
      ContinuousAt (fun z : World n Seed =>
        (P.valuePolicy hP hw.le hc.le).rule.stoppingTime () Finset.univ z.1 z.2.1) ω := by
  have hmap : Continuous (fun z : World n Seed => (z.1,z.2.1)) :=
    continuous_fst.prodMk (continuous_fst.comp continuous_snd)
  filter_upwards [P.canonical_outcomes_continuousAt_ae hP ν hw hc] with ω hω
  have hMapAt : ContinuousAt (fun z : World n Seed => (z.1,z.2.1)) ω := hmap.continuousAt
  exact ⟨ContinuousAt.comp (f := fun z : World n Seed => (z.1,z.2.1)) (x := ω) hω.1 hMapAt,
    ContinuousAt.comp (f := fun z : World n Seed => (z.1,z.2.1)) (x := ω) hω.2 hMapAt⟩

/-- Globally bounded clipping preserves the actual AE continuity, as needed
by weak almost-continuous integral transfer. Equality with raw payoffs on
cap-supported valid worlds is a separate pointwise range statement. -/
theorem Instance.canonical_clipped_outcomes_continuousAt_ae [TopologicalSpace Seed] (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (ν : Measure Seed) [IsProbabilityMeasure ν]
    {w c : ℝ} (hw : 0 < w) (hc : 0 < c) (H : ℝ≥0) :
    ∀ᵐ ω : World n Seed ∂P.worldLaw ν,
      ContinuousAt (fun z : World n Seed => ProphetSecretary.Probability.boundedOfferValue H
        ((P.valuePolicy hP hw.le hc.le).rule.reward () Finset.univ z.1 z.2.1)) ω ∧
      ContinuousAt (fun z : World n Seed => ProphetSecretary.Probability.boundedOfferValue 1
        ((P.valuePolicy hP hw.le hc.le).rule.stoppingTime () Finset.univ z.1 z.2.1)) ω := by
  filter_upwards [P.canonical_outcomes_continuousAt_world_ae hP ν hw hc] with ω hω
  exact ⟨(ProphetSecretary.Probability.boundedOfferValue H).continuous.continuousAt.comp hω.1,
    (ProphetSecretary.Probability.boundedOfferValue 1).continuous.continuousAt.comp hω.2⟩

end ProphetSecretary.Model
