import ProphetSecretary.Limiting.CountableScalarObjectives

/-!
# An individual's analytical likelihood score

The score evaluates the complete realized value coordinate, including offers
arriving after stopping. The actual product law gives its marginal, mean and
bounds independently of every auxiliary policy seed.
-/

open MeasureTheory Set

namespace ProphetSecretary.Limiting.CountableInstance

lemma individualValue_completeWorld_measurePreserving (B : CountableInstance)
    {Seed : Type*} [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν] (i : ℕ) :
    MeasurePreserving (fun v : CompleteWorld Seed => v.2.1 i) (B.completeWorldLaw ν)
      (B.individuals i : Measure ℝ) :=
  (B.individualValue_measurePreserving i).comp (measurePreserving_fst.comp measurePreserving_snd)

lemma measurable_individualScore {Seed : Type*} [MeasurableSpace Seed]
    (i : ℕ) {h : ℝ → ℝ} (hh : Measurable h) :
    Measurable (fun v : CompleteWorld Seed => h (v.2.1 i)) :=
  hh.comp ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd))

lemma individualScore_bounded_ae (B : CountableInstance) {Seed : Type*} [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν] (i : ℕ) {h : ℝ → ℝ}
    (hb : ∀ᵐ x ∂(B.individuals i : Measure ℝ), |h x| ≤ 1) :
    ∀ᵐ v ∂B.completeWorldLaw ν, |h (v.2.1 i)| ≤ 1 :=
  (B.individualValue_completeWorld_measurePreserving ν i).quasiMeasurePreserving.ae hb

lemma individualScore_mean_zero (B : CountableInstance) {Seed : Type*} [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν] (i : ℕ) {h : ℝ → ℝ}
    (hh : Measurable h) (hm : ∫ x, h x ∂(B.individuals i : Measure ℝ)=0) :
    (∫ v, h (v.2.1 i) ∂B.completeWorldLaw ν)=0 :=
  ((B.individualValue_completeWorld_measurePreserving ν i).hasLaw.integral_comp hh.aestronglyMeasurable).trans hm

end ProphetSecretary.Limiting.CountableInstance
