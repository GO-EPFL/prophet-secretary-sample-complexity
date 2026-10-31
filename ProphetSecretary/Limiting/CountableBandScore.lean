import ProphetSecretary.Limiting.CountableBandLikelihood
import ProphetSecretary.Probability.PoissonCenteredScore

/-!
# Actual complete band count and centered likelihood score

For a measurable band bounded away from the reserve, the full count has its
proved Poisson law under every independent auxiliary seed. The centered score
has mean zero, lies in L², and has exact information μ(S). Counts after stopping
remain part of this analytical random variable.
-/

open MeasureTheory ProbabilityTheory Set
open scoped Classical NNReal

namespace ProphetSecretary.Limiting.CountableInstance

noncomputable def completeBandCount {Seed : Type*} (S : Set ℝ) (v : CompleteWorld Seed) : ℕ :=
  bandPointCount (univ ×ˢ S) v.1

noncomputable def bandRate (B : CountableInstance) (S : Set ℝ) : ℝ≥0 := (B.intensity S).toNNReal

lemma bandRate_coe (B : CountableInstance) (S : Set ℝ) : (B.bandRate S : ℝ)=B.intensity.real S := rfl

noncomputable def bandScore (B : CountableInstance) {Seed : Type*} (S : Set ℝ)
    (v : CompleteWorld Seed) : ℝ :=
  ProphetSecretary.Probability.poissonCenteredScore (B.bandRate S) (completeBandCount S v)

lemma bandScore_eq (B : CountableInstance) {Seed : Type*} (S : Set ℝ) (v : CompleteWorld Seed) :
    B.bandScore S v=(completeBandCount S v : ℝ)-B.intensity.real S := rfl

lemma intensity_band_finite (B : CountableInstance) {S : Set ℝ} {b : ℝ}
    (hb : (B.terminal : ℝ) < b) (hSub : S ⊆ Ioi b) : B.intensity S < ⊤ :=
  (measure_mono hSub).trans_lt (B.intensity_tail_finite b hb)

lemma measurable_completeBandCount {Seed : Type*} [MeasurableSpace Seed] {S : Set ℝ}
    (hS : MeasurableSet S) : Measurable (completeBandCount (Seed := Seed) S) :=
  (measurable_bandPointCount (MeasurableSet.univ.prod hS)).comp measurable_fst

lemma measurable_bandScore (B : CountableInstance) {Seed : Type*} [MeasurableSpace Seed]
    {S : Set ℝ} (hS : MeasurableSet S) : Measurable (B.bandScore (Seed := Seed) S) :=
  (ProphetSecretary.Probability.measurable_poissonCenteredScore (B.bandRate S)).comp (measurable_completeBandCount hS)

theorem completeBandCount_hasLaw (B : CountableInstance) {S : Set ℝ} (hS : MeasurableSet S)
    {b : ℝ} (hb : (B.terminal : ℝ) < b) (hSub : S ⊆ Ioi b)
    {Seed : Type*} [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν] :
    HasLaw (completeBandCount S) (poissonMeasure (B.bandRate S)) (B.completeWorldLaw ν) := by
  have hCount := B.bandPointCount_hasLaw hb (MeasurableSet.univ.prod hS) (fun p hp => ⟨hp.1,hSub hp.2⟩)
  have hMP : MeasurePreserving (Prod.fst : CompleteWorld Seed → BandConfigurations)
      (B.completeWorldLaw ν) B.bandConfigurationsLaw := measurePreserving_fst
  have h := hCount.fun_comp hMP.hasLaw
  change HasLaw (fun v : CompleteWorld Seed => bandPointCount (univ ×ˢ S) v.1)
    (poissonMeasure (B.bandRate S)) (B.completeWorldLaw ν)
  simpa only [poissonRegionRate,bandRate,Measure.prod_prod,measure_univ,one_mul,Function.comp_def] using h

lemma completeBandCount_measurePreserving (B : CountableInstance) {S : Set ℝ} (hS : MeasurableSet S)
    {b : ℝ} (hb : (B.terminal : ℝ) < b) (hSub : S ⊆ Ioi b)
    {Seed : Type*} [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν] :
    MeasurePreserving (completeBandCount S) (B.completeWorldLaw ν) (poissonMeasure (B.bandRate S)) :=
  ⟨measurable_completeBandCount hS,(B.completeBandCount_hasLaw hS hb hSub ν).map_eq⟩

lemma integrable_bandScore (B : CountableInstance) {S : Set ℝ} (hS : MeasurableSet S)
    {b : ℝ} (hb : (B.terminal : ℝ) < b) (hSub : S ⊆ Ioi b)
    {Seed : Type*} [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν] :
    Integrable (B.bandScore S) (B.completeWorldLaw ν) :=
  (B.completeBandCount_measurePreserving hS hb hSub ν).integrable_comp_of_integrable
    (ProphetSecretary.Probability.integrable_poissonCenteredScore (B.bandRate S))

lemma bandScore_mean_zero (B : CountableInstance) {S : Set ℝ} (hS : MeasurableSet S)
    {b : ℝ} (hb : (B.terminal : ℝ) < b) (hSub : S ⊆ Ioi b)
    {Seed : Type*} [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν] :
    (∫ v, B.bandScore S v ∂B.completeWorldLaw ν)=0 :=
  ((B.completeBandCount_hasLaw hS hb hSub ν).integral_comp
    (ProphetSecretary.Probability.measurable_poissonCenteredScore (B.bandRate S)).aestronglyMeasurable).trans
      (ProphetSecretary.Probability.integral_poissonCenteredScore (B.bandRate S))

lemma bandScore_memLp_two (B : CountableInstance) {S : Set ℝ} (hS : MeasurableSet S)
    {b : ℝ} (hb : (B.terminal : ℝ) < b) (hSub : S ⊆ Ioi b)
    {Seed : Type*} [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν] :
    MemLp (B.bandScore S) 2 (B.completeWorldLaw ν) :=
  (ProphetSecretary.Probability.poissonCenteredScore_memLp_two (B.bandRate S)).comp_measurePreserving
    (B.completeBandCount_measurePreserving hS hb hSub ν)

lemma bandScore_information (B : CountableInstance) {S : Set ℝ} (hS : MeasurableSet S)
    {b : ℝ} (hb : (B.terminal : ℝ) < b) (hSub : S ⊆ Ioi b)
    {Seed : Type*} [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν] :
    (∫ v, (B.bandScore S v)^2 ∂B.completeWorldLaw ν)=B.intensity.real S := by
  have h := (B.completeBandCount_hasLaw hS hb hSub ν).integral_comp
    ((measurable_of_countable (fun n : ℕ => (ProphetSecretary.Probability.poissonCenteredScore (B.bandRate S) n)^2))).aestronglyMeasurable
  exact h.trans (ProphetSecretary.Probability.integral_poissonCenteredScore_sq (B.bandRate S))

end ProphetSecretary.Limiting.CountableInstance
