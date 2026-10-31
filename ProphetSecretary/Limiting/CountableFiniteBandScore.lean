import ProphetSecretary.Limiting.CountableFiniteBandLikelihood
import ProphetSecretary.Limiting.CountableBandScore

/-!
# Complete scores for every finite-intensity mark set

The set may accumulate at the reserve and need not meet only finitely many
construction bands. The actual complete count has its Poisson law. Its
centered score has mean zero, lies in L², and has information exactly μ(S),
including μ(S)=0. The complete count is analytical, not policy information.
-/

open MeasureTheory ProbabilityTheory Set
open scoped Classical NNReal
namespace ProphetSecretary.Limiting.CountableInstance

theorem completeBandCount_hasLaw_of_finite (B : CountableInstance) {S : Set ℝ}
    (hS : MeasurableSet S) (hFinite : B.intensity S<⊤)
    {Seed : Type*} [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν] :
    HasLaw (completeBandCount S) (poissonMeasure (B.bandRate S)) (B.completeWorldLaw ν) := by
  have hCount := B.bandPointCount_hasLaw_of_finite_region (MeasurableSet.univ.prod hS) (B.fullTime_region_finite hFinite)
  have hMP : MeasurePreserving (Prod.fst : CompleteWorld Seed → BandConfigurations)
      (B.completeWorldLaw ν) B.bandConfigurationsLaw := measurePreserving_fst
  have h := hCount.fun_comp hMP.hasLaw
  change HasLaw (fun v : CompleteWorld Seed => bandPointCount (univ ×ˢ S) v.1)
    (poissonMeasure (B.bandRate S)) (B.completeWorldLaw ν)
  simpa only [poissonRegionRate,bandRate,Measure.prod_prod,measure_univ,one_mul,Function.comp_def] using h

lemma completeBandCount_measurePreserving_of_finite (B : CountableInstance) {S : Set ℝ}
    (hS : MeasurableSet S) (hFinite : B.intensity S<⊤)
    {Seed : Type*} [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν] :
    MeasurePreserving (completeBandCount S) (B.completeWorldLaw ν) (poissonMeasure (B.bandRate S)) :=
  ⟨measurable_completeBandCount hS,(B.completeBandCount_hasLaw_of_finite hS hFinite ν).map_eq⟩

lemma integrable_bandScore_of_finite (B : CountableInstance) {S : Set ℝ}
    (hS : MeasurableSet S) (hFinite : B.intensity S<⊤)
    {Seed : Type*} [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν] :
    Integrable (B.bandScore S) (B.completeWorldLaw ν) :=
  (B.completeBandCount_measurePreserving_of_finite hS hFinite ν).integrable_comp_of_integrable
    (ProphetSecretary.Probability.integrable_poissonCenteredScore (B.bandRate S))

lemma bandScore_mean_zero_of_finite (B : CountableInstance) {S : Set ℝ}
    (hS : MeasurableSet S) (hFinite : B.intensity S<⊤)
    {Seed : Type*} [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν] :
    (∫ v, B.bandScore S v ∂B.completeWorldLaw ν)=0 :=
  ((B.completeBandCount_hasLaw_of_finite hS hFinite ν).integral_comp
    (ProphetSecretary.Probability.measurable_poissonCenteredScore (B.bandRate S)).aestronglyMeasurable).trans
      (ProphetSecretary.Probability.integral_poissonCenteredScore (B.bandRate S))

lemma bandScore_memLp_two_of_finite (B : CountableInstance) {S : Set ℝ}
    (hS : MeasurableSet S) (hFinite : B.intensity S<⊤)
    {Seed : Type*} [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν] :
    MemLp (B.bandScore S) 2 (B.completeWorldLaw ν) :=
  (ProphetSecretary.Probability.poissonCenteredScore_memLp_two (B.bandRate S)).comp_measurePreserving
    (B.completeBandCount_measurePreserving_of_finite hS hFinite ν)

lemma bandScore_information_of_finite (B : CountableInstance) {S : Set ℝ}
    (hS : MeasurableSet S) (hFinite : B.intensity S<⊤)
    {Seed : Type*} [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν] :
    (∫ v, (B.bandScore S v)^2 ∂B.completeWorldLaw ν)=B.intensity.real S := by
  have h := (B.completeBandCount_hasLaw_of_finite hS hFinite ν).integral_comp
    ((measurable_of_countable (fun n : ℕ => (ProphetSecretary.Probability.poissonCenteredScore (B.bandRate S) n)^2))).aestronglyMeasurable
  exact h.trans (ProphetSecretary.Probability.integral_poissonCenteredScore_sq (B.bandRate S))

end ProphetSecretary.Limiting.CountableInstance
