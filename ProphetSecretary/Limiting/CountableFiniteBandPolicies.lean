import ProphetSecretary.Limiting.CountableFiniteBandScore
import ProphetSecretary.Limiting.CountableBandPolicies

/-!
# Common unrestricted policies for every finite-intensity mark set

The actual whole-product likelihood is positive on the quarter interval.
Mutual absolute continuity preserves admissibility of the same observable
callbacks and arbitrary independent auxiliary seed, even when the affected
set meets infinitely many construction bands near the reserve.
-/
open MeasureTheory Set Filter
open scoped Classical NNReal ENNReal
namespace ProphetSecretary.Limiting
open CountableInstance
namespace CountableInstance

private lemma finiteBandParameter_positive {θ : ℝ} (hθ : |θ|≤1/4) : 0<1+θ := by
  linarith only [(abs_le.mp hθ).1]

lemma scaleBand_absolutelyContinuous_of_finite (B : CountableInstance) {S : Set ℝ}
    (hS : MeasurableSet S) (hFinite : B.intensity S<⊤) {r : ℝ≥0} (hr : 0<r)
    {Seed : Type*} [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν] :
    (B.scaleBand S r).completeWorldLaw ν≪B.completeWorldLaw ν := by
  rw [B.completeWorldLaw_scaleBand_withDensity_of_finite hS hFinite hr ν]
  exact withDensity_absolutelyContinuous _ _

lemma absolutelyContinuous_scaleBand_of_finite (B : CountableInstance) {S : Set ℝ}
    (hS : MeasurableSet S) (hFinite : B.intensity S<⊤) {r : ℝ≥0} (hr : 0<r)
    {Seed : Type*} [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν] :
    B.completeWorldLaw ν≪(B.scaleBand S r).completeWorldLaw ν := by
  rw [B.completeWorldLaw_scaleBand_withDensity_of_finite hS hFinite hr ν]
  have hDensity : Measurable (fun v : CompleteWorld Seed => ENNReal.ofReal (B.bandScalingLikelihood S r v.1)) :=
    ENNReal.measurable_ofReal.comp ((B.measurable_bandScalingLikelihood hS r).comp measurable_fst)
  apply withDensity_absolutelyContinuous' hDensity.aemeasurable
  exact Eventually.of_forall (fun v => ENNReal.ofReal_ne_zero_iff.mpr (B.bandScalingLikelihood_positive S hr v.1))

lemma bandLikelihoodPath_absolutelyContinuous_of_finite (B : CountableInstance) {S : Set ℝ}
    (hS : MeasurableSet S) (hFinite : B.intensity S<⊤) (θ : ℝ)
    {Seed : Type*} [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν] :
    (B.bandLikelihoodPath S θ).completeWorldLaw ν≪B.completeWorldLaw ν := by
  by_cases hθ : |θ|≤1/4
  · rw [B.bandLikelihoodPath_of_mem S hθ]
    exact B.scaleBand_absolutelyContinuous_of_finite hS hFinite (finiteBandParameter_positive hθ) ν
  · simp only [bandLikelihoodPath,dif_neg hθ]
    exact fun _ hs => hs

lemma absolutelyContinuous_bandLikelihoodPath_of_finite (B : CountableInstance) {S : Set ℝ}
    (hS : MeasurableSet S) (hFinite : B.intensity S<⊤) (θ : ℝ)
    {Seed : Type*} [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν] :
    B.completeWorldLaw ν≪(B.bandLikelihoodPath S θ).completeWorldLaw ν := by
  by_cases hθ : |θ|≤1/4
  · rw [B.bandLikelihoodPath_of_mem S hθ]
    exact B.absolutelyContinuous_scaleBand_of_finite hS hFinite (finiteBandParameter_positive hθ) ν
  · simp only [bandLikelihoodPath,dif_neg hθ]
    exact fun _ hs => hs
end CountableInstance

noncomputable def RandomizedCountablePolicy.finiteBandLikelihoodPolicy {B : CountableInstance}
    (π : RandomizedCountablePolicy B) {S : Set ℝ} (hS : MeasurableSet S) (hFinite : B.intensity S<⊤)
    (θ : ℝ) : RandomizedCountablePolicy (B.bandLikelihoodPath S θ) :=
  π.changeInstance (B.bandLikelihoodPath S θ) (B.bandLikelihoodPath_absolutelyContinuous_of_finite hS hFinite θ π.seedLaw)

lemma RandomizedCountablePolicy.integrable_scalarBandLikelihood_of_finite {B : CountableInstance}
    (π : RandomizedCountablePolicy B) {S : Set ℝ} (hS : MeasurableSet S) (hFinite : B.intensity S<⊤)
    {w c : ℝ} (hw : 0≤w) (hc : 0≤c) :
    Integrable (fun v => π.scalarPayoff w c v*B.bandScore S v) (B.completeWorldLaw π.seedLaw) := by
  have h := (B.integrable_bandScore_of_finite hS hFinite π.seedLaw).mul_bdd
    (π.measurable_scalarPayoff w c).aestronglyMeasurable
    ((π.scalarPayoff_bounded hw hc).mono (fun v hv => by rw [Real.norm_eq_abs,abs_of_nonneg hv.1]; exact hv.2))
  apply h.congr
  exact Eventually.of_forall (fun v => mul_comm _ _)
end ProphetSecretary.Limiting
