import ProphetSecretary.Limiting.CountableBandScore
import ProphetSecretary.Limiting.CountablePolicyLawTransport

/-!
# Fixed full policies along a band-intensity likelihood path

The actual complete-world density is positive on the stated neighborhood.
Mutual absolute continuity transports the unrestricted observable policy
class, retaining every independent auxiliary law and every observed identity.
-/

open MeasureTheory Set Filter
open scoped Classical NNReal ENNReal

namespace ProphetSecretary.Limiting
open CountableInstance

namespace CountableInstance

private lemma quarter_unit_add_pos {θ : ℝ} (hθ : |θ| ≤ 1/4) : 0 < 1+θ := by
  have h := (abs_le.mp hθ).1
  linarith only [h]

lemma bandScalingLikelihood_positive (B : CountableInstance) (S : Set ℝ)
    {r : ℝ≥0} (hr : 0 < r) (ω : BandConfigurations) : 0 < B.bandScalingLikelihood S r ω := by
  unfold bandScalingLikelihood
  exact mul_pos (Real.exp_pos _) (pow_pos hr _)

lemma scaleBand_absolutelyContinuous (B : CountableInstance) {S : Set ℝ} (hS : MeasurableSet S)
    {b : ℝ} (hb : (B.terminal : ℝ) < b) (hSub : S ⊆ Ioi b) {r : ℝ≥0} (hr : 0 < r)
    {Seed : Type*} [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν] :
    (B.scaleBand S r).completeWorldLaw ν ≪ B.completeWorldLaw ν := by
  rw [B.completeWorldLaw_scaleBand_withDensity hS hb hSub hr ν]
  exact withDensity_absolutelyContinuous _ _

lemma absolutelyContinuous_scaleBand (B : CountableInstance) {S : Set ℝ} (hS : MeasurableSet S)
    {b : ℝ} (hb : (B.terminal : ℝ) < b) (hSub : S ⊆ Ioi b) {r : ℝ≥0} (hr : 0 < r)
    {Seed : Type*} [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν] :
    B.completeWorldLaw ν ≪ (B.scaleBand S r).completeWorldLaw ν := by
  rw [B.completeWorldLaw_scaleBand_withDensity hS hb hSub hr ν]
  have hDensity : Measurable (fun v : CompleteWorld Seed => ENNReal.ofReal (B.bandScalingLikelihood S r v.1)) :=
    ENNReal.measurable_ofReal.comp ((B.measurable_bandScalingLikelihood hS r).comp measurable_fst)
  apply withDensity_absolutelyContinuous' hDensity.aemeasurable
  exact Eventually.of_forall (fun v => ENNReal.ofReal_ne_zero_iff.mpr (B.bandScalingLikelihood_positive S hr v.1))

noncomputable def bandLikelihoodPath (B : CountableInstance) (S : Set ℝ) (θ : ℝ) : CountableInstance :=
  if hθ : |θ| ≤ 1/4 then B.scaleBand S ⟨1+θ,(quarter_unit_add_pos hθ).le⟩ else B

lemma bandLikelihoodPath_of_mem (B : CountableInstance) (S : Set ℝ) {θ : ℝ} (hθ : |θ| ≤ 1/4) :
    B.bandLikelihoodPath S θ=B.scaleBand S ⟨1+θ,(quarter_unit_add_pos hθ).le⟩ := dif_pos hθ

lemma bandLikelihoodPath_zero (B : CountableInstance) (S : Set ℝ) : B.bandLikelihoodPath S 0=B := by
  have h0 : |(0 : ℝ)| ≤ 1/4 := by norm_num
  rw [B.bandLikelihoodPath_of_mem S h0]
  have hCoefficient : (⟨1+(0 : ℝ),(quarter_unit_add_pos h0).le⟩ : ℝ≥0)=1 := by
    apply Subtype.ext
    change (1 : ℝ)+0=1
    ring
  rw [hCoefficient]
  exact B.scaleBand_one S

lemma bandLikelihoodPath_absolutelyContinuous (B : CountableInstance) {S : Set ℝ} (hS : MeasurableSet S)
    {b : ℝ} (hb : (B.terminal : ℝ) < b) (hSub : S ⊆ Ioi b) (θ : ℝ)
    {Seed : Type*} [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν] :
    (B.bandLikelihoodPath S θ).completeWorldLaw ν ≪ B.completeWorldLaw ν := by
  by_cases hθ : |θ| ≤ 1/4
  · rw [B.bandLikelihoodPath_of_mem S hθ]
    exact B.scaleBand_absolutelyContinuous hS hb hSub (quarter_unit_add_pos hθ) ν
  · simp only [bandLikelihoodPath,dif_neg hθ]
    exact fun _ hs => hs

lemma absolutelyContinuous_bandLikelihoodPath (B : CountableInstance) {S : Set ℝ} (hS : MeasurableSet S)
    {b : ℝ} (hb : (B.terminal : ℝ) < b) (hSub : S ⊆ Ioi b) (θ : ℝ)
    {Seed : Type*} [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν] :
    B.completeWorldLaw ν ≪ (B.bandLikelihoodPath S θ).completeWorldLaw ν := by
  by_cases hθ : |θ| ≤ 1/4
  · rw [B.bandLikelihoodPath_of_mem S hθ]
    exact B.absolutelyContinuous_scaleBand hS hb hSub (quarter_unit_add_pos hθ) ν
  · simp only [bandLikelihoodPath,dif_neg hθ]
    exact fun _ hs => hs

end CountableInstance

noncomputable def RandomizedCountablePolicy.bandLikelihoodPolicy {B : CountableInstance}
    (π : RandomizedCountablePolicy B) {S : Set ℝ} (hS : MeasurableSet S)
    {b : ℝ} (hb : (B.terminal : ℝ) < b) (hSub : S ⊆ Ioi b) (θ : ℝ) :
    RandomizedCountablePolicy (B.bandLikelihoodPath S θ) :=
  π.changeInstance (B.bandLikelihoodPath S θ) (B.bandLikelihoodPath_absolutelyContinuous hS hb hSub θ π.seedLaw)

noncomputable def RandomizedCountablePolicy.scalarBandLikelihoodDerivative {B : CountableInstance}
    (π : RandomizedCountablePolicy B) (S : Set ℝ) (w c : ℝ) : ℝ :=
  ∫ v, π.scalarPayoff w c v*B.bandScore S v ∂B.completeWorldLaw π.seedLaw

lemma RandomizedCountablePolicy.integrable_scalarBandLikelihood {B : CountableInstance}
    (π : RandomizedCountablePolicy B) {S : Set ℝ} (hS : MeasurableSet S)
    {b : ℝ} (hb : (B.terminal : ℝ) < b) (hSub : S ⊆ Ioi b) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    Integrable (fun v => π.scalarPayoff w c v*B.bandScore S v) (B.completeWorldLaw π.seedLaw) := by
  have h := (B.integrable_bandScore hS hb hSub π.seedLaw).mul_bdd
    (π.measurable_scalarPayoff w c).aestronglyMeasurable
    ((π.scalarPayoff_bounded hw hc).mono (fun v hv => by rw [Real.norm_eq_abs,abs_of_nonneg hv.1]; exact hv.2))
  apply h.congr
  exact Eventually.of_forall (fun v => mul_comm _ _)

end ProphetSecretary.Limiting
