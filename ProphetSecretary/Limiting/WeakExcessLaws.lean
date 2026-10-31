import ProphetSecretary.Limiting.RareMarginalPositivePart
import ProphetSecretary.Limiting.HybridExcessState
import ProphetSecretary.Model.WeakValueContinuity

/-!
# Continuous excess pushforwards before removing their zero atom

The full excess pushforward is weakly continuous. Its positive restriction
need not be; fixed rare offer laws nevertheless coincide by an actual zero
atom calculation. This distinction is used for fixed-terminal value limits.
-/
open MeasureTheory Set Filter
open scoped Topology NNReal Classical
namespace ProphetSecretary.Limiting
variable {n : ℕ}

lemma continuous_excessValueMap (a : ℝ) : Continuous (Model.excessValueMap a) := by
  unfold Model.excessValueMap
  fun_prop

noncomputable def fullExcessIntensity (μ : FiniteMeasure ℝ) (a : ℝ) : FiniteMeasure ℝ :=
  μ.map (Model.excessValueMap a)

lemma fullExcessIntensity_bounds (μ : FiniteMeasure ℝ) (a H : ℝ≥0)
    (hμ : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc (0 : ℝ) H) :
    ∀ᵐ y ∂(fullExcessIntensity μ a : Measure ℝ), y ∈ Icc (0 : ℝ) H := by
  change ∀ᵐ y ∂(μ : Measure ℝ).map (Model.excessValueMap a), y ∈ Icc (0 : ℝ) H
  apply (ae_map_iff (Model.measurable_excessValueMap a).aemeasurable measurableSet_Icc).mpr
  filter_upwards [hμ] with x hx
  refine ⟨Model.excessValueMap_nonnegative hx.1,?_⟩
  have hn : 0 ≤ min (a : ℝ) (max x 0) := le_min a.property (le_max_right _ _)
  change x-min (a : ℝ) (max x 0) ≤ (H : ℝ)
  linarith only [hx.2,hn]

lemma fullExcessIntensity_mass (μ : FiniteMeasure ℝ) (a : ℝ) : (fullExcessIntensity μ a).mass = μ.mass := by
  change μ.map (Model.excessValueMap a) univ = μ univ
  rw [FiniteMeasure.map_apply μ (continuous_excessValueMap a).measurable MeasurableSet.univ]
  rfl

lemma excessIntensity_eq_full_positiveRestriction (μ : FiniteMeasure ℝ) (a : ℝ) :
    excessIntensity μ a = (fullExcessIntensity μ a).restrict (Ioi 0) := by
  apply FiniteMeasure.toMeasure_injective
  rfl

lemma fullExcessIntensity_tendsto {Γ : Type*} {l : Filter Γ} {μs : Γ → FiniteMeasure ℝ}
    {μ : FiniteMeasure ℝ} (hweak : Tendsto μs l (𝓝 μ)) (a : ℝ) :
    Tendsto (fun m => fullExcessIntensity (μs m) a) l (𝓝 (fullExcessIntensity μ a)) :=
  FiniteMeasure.tendsto_map_of_tendsto_of_continuous μs μ hweak (continuous_excessValueMap a)

lemma excessOffers_coordinatewise_weak {Γ : Type*} {l : Filter Γ}
    (Ps : Γ → Model.Instance n) (P : Model.Instance n) (a : ℝ)
    (hweak : ∀ i, Tendsto (fun m => (Ps m).marginalProbabilityLaw i) l (𝓝 (P.marginalProbabilityLaw i))) :
    ∀ i, Tendsto (fun m => ((Ps m).excessOffers a).marginalProbabilityLaw i) l
      (𝓝 ((P.excessOffers a).marginalProbabilityLaw i)) := by
  intro i
  have h := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (fun m => (Ps m).marginalProbabilityLaw i) (P.marginalProbabilityLaw i) (hweak i) (continuous_excessValueMap a)
  convert h using 1
  · funext m
    apply Subtype.ext
    rfl
  · congr 1

end ProphetSecretary.Limiting
