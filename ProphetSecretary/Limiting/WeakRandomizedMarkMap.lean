import ProphetSecretary.Limiting.PoissonPayloadIntensity
import ProphetSecretary.Probability.WeakFiniteAlmostContinuousIntegral

/-!
# Almost-everywhere weakly continuous randomized mark images

A mark kernel is its actual independent-tag pushforward law. Testing the
image measure against a bounded continuous function gives a bounded
measurable function of the old mark. Almost-everywhere weak continuity of
the kernel supplies exactly the continuity needed by finite weak convergence.
-/
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Classical Topology
namespace ProphetSecretary.Limiting
variable {T : Type*} [MeasurableSpace T]

noncomputable def randomizedMarkKernel (κ : Measure T) [IsProbabilityMeasure κ]
    (Φ : ℝ × T → ℝ) (hΦ : Measurable Φ) (x : ℝ) : ProbabilityMeasure ℝ :=
  ⟨κ.map (fun t => Φ (x,t)),Measure.isProbabilityMeasure_map
    ((hΦ.comp (measurable_const.prodMk measurable_id)).aemeasurable)⟩

lemma integral_randomizedMarkKernel (κ : Measure T) [IsProbabilityMeasure κ]
    (Φ : ℝ × T → ℝ) (hΦ : Measurable Φ) (x : ℝ) (f : ℝ →ᵇ ℝ) :
    (∫ y, f y ∂(randomizedMarkKernel κ Φ hΦ x : Measure ℝ))=
      ∫ t, f (Φ (x,t)) ∂κ := by
  exact integral_map (hΦ.comp (measurable_const.prodMk measurable_id)).aemeasurable f.continuous.measurable.aestronglyMeasurable

lemma integral_displayedPayloadIntensity (μ : FiniteMeasure ℝ) (κ : Measure T) [IsProbabilityMeasure κ]
    (Φ : ℝ × T → ℝ) (hΦ : Measurable Φ) (f : ℝ →ᵇ ℝ) :
    (∫ y, f y ∂(displayedPayloadIntensity μ κ Φ hΦ : Measure ℝ))=
      ∫ x, (∫ t, f (Φ (x,t)) ∂κ) ∂(μ : Measure ℝ) := by
  rw [displayedPayloadIntensity_toMeasure,integral_map hΦ.aemeasurable f.continuous.measurable.aestronglyMeasurable]
  have hI : Integrable (fun z : ℝ × T => f (Φ z)) ((μ : Measure ℝ).prod κ) := by
    apply Integrable.of_bound (f.continuous.measurable.comp hΦ).aestronglyMeasurable ‖f‖
    exact Eventually.of_forall (fun z => f.norm_coe_le_norm (Φ z))
  exact integral_prod _ hI

theorem displayedPayloadIntensity_tendsto_of_weak_kernel {Γ : Type*} {l : Filter Γ}
    [l.IsCountablyGenerated] {μs : Γ → FiniteMeasure ℝ} {μ : FiniteMeasure ℝ}
    (hWeak : Tendsto μs l (𝓝 μ)) (κ : Measure T) [IsProbabilityMeasure κ]
    (Φ : ℝ × T → ℝ) (hΦ : Measurable Φ)
    (hKernel : ∀ᵐ x ∂(μ : Measure ℝ), ContinuousAt (randomizedMarkKernel κ Φ hΦ) x) :
    Tendsto (fun m => displayedPayloadIntensity (μs m) κ Φ hΦ) l
      (𝓝 (displayedPayloadIntensity μ κ Φ hΦ)) := by
  apply FiniteMeasure.tendsto_of_forall_integral_tendsto
  intro f
  let G := fun x : ℝ => ∫ t, f (Φ (x,t)) ∂κ
  have hG : Measurable G := (f.continuous.measurable.comp hΦ).stronglyMeasurable.integral_prod_right'.measurable
  have hBound (x : ℝ) : |G x|≤‖f‖ := by
    have h := norm_integral_le_of_norm_le_const (μ := κ) (f := fun t => f (Φ (x,t)))
      (Eventually.of_forall (fun t => f.norm_coe_le_norm (Φ (x,t))))
    simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using h
  have hContinuous : ∀ᵐ x ∂(μ : Measure ℝ), ContinuousAt G x := by
    filter_upwards [hKernel] with x hx
    have h := (ProbabilityMeasure.continuous_integral_boundedContinuousFunction f).continuousAt.comp hx
    have hEq : (fun x => ∫ y, f y ∂(randomizedMarkKernel κ Φ hΦ x : Measure ℝ))=G :=
      funext (fun x => integral_randomizedMarkKernel κ Φ hΦ x f)
    simp only [Function.comp_def] at h
    rwa [hEq] at h
  have h := ProphetSecretary.Probability.finite_integral_tendsto_of_weak_ae_continuous_bounded
    hWeak hG hBound hContinuous
  simp_rw [integral_displayedPayloadIntensity]
  exact h

end ProphetSecretary.Limiting
