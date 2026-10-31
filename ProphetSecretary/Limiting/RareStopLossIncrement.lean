import ProphetSecretary.Limiting.RareMarginalNormalization
import ProphetSecretary.Probability.WeakStopLoss

/-!
# Stop-loss increments from added finite mark intensity

The common rare-offer multiplicity is fixed. Its zero-atom compensation makes
the stop-loss increment the centered premium integral of the added intensity,
divided by that multiplicity. Nonnegative marks bound it by their first moment.
-/
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Topology NNReal Classical
namespace ProphetSecretary.Limiting
open ProphetSecretary.Probability

lemma finiteMeasure_mass_le_add (μ ρ : FiniteMeasure ℝ) : μ.mass ≤ (μ+ρ).mass := by
  change μ univ ≤ (μ+ρ) univ
  rw [FiniteMeasure.coeFn_add,Pi.add_apply]
  exact le_add_of_nonneg_right (by positivity)

lemma integral_rareProbabilityLaw_centered (μ : FiniteMeasure ℝ) (q : ℝ≥0) (hq : 0 < q) (hm : μ.mass ≤ q)
    (f : ℝ →ᵇ ℝ) :
    (∫ x, f x ∂(rareProbabilityLaw μ q hq hm : Measure ℝ)) =
      f 0+(q : ℝ)⁻¹*(∫ x, f x-f 0 ∂(μ : Measure ℝ)) := by
  rw [integral_rareProbabilityLaw]
  rw [integral_sub (f.integrable _) (integrable_const _),integral_const]
  rfl

lemma boundedStopLossTest_centered_bounds (H : ℝ≥0) (b x : ℝ) :
    0 ≤ boundedStopLossTest H b x-boundedStopLossTest H b 0 ∧
      boundedStopLossTest H b x-boundedStopLossTest H b 0 ≤ boundedOfferValue H x := by
  have h0 : boundedOfferValue H 0 = 0 := boundedOfferValue_eq H ⟨le_rfl,H.property⟩
  change 0 ≤ max 0 (boundedOfferValue H x-b)-max 0 (boundedOfferValue H 0-b) ∧
    max 0 (boundedOfferValue H x-b)-max 0 (boundedOfferValue H 0-b) ≤ boundedOfferValue H x
  rw [h0,zero_sub]
  have hv := (boundedOfferValue_mem_range H x).1
  have hlow : max 0 (-b) ≤ max 0 (boundedOfferValue H x-b) := max_le_max_left 0 (by linarith)
  have hu : max 0 (boundedOfferValue H x-b) ≤ max 0 (-b)+boundedOfferValue H x := by
    apply max_le
    · exact add_nonneg (le_max_left _ _) hv
    · linarith [le_max_right 0 (-b)]
  constructor <;> linarith

/-- The exact common-multiplicity increment is nonnegative and bounded by
q^{-1} times the added first moment, uniformly over every real threshold. -/
theorem rareProbabilityLaw_stopLoss_add_bounds (μ ρ : FiniteMeasure ℝ) (H : ℝ≥0)
    (hμ : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc (0 : ℝ) H)
    (hρ : ∀ᵐ x ∂(ρ : Measure ℝ), x ∈ Icc (0 : ℝ) H)
    (q : ℝ≥0) (hq : 0 < q) (hm : (μ+ρ).mass ≤ q) (b : ℝ) :
    let hmμ := (finiteMeasure_mass_le_add μ ρ).trans hm
    0 ≤ Model.stopLoss (rareProbabilityLaw (μ+ρ) q hq hm : Measure ℝ) b-
      Model.stopLoss (rareProbabilityLaw μ q hq hmμ : Measure ℝ) b ∧
    Model.stopLoss (rareProbabilityLaw (μ+ρ) q hq hm : Measure ℝ) b-
      Model.stopLoss (rareProbabilityLaw μ q hq hmμ : Measure ℝ) b ≤ (q : ℝ)⁻¹*(∫ x, x ∂(ρ : Measure ℝ)) := by
  let hmμ := (finiteMeasure_mass_le_add μ ρ).trans hm
  have hsum : ∀ᵐ x ∂((μ+ρ : FiniteMeasure ℝ) : Measure ℝ), x ∈ Icc (0 : ℝ) H := by
    change ∀ᵐ x ∂((μ : Measure ℝ)+(ρ : Measure ℝ)), x ∈ Icc (0 : ℝ) H
    exact ae_add_measure_iff.mpr ⟨hμ,hρ⟩
  have hfμ := (boundedStopLossTest H b).integrable (μ : Measure ℝ)
  have hfρ := (boundedStopLossTest H b).integrable (ρ : Measure ℝ)
  have hIρ : Integrable (fun x : ℝ => x) (ρ : Measure ℝ) := by
    apply Integrable.of_bound aestronglyMeasurable_id H
    exact hρ.mono fun x hx => by simpa only [id_eq,Real.norm_eq_abs,abs_of_nonneg hx.1] using hx.2
  have hcμ : Integrable (fun x : ℝ => boundedStopLossTest H b x-boundedStopLossTest H b 0) (μ : Measure ℝ) := hfμ.sub (integrable_const _)
  have hcρ : Integrable (fun x : ℝ => boundedStopLossTest H b x-boundedStopLossTest H b 0) (ρ : Measure ℝ) := hfρ.sub (integrable_const _)
  have hEq : Model.stopLoss (rareProbabilityLaw (μ+ρ) q hq hm : Measure ℝ) b-
      Model.stopLoss (rareProbabilityLaw μ q hq hmμ : Measure ℝ) b =
      (q : ℝ)⁻¹*(∫ x, boundedStopLossTest H b x-boundedStopLossTest H b 0 ∂(ρ : Measure ℝ)) := by
    rw [← clippedStopLoss_eq_stopLoss (rareProbabilityLaw (μ+ρ) q hq hm) H
        (rareProbabilityLaw_bounds _ H hsum q hq hm) b,
      ← clippedStopLoss_eq_stopLoss (rareProbabilityLaw μ q hq hmμ) H
        (rareProbabilityLaw_bounds _ H hμ q hq hmμ) b]
    unfold clippedStopLoss
    rw [integral_rareProbabilityLaw_centered,integral_rareProbabilityLaw_centered]
    change (_+(q : ℝ)⁻¹*(∫ x, _ ∂((μ : Measure ℝ)+(ρ : Measure ℝ))))-_ = _
    rw [integral_add_measure hcμ hcρ]
    ring
  have hlow : 0 ≤ ∫ x, boundedStopLossTest H b x-boundedStopLossTest H b 0 ∂(ρ : Measure ℝ) :=
    integral_nonneg fun x => (boundedStopLossTest_centered_bounds H b x).1
  have hu : (∫ x, boundedStopLossTest H b x-boundedStopLossTest H b 0 ∂(ρ : Measure ℝ)) ≤ ∫ x, x ∂(ρ : Measure ℝ) := by
    apply integral_mono_ae hcρ hIρ
    filter_upwards [hρ] with x hx
    exact (boundedStopLossTest_centered_bounds H b x).2.trans_eq (boundedOfferValue_eq H hx)
  dsimp only
  rw [hEq]
  exact ⟨mul_nonneg (inv_nonneg.mpr q.property) hlow,mul_le_mul_of_nonneg_left hu (inv_nonneg.mpr q.property)⟩

end ProphetSecretary.Limiting
