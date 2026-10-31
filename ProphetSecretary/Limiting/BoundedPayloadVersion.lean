import ProphetSecretary.Limiting.CountableCutoffPayload
import ProphetSecretary.Limiting.ResidualPayloadInstance
import ProphetSecretary.Limiting.CountableRemainingState

/-!
# Bounded versions of randomized mark kernels

Clipping the output into the certified target interval is continuous. It
preserves almost-everywhere weak kernel continuity and agrees with the
original map on every actual law where its image already lies in that
interval. Thus the limiting intensity and the bounded finite approximations
can use one globally bounded measurable version.
-/
open MeasureTheory Set Filter
open scoped Classical Topology NNReal
namespace ProphetSecretary.Limiting
open ProphetSecretary.Probability
variable {T : Type*} [MeasurableSpace T]

noncomputable def boundedPayloadVersion (H : ℝ≥0) (Φ : ℝ × T → ℝ) (z : ℝ × T) : ℝ :=
  boundedOfferValue H (Φ z)

lemma measurable_boundedPayloadVersion (H : ℝ≥0) {Φ : ℝ × T → ℝ} (hΦ : Measurable Φ) :
    Measurable (boundedPayloadVersion H Φ) := (boundedOfferValue H).continuous.measurable.comp hΦ

omit [MeasurableSpace T] in
lemma boundedPayloadVersion_mem_range (H : ℝ≥0) (Φ : ℝ × T → ℝ) (z : ℝ × T) :
    boundedPayloadVersion H Φ z∈Icc (0 : ℝ) H := boundedOfferValue_mem_range H _

lemma randomizedMarkKernel_boundedPayloadVersion (κ : Measure T) [IsProbabilityMeasure κ]
    (H : ℝ≥0) (Φ : ℝ × T → ℝ) (hΦ : Measurable Φ) (x : ℝ) :
    randomizedMarkKernel κ (boundedPayloadVersion H Φ) (measurable_boundedPayloadVersion H hΦ) x=
      (randomizedMarkKernel κ Φ hΦ x).map (boundedOfferValue H).continuous.measurable.aemeasurable := by
  apply ProbabilityMeasure.toMeasure_injective
  change κ.map (fun t => boundedOfferValue H (Φ (x,t)))=
    (κ.map (fun t => Φ (x,t))).map (boundedOfferValue H)
  have hFixed : Measurable (fun t : T => Φ (x,t)) := hΦ.comp (measurable_const.prodMk measurable_id)
  rw [Measure.map_map (boundedOfferValue H).continuous.measurable hFixed]
  rfl

lemma randomizedMarkKernel_boundedPayloadVersion_continuousAt (κ : Measure T) [IsProbabilityMeasure κ]
    (H : ℝ≥0) (Φ : ℝ × T → ℝ) (hΦ : Measurable Φ) {x : ℝ}
    (h : ContinuousAt (randomizedMarkKernel κ Φ hΦ) x) :
    ContinuousAt (randomizedMarkKernel κ (boundedPayloadVersion H Φ) (measurable_boundedPayloadVersion H hΦ)) x := by
  have hComp := (ProbabilityMeasure.continuous_map (boundedOfferValue H).continuous).continuousAt.comp h
  have hEq : ((fun q : ProbabilityMeasure ℝ => q.map (boundedOfferValue H).continuous.measurable.aemeasurable) ∘
      randomizedMarkKernel κ Φ hΦ)=
      randomizedMarkKernel κ (boundedPayloadVersion H Φ) (measurable_boundedPayloadVersion H hΦ) :=
    funext (fun y => (randomizedMarkKernel_boundedPayloadVersion κ H Φ hΦ y).symm)
  rwa [hEq] at hComp

lemma cutoffPayloadDisplay_bounded_eq_ae (μ : Measure ℝ) (κ : Measure T) (H : ℝ≥0)
    (b : ℝ) (Φ : ℝ × T → ℝ)
    (hImage : ∀ᵐ z ∂μ.prod κ, b<z.1 → Φ z∈Icc (0 : ℝ) H) :
    cutoffPayloadDisplay b (boundedPayloadVersion H Φ)=ᵐ[μ.prod κ]cutoffPayloadDisplay b Φ := by
  filter_upwards [hImage] with z hz
  unfold cutoffPayloadDisplay
  split_ifs with h
  · exact boundedOfferValue_eq H (hz h)
  · rfl

lemma CountableInstance.mapPoissonAbove_boundedPayloadVersion (B : CountableInstance)
    (b : ℝ) (hb : (B.terminal : ℝ)<b) (H : ℝ≥0) (hH : B.cap≤H)
    (κ : Measure T) [IsProbabilityMeasure κ] (Φ : ℝ × T → ℝ) (hΦ : Measurable Φ)
    (hImage : ∀ᵐ z ∂B.intensity.prod κ, b<z.1 → Φ z∈Icc (0 : ℝ) H) :
    B.mapPoissonAbove b hb H hH κ (boundedPayloadVersion H Φ) (measurable_boundedPayloadVersion H hΦ)
      (Eventually.of_forall (fun z _ => boundedPayloadVersion_mem_range H Φ z))=
      B.mapPoissonAbove b hb H hH κ Φ hΦ hImage := by
  apply CountableInstance.ext_data
  · rfl
  · rfl
  · rfl
  · change (((B.intensity.prod κ).map (cutoffPayloadDisplay b (boundedPayloadVersion H Φ))).restrict (Ioi (B.terminal : ℝ)))=
      (((B.intensity.prod κ).map (cutoffPayloadDisplay b Φ)).restrict (Ioi (B.terminal : ℝ)))
    exact congrArg (fun ν : Measure ℝ => ν.restrict (Ioi (B.terminal : ℝ)))
      (Measure.map_congr (cutoffPayloadDisplay_bounded_eq_ae B.intensity κ H b Φ hImage))

lemma mapResidualOffers_boundedPayloadVersion {n : ℕ} (P : Model.Instance n)
    (N : ℕ) (H : ℝ≥0) (hCap : ∀ i, ∀ᵐ x ∂P.law i, x≤(H : ℝ))
    (κ : Measure T) [IsProbabilityMeasure κ] (b : ℝ) (Φ : ℝ × T → ℝ) (hΦ : Measurable Φ)
    (hImage : ∀ i, ∀ᵐ z ∂(P.law i).prod κ, b<z.1 → Φ z∈Icc (0 : ℝ) H) :
    mapResidualOffers P N H hCap κ b (boundedPayloadVersion H Φ) (measurable_boundedPayloadVersion H hΦ)
      (fun _ => Eventually.of_forall (fun z _ => boundedPayloadVersion_mem_range H Φ z))=
      mapResidualOffers P N H hCap κ b Φ hΦ hImage := by
  apply Model.Instance.eq_of_law_eq
  funext i
  change (if N≤ i.val then _ else P.law i)=(if N≤ i.val then _ else P.law i)
  by_cases hi : N≤ i.val
  · rw [if_pos hi,if_pos hi]
    change ((P.law i).prod κ).map (cutoffPayloadDisplay b (boundedPayloadVersion H Φ))=
      ((P.law i).prod κ).map (cutoffPayloadDisplay b Φ)
    exact Measure.map_congr (cutoffPayloadDisplay_bounded_eq_ae (P.law i) κ H b Φ (hImage i))
  · rw [if_neg hi,if_neg hi]

end ProphetSecretary.Limiting
