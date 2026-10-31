import ProphetSecretary.Limiting.BoundedPayloadVersion
import ProphetSecretary.Limiting.CountableRemainingState

/-!
# Extending a randomized mark map from the actual cap interval

Clamping only the old mark leaves every actual finite and limiting law
unchanged. It converts weak kernel continuity relative to the cap into
ordinary weak continuity on the real line. Independent tags and all chosen
finite identity labels are retained.
-/
open MeasureTheory Set Filter
open scoped Classical Topology NNReal
namespace ProphetSecretary.Limiting
open ProphetSecretary.Probability
variable {T : Type*} [MeasurableSpace T]

noncomputable def inputCapPayloadVersion (H : ℝ≥0) (Φ : ℝ × T → ℝ) (z : ℝ × T) : ℝ :=
  Φ (boundedOfferValue H z.1,z.2)

lemma measurable_inputCapPayloadVersion (H : ℝ≥0) {Φ : ℝ × T → ℝ} (hΦ : Measurable Φ) :
    Measurable (inputCapPayloadVersion H Φ) :=
  hΦ.comp (((boundedOfferValue H).continuous.measurable.comp measurable_fst).prodMk measurable_snd)

lemma inputCapPayloadVersion_eq_ae (μ : Measure ℝ) [SFinite μ] (κ : Measure T) [IsProbabilityMeasure κ]
    (H : ℝ≥0) (hCap : ∀ᵐ x ∂μ, x∈Icc (0 : ℝ) H) (Φ : ℝ × T → ℝ) :
    inputCapPayloadVersion H Φ=ᵐ[μ.prod κ]Φ := by
  have hMP : MeasurePreserving (Prod.fst : ℝ × T → ℝ) (μ.prod κ) μ := measurePreserving_fst
  filter_upwards [hMP.quasiMeasurePreserving.ae hCap] with z hz
  unfold inputCapPayloadVersion
  rw [boundedOfferValue_eq H hz]

lemma randomizedMarkKernel_inputCapPayloadVersion (κ : Measure T) [IsProbabilityMeasure κ]
    (H : ℝ≥0) (Φ : ℝ × T → ℝ) (hΦ : Measurable Φ) (x : ℝ) :
    randomizedMarkKernel κ (inputCapPayloadVersion H Φ) (measurable_inputCapPayloadVersion H hΦ) x=
      randomizedMarkKernel κ Φ hΦ (boundedOfferValue H x) := by
  apply ProbabilityMeasure.toMeasure_injective
  rfl

lemma randomizedMarkKernel_inputCap_continuousAt (κ : Measure T) [IsProbabilityMeasure κ]
    (H : ℝ≥0) (Φ : ℝ × T → ℝ) (hΦ : Measurable Φ) {x : ℝ}
    (hx : x∈Icc (0 : ℝ) H)
    (h : ContinuousWithinAt (randomizedMarkKernel κ Φ hΦ) (Icc (0 : ℝ) H) x) :
    ContinuousAt (randomizedMarkKernel κ (inputCapPayloadVersion H Φ) (measurable_inputCapPayloadVersion H hΦ)) x := by
  have hWithin : ContinuousWithinAt (randomizedMarkKernel κ Φ hΦ ∘ boundedOfferValue H) univ x :=
    h.comp_of_eq (boundedOfferValue H).continuous.continuousAt.continuousWithinAt
      (fun y _ => boundedOfferValue_mem_range H y) (boundedOfferValue_eq H hx)
  have hAt := hWithin.continuousAt Filter.univ_mem
  have hEq : (randomizedMarkKernel κ Φ hΦ ∘ boundedOfferValue H)=
      randomizedMarkKernel κ (inputCapPayloadVersion H Φ) (measurable_inputCapPayloadVersion H hΦ) :=
    funext (fun y => (randomizedMarkKernel_inputCapPayloadVersion κ H Φ hΦ y).symm)
  rwa [hEq] at hAt

lemma randomizedMarkKernel_boundedPayloadVersion_continuousWithinAt (κ : Measure T) [IsProbabilityMeasure κ]
    (H : ℝ≥0) (Φ : ℝ × T → ℝ) (hΦ : Measurable Φ) {x : ℝ} {S : Set ℝ}
    (h : ContinuousWithinAt (randomizedMarkKernel κ Φ hΦ) S x) :
    ContinuousWithinAt (randomizedMarkKernel κ (boundedPayloadVersion H Φ) (measurable_boundedPayloadVersion H hΦ)) S x := by
  have hComp := (ProbabilityMeasure.continuous_map (boundedOfferValue H).continuous).continuousWithinAt.comp h
    (fun _ _ => mem_univ _)
  have hEq : ((fun q : ProbabilityMeasure ℝ => q.map (boundedOfferValue H).continuous.measurable.aemeasurable) ∘
      randomizedMarkKernel κ Φ hΦ)=
      randomizedMarkKernel κ (boundedPayloadVersion H Φ) (measurable_boundedPayloadVersion H hΦ) :=
    funext (fun y => (randomizedMarkKernel_boundedPayloadVersion κ H Φ hΦ y).symm)
  rwa [hEq] at hComp

lemma cutoffPayloadDisplay_congr_ae (μ : Measure ℝ) (κ : Measure T) (b : ℝ)
    {Φ Ψ : ℝ × T → ℝ} (hEq : Φ=ᵐ[μ.prod κ]Ψ) :
    cutoffPayloadDisplay b Φ=ᵐ[μ.prod κ]cutoffPayloadDisplay b Ψ := by
  filter_upwards [hEq] with z hz
  unfold cutoffPayloadDisplay
  split_ifs
  · exact hz
  · rfl

lemma CountableInstance.mapPoissonAbove_congr_ae (B : CountableInstance) (b : ℝ) (hb : (B.terminal : ℝ)<b)
    (H : ℝ≥0) (hH : B.cap≤H) (κ : Measure T) [IsProbabilityMeasure κ]
    (Φ Ψ : ℝ × T → ℝ) (hΦ : Measurable Φ) (hΨ : Measurable Ψ)
    (hImageΦ : ∀ᵐ z ∂B.intensity.prod κ, b<z.1 → Φ z∈Icc (0 : ℝ) H)
    (hImageΨ : ∀ᵐ z ∂B.intensity.prod κ, b<z.1 → Ψ z∈Icc (0 : ℝ) H)
    (hEq : Φ=ᵐ[B.intensity.prod κ]Ψ) :
    B.mapPoissonAbove b hb H hH κ Φ hΦ hImageΦ=B.mapPoissonAbove b hb H hH κ Ψ hΨ hImageΨ := by
  apply CountableInstance.ext_data
  · rfl
  · rfl
  · rfl
  · change (((B.intensity.prod κ).map (cutoffPayloadDisplay b Φ)).restrict (Ioi (B.terminal : ℝ)))=
      (((B.intensity.prod κ).map (cutoffPayloadDisplay b Ψ)).restrict (Ioi (B.terminal : ℝ)))
    exact congrArg (fun μ : Measure ℝ => μ.restrict (Ioi (B.terminal : ℝ)))
      (Measure.map_congr (cutoffPayloadDisplay_congr_ae B.intensity κ b hEq))

lemma mapResidualOffers_congr_ae {n : ℕ} (P : Model.Instance n) (N : ℕ) (H : ℝ≥0)
    (hCap : ∀ i, ∀ᵐ x ∂P.law i, x≤(H : ℝ)) (κ : Measure T) [IsProbabilityMeasure κ]
    (b : ℝ) (Φ Ψ : ℝ × T → ℝ) (hΦ : Measurable Φ) (hΨ : Measurable Ψ)
    (hImagesΦ : ∀ i, ∀ᵐ z ∂(P.law i).prod κ, b<z.1 → Φ z∈Icc (0 : ℝ) H)
    (hImagesΨ : ∀ i, ∀ᵐ z ∂(P.law i).prod κ, b<z.1 → Ψ z∈Icc (0 : ℝ) H)
    (hEq : ∀ i, Φ=ᵐ[(P.law i).prod κ]Ψ) :
    mapResidualOffers P N H hCap κ b Φ hΦ hImagesΦ=mapResidualOffers P N H hCap κ b Ψ hΨ hImagesΨ := by
  apply Model.Instance.eq_of_law_eq
  funext i
  change (if N≤ i.val then _ else P.law i)=(if N≤ i.val then _ else P.law i)
  by_cases hi : N≤ i.val
  · rw [if_pos hi,if_pos hi]
    change ((P.law i).prod κ).map (cutoffPayloadDisplay b Φ)=((P.law i).prod κ).map (cutoffPayloadDisplay b Ψ)
    exact Measure.map_congr (cutoffPayloadDisplay_congr_ae (P.law i) κ b (hEq i))
  · rw [if_neg hi,if_neg hi]

end ProphetSecretary.Limiting
