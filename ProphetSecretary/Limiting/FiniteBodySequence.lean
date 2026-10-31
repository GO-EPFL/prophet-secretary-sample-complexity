import ProphetSecretary.Limiting.ClosureIndividualReplacement
import ProphetSecretary.Limiting.ClosureReserveTranslation
import ProphetSecretary.Limiting.ClosureResidualPayloadRelative
import ProphetSecretary.Limiting.BoundedPayloadVersion
import ProphetSecretary.Limiting.CountableAmbientCap

/-!
# Bounded finite sequences paired with proposed target body data

Convergence is a separate proposition. The data do not include value, maximum
or policy convergence. The operations below specify the consecutive actual
finite families used by the finite-composition statement of `lem:closure`.
-/
open MeasureTheory Set Filter
open scoped Classical Topology NNReal
namespace ProphetSecretary.Limiting

structure FiniteBodySequence where
  size : ℕ → ℕ
  offers : ∀ m, Model.Instance (size m)
  target : CountableInstance
  bounded : ∀ m i, ∀ᵐ x ∂(offers m).law i, x≤(target.cap : ℝ)

def FiniteBodySequence.Converges (A : FiniteBodySequence) : Prop :=
  LabeledBandConvergence A.size A.offers A.target

namespace FiniteBodySequence

noncomputable def ofSequence (sizes : ℕ → ℕ) (P : ∀ m, Model.Instance (sizes m)) (B : CountableInstance)
    (hCap : ∀ m i, ∀ᵐ x ∂(P m).law i, x≤(B.cap : ℝ)) : FiniteBodySequence :=
  ⟨sizes,P,B,hCap⟩

noncomputable def enlargeCap (A : FiniteBodySequence) (H : ℝ≥0) (hH : A.target.cap≤H) : FiniteBodySequence where
  size := A.size
  offers := A.offers
  target := A.target.withCap H hH
  bounded m i := (A.bounded m i).mono (fun _ hx => hx.trans hH)

noncomputable def replaceIndividual (A : FiniteBodySequence) (i : ℕ) (q : ProbabilityMeasure ℝ)
    (hq : ∀ᵐ x ∂(q : Measure ℝ), x∈Icc (0 : ℝ) A.target.cap)
    (qs : ℕ → ProbabilityMeasure ℝ) (hqs : ∀ m, ∀ᵐ x ∂(qs m : Measure ℝ), x∈Icc (0 : ℝ) A.target.cap) :
    FiniteBodySequence where
  size m := A.size m+(i+1)
  offers m := replaceLabeledIndividual (A.offers m) i (qs m) ((hqs m).mono (fun _ hx => hx.1))
  target := A.target.updateIndividual i q hq
  bounded m := replaceLabeledIndividual_bounded (A.offers m) i (qs m) _ A.target.cap.property (A.bounded m)
    ((hqs m).mono (fun _ hx => hx.2))

noncomputable def translateReserve (A : FiniteBodySequence) (a : ℝ≥0) (ha : a<A.target.terminal) :
    FiniteBodySequence where
  size := A.size
  offers m := (A.offers m).excessOffers a
  target := A.target.reserveTranslation a ha
  bounded m := excessOffers_bounded (A.offers m) a.property (A.bounded m)

noncomputable def replaceResidualMarks (A : FiniteBodySequence) {T : Type*} [MeasurableSpace T]
    (b : ℝ) (hb : (A.target.terminal : ℝ)<b) (H : ℝ≥0) (hH : A.target.cap≤H)
    (κ : Measure T) [IsProbabilityMeasure κ] (Φ : ℝ × T → ℝ) (hΦ : Measurable Φ)
    (hImage : ∀ᵐ z ∂A.target.intensity.prod κ, b<z.1 → Φ z∈Icc (0 : ℝ) H) (Ns : ℕ → ℕ) :
    FiniteBodySequence where
  size := A.size
  offers m := mapResidualOffers (A.offers m) (Ns m) H
    (fun i => (A.bounded m i).mono (fun _ hx => hx.trans hH)) κ b (boundedPayloadVersion H Φ)
      (measurable_boundedPayloadVersion H hΦ)
      (fun _ => Eventually.of_forall (fun z _ => boundedPayloadVersion_mem_range H Φ z))
  target := A.target.mapPoissonAbove b hb H hH κ Φ hΦ hImage
  bounded m := mapResidualOffers_bounded (A.offers m) (Ns m) H
    (fun i => (A.bounded m i).mono (fun _ hx => hx.trans hH)) κ b (boundedPayloadVersion H Φ)
      (measurable_boundedPayloadVersion H hΦ)
      (fun _ => Eventually.of_forall (fun z _ => boundedPayloadVersion_mem_range H Φ z))

lemma converges_enlargeCap (A : FiniteBodySequence) (hA : A.Converges) (H : ℝ≥0) (hH : A.target.cap≤H) :
    (A.enlargeCap H hH).Converges := by
  exact ⟨hA.individual_weak,hA.residual_bands,hA.rare,hA.below_reserve,hA.above_reserve⟩

lemma converges_replaceIndividual (A : FiniteBodySequence) (hA : A.Converges)
    (i : ℕ) (q : ProbabilityMeasure ℝ) (hq : ∀ᵐ x ∂(q : Measure ℝ), x∈Icc (0 : ℝ) A.target.cap)
    (qs : ℕ → ProbabilityMeasure ℝ) (hqs : ∀ m, ∀ᵐ x ∂(qs m : Measure ℝ), x∈Icc (0 : ℝ) A.target.cap)
    (hWeak : Tendsto qs atTop (𝓝 q)) : (A.replaceIndividual i q hq qs hqs).Converges :=
  hA.updateIndividual i q hq qs (fun m => (hqs m).mono (fun _ hx => hx.1)) hWeak

lemma converges_translateReserve (A : FiniteBodySequence) (hA : A.Converges) (a : ℝ≥0) (ha : a<A.target.terminal) :
    (A.translateReserve a ha).Converges := hA.reserveTranslation a ha

lemma converges_replaceResidualMarks (A : FiniteBodySequence) (hA : A.Converges)
    {T : Type*} [MeasurableSpace T] (b : ℝ) (hb : (A.target.terminal : ℝ)<b)
    (H : ℝ≥0) (hH : A.target.cap≤H) (κ : Measure T) [IsProbabilityMeasure κ]
    (Φ : ℝ × T → ℝ) (hΦ : Measurable Φ)
    (hImage : ∀ᵐ z ∂A.target.intensity.prod κ, b<z.1 → Φ z∈Icc (0 : ℝ) H)
    (hKernel : ∀ᵐ x ∂(A.target.intensityAbove b hb : Measure ℝ), ContinuousWithinAt (randomizedMarkKernel κ Φ hΦ) (Icc (0 : ℝ) A.target.cap) x)
    (Ns : ℕ → ℕ) (hNs : Tendsto Ns atTop atTop)
    (hDiagonal : Tendsto (fun m => labeledBandResidual (A.offers m) (Ns m) b) atTop
      (𝓝 (A.target.intensityAbove b hb))) :
    (A.replaceResidualMarks b hb H hH κ Φ hΦ hImage Ns).Converges := by
  let Ψ := boundedPayloadVersion H Φ
  have hΨ : Measurable Ψ := measurable_boundedPayloadVersion H hΦ
  have hImageΨ : ∀ᵐ z ∂A.target.intensity.prod κ, b<z.1 → Ψ z∈Icc (0 : ℝ) H :=
    Eventually.of_forall (fun z _ => boundedPayloadVersion_mem_range H Φ z)
  have hImagesΨ : ∀ m i, ∀ᵐ z ∂((A.offers m).law i).prod κ, b<z.1 → Ψ z∈Icc (0 : ℝ) H :=
    fun _ _ => Eventually.of_forall (fun z _ => boundedPayloadVersion_mem_range H Φ z)
  have hKernelΨ : ∀ᵐ x ∂(A.target.intensityAbove b hb : Measure ℝ), ContinuousWithinAt (randomizedMarkKernel κ Ψ hΨ) (Icc (0 : ℝ) A.target.cap) x :=
    hKernel.mono (fun _ hx => randomizedMarkKernel_boundedPayloadVersion_continuousWithinAt κ H Φ hΦ hx)
  have hNew := hA.mapResidualOffers_relative_of_diagonal A.bounded b hb H hH κ Ψ hΨ hImageΨ hImagesΨ hKernelΨ Ns hNs hDiagonal
  have hEqual : A.target.mapPoissonAbove b hb H hH κ Ψ hΨ hImageΨ=A.target.mapPoissonAbove b hb H hH κ Φ hΦ hImage :=
    A.target.mapPoissonAbove_boundedPayloadVersion b hb H hH κ Φ hΦ hImage
  change LabeledBandConvergence A.size
    (fun m => mapResidualOffers (A.offers m) (Ns m) H
      (fun i => (A.bounded m i).mono (fun _ hx => hx.trans hH)) κ b Ψ hΨ (hImagesΨ m))
    (A.target.mapPoissonAbove b hb H hH κ Φ hΦ hImage)
  rw [← hEqual]
  exact hNew

lemma replaceResidualMarks_offers_eq_of_bounded (A : FiniteBodySequence)
    {T : Type*} [MeasurableSpace T] (b : ℝ) (hb : (A.target.terminal : ℝ)<b)
    (H : ℝ≥0) (hH : A.target.cap≤H) (κ : Measure T) [IsProbabilityMeasure κ]
    (Φ : ℝ × T → ℝ) (hΦ : Measurable Φ)
    (hImage : ∀ᵐ z ∂A.target.intensity.prod κ, b<z.1 → Φ z∈Icc (0 : ℝ) H)
    (hImages : ∀ m i, ∀ᵐ z ∂((A.offers m).law i).prod κ, b<z.1 → Φ z∈Icc (0 : ℝ) H)
    (Ns : ℕ → ℕ) (m : ℕ) :
    (A.replaceResidualMarks b hb H hH κ Φ hΦ hImage Ns).offers m=
      mapResidualOffers (A.offers m) (Ns m) H (fun i => (A.bounded m i).mono (fun _ hx => hx.trans hH)) κ b Φ hΦ (hImages m) :=
  mapResidualOffers_boundedPayloadVersion (A.offers m) (Ns m) H
    (fun i => (A.bounded m i).mono (fun _ hx => hx.trans hH)) κ b Φ hΦ (hImages m)

end FiniteBodySequence
end ProphetSecretary.Limiting
