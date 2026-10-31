import ProphetSecretary.Limiting.ClosureResidualPayload
import ProphetSecretary.Limiting.InputCapPayloadVersion

/-!
# Original-sequence mark-map closure with cap-relative kernel continuity

The input clamp extends the old mark map beyond its actual support. It changes
neither the original finite mapped laws nor the new limiting intensity. The
ordinary weak-kernel theorem therefore applies under the source's continuity
hypothesis relative to the mark space, including atoms at the cap.
-/
open MeasureTheory Set Filter
open scoped Classical Topology NNReal
namespace ProphetSecretary.Limiting
variable {T : Type*} [MeasurableSpace T]

lemma LabeledBandConvergence.mapResidualOffers_relative_of_diagonal {sizes : ℕ → ℕ}
    {P : ∀ m, Model.Instance (sizes m)} {B : CountableInstance}
    (h : LabeledBandConvergence sizes P B)
    (hCap : ∀ m i, ∀ᵐ x ∂(P m).law i, x≤(B.cap : ℝ))
    (b : ℝ) (hb : (B.terminal : ℝ)<b) (H : ℝ≥0) (hH : B.cap≤H)
    (κ : Measure T) [IsProbabilityMeasure κ] (Φ : ℝ × T → ℝ) (hΦ : Measurable Φ)
    (hImage : ∀ᵐ z ∂B.intensity.prod κ, b<z.1 → Φ z∈Icc (0 : ℝ) H)
    (hImages : ∀ m i, ∀ᵐ z ∂((P m).law i).prod κ, b<z.1 → Φ z∈Icc (0 : ℝ) H)
    (hKernel : ∀ᵐ x ∂(B.intensityAbove b hb : Measure ℝ),
      ContinuousWithinAt (randomizedMarkKernel κ Φ hΦ) (Icc (0 : ℝ) B.cap) x)
    (Ns : ℕ → ℕ) (hNs : Tendsto Ns atTop atTop)
    (hDiagonal : Tendsto (fun m => labeledBandResidual (P m) (Ns m) b) atTop (𝓝 (B.intensityAbove b hb))) :
    LabeledBandConvergence sizes
      (fun m => mapResidualOffers (P m) (Ns m) H (fun i => (hCap m i).mono (fun _ hx => hx.trans hH)) κ b Φ hΦ (hImages m))
      (B.mapPoissonAbove b hb H hH κ Φ hΦ hImage) := by
  let Ψ := inputCapPayloadVersion B.cap Φ
  have hΨ : Measurable Ψ := measurable_inputCapPayloadVersion B.cap hΦ
  have hSupport : ∀ᵐ x ∂B.intensity, x∈Icc (0 : ℝ) B.cap :=
    B.intensity_supported.mono (fun _ hx => ⟨B.terminal.property.trans hx.1.le,hx.2⟩)
  have hEq : Ψ=ᵐ[B.intensity.prod κ]Φ := inputCapPayloadVersion_eq_ae B.intensity κ B.cap hSupport Φ
  have hEqRows (m : ℕ) (i : Fin (sizes m)) : Ψ=ᵐ[((P m).law i).prod κ]Φ := by
    have hRowSupport : ∀ᵐ x ∂(P m).law i, x∈Icc (0 : ℝ) B.cap := by
      filter_upwards [(P m).nonnegative i,hCap m i] with x hx hX
      exact ⟨hx,hX⟩
    exact inputCapPayloadVersion_eq_ae ((P m).law i) κ B.cap hRowSupport Φ
  have hImageΨ : ∀ᵐ z ∂B.intensity.prod κ, b<z.1 → Ψ z∈Icc (0 : ℝ) H := by
    filter_upwards [hEq,hImage] with z he hz hbz
    rw [he]
    exact hz hbz
  have hImagesΨ : ∀ m i, ∀ᵐ z ∂((P m).law i).prod κ, b<z.1 → Ψ z∈Icc (0 : ℝ) H := by
    intro m i
    filter_upwards [hEqRows m i,hImages m i] with z he hz hbz
    rw [he]
    exact hz hbz
  have hKernelΨ : ∀ᵐ x ∂(B.intensityAbove b hb : Measure ℝ), ContinuousAt (randomizedMarkKernel κ Ψ hΨ) x := by
    have hBandSupport : ∀ᵐ x ∂(B.intensityAbove b hb : Measure ℝ), x∈Icc (0 : ℝ) B.cap := ae_restrict_of_ae hSupport
    filter_upwards [hKernel,hBandSupport] with x hx hX
    exact randomizedMarkKernel_inputCap_continuousAt κ B.cap Φ hΦ hX hx
  have hNew := h.mapResidualOffers_of_diagonal hCap b hb H hH κ Ψ hΨ hImageΨ hImagesΨ hKernelΨ Ns hNs hDiagonal
  have hTarget : B.mapPoissonAbove b hb H hH κ Ψ hΨ hImageΨ=B.mapPoissonAbove b hb H hH κ Φ hΦ hImage :=
    B.mapPoissonAbove_congr_ae b hb H hH κ Ψ Φ hΨ hΦ hImageΨ hImage hEq
  have hRows : (fun m => mapResidualOffers (P m) (Ns m) H (fun i => (hCap m i).mono (fun _ hx => hx.trans hH)) κ b Ψ hΨ (hImagesΨ m))=
      fun m => mapResidualOffers (P m) (Ns m) H (fun i => (hCap m i).mono (fun _ hx => hx.trans hH)) κ b Φ hΦ (hImages m) := by
    funext m
    exact mapResidualOffers_congr_ae (P m) (Ns m) H (fun i => (hCap m i).mono (fun _ hx => hx.trans hH)) κ b Ψ Φ hΨ hΦ
      (hImagesΨ m) (hImages m) (hEqRows m)
  rw [hRows,hTarget] at hNew
  exact hNew

theorem LabeledBandConvergence.mapPoissonAbove_relative {sizes : ℕ → ℕ}
    {P : ∀ m, Model.Instance (sizes m)} {B : CountableInstance}
    (h : LabeledBandConvergence sizes P B)
    (hCap : ∀ m i, ∀ᵐ x ∂(P m).law i, x≤(B.cap : ℝ))
    (b : ℝ) (hb : (B.terminal : ℝ)<b) (hAtom : B.intensity {b}=0)
    (H : ℝ≥0) (hH : B.cap≤H) (κ : Measure T) [IsProbabilityMeasure κ]
    (Φ : ℝ × T → ℝ) (hΦ : Measurable Φ)
    (hImage : ∀ᵐ z ∂B.intensity.prod κ, b<z.1 → Φ z∈Icc (0 : ℝ) H)
    (hImages : ∀ m i, ∀ᵐ z ∂((P m).law i).prod κ, b<z.1 → Φ z∈Icc (0 : ℝ) H)
    (hKernel : ∀ᵐ x ∂(B.intensityAbove b hb : Measure ℝ),
      ContinuousWithinAt (randomizedMarkKernel κ Φ hΦ) (Icc (0 : ℝ) B.cap) x) :
    ∃ Ns : ℕ → ℕ, Monotone Ns ∧ (∀ m, Ns m≤m) ∧ Tendsto Ns atTop atTop ∧
      LabeledBandConvergence sizes
        (fun m => mapResidualOffers (P m) (Ns m) H (fun i => (hCap m i).mono (fun _ hx => hx.trans hH)) κ b Φ hΦ (hImages m))
        (B.mapPoissonAbove b hb H hH κ Φ hΦ hImage) := by
  obtain ⟨Ns,hMono,hLe,hTop,hDiag,_hRare⟩ := h.exists_all_continuity_residual_diagonal
  exact ⟨Ns,hMono,hLe,hTop,h.mapResidualOffers_relative_of_diagonal hCap b hb H hH κ Φ hΦ hImage hImages hKernel Ns hTop (hDiag b hb hAtom)⟩

end ProphetSecretary.Limiting
