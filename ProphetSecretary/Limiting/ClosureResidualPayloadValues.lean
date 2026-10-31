import ProphetSecretary.Limiting.ClosureResidualPayload

/-!
# Actual scalar and maximum limits after a residual randomized mark map

The residual schedule is chosen before weights. Structural convergence of
its actual finite product laws then gives all nonnegative scalar values and
expected maxima, uniformly on bounded weight rectangles.
-/
open MeasureTheory Set Filter
open scoped Classical Topology NNReal
namespace ProphetSecretary.Limiting
variable {T : Type*} [MeasurableSpace T]

theorem LabeledBandConvergence.mapPoissonAbove_values_and_maxima {sizes : ℕ → ℕ}
    {P : ∀ m, Model.Instance (sizes m)} {B : CountableInstance}
    (h : LabeledBandConvergence sizes P B)
    (hCap : ∀ m j, ∀ᵐ x ∂(P m).law j, x≤(B.cap : ℝ))
    (b : ℝ) (hb : (B.terminal : ℝ)<b) (hAtom : B.intensity {b}=0)
    (H : ℝ≥0) (hH : B.cap≤H) (κ : Measure T) [IsProbabilityMeasure κ]
    (Φ : ℝ × T → ℝ) (hΦ : Measurable Φ)
    (hImage : ∀ᵐ z ∂B.intensity.prod κ, b<z.1 → Φ z∈Icc (0 : ℝ) H)
    (hImages : ∀ m j, ∀ᵐ z ∂((P m).law j).prod κ, b<z.1 → Φ z∈Icc (0 : ℝ) H)
    (hKernel : ∀ᵐ x ∂(B.intensityAbove b hb : Measure ℝ), ContinuousAt (randomizedMarkKernel κ Φ hΦ) x) :
    ∃ Ns : ℕ → ℕ, Monotone Ns ∧ (∀ m, Ns m≤m) ∧ Tendsto Ns atTop atTop ∧
      ∀ W C : ℝ≥0, ∀ ε>(0 : ℝ), ∀ᶠ m in atTop,
        (∀ w c : ℝ, 0≤w → w≤W → 0≤c → c≤C →
          |Model.optimalScalarValue
              (mapResidualOffers (P m) (Ns m) H (fun j => (hCap m j).mono (fun _ hx => hx.trans hH)) κ b Φ hΦ (hImages m)) w c-
            (B.mapPoissonAbove b hb H hH κ Φ hΦ hImage).optimalScalarValue w c|<ε) ∧
        |(mapResidualOffers (P m) (Ns m) H (fun j => (hCap m j).mono (fun _ hx => hx.trans hH)) κ b Φ hΦ (hImages m)).expectedMaximum-
          (B.mapPoissonAbove b hb H hH κ Φ hΦ hImage).expectedMaximum|<ε := by
  obtain ⟨Ns,hMono,hLe,hTop,hConv⟩ := h.mapPoissonAbove hCap b hb hAtom H hH κ Φ hΦ hImage hImages hKernel
  refine ⟨Ns,hMono,hLe,hTop,?_⟩
  intro W C
  exact hConv.values_and_maxima
    (fun m => mapResidualOffers_bounded (P m) (Ns m) H (fun j => (hCap m j).mono (fun _ hx => hx.trans hH)) κ b Φ hΦ (hImages m)) W C

end ProphetSecretary.Limiting
