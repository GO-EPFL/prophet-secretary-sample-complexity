import ProphetSecretary.Limiting.Campbell
import ProphetSecretary.Model.Independence

/-!
# An independent inserted clock avoids a measurable stopping duration

The marked point intensity uses the uniform clock product. Its clock has
zero mass at every fixed real time. Measurable Fubini sections therefore
exclude equality with any measurable function of the independent base world.
-/
open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Limiting

theorem intensity_time_ne_measurable_ae {Ω : Type*} [MeasurableSpace Ω]
    (μ : FiniteMeasure ℝ) (ν : Measure Ω) [SFinite ν]
    (T : Ω → ℝ) (hT : Measurable T) :
    ∀ᵐ z : Point × Ω ∂(intensity μ).prod ν, z.1.1≠T z.2 := by
  have hSections (ω : Ω) : ∀ᵐ p : Point ∂intensity μ, p.1≠T ω :=
    (Measure.quasiMeasurePreserving_fst (μ := Model.Instance.uniformClock) (ν := (μ : Measure ℝ))).ae
      (Model.Instance.uniformClock.ae_ne (T ω))
  have hMeas : MeasurableSet {z : Ω × Point | z.2.1≠T z.1} :=
    (measurableSet_eq_fun (measurable_fst.comp measurable_snd) (hT.comp measurable_fst)).compl
  have hReverse : ∀ᵐ z : Ω × Point ∂ν.prod (intensity μ), z.2.1≠T z.1 :=
    (Measure.ae_prod_iff_ae_ae hMeas).mpr (Eventually.of_forall hSections)
  exact (Measure.measurePreserving_swap (μ := intensity μ) (ν := ν)).quasiMeasurePreserving.ae hReverse

end ProphetSecretary.Limiting
