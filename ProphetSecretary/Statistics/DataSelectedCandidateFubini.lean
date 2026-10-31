import ProphetSecretary.Statistics.DataSelectedClockLossIntegrability

/-!
# Integrating an independent candidate value after fixing the scalar selector

Both directions admit the same genuine Fubini interchange. The scalar is held
fixed as a function of the other training rows and never depends on time or on
the independent candidate value being integrated here.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

theorem Instance.dataSelectedCandidateFubini (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x≤1) {Z : ((Fin n × Fin k) → ℝ) → ℝ} {hi : ℝ}
    (hZ : Measurable Z) (hZrange : ∀ a, Z a∈Icc (0:ℝ) hi)
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ] :
    ((∫ b, (∫ v, (∫ x, (∫ t,
      empiricalClockGapLoss P (reservoirCoordinates.symm b) (Z b) v x t
        ∂Instance.uniformClock) ∂ρ) ∂Instance.clocksLaw n) ∂P.trainingCoordinateLaw k) =
      ∫ x, (∫ q, (∫ t, dataSelectedClockLoss P Z x q t ∂Instance.uniformClock)
        ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ∂ρ) ∧
    ((∫ b, (∫ v, (∫ x, (∫ t,
      trueClockGapLossEmpiricalEval P (reservoirCoordinates.symm b) (Z b) v x t
        ∂Instance.uniformClock) ∂ρ) ∂Instance.clocksLaw n) ∂P.trainingCoordinateLaw k) =
      ∫ x, (∫ q, (∫ t, dataSelectedClockLossReverse P Z x q t ∂Instance.uniformClock)
        ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ∂ρ) := by
  have hp := P.integrable_dataSelectedClockLoss_pair_jointValue hbound hZ hZrange ρ
  constructor
  · have hI := hp.1.integral_prod_left
    have hQ := hI.integral_prod_left
    calc
      _ = ∫ q, (∫ x, (∫ t, dataSelectedClockLoss P Z x q t ∂Instance.uniformClock) ∂ρ)
          ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n) :=
        (integral_prod _ hQ).symm
      _ = _ := integral_integral_swap hI
  · have hI := hp.2.integral_prod_left
    have hQ := hI.integral_prod_left
    calc
      _ = ∫ q, (∫ x, (∫ t, dataSelectedClockLossReverse P Z x q t ∂Instance.uniformClock) ∂ρ)
          ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n) :=
        (integral_prod _ hQ).symm
      _ = _ := integral_integral_swap hI

/-- The remaining candidate-value integral is integrable, independently of its
support or first moment; support and first moments enter only the rate bound. -/
theorem Instance.integrable_dataSelectedCandidateAverage (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x≤1) {Z : ((Fin n × Fin k) → ℝ) → ℝ} {hi : ℝ}
    (hZ : Measurable Z) (hZrange : ∀ a, Z a∈Icc (0:ℝ) hi)
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ] :
    Integrable (fun x => ∫ q, (∫ t, dataSelectedClockLoss P Z x q t ∂Instance.uniformClock)
      ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ρ ∧
    Integrable (fun x => ∫ q, (∫ t, dataSelectedClockLossReverse P Z x q t ∂Instance.uniformClock)
      ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ρ := by
  have hp := P.integrable_dataSelectedClockLoss_pair_jointValue hbound hZ hZrange ρ
  exact ⟨hp.1.integral_prod_left.integral_prod_right,hp.2.integral_prod_left.integral_prod_right⟩

end ProphetSecretary.Model
