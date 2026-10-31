import ProphetSecretary.Statistics.DataSelectedCandidateFubini

/-!
# Integration of a candidate loss estimate against its true marginal

This reduction uses an explicitly supplied per-value estimate. Integrability
comes from the actual joint losses, rather than being inferred from the estimate.
The scalar selector depends only on the training rows represented by this model.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

/-- A per-value rate integrates to the same coefficient times the candidate's
first moment. The two loss directions remain separate. -/
theorem Instance.integrated_candidateRate (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x≤1) {Z : ((Fin n × Fin k) → ℝ) → ℝ} {hi C : ℝ}
    (hZ : Measurable Z) (hZrange : ∀ a, Z a∈Icc (0:ℝ) hi)
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (hρ0 : ∀ᵐ x ∂ρ, 0≤x) (hρI : Integrable (fun x : ℝ => x) ρ)
    (hRate : ∀ x, 0≤x →
      (∫ q, ∫ t, dataSelectedClockLoss P Z x q t ∂Instance.uniformClock
        ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n))≤C*x ∧
      (∫ q, ∫ t, dataSelectedClockLossReverse P Z x q t ∂Instance.uniformClock
        ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n))≤C*x) :
    (∫ b, (∫ v, (∫ x, (∫ t,
      empiricalClockGapLoss P (reservoirCoordinates.symm b) (Z b) v x t
        ∂Instance.uniformClock) ∂ρ) ∂Instance.clocksLaw n) ∂P.trainingCoordinateLaw k)≤C*(∫ x, x ∂ρ) ∧
    (∫ b, (∫ v, (∫ x, (∫ t,
      trueClockGapLossEmpiricalEval P (reservoirCoordinates.symm b) (Z b) v x t
        ∂Instance.uniformClock) ∂ρ) ∂Instance.clocksLaw n) ∂P.trainingCoordinateLaw k)≤C*(∫ x, x ∂ρ) := by
  have he := P.dataSelectedCandidateFubini hbound hZ hZrange ρ
  have hI := P.integrable_dataSelectedCandidateAverage hbound hZ hZrange ρ
  constructor
  · rw [he.1,←integral_const_mul]
    exact integral_mono_ae hI.1 (hρI.const_mul C)
      (hρ0.mono fun x hx => (hRate x hx).1)
  · rw [he.2,←integral_const_mul]
    exact integral_mono_ae hI.2 (hρI.const_mul C)
      (hρ0.mono fun x hx => (hRate x hx).2)

end ProphetSecretary.Model
