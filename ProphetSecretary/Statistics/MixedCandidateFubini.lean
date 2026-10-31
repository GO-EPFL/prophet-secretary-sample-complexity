import ProphetSecretary.Statistics.MixedDataSelectedClockLossIntegrability
import ProphetSecretary.Statistics.MixedClockLossDirection

/-!
# Actual independent-candidate Fubini for mixed designs

Both actual directions admit the same genuine interchange with an independent
candidate-value law. The scalar is fixed as a function of other training rows;
it depends neither on candidate time nor on the independent candidate value.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

theorem Instance.mixedDataSelectedCandidateFubini (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x≤1) {Z : ((Fin n × Fin k) → ℝ) → ℝ} {hi : ℝ}
    (hZ : Measurable Z) (hZrange : ∀ a, Z a∈Icc (0:ℝ) hi)
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ] :
    ((∫ b, (∫ v, (∫ x, (∫ t,
      mixedClockGapLoss P known (reservoirCoordinates.symm b) (Z b) v x t
        ∂Instance.uniformClock) ∂ρ) ∂Instance.clocksLaw n) ∂P.trainingCoordinateLaw k) =
      ∫ x, (∫ q, (∫ t, mixedDataSelectedClockLoss P known Z x q t ∂Instance.uniformClock)
        ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ∂ρ) ∧
    ((∫ b, (∫ v, (∫ x, (∫ t,
      trueClockGapLossMixedEval P known (reservoirCoordinates.symm b) (Z b) v x t
        ∂Instance.uniformClock) ∂ρ) ∂Instance.clocksLaw n) ∂P.trainingCoordinateLaw k) =
      ∫ x, (∫ q, (∫ t, mixedDataSelectedClockLossReverse P known Z x q t ∂Instance.uniformClock)
        ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ∂ρ) := by
  have hp := P.integrable_mixedDataSelectedClockLoss_pair_jointValue known hbound hZ hZrange ρ
  constructor
  · have hI := hp.1.integral_prod_left
    have hQ := hI.integral_prod_left
    calc
      _ = ∫ q, (∫ x, (∫ t, mixedDataSelectedClockLoss P known Z x q t ∂Instance.uniformClock) ∂ρ)
          ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n) :=
        (integral_prod _ hQ).symm
      _ = _ := integral_integral_swap hI
  · have hI := hp.2.integral_prod_left
    have hQ := hI.integral_prod_left
    calc
      _ = ∫ q, (∫ x, (∫ t, mixedDataSelectedClockLossReverse P known Z x q t ∂Instance.uniformClock) ∂ρ)
          ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n) :=
        (integral_prod _ hQ).symm
      _ = _ := integral_integral_swap hI

/-- The remaining candidate-value integral is integrable, independently of its
support or first moment; support and first moments enter only the rate bound. -/
theorem Instance.integrable_mixedDataSelectedCandidateAverage (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x≤1) {Z : ((Fin n × Fin k) → ℝ) → ℝ} {hi : ℝ}
    (hZ : Measurable Z) (hZrange : ∀ a, Z a∈Icc (0:ℝ) hi)
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ] :
    Integrable (fun x => ∫ q, (∫ t, mixedDataSelectedClockLoss P known Z x q t ∂Instance.uniformClock)
      ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ρ ∧
    Integrable (fun x => ∫ q, (∫ t, mixedDataSelectedClockLossReverse P known Z x q t ∂Instance.uniformClock)
      ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ρ := by
  have hp := P.integrable_mixedDataSelectedClockLoss_pair_jointValue known hbound hZ hZrange ρ
  exact ⟨hp.1.integral_prod_left.integral_prod_right,hp.2.integral_prod_left.integral_prod_right⟩

theorem Instance.mixedCandidateDirectionFubini (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x≤1) {Z : ((Fin n × Fin k) → ℝ) → ℝ} {hi : ℝ}
    (hZ : Measurable Z) (hZrange : ∀ a, Z a∈Icc (0:ℝ) hi)
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (reverse : Bool) :
    (∫ b, (∫ v, (∫ x, (∫ t,
      mixedClockGapLossDirection P known (reservoirCoordinates.symm b) (Z b) reverse v x t
        ∂Instance.uniformClock) ∂ρ) ∂Instance.clocksLaw n) ∂P.trainingCoordinateLaw k) =
      ∫ x, (∫ q, (∫ t, mixedDataSelectedClockLossDirection P known Z reverse x q t ∂Instance.uniformClock)
        ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ∂ρ := by
  have h := P.mixedDataSelectedCandidateFubini known hbound hZ hZrange ρ
  cases reverse
  · exact h.1
  · exact h.2

theorem Instance.integrable_mixedCandidateDirectionAverage (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x≤1) {Z : ((Fin n × Fin k) → ℝ) → ℝ} {hi : ℝ}
    (hZ : Measurable Z) (hZrange : ∀ a, Z a∈Icc (0:ℝ) hi)
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (reverse : Bool) :
    Integrable (fun x => ∫ q, (∫ t, mixedDataSelectedClockLossDirection P known Z reverse x q t ∂Instance.uniformClock)
      ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ρ := by
  have h := P.integrable_mixedDataSelectedCandidateAverage known hbound hZ hZrange ρ
  cases reverse
  · exact h.1
  · exact h.2

end ProphetSecretary.Model
