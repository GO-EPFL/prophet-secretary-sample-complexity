import ProphetSecretary.Statistics.MixedCandidateFubini
import ProphetSecretary.Statistics.MixedDataSelectedCandidateRate

/-!
# Integrating the actual mixed rate against an independent true candidate

The unconditional per-value rate is integrated using proved joint loss
integrability and Fubini. Its coefficient is the original scalar-interval
constant and remains uniform in the set of exact known marginals.
-/

open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Model
variable {n k : ℕ} [NeZero k]

theorem Instance.integrated_mixedCandidateDirection_rate (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x≤1) {Z : ((Fin n × Fin k) → ℝ) → ℝ} {lo hi : ℝ}
    (hZ : Measurable Z) (hlo : 0<lo) (hlohi : lo≤hi) (hZrange : ∀ a, Z a∈Icc lo hi)
    (ρ : Measure ℝ) [IsProbabilityMeasure ρ]
    (hρ0 : ∀ᵐ x ∂ρ, 0≤x) (hρI : Integrable (fun x : ℝ => x) ρ) (reverse : Bool) :
    (∫ b, (∫ v, (∫ x, (∫ t,
      mixedClockGapLossDirection P known (reservoirCoordinates.symm b) (Z b) reverse v x t
        ∂Instance.uniformClock) ∂ρ) ∂Instance.clocksLaw n) ∂P.trainingCoordinateLaw k) ≤
      empiricalCandidateRegretConstant lo hi*(1+P.totalFirstMoment)*(∫ x, x ∂ρ)/(k:ℝ) := by
  let C := empiricalCandidateRegretConstant lo hi*(1+P.totalFirstMoment)/(k:ℝ)
  have hz0 : ∀ a, Z a∈Icc (0:ℝ) hi := fun a => ⟨(hlo.trans_le (hZrange a).1).le,(hZrange a).2⟩
  have he := P.mixedCandidateDirectionFubini known hbound hZ hz0 ρ reverse
  have hI := P.integrable_mixedCandidateDirectionAverage known hbound hZ hz0 ρ reverse
  rw [he]
  calc
    _ ≤ ∫ x, C*x ∂ρ := integral_mono_ae hI (hρI.const_mul C) (hρ0.mono fun x hx =>
      (P.mixedDataSelectedClockLossDirection_rate known hbound hZ hlo hlohi hZrange hx reverse).trans_eq (by dsimp [C]; ring))
    _ = _ := by rw [integral_const_mul]; dsimp [C]; ring

end ProphetSecretary.Model
