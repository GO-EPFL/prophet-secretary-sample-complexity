import ProphetSecretary.Statistics.StateContinuationRescaling

/-!
# Transferring a child envelope to the original later path

This deterministic implication transports a proved child-state envelope through
the actual identity restriction and normalized clocks. Its probability-one
premise will be supplied by the constructed reset law, rather than assumed for
a random state. Scalar interval weights are rescaled with the physical horizon.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

/-- A child envelope, when valid at the actual child coordinates, bounds the
original continuation errors at all later times and all original scalars. -/
theorem Instance.stateFutureError_transfer (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {lo hi t₀ : ℝ} (hlo : 0 ≤ lo) (ht₀ : t₀ < 1)
    (q : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ))) (A : Finset (Fin n))
    (hA : ProphetSecretary.Probability.pendingClockSet t₀ q.2 = A)
    (hdom : ∀ s ∈ Icc (0 : ℝ) 1, ∀ ζ ∈ Icc (lo*(1-t₀)) (hi*(1-t₀)),
      let qA := stateTrainingFutureCoordinates A t₀ q
      |(totalEmpiricalInstance (reservoirCoordinates.symm qA.1)).continuationValue
          (ProphetSecretary.Probability.pendingClockSet s qA.2) (1-s) 1 ζ -
        (P.restrictTo A).continuationValue (ProphetSecretary.Probability.pendingClockSet s qA.2) (1-s) 1 ζ| ≤
        (P.restrictTo A).empiricalFutureError k (lo*(1-t₀)) (hi*(1-t₀)) qA) :
    ∀ t ∈ Icc t₀ 1, ∀ z ∈ Icc lo hi,
      |(totalEmpiricalInstance (reservoirCoordinates.symm q.1)).continuationValue
          (ProphetSecretary.Probability.pendingClockSet t q.2) (1-t) 1 z -
        P.continuationValue (ProphetSecretary.Probability.pendingClockSet t q.2) (1-t) 1 z| ≤
        P.stateFutureError k lo hi t₀ q := by
  subst A
  let Q := totalEmpiricalInstance (reservoirCoordinates.symm q.1)
  have hQ := totalEmpiricalInstance_integrable (reservoirCoordinates.symm q.1)
  intro t ht z hz
  let s := (t-t₀)/(1-t₀)
  have hd : 0 < 1-t₀ := sub_pos.mpr ht₀
  have hs : s ∈ Icc (0 : ℝ) 1 := ⟨div_nonneg (sub_nonneg.mpr ht.1) hd.le,
    (div_le_one hd).mpr (by linarith only [ht.2])⟩
  have hζ : z*(1-t₀) ∈ Icc (lo*(1-t₀)) (hi*(1-t₀)) :=
    ⟨mul_le_mul_of_nonneg_right hz.1 hd.le,mul_le_mul_of_nonneg_right hz.2 hd.le⟩
  have hsub := hdom s hs (z*(1-t₀)) hζ
  have hz0 : 0 ≤ z := hlo.trans hz.1
  have hRQ := Q.pendingContinuationValue_rescale hQ hz0 ht₀ ht.1 ht.2 q.2
  have hRP := P.pendingContinuationValue_rescale hP hz0 ht₀ ht.1 ht.2 q.2
  change |(Q.restrictTo (ProphetSecretary.Probability.pendingClockSet t₀ q.2)).continuationValue
      (ProphetSecretary.Probability.pendingClockSet s (ProphetSecretary.Probability.normalizedStateClocks t₀ q.2))
      (1-s) 1 (z*(1-t₀)) -
    (P.restrictTo (ProphetSecretary.Probability.pendingClockSet t₀ q.2)).continuationValue
      (ProphetSecretary.Probability.pendingClockSet s (ProphetSecretary.Probability.normalizedStateClocks t₀ q.2))
      (1-s) 1 (z*(1-t₀))| ≤ _ at hsub
  rw [hRQ,hRP] at hsub
  rw [P.stateFutureError_eq]
  exact hsub

end ProphetSecretary.Model
