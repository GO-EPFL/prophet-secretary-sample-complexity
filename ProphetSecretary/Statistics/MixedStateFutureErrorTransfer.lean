import ProphetSecretary.Statistics.StateContinuationRescaling
import ProphetSecretary.Statistics.MixedStateFutureError

/-!
# Transporting mixed child error to the original later path

The exact mixed-law restriction identity includes the retained known labels.
Combined with the proved physical-horizon clock rescaling, it transports an
actual child envelope to all later original states. The common child event is
supplied separately by the constructed reset law.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

lemma mixedEmpiricalInstance_restrictTo_coordinates (P : Instance n) (known A : Finset (Fin n))
    (a : (Fin n × Fin k) → ℝ) :
    (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)).restrictTo A =
      mixedEmpiricalInstance (P.restrictTo A) (knownInState known A)
        (reservoirCoordinates.symm (restrictTrainingCoordinates A a)) := by
  apply Instance.eq_of_law_eq
  funext j
  change (if stateEmbedding A j∈known then _ else _) = (if j∈knownInState known A then _ else _)
  simp only [mem_knownInState]
  rfl

/-- A child envelope, when valid at the actual child coordinates, bounds the
original continuation errors at all later times and all original scalars. -/
theorem Instance.mixedStateFutureError_transfer (P : Instance n) (known : Finset (Fin n))
    (hP : Integrable Instance.maximum P.valuesLaw) {lo hi t₀ : ℝ} (hlo : 0 ≤ lo) (ht₀ : t₀ < 1)
    (q : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ))) (A : Finset (Fin n))
    (hA : ProphetSecretary.Probability.pendingClockSet t₀ q.2 = A)
    (hdom : ∀ s ∈ Icc (0 : ℝ) 1, ∀ ζ ∈ Icc (lo*(1-t₀)) (hi*(1-t₀)),
      let qA := stateTrainingFutureCoordinates A t₀ q
      |(mixedEmpiricalInstance (P.restrictTo A) (knownInState known A) (reservoirCoordinates.symm qA.1)).continuationValue
          (ProphetSecretary.Probability.pendingClockSet s qA.2) (1-s) 1 ζ -
        (P.restrictTo A).continuationValue (ProphetSecretary.Probability.pendingClockSet s qA.2) (1-s) 1 ζ| ≤
        (P.restrictTo A).mixedFutureError (knownInState known A) k (lo*(1-t₀)) (hi*(1-t₀)) qA) :
    ∀ t ∈ Icc t₀ 1, ∀ z ∈ Icc lo hi,
      |(mixedEmpiricalInstance P known (reservoirCoordinates.symm q.1)).continuationValue
          (ProphetSecretary.Probability.pendingClockSet t q.2) (1-t) 1 z -
        P.continuationValue (ProphetSecretary.Probability.pendingClockSet t q.2) (1-t) 1 z| ≤
        P.mixedStateFutureError known k lo hi t₀ q := by
  subst A
  let Q := mixedEmpiricalInstance P known (reservoirCoordinates.symm q.1)
  have hQ := mixedEmpiricalInstance_integrable P hP known (reservoirCoordinates.symm q.1)
  intro t ht z hz
  let s := (t-t₀)/(1-t₀)
  have hd : 0 < 1-t₀ := sub_pos.mpr ht₀
  have hs : s ∈ Icc (0 : ℝ) 1 := ⟨div_nonneg (sub_nonneg.mpr ht.1) hd.le,
    (div_le_one hd).mpr (by linarith only [ht.2])⟩
  have hζ : z*(1-t₀) ∈ Icc (lo*(1-t₀)) (hi*(1-t₀)) :=
    ⟨mul_le_mul_of_nonneg_right hz.1 hd.le,mul_le_mul_of_nonneg_right hz.2 hd.le⟩
  have hsub := hdom s hs (z*(1-t₀)) hζ
  dsimp only [stateTrainingFutureCoordinates,restrictTrainingCoordinates] at hsub
  rw [←mixedEmpiricalInstance_restrictTo_coordinates P known (ProphetSecretary.Probability.pendingClockSet t₀ q.2) q.1] at hsub
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
  rw [P.mixedStateFutureError_eq]
  exact hsub

end ProphetSecretary.Model
