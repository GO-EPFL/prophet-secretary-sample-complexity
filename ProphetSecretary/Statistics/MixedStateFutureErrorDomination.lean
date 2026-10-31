import ProphetSecretary.Statistics.MixedStateFutureErrorFixedDomination
import ProphetSecretary.Statistics.PendingValueEnvelopeExtension

/-!
# Common mixed error domination after an actual fixed prefix

Two countable grids and proved scalar/time limits extend the actual fixed-time
comparison to one event controlling all later times and interval scalars. The
child reset and known-label restriction are constructed rather than assumed.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

theorem Instance.mixedStateFutureError_dominates_later (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {lo hi t₀ : ℝ}
    (hlo : 0 ≤ lo) (hlohi : lo ≤ hi) (ht₀0 : 0 ≤ t₀) (ht₀1 : t₀ < 1) :
    ∀ᵐ q ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n),
      ∀ t ∈ Icc t₀ 1, ∀ z ∈ Icc lo hi,
      |(mixedEmpiricalInstance P known (reservoirCoordinates.symm q.1)).continuationValue
          (ProphetSecretary.Probability.pendingClockSet t q.2) (1-t) 1 z -
        P.continuationValue (ProphetSecretary.Probability.pendingClockSet t q.2) (1-t) 1 z| ≤
      P.mixedStateFutureError known k lo hi t₀ q := by
  let T : ℕ → ℝ := fun j => t₀+(1-t₀)*ProphetSecretary.Probability.rationalObservationTime j
  let Z : ℕ → ℝ := fun l => lo+(hi-lo)*ProphetSecretary.Probability.rationalObservationTime l
  have hT (j : ℕ) : T j ∈ Icc t₀ 1 := by
    have hj := ProphetSecretary.Probability.rationalObservationTime_mem j
    have hnn := mul_nonneg (sub_nonneg.mpr ht₀1.le) hj.1
    have hup := mul_le_mul_of_nonneg_left hj.2.le (sub_nonneg.mpr ht₀1.le)
    dsimp [T]
    constructor <;> nlinarith only [hnn,hup]
  have hZ (l : ℕ) : Z l ∈ Icc lo hi := by
    have hl := ProphetSecretary.Probability.rationalObservationTime_mem l
    have hnn := mul_nonneg (sub_nonneg.mpr hlohi) hl.1
    have hup := mul_le_mul_of_nonneg_left hl.2.le (sub_nonneg.mpr hlohi)
    dsimp [Z]
    constructor <;> nlinarith only [hnn,hup]
  have hgrid : ∀ᵐ q ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n), ∀ j l,
      |(mixedEmpiricalInstance P known (reservoirCoordinates.symm q.1)).continuationValue
          (ProphetSecretary.Probability.pendingClockSet (T j) q.2) (max 0 (1-T j)) 1 (Z l) -
        P.continuationValue (ProphetSecretary.Probability.pendingClockSet (T j) q.2) (max 0 (1-T j)) 1 (Z l)| ≤
      P.mixedStateFutureError known k lo hi t₀ q := by
    apply ae_all_iff.mpr
    intro j
    apply ae_all_iff.mpr
    intro l
    have h := P.mixedStateFutureError_fixedLater_dominates (k := k) known hbound hlo hlohi ht₀0 ht₀1 (hT j) (hZ l)
    simpa only [max_eq_right (sub_nonneg.mpr (hT j).2)] using h
  have hP := P.integrable_maximum_of_bounded hbound
  filter_upwards [hgrid] with q hq
  let Q := mixedEmpiricalInstance P known (reservoirCoordinates.symm q.1)
  have hQ := mixedEmpiricalInstance_integrable P hP known (reservoirCoordinates.symm q.1)
  have hAll := pendingValueError_extend_unitGrid Q P hQ hP hlo hlohi ht₀1 q.2 hq
  intro t ht z hz
  have h := hAll t ht z hz
  simpa only [max_eq_right (sub_nonneg.mpr ht.2)] using h

end ProphetSecretary.Model
