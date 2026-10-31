import ProphetSecretary.Statistics.StateFutureErrorFixedDomination
import ProphetSecretary.Statistics.PendingValueEnvelopeExtension

/-!
# Common actual later-error domination after a fixed prefix

Fixed-parameter domination is intersected over two countable unit grids and
extended by proved scalar continuity and one-sided state limits. Thus the raw
state-local envelope controls all later original-path states and coefficients
on one probability-one event. The conditional reset law is fully constructed.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

theorem Instance.stateFutureError_dominates_later (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {lo hi t₀ : ℝ}
    (hlo : 0 ≤ lo) (hlohi : lo ≤ hi) (ht₀0 : 0 ≤ t₀) (ht₀1 : t₀ < 1) :
    ∀ᵐ q ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n),
      ∀ t ∈ Icc t₀ 1, ∀ z ∈ Icc lo hi,
      |(totalEmpiricalInstance (reservoirCoordinates.symm q.1)).continuationValue
          (ProphetSecretary.Probability.pendingClockSet t q.2) (1-t) 1 z -
        P.continuationValue (ProphetSecretary.Probability.pendingClockSet t q.2) (1-t) 1 z| ≤
      P.stateFutureError k lo hi t₀ q := by
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
      |(totalEmpiricalInstance (reservoirCoordinates.symm q.1)).continuationValue
          (ProphetSecretary.Probability.pendingClockSet (T j) q.2) (max 0 (1-T j)) 1 (Z l) -
        P.continuationValue (ProphetSecretary.Probability.pendingClockSet (T j) q.2) (max 0 (1-T j)) 1 (Z l)| ≤
      P.stateFutureError k lo hi t₀ q := by
    apply ae_all_iff.mpr
    intro j
    apply ae_all_iff.mpr
    intro l
    have h := P.stateFutureError_fixedLater_dominates (k := k) hbound hlo hlohi ht₀0 ht₀1 (hT j) (hZ l)
    simpa only [max_eq_right (sub_nonneg.mpr (hT j).2)] using h
  have hP := P.integrable_maximum_of_bounded hbound
  filter_upwards [hgrid] with q hq
  let Q := totalEmpiricalInstance (reservoirCoordinates.symm q.1)
  have hQ := totalEmpiricalInstance_integrable (reservoirCoordinates.symm q.1)
  have hAll := pendingValueError_extend_unitGrid Q P hQ hP hlo hlohi ht₀1 q.2 hq
  intro t ht z hz
  have h := hAll t ht z hz
  simpa only [max_eq_right (sub_nonneg.mpr ht.2)] using h

end ProphetSecretary.Model
