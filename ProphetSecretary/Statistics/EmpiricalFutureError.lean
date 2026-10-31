import ProphetSecretary.Statistics.EmpiricalCountableFutureError
import ProphetSecretary.Statistics.EmpiricalUniformLocalization
import ProphetSecretary.Probability.PendingStateLeftLimit
import ProphetSecretary.Probability.RationalObservationTimes

/-!
# A uniform empirical error for every later finite state

The countable conditional maximum is taken over a fixed rational enumeration.
Pathwise left limits extend the common bound to all real elapsed times,
including the terminal time. Thus E_a controls every scalar coefficient and
all later states on a single probability-one event. Its localized moment
constants are explicit and independent of instance size.
-/

open MeasureTheory Set Filter
open scoped Classical Topology

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

noncomputable def Instance.empiricalFutureError (P : Instance n) (k : ℕ) [NeZero k]
    (lo hi : ℝ) := P.empiricalCountableFutureError k lo hi ProphetSecretary.Probability.rationalObservationTime

lemma Instance.measurable_empiricalFutureError (P : Instance n) (lo hi : ℝ) :
    Measurable (P.empiricalFutureError k lo hi) := P.measurable_empiricalCountableFutureError _ _ _

/-- The complete-path suffix comparison in `upstat:suffix`, uniform over every
later state and all interval weights on the same training/clock outcome. -/
theorem Instance.empiricalFutureError_dominates (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {lo hi : ℝ} (hlo : 0 ≤ lo) (hlohi : lo ≤ hi) :
    ∀ᵐ q ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n),
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ Icc lo hi,
      |(totalEmpiricalInstance (reservoirCoordinates.symm q.1)).continuationValue
          (ProphetSecretary.Probability.pendingClockSet t q.2) (1-t) 1 z -
        P.continuationValue (ProphetSecretary.Probability.pendingClockSet t q.2) (1-t) 1 z| ≤
      P.empiricalFutureError k lo hi q := by
  have hb := P.empiricalCountableFutureError_dominates (k := k) hbound hlo hlohi
    ProphetSecretary.Probability.rationalObservationTime ProphetSecretary.Probability.rationalObservationTime_mem
  have hP := P.integrable_maximum_of_bounded hbound
  filter_upwards [hb] with q hq
  intro t ht z hz
  let Q := totalEmpiricalInstance (reservoirCoordinates.symm q.1)
  have hQ := totalEmpiricalInstance_integrable (reservoirCoordinates.symm q.1)
  have hz0 : 0 ≤ z := hlo.trans hz.1
  let F : ℝ → ℝ := fun s => |Q.continuationValue (ProphetSecretary.Probability.pendingClockSet s q.2)
      (max 0 (1-s)) 1 z - P.continuationValue (ProphetSecretary.Probability.pendingClockSet s q.2) (max 0 (1-s)) 1 z|
  have hF : Tendsto F (𝓝[<] t) (𝓝 (F t)) :=
    continuous_abs.continuousAt.tendsto.comp
      ((ProphetSecretary.Probability.pendingContinuationValue_tendsto_left Q hQ hz0 q.2 t).sub
        (ProphetSecretary.Probability.pendingContinuationValue_tendsto_left P hP hz0 q.2 t))
  have hall : ∀ j, F (ProphetSecretary.Probability.rationalObservationTime j) ≤ P.empiricalFutureError k lo hi q := by
    intro j
    have hj := ProphetSecretary.Probability.rationalObservationTime_mem j
    change |Q.continuationValue _ (max 0 (1-ProphetSecretary.Probability.rationalObservationTime j)) 1 z -
      P.continuationValue _ (max 0 (1-ProphetSecretary.Probability.rationalObservationTime j)) 1 z| ≤ _
    rw [max_eq_right (sub_nonneg.mpr hj.2.le)]
    exact hq j z hz
  have he : F t ≤ P.empiricalFutureError k lo hi q := by
    by_cases ht0 : t = 0
    · have hzero := ProphetSecretary.Probability.rationalObservationTime_covers (0 : ℚ)
        (by norm_num : ((0 : ℚ) : ℝ) ∈ Ico (0 : ℝ) 1)
      have h := hall (Encodable.encode (0 : ℚ))
      simpa only [hzero, Rat.cast_zero, ht0] using h
    · exact ProphetSecretary.Probability.le_of_rationalObservationTime_left_limit
        (lt_of_le_of_ne ht.1 (Ne.symm ht0)) ht.2 hF hall
  change |Q.continuationValue _ (1-t) 1 z - P.continuationValue _ (1-t) 1 z| ≤ _
  simpa only [F, max_eq_right (sub_nonneg.mpr ht.2)] using he

/-- Localized second moment in `upstat:suffix`, before restarting at an entrance. -/
theorem Instance.empiricalFutureError_secondMoment_localized (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {lo hi u a : ℝ}
    (hlo : 0 ≤ lo) (hlohi : lo ≤ hi) (hhi : 0 < hi) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hValue : optimalScalarValue P 1 (hi*u) ≤ a) :
    Integrable (fun q => P.empiricalFutureError k (lo*u) (hi*u) q ^ 2)
      ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ∧
    (∫ q, P.empiricalFutureError k (lo*u) (hi*u) q ^ 2
      ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ≤
      (16 * (18 * (128 + 4 * (hi-lo)^2 / hi))) * (a / (k : ℝ) + 1 / (k : ℝ)^2) := by
  have hm := P.empiricalCountableFutureError_moment (k := k) hbound (lo*u) (hi*u)
    ProphetSecretary.Probability.rationalObservationTime (Or.inl rfl)
  refine ⟨hm.1, ?_⟩
  have he := P.empiricalUniformResidualEnvelope_two_localized (k := k) hbound hlo hlohi hhi hu0 hu1 hValue
  have hb := mul_le_mul_of_nonneg_left he (by norm_num : (0 : ℝ) ≤ 16)
  norm_num at hm
  exact hm.2.trans (by simpa only [mul_assoc] using hb)

/-- Localized sixth moment, with the same all-state envelope. -/
theorem Instance.empiricalFutureError_sixthMoment_localized (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {lo hi u a : ℝ}
    (hlo : 0 ≤ lo) (hlohi : lo ≤ hi) (hhi : 0 < hi) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hValue : optimalScalarValue P 1 (hi*u) ≤ a) :
    Integrable (fun q => P.empiricalFutureError k (lo*u) (hi*u) q ^ 6)
      ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ∧
    (∫ q, P.empiricalFutureError k (lo*u) (hi*u) q ^ 6
      ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ≤
      (832 * (23328 * (2 * (6672000000000 ^ 2 + 13348000000000) +
        (106000000000 ^ 2 + 212000000000) * (hi-lo)^6 / hi^3))) *
        (a^3 / (k : ℝ)^3 + 1 / (k : ℝ)^6) := by
  have hm := P.empiricalCountableFutureError_moment (k := k) hbound (lo*u) (hi*u)
    ProphetSecretary.Probability.rationalObservationTime (Or.inr rfl)
  refine ⟨hm.1, ?_⟩
  have he := P.empiricalUniformResidualEnvelope_six_localized (k := k) hbound hlo hlohi hhi hu0 hu1 hValue
  have hb := mul_le_mul_of_nonneg_left he (by norm_num : (0 : ℝ) ≤ 832)
  norm_num at hm
  exact hm.2.trans (by simpa only [mul_assoc] using hb)

end ProphetSecretary.Model
