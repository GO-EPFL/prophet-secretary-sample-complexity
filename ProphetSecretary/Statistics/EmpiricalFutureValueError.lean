import ProphetSecretary.Probability.CensoredContinuation
import ProphetSecretary.Statistics.EmpiricalUniformEnvelope

/-!
# Uniform future value errors as actual conditional expectations

Training is held fixed while pending uniform clocks are resampled. The proved
continuation residual comparison and the complete-path uniform envelope give a
single almost-sure bound for every scalar in the interval, including scalars
selected from the training array. Conditioning retains only elapsed clocks.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

lemma Instance.integrable_empiricalUniformResidualEnvelope (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) (lo hi : ℝ) :
    Integrable (P.empiricalUniformResidualEnvelope k lo hi)
      ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) := by
  have hP := P.integrable_maximum_of_bounded hbound
  have hI := (P.empiricalUniformResidualEnvelope_moment (k := k) hbound (Or.inl rfl) lo hi).1
  apply ((integrable_const (1 : ℝ)).add hI).mono'
    (P.measurable_empiricalUniformResidualEnvelope hP lo hi).aestronglyMeasurable
  exact Eventually.of_forall fun v => by
    change ‖P.empiricalUniformResidualEnvelope k lo hi v‖ ≤ 1 + P.empiricalUniformResidualEnvelope k lo hi v ^ 2
    rw [Real.norm_eq_abs, abs_of_nonneg (P.empiricalUniformResidualEnvelope_nonnegative lo hi v)]
    nlinarith [sq_nonneg (P.empiricalUniformResidualEnvelope k lo hi v - 1)]

/-- This is the future-state comparison underlying `upstat:suffix`, before Doob
maximization over elapsed time. No unbiasedness is used after choosing z. -/
theorem Instance.empirical_future_value_error_le_condExp (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1)
    {lo hi t : ℝ} (hlo : 0 ≤ lo) (hlohi : lo ≤ hi) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    let μ := (P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)
    let E := P.empiricalUniformResidualEnvelope k lo hi
    ∀ᵐ q : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) ∂μ,
      ∀ z ∈ Icc lo hi,
        |(totalEmpiricalInstance (reservoirCoordinates.symm q.1)).continuationValue
            (ProphetSecretary.Probability.pendingClockSet t q.2) (1-t) 1 z -
          P.continuationValue (ProphetSecretary.Probability.pendingClockSet t q.2) (1-t) 1 z| ≤
          2 * μ[E | ProphetSecretary.Probability.dataClockHistorySigma ((Fin n × Fin k) → ℝ) n t] q := by
  let μ := (P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)
  let E := P.empiricalUniformResidualEnvelope k lo hi
  have hP := P.integrable_maximum_of_bounded hbound
  have hEm : Measurable E := P.measurable_empiricalUniformResidualEnvelope hP lo hi
  have hEI : Integrable E μ := P.integrable_empiricalUniformResidualEnvelope hbound lo hi
  have hMP := ProphetSecretary.Probability.resampleDataClocks_measurePreserving (n := n)
    (P.trainingCoordinateLaw k) ht0 ht1
  have hRI := hMP.integrable_comp_of_integrable hEI
  have hdom := hMP.quasiMeasurePreserving.ae
    (P.empiricalUniformResidualEnvelope_dominates (k := k) hbound hlo hlohi)
  have hCE := ProphetSecretary.Probability.condExp_dataClockHistory (n := n) (P.trainingCoordinateLaw k) ht0 ht1 hEm hEI
  filter_upwards [Measure.ae_ae_of_ae_prod hdom, hRI.prod_right_ae, hCE] with q hq hInt hce
  intro z hz
  let Q := totalEmpiricalInstance (reservoirCoordinates.symm q.1)
  have hQ := totalEmpiricalInstance_integrable (reservoirCoordinates.symm q.1)
  have hz0 : 0 ≤ z := hlo.trans hz.1
  have hv := ProphetSecretary.Probability.abs_value_difference_pending_le_refreshEnvelope Q P hQ hP
    ht1 (by norm_num : (0 : ℝ) < 1) hz0 q.2
  have hI : Integrable (fun v => Q.residualSuffixEnvelope P 1 z
      (ProphetSecretary.Probability.refreshClocks t (q.2,v))) (Instance.clocksLaw n) :=
    Q.integrable_residualSuffixEnvelope_comp P hQ hP (by norm_num : (0 : ℝ) < 1) hz0 _ _
      ((ProphetSecretary.Probability.measurable_refreshClocks t).comp (measurable_const.prodMk measurable_id))
  have hmean := integral_mono_ae hI hInt (hq.mono (fun v hv => hv z hz))
  have hfinal := hv.trans (mul_le_mul_of_nonneg_left hmean (by norm_num : (0 : ℝ) ≤ 2))
  rw [hce]
  exact hfinal

end ProphetSecretary.Model
