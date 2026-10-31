import ProphetSecretary.Limiting.CountableValueOutcomeLimit
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Expected outcomes of actual canonical finite truncations

Almost-sure reward/duration convergence has already been proved on the common
online world. Bounded domination now transfers those outcomes to their actual
expectations, including the policy's independent seed law.
-/

open MeasureTheory Set Filter
open scoped Topology NNReal Classical

namespace ProphetSecretary.Limiting.CountableInstance

theorem valuePolicy_truncation_means_tendsto (B : CountableInstance) (hZero : B.terminal = 0)
    {w c : ℝ} (hw : 0 < w) (hc : 0 < c) :
    Tendsto (fun N => (B.truncatedValuePolicy N (B.markCutoff N) (B.terminal_lt_markCutoff N) hw.le hc.le).expectedReward)
      atTop (𝓝 (B.valuePolicy hw hc).expectedReward) ∧
    Tendsto (fun N => (B.truncatedValuePolicy N (B.markCutoff N) (B.terminal_lt_markCutoff N) hw.le hc.le).expectedDuration)
      atTop (𝓝 (B.valuePolicy hw hc).expectedDuration) := by
  let μ := B.completeWorldLaw (Measure.dirac ())
  let Rs : ℕ → CompleteWorld Unit → ℝ := fun N =>
    (B.truncatedValueRule N (B.markCutoff N) (B.terminal_lt_markCutoff N) w c).realizedReward B.terminal
  let Ts : ℕ → CompleteWorld Unit → ℝ := fun N =>
    (B.truncatedValueRule N (B.markCutoff N) (B.terminal_lt_markCutoff N) w c).realizedDuration
  let R := (B.valueRule w c).realizedReward B.terminal
  let T := (B.valueRule w c).realizedDuration
  have hRule (N : ℕ) : (B.truncatedValueRule N (B.markCutoff N) (B.terminal_lt_markCutoff N) w c).IsMeasurable :=
    extendTruncatedRule_measurable _ ((B.truncation N (B.markCutoff N) (B.terminal_lt_markCutoff N)).valueRule_isMeasurable hw.le hc.le) _
  have hRm : ∀ᶠ N in atTop, AEStronglyMeasurable (Rs N) μ := Eventually.of_forall fun N =>
    ((B.truncatedValueRule N (B.markCutoff N) (B.terminal_lt_markCutoff N) w c).measurable_realizedReward (hRule N) B.terminal).aestronglyMeasurable
  have hTm : ∀ᶠ N in atTop, AEStronglyMeasurable (Ts N) μ := Eventually.of_forall fun N =>
    ((B.truncatedValueRule N (B.markCutoff N) (B.terminal_lt_markCutoff N) w c).measurable_realizedDuration (hRule N)).aestronglyMeasurable
  have hRb : ∀ᶠ N in atTop, ∀ᵐ v ∂μ, ‖Rs N v‖ ≤ (B.cap : ℝ) := by
    apply Eventually.of_forall
    intro N
    filter_upwards [(B.truncatedValueRule N (B.markCutoff N) (B.terminal_lt_markCutoff N) w c).reward_bounded B (Measure.dirac ())] with v hv
    change ‖(B.truncatedValueRule N (B.markCutoff N) (B.terminal_lt_markCutoff N) w c).realizedReward B.terminal v‖ ≤ _
    rw [Real.norm_eq_abs,abs_of_nonneg hv.1]
    exact hv.2
  have hTb : ∀ᶠ N in atTop, ∀ᵐ v ∂μ, ‖Ts N v‖ ≤ (1 : ℝ) := by
    apply Eventually.of_forall
    intro N
    apply Eventually.of_forall
    intro v
    have hv := (B.truncatedValueRule N (B.markCutoff N) (B.terminal_lt_markCutoff N) w c).duration_bounds v
    change ‖(B.truncatedValueRule N (B.markCutoff N) (B.terminal_lt_markCutoff N) w c).realizedDuration v‖ ≤ _
    rw [Real.norm_eq_abs,abs_of_nonneg hv.1]
    exact hv.2
  have hOutcome := B.valueRule_truncation_outcomes_tendsto_ae hZero hw hc
  have hRlim : ∀ᵐ v ∂μ, Tendsto (fun N => Rs N v) atTop (𝓝 (R v)) := hOutcome.mono (fun _ h => h.1)
  have hTlim : ∀ᵐ v ∂μ, Tendsto (fun N => Ts N v) atTop (𝓝 (T v)) := hOutcome.mono (fun _ h => h.2)
  have hRI : Integrable (fun _ : CompleteWorld Unit => (B.cap : ℝ)) μ := integrable_const _
  have hTI : Integrable (fun _ : CompleteWorld Unit => (1 : ℝ)) μ := integrable_const _
  have hR := tendsto_integral_filter_of_dominated_convergence (fun _ : CompleteWorld Unit => (B.cap : ℝ)) hRm hRb hRI hRlim
  have hT := tendsto_integral_filter_of_dominated_convergence (fun _ : CompleteWorld Unit => (1 : ℝ)) hTm hTb hTI hTlim
  have heRN (N : ℕ) : (B.truncatedValuePolicy N (B.markCutoff N) (B.terminal_lt_markCutoff N) hw.le hc.le).expectedReward = ∫ v, Rs N v ∂μ := rfl
  have heTN (N : ℕ) : (B.truncatedValuePolicy N (B.markCutoff N) (B.terminal_lt_markCutoff N) hw.le hc.le).expectedDuration = ∫ v, Ts N v ∂μ := rfl
  have heR : (B.valuePolicy hw hc).expectedReward = ∫ v, R v ∂μ := rfl
  have heT : (B.valuePolicy hw hc).expectedDuration = ∫ v, T v ∂μ := rfl
  constructor
  · simpa only [heRN,heR] using hR
  · simpa only [heTN,heT] using hT

end ProphetSecretary.Limiting.CountableInstance
