import ProphetSecretary.Statistics.CalibratedOuter.FixedSimulation
import ProphetSecretary.Analysis.OuterReductionLoss

/-!
# Conditional positive-pilot performance from bounded guarantees

The bounded learner's three guarantees are explicit conditional inputs. The
cutoff and pilot events discharge its eligibility conditions; the actual raw
inner/online experiment then loses at most D M/m with D=1000001 K+1000000.
-/

open MeasureTheory Set Filter
open scoped Classical NNReal
namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model ProphetSecretary.Model.Instance ProphetSecretary.Analysis
variable {n : ℕ}

/-- The positive-pilot part of the outer reduction, conditional on the bounded
learner's reward, reach, and reached-cap guarantees on its eligible class. -/
theorem outer_positive_branch_of_bounded_guarantees
    (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw) (m : ℕ) (hm : 2000000≤m)
    (t : ℝ × ℝ) (B : ℝ≥0) (hB : (0:ℝ)<B) (L : Learner n (2*m))
    {C K : ℝ} (hK : 0≤K) (hC : C≤1) (hρ : 0≤C-K/(m:ℝ))
    (hStrict : (P.retainedAtTag t).valuesLaw.real {x | (B:ℝ)<Instance.maximum x}≤3/1000)
    (hClosed : 1/1000≤(P.retainedAtTag t).valuesLaw.real {x | (B:ℝ)≤Instance.maximum x})
    (hCount : (P.retainedAtTag t).positiveCount≤2*Real.log (m:ℝ))
    (hBounded : ∀ Q : Instance n,
      (1/10000000≤Q.expectedMaximum ∧ Q.expectedMaximum≤1/80) →
      Q.positiveCount≤2*Real.log (m:ℝ) →
      (∀ i, ∀ᵐ x ∂Q.law i, x∈meshGrid 1 m) →
      (∀ i, ∀ᵐ x ∂Q.law i, x≤1) →
      (∀ᵐ ω : (L.randomizedPolicy Q).World ∂Q.worldLaw (L.randomizedPolicy Q).seedLaw,
        L.policy.AcceptsReachedCap 1 ω.2.2 ω.1 ω.2.1) ∧
      (C*Q.expectedMaximum-K/(m:ℝ)≤L.expectedReward Q) ∧
      (∀ i, C-K/(m:ℝ)≤L.reachProbability Q i)) :
    C*(P.retainedAtTag t).expectedMaximum-outerReductionLocalConstant K*P.expectedMaximum/(m:ℝ)≤
      (outerFixedRawResponse P m t (outerPilotCap B) L).expectedReward P := by
  let H := outerPilotCap B
  have hH : (0:ℝ)<(H:ℝ) := by change 0<1000*(B:ℝ);positivity
  let Q := P.outerTransformedInstance m (show 0<m by omega) t H
  have hEligibility := outerTransformedInstance_pilot_eligible P hP m hm t B hB hStrict hClosed hCount
  have hBounds := hBounded Q hEligibility.1 hEligibility.2.1 hEligibility.2.2.1 hEligibility.2.2.2.1
  have hSmall : 0≤K/(m:ℝ) := div_nonneg hK (Nat.cast_nonneg m)
  have hR : (C-K/(m:ℝ))*Q.expectedMaximum-K/(m:ℝ)≤L.expectedReward Q := by
    have hMul := mul_le_mul_of_nonneg_right (sub_le_self C hSmall) Q.expectedMaximum_nonnegative
    exact (sub_le_sub_right hMul _).trans hBounds.2.1
  have hGain := outerFixedRawResponse_reward_of_bounded_guarantees P hP m (show 0<m by omega) t H hH L
    hρ hBounds.1 hR hBounds.2.2
  have hPilot := (P.retainedAtTag t).capPilot_scale_bounds (P.retainedAtTag_integrable_maximum hP t) B hB hStrict hClosed
  have hScale : (H:ℝ)≤1000000*P.expectedMaximum :=
    (hPilot.2.2.2.1.trans hPilot.2.2.2.2).trans
      (mul_le_mul_of_nonneg_left (P.retainedAtTag_expectedMaximum_le hP t) (by norm_num))
  exact outer_reduction_local_loss (show 0<m by omega) hK hC (P.retainedAtTag_expectedMaximum_le hP t) H.property hScale hGain

end ProphetSecretary.Statistics.Calibration
