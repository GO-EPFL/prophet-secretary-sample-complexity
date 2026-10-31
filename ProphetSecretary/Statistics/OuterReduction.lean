import ProphetSecretary.Statistics.OuterPositiveBranch
import ProphetSecretary.Statistics.OuterZeroConditional
import ProphetSecretary.Statistics.OuterGoodData
import ProphetSecretary.Statistics.OuterConditionalMeans
import ProphetSecretary.Analysis.OuterReductionAverage

/-!
# The actual outer reduction from bounded learner guarantees

A single raw learner is fixed before the unknown product law. Its independent
cutoff, pilot, inner, and online experiments were constructed explicitly.
The bounded learner's guarantees are conditional inputs in this theorem. Once
provided uniformly on the eligible class, all outer losses have the explicit
constant 1000001 K+1000000+3C and budget 5m+q_m.
Paper correspondence: the reduction in the proof of `upouter:theorem`.
-/

open MeasureTheory Set Filter
open scoped Classical NNReal
namespace ProphetSecretary.Statistics
open ProphetSecretary.Model ProphetSecretary.Analysis
variable {n : ℕ}

/-- Conditional reduction for the actual law-independent outer learner. The
bounded learner is fixed before the unknown instance is quantified. -/
theorem outer_reduction_of_bounded_guarantees (m : ℕ) (hm : 2000000≤m) (L : Learner n (4*m))
    {C K : ℝ} (hK : 0≤K) (hC : 0≤C) (hCupper : C≤997/1000) (hρ : 0≤C-K/(m:ℝ))
    (hBounded : ∀ Q : Instance n,
      (1/10000000≤Q.expectedMaximum ∧ Q.expectedMaximum≤1/80) →
      Q.positiveCount≤2*Real.log (m:ℝ) →
      (∀ i, ∀ᵐ x ∂Q.law i, x∈meshGrid 1 m) →
      (∀ i, ∀ᵐ x ∂Q.law i, x≤1) →
      (∀ᵐ ω : (L.randomizedPolicy Q).World ∂Q.worldLaw (L.randomizedPolicy Q).seedLaw,
        L.policy.AcceptsReachedCap 1 ω.2.2 ω.1 ω.2.1) ∧
      (C*Q.expectedMaximum-K/(m:ℝ)≤L.expectedReward Q) ∧
      (∀ i, C-K/(m:ℝ)≤L.reachProbability Q i))
    (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw) :
    (C-(outerReductionLocalConstant K+3*C)/(m:ℝ))*P.expectedMaximum≤
      (outerLearner m (by omega) L).expectedReward P := by
  have hm1 : 1≤m := by omega
  let G := outerCountGoodData P m hm1∩outerPilotGoodData P m hm1
  have hG : MeasurableSet G := (measurableSet_outerCountGoodData P m hm1).inter (measurableSet_outerPilotGoodData P m hm1)
  have hD : 0≤outerReductionLocalConstant K := outerReductionLocalConstant_nonneg hK
  have hGood (a : OuterObservedData n m) (ha : a∈G) :
      C*(P.retainedAtTag (outerObservedCutoff m hm1 a)).expectedMaximum-
        outerReductionLocalConstant K*P.expectedMaximum/(m:ℝ)≤outerConditionalReward P m hm1 L a := by
    have hCount : (P.retainedAtTag (outerObservedCutoff m hm1 a)).positiveCount≤2*Real.log (m:ℝ) := ha.1
    have hPilot : a.2∈outerPilotGoodAt P m hm1 (outerObservedCutoff m hm1 a) := ha.2
    have hStrict : (P.retainedAtTag (outerObservedCutoff m hm1 a)).valuesLaw.real
        {x | outerObservedPilot m hm1 a<Instance.maximum x}≤3/1000 := by
      have h : (P.retainedMaximumLaw (outerObservedCutoff m hm1 a)).real (Ioi (outerObservedPilot m hm1 a))≤3/1000 := hPilot.1
      rwa [P.retainedMaximumLaw_Ioi_values] at h
    have hClosed : 1/1000≤(P.retainedAtTag (outerObservedCutoff m hm1 a)).valuesLaw.real
        {x | outerObservedPilot m hm1 a≤Instance.maximum x} := by
      have h : 1/1000≤(P.retainedMaximumLaw (outerObservedCutoff m hm1 a)).real (Ici (outerObservedPilot m hm1 a)) := hPilot.2
      rwa [P.retainedMaximumLaw_Ici_values] at h
    by_cases hB : outerObservedPilot m hm1 a=0
    · have hZero := outerConditionalReward_zero_pilot_ge P hP m hm1 L a hB (by simpa only [hB] using hStrict)
      have hCM := mul_le_mul_of_nonneg_right hCupper (P.retainedAtTag (outerObservedCutoff m hm1 a)).expectedMaximum_nonnegative
      have hLoss : 0≤outerReductionLocalConstant K*P.expectedMaximum/(m:ℝ) :=
        div_nonneg (mul_nonneg hD P.expectedMaximum_nonnegative) (Nat.cast_nonneg m)
      linarith only [hZero,hCM,hLoss]
    · have hBpos : 0<outerObservedPilot m hm1 a :=
        lt_of_le_of_ne (outerObservedPilot_nonnegative m hm1 a) (Ne.symm hB)
      rw [outerConditionalReward_positive_pilot P hP m hm1 L a hBpos]
      exact outer_positive_branch_of_bounded_guarantees P hP m hm (outerObservedCutoff m hm1 a)
        ⟨outerObservedPilot m hm1 a,outerObservedPilot_nonnegative m hm1 a⟩ hBpos L hK
        (by linarith only [hCupper] : C≤1) hρ hStrict hClosed hCount hBounded
  have hAvg := outer_reduction_average (outerObservedDataLaw P m) hm1 hC hD P.expectedMaximum_nonnegative hG
    (outerGoodData_failure_probability P m hm1) (integrable_outerObservedRetainedMaximum P hP m hm1)
    (integrable_outerConditionalReward P hP m hm1 L)
    (fun a => P.retainedAtTag_expectedMaximum_le hP (outerObservedCutoff m hm1 a))
    (outerConditionalReward_nonnegative P m hm1 L) hGood (outerObservedRetainedMaximum_mean P hP m hm1)
  rw [integral_outerConditionalReward P hP m hm1 L] at hAvg
  exact hAvg

end ProphetSecretary.Statistics
