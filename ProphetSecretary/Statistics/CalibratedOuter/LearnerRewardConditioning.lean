import ProphetSecretary.Statistics.CalibratedOuter.LearnerReassembly
import ProphetSecretary.Model.EmpiricalConditionalValues
import ProphetSecretary.Model.LearnerConditioning
import ProphetSecretary.Probability.ProductConditioning

/-!
# Conditional reward given the actual cutoff and pilot data

Online reward is first averaged with each realized training transcript and
auxiliary seed fixed. Reassembly then integrates the independent fresh factor.
Product Fubini identifies its outer average with the actual learner reward.
-/

open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model
variable {n : ℕ}

noncomputable def outerFrozenReward (P : Instance n) (m : ℕ) (hm : 1≤m) (L : Learner n (2*m))
    (p : OuterLearnerInput m L) : ℝ :=
  ((outerLearner m hm L).frozenRandomizedPolicy p.1 p.2).expectedReward P

lemma measurable_outerFrozenReward (P : Instance n) (m : ℕ) (hm : 1≤m) (L : Learner n (2*m)) :
    Measurable (outerFrozenReward P m hm L) := (outerLearner m hm L).measurable_frozenExpectedReward P

lemma integrable_outerFrozenReward (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw)
    (m : ℕ) (hm : 1≤m) (L : Learner n (2*m)) :
    Integrable (outerFrozenReward P m hm L) (outerLearnerInputLaw P m L) := by
  exact @Learner.integrable_frozenExpectedReward n (outerSampleBudget m) (outerLearner m hm L) P hP
    (outerLearnerInputLaw P m L) (outerLearnerInputLaw_probability P m L)

noncomputable def outerConditionalReward (P : Instance n) (m : ℕ) (hm : 1≤m) (L : Learner n (2*m))
    (a : OuterObservedData n m) : ℝ :=
  ∫ r, outerFrozenReward P m hm L (outerReassemble m L (a,r)) ∂outerFreshInputLaw P m L

lemma measurable_outerConditionalReward (P : Instance n) (m : ℕ) (hm : 1≤m) (L : Learner n (2*m)) :
    Measurable (outerConditionalReward P m hm L) := by
  have hF := (measurable_outerFrozenReward P m hm L).comp (measurable_outerReassemble m L)
  exact (hF.stronglyMeasurable.integral_prod_right' (ν:=outerFreshInputLaw P m L)).measurable

lemma integrable_outerConditionalReward (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw)
    (m : ℕ) (hm : 1≤m) (L : Learner n (2*m)) :
    Integrable (outerConditionalReward P m hm L) (outerObservedDataLaw P m) := by
  have hMP := outerReassemble_measurePreserving P m L
  have hFI := hMP.integrable_comp_of_integrable (integrable_outerFrozenReward P hP m hm L)
  exact hFI.integral_prod_left

/-- Average over the actual independent outer and fresh sampling blocks. -/
theorem integral_outerConditionalReward (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw)
    (m : ℕ) (hm : 1≤m) (L : Learner n (2*m)) :
    (∫ a, outerConditionalReward P m hm L a ∂outerObservedDataLaw P m)=(outerLearner m hm L).expectedReward P := by
  have hMP := outerReassemble_measurePreserving P m L
  have hFI := hMP.integrable_comp_of_integrable (integrable_outerFrozenReward P hP m hm L)
  have hFub := integral_prod (fun p : OuterObservedData n m × OuterFreshInput m L =>
    outerFrozenReward P m hm L (outerReassemble m L p)) hFI
  have hMap := integral_map (μ:=(outerObservedDataLaw P m).prod (outerFreshInputLaw P m L))
    hMP.measurable.aemeasurable (measurable_outerFrozenReward P m hm L).aestronglyMeasurable
  rw [hMP.map_eq] at hMap
  have hOuter := @Learner.integral_frozenExpectedReward n (outerSampleBudget m) (outerLearner m hm L) P hP
    (outerLearnerInputLaw P m L) (outerLearnerInputLaw_probability P m L)
  exact hFub.symm.trans (hMap.symm.trans hOuter)

/-- The outer conditional reward is an actual conditional expectation. -/
theorem outerConditionalReward_condExp (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw)
    (m : ℕ) (hm : 1≤m) (L : Learner n (2*m)) :
    (outerLearnerInputLaw P m L)[outerFrozenReward P m hm L|
      MeasurableSpace.comap (fun p : OuterLearnerInput m L => (outerSeparate m L p).1) inferInstance]
      =ᵐ[outerLearnerInputLaw P m L] (fun p => outerConditionalReward P m hm L (outerSeparate m L p).1) := by
  have hMP := outerSeparate_measurePreserving P m L
  have hFm := (measurable_outerFrozenReward P m hm L).comp (measurable_outerReassemble m L)
  have hFI := (outerReassemble_measurePreserving P m L).integrable_comp_of_integrable
    (integrable_outerFrozenReward P hP m hm L)
  have h := ProphetSecretary.Probability.condExp_productPair (outerObservedDataLaw P m) (outerFreshInputLaw P m L)
    (outerLearnerInputLaw P m L) hMP hFm hFI
  have hEq : (fun p : OuterLearnerInput m L => outerFrozenReward P m hm L (outerReassemble m L (outerSeparate m L p)))=
      outerFrozenReward P m hm L := by
    funext p
    exact congrArg (outerFrozenReward P m hm L) ((outerReassembly m L).apply_symm_apply p)
  change (outerLearnerInputLaw P m L)[(fun p => outerFrozenReward P m hm L (outerReassemble m L (outerSeparate m L p)))|
      MeasurableSpace.comap (fun p : OuterLearnerInput m L => (outerSeparate m L p).1) inferInstance]
      =ᵐ[outerLearnerInputLaw P m L] (fun p => outerConditionalReward P m hm L (outerSeparate m L p).1) at h
  rw [hEq] at h
  exact h

end ProphetSecretary.Statistics.Calibration
