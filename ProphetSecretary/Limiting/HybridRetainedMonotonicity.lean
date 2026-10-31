import ProphetSecretary.Limiting.CompleteVirtualState
import ProphetSecretary.Limiting.BernoulliChildValueApproximation
import ProphetSecretary.Limiting.HybridStrictReach

/-!
# Actual hybrid value monotonicity under retained-state inclusion

Every finite approximation keeps all virtual identities and only varies its
original retained state. The proved finite full-policy value monotonicity
passes to the actual hybrid supremum through the quantitative state error.
The resulting threshold monotonicity applies to the constructed value rule;
it is not asserted for arbitrary competing policies.
-/
open MeasureTheory Set Filter
open scoped Topology NNReal Classical
namespace ProphetSecretary.Limiting
variable {n : ℕ}

lemma FiniteIntensityHybridInstance.remainingHorizon_one (B : FiniteIntensityHybridInstance n) :
    B.remainingHorizon 1 = B := by
  cases B
  simp only [FiniteIntensityHybridInstance.remainingHorizon,one_smul]

/-- Increasing the retained unseen set can only increase the actual
zero-terminal hybrid optimum. The policy supremum remains unrestricted. -/
theorem FiniteIntensityHybridInstance.optimalScalarValue_restrictIndividuals_mono
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal = 0) {A D : Finset (Fin n)} (hAD : A ⊆ D)
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    (B.restrictIndividuals A).optimalScalarValue w c ≤ (B.restrictIndividuals D).optimalScalarValue w c := by
  by_cases hμ : B.intensity = 0
  · rw [(B.restrictIndividuals A).value_zero_intensity ha hμ hw hc,
      (B.restrictIndividuals D).value_zero_intensity ha hμ hw hc]
    exact B.individuals.optimalScalarValue_restrictTo_mono
      (B.individuals.integrable_maximum_of_bounded B.individual_bounded) hAD hw hc
  by_cases hw0 : w = 0
  · subst w
    rw [(B.restrictIndividuals A).value_zero_rewardWeight hc,(B.restrictIndividuals D).value_zero_rewardWeight hc]
  have hwP : 0 < w := lt_of_le_of_ne hw (Ne.symm hw0)
  let rate := (B.intensity : Measure ℝ).real univ
  let qs := fun j => bernoulliMultiplicity rate j
  let ps := fun j => bernoulliProbability rate measureReal_nonneg j
  let Qs := fun j => finitePoissonDesign B.individuals (B.intensity.normalize : Measure ℝ)
    (B.normalizedMark_nonnegative hμ) (ps j) (qs j)
  have hQ (j : ℕ) : Integrable Model.Instance.maximum (Qs j).valuesLaw :=
    finitePoissonDesign_integrable_maximum B.individuals _ _ _ _
      (B.individuals.integrable_maximum_of_bounded B.individual_bounded) (B.normalizedMark_integrable hμ)
  have hBound (S : Finset (Fin n)) (j : ℕ) :
      |Model.optimalScalarValue ((Qs j).restrictTo (completeVirtualState (qs j) S)) w c-
        (B.restrictIndividuals S).optimalScalarValue w c| ≤ B.bernoulliStateError w j := by
    have h := B.bernoulliChild_value_error ha hμ j (completeVirtualState (qs j) S) (1 : ℝ≥0) hwP hc
    dsimp only at h
    rw [completeVirtualState_retained,completeVirtualState_virtual] at h
    simp only [Finset.card_univ,Fintype.card_fin] at h
    have hq0 : (qs j : ℝ≥0) ≠ 0 := by exact_mod_cast (bernoulliMultiplicity_positive rate j).ne'
    rw [div_self hq0] at h
    simp only [NNReal.coe_one,sub_self,abs_zero,mul_zero,zero_mul,add_zero,
      FiniteIntensityHybridInstance.remainingHorizon_one] at h
    exact h
  have hLimit (S : Finset (Fin n)) :
      Tendsto (fun j => Model.optimalScalarValue ((Qs j).restrictTo (completeVirtualState (qs j) S)) w c)
        atTop (𝓝 ((B.restrictIndividuals S).optimalScalarValue w c)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) _ (B.bernoulliStateError_tendsto_zero w)
    intro j
    simpa only [Real.norm_eq_abs] using hBound S j
  apply le_of_tendsto_of_tendsto (hLimit A) (hLimit D)
  exact Eventually.of_forall fun j => (Qs j).optimalScalarValue_restrictTo_mono (hQ j)
    (completeVirtualState_mono hAD) hw hc

/-- Monotonicity is derived for actual-continuation thresholds and only then
used in the Markov threshold reach comparison. -/
theorem FiniteIntensityHybridInstance.valueHybridThreshold_monotone
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal = 0)
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) : MonotoneHybridThresholds (B.valueHybridThreshold w c) := by
  intro _r t _ht
  constructor
  · intro i A D _hi hAD
    apply div_le_div_of_nonneg_right _ hw.le
    exact (B.remainingHorizon (remainingTime t)).optimalScalarValue_restrictIndividuals_mono ha
      (Finset.erase_subset_erase i hAD) hw.le (mul_nonneg hc (remainingTime t).property)
  · intro A D hAD
    apply div_le_div_of_nonneg_right _ hw.le
    exact (B.remainingHorizon (remainingTime t)).optimalScalarValue_restrictIndividuals_mono ha hAD hw.le
      (mul_nonneg hc (remainingTime t).property)

/-- Strict retained reach for the actual-continuation rule, even under another
independent evaluation law. Optimality of that rule is a separate result. -/
theorem FiniteIntensityHybridInstance.valueRule_strict_retained_reach
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal = 0)
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) (P : Model.Instance n) (μ : FiniteMeasure ℝ) (i : Fin n) :
    (B.valueRule w c).individualReachProbability P μ (Measure.dirac ()) i-
      (B.valueRule w c).meanDuration P μ (Measure.dirac ()) ≥
      ((B.valueRule w c).individualSelectionProbability P μ (Measure.dirac ()) i)^2/2 := by
  exact hybridThresholdRule_strict_reach _ (B.valueHybridThreshold_monotone ha hw hc)
    (B.valueRule_isMeasurable hw.le hc) P μ (Measure.dirac ()) i

end ProphetSecretary.Limiting
