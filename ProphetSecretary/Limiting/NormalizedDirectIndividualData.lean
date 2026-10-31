import ProphetSecretary.Limiting.NormalizedDirectLimits
import ProphetSecretary.Limiting.DirectScheduledIndividualScores
import ProphetSecretary.Model.FiniteNormalizationPolicies
import ProphetSecretary.Probability.TargetScoreResponse

/-!
# Concrete normalized individual-score data

The base laws and normalized weights use the prescribed direct schedule after
one fixed tail shift. The score is explicitly reversed. Its centering, global
unit bound and information bound are proved under those actual normalized
laws. The base policy is the transported raw canonical optimizer.
-/

open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Classical Topology NNReal
namespace ProphetSecretary.Limiting.CountableInstance
open ProphetSecretary.Model ProphetSecretary.Probability

noncomputable def directIndividualArrayScore (B : CountableInstance) (hZero : B.terminal=0)
    (i : ℕ) (f : ℝ →ᵇ ℝ) (m : ℕ) : Fin (m+B.directVirtualCount hZero m) → ℝ → ℝ :=
  directIndividualScore (B.individualPrefix m) (B.directVirtualOfferInstance hZero m) i f

lemma directIndividualArrayScore_properties (B : CountableInstance) (hZero : B.terminal=0)
    (i : ℕ) (f : ℝ →ᵇ ℝ) (m : ℕ) :
    (∀ j, Measurable (B.directIndividualArrayScore hZero i f m j)) ∧
      (∀ j x, |B.directIndividualArrayScore hZero i f m j x|≤1) ∧
      (∀ j, (∫ x, B.directIndividualArrayScore hZero i f m j x ∂(B.directFiniteApproximation hZero m).law j)=0) ∧
      information (B.directFiniteApproximation hZero m).law (B.directIndividualArrayScore hZero i f m)≤1 := by
  have h := directIndividualScore_properties (B.individualPrefix m) (B.directVirtualOfferInstance hZero m) i f
  refine ⟨h.1,h.2.1,?_,?_⟩
  · intro j
    rw [B.directFiniteApproximation_eq_appendVirtual hZero m]
    exact h.2.2.1 j
  · rw [B.directFiniteApproximation_eq_appendVirtual hZero m]
    exact h.2.2.2

noncomputable def normalizedDirectIndividualScore (B : CountableInstance) (hZero : B.terminal=0)
    (J : ℕ) (i : ℕ) (f : ℝ →ᵇ ℝ) (m : ℕ) : Fin (B.shiftedDirectSize hZero J m) → ℝ → ℝ :=
  fun j y => -fixedBaseNormalizedScore (B.shiftedDirectMean hZero J m)
    (B.directIndividualArrayScore hZero i f (m+J)) j y

noncomputable def normalizedDirectCanonicalPolicy (B : CountableInstance) (hZero : B.terminal=0)
    (J : ℕ) {w c : ℝ} (hw : 0<w) (hc : 0<c) (m : ℕ) : RandomizedPolicy (B.shiftedDirectSize hZero J m) :=
  (B.directCanonicalPolicy hZero hw hc (m+J)).fixedBaseNormalizedPolicy (B.shiftedDirectMean hZero J m)

lemma normalizedDirectIndividualScore_properties (B : CountableInstance) (hZero : B.terminal=0)
    (hMean : B.expectedMaximum=1) {J : ℕ} (hJ : B.directNormalizationStart hZero hMean≤J)
    (i : ℕ) (f : ℝ →ᵇ ℝ) (m : ℕ) :
    (∀ j, Measurable (B.normalizedDirectIndividualScore hZero J i f m j)) ∧
      (∀ j y, |B.normalizedDirectIndividualScore hZero J i f m j y|≤1) ∧
      (∀ j, (∫ y, B.normalizedDirectIndividualScore hZero J i f m j y
        ∂(B.normalizedDirectBase hZero hMean hJ m).law j)=0) ∧
      information (B.normalizedDirectBase hZero hMean hJ m).law
        (B.normalizedDirectIndividualScore hZero J i f m)≤1 := by
  have hRaw := B.directIndividualArrayScore_properties hZero i f (m+J)
  have hPos := B.shiftedDirectMean_positive hZero hMean hJ m
  let h := B.directIndividualArrayScore hZero i f (m+J)
  let M := B.shiftedDirectMean hZero J m
  have hMeas := fixedBaseNormalizedScore_measurable M hRaw.1
  have hBound := fixedBaseNormalizedScore_bound M hRaw.2.1
  have hCenter := (B.shiftedDirectBase hZero J m).fixedBaseNormalizedScore_centered hPos h hRaw.1 hRaw.2.2.1
  have hInfoEq := (B.shiftedDirectBase hZero J m).fixedBaseNormalizedScore_information hPos h hRaw.1
  refine ⟨(fun j => (hMeas j).neg),?_,?_,?_⟩
  · intro j y
    change |-fixedBaseNormalizedScore M h j y|≤1
    simpa only [abs_neg] using hBound j y
  · intro j
    change (∫ y, -fixedBaseNormalizedScore M h j y
      ∂(B.normalizedDirectBase hZero hMean hJ m).law j)=0
    rw [integral_neg]
    exact neg_eq_zero.mpr (hCenter j)
  · unfold information
    simp only [normalizedDirectIndividualScore,neg_sq]
    exact hInfoEq.trans_le hRaw.2.2.2

private lemma valuePolicy_change_duration {n : ℕ} (P : Model.Instance n)
    (hP0 hP1 : Integrable Model.Instance.maximum P.valuesLaw) {w c0 c1 : ℝ}
    (hC : c0=c1) (hw0 : 0≤w) (hc0 : 0≤c0) (hw1 : 0≤w) (hc1 : 0≤c1) :
    P.valuePolicy hP0 hw0 hc0=P.valuePolicy hP1 hw1 hc1 := by
  cases hC
  rfl

lemma normalizedDirectCanonicalPolicy_eq_canonical (B : CountableInstance) (hZero : B.terminal=0)
    (hMean : B.expectedMaximum=1) {J : ℕ} (hJ : B.directNormalizationStart hZero hMean≤J)
    {w c : ℝ} (hw : 0<w) (hc : 0<c) (m : ℕ)
    (hww : 0≤B.normalizedDirectRewardWeight hZero J w c m)
    (hcc : 0≤1-B.normalizedDirectRewardWeight hZero J w c m) :
    B.normalizedDirectCanonicalPolicy hZero J hw hc m=
      (B.normalizedDirectBase hZero hMean hJ m).valuePolicy
        ((B.normalizedDirectBase hZero hMean hJ m).integrable_maximum_of_bounded
          (B.normalizedDirectBase_cap hZero hMean hJ m)) hww hcc := by
  have hM := B.shiftedDirectMean_positive hZero hMean hJ m
  have hWeights := finiteNormalizationWeights (w:=w) (c:=c) hM hw hc.le
  let Q := B.normalizedDirectBase hZero hMean hJ m
  let hQ := Q.integrable_maximum_of_bounded (B.normalizedDirectBase_cap hZero hMean hJ m)
  have hE : B.normalizedDirectCanonicalPolicy hZero J hw hc m=
      Q.valuePolicy hQ hWeights.1.le hWeights.2.1 := by
    exact ((B.shiftedDirectBase hZero J m).fixedBaseNormalization_canonicalPolicy
      ((B.shiftedDirectBase hZero J m).integrable_maximum_of_bounded (B.directFiniteApproximation_bounded hZero (m+J)))
      hM hw hc.le).symm
  have hC : B.normalizedDirectDurationWeight hZero J w c m=1-B.normalizedDirectRewardWeight hZero J w c m := by
    have hs := B.normalizedDirectWeights_sum hZero hMean hJ hw hc.le m
    linarith only [hs]
  exact hE.trans (valuePolicy_change_duration Q hQ hQ hC hWeights.1.le hWeights.2.1 hww hcc)

lemma normalizedDirectCanonicalPolicy_optimal (B : CountableInstance) (hZero : B.terminal=0)
    (hMean : B.expectedMaximum=1) {J : ℕ} (hJ : B.directNormalizationStart hZero hMean≤J)
    {w c : ℝ} (hw : 0<w) (hc : 0<c) (m : ℕ) :
    (B.normalizedDirectCanonicalPolicy hZero J hw hc m).scalarObjective (B.normalizedDirectBase hZero hMean hJ m)
      (B.normalizedDirectRewardWeight hZero J w c m) (1-B.normalizedDirectRewardWeight hZero J w c m)=
      Model.optimalScalarValue (B.normalizedDirectBase hZero hMean hJ m)
        (B.normalizedDirectRewardWeight hZero J w c m) (1-B.normalizedDirectRewardWeight hZero J w c m) := by
  have hWeights := B.normalizedDirectWeights_sum hZero hMean hJ hw hc.le m
  have hC : 1-B.normalizedDirectRewardWeight hZero J w c m=B.normalizedDirectDurationWeight hZero J w c m := by
    linarith only [hWeights]
  rw [hC]
  apply ((B.directCanonicalPolicy hZero hw hc (m+J)).fixedBaseNormalization_optimal_iff
    (B.shiftedDirectBase hZero J m)
    ((B.shiftedDirectBase hZero J m).integrable_maximum_of_bounded (B.directFiniteApproximation_bounded hZero (m+J)))
    (B.shiftedDirectMean_positive hZero hMean hJ m) hw hc.le).mpr
  exact (B.directFiniteApproximation hZero (m+J)).valuePolicy_optimal
    ((B.directFiniteApproximation hZero (m+J)).integrable_maximum_of_bounded
      (B.directFiniteApproximation_bounded hZero (m+J))) hw hc.le

end ProphetSecretary.Limiting.CountableInstance
