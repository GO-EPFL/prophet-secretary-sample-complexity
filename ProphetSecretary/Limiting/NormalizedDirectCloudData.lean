import ProphetSecretary.Limiting.NormalizedDirectIndividualData
import ProphetSecretary.Limiting.DirectScheduledCloudScores
import ProphetSecretary.Limiting.DirectScheduledCloudMaximumScore

/-!
# Actual normalized and reversed cloud-score data

The same fixed base mean rescales all laws at one array index. The reversed
score preserves its global unit bound, mean and information under the actual
normalized product law. Its information bound is twice the finite intensity
of the chosen positive band, with no total-first-moment assumption.
-/
open MeasureTheory Set
open scoped Classical Topology NNReal
namespace ProphetSecretary.Limiting.CountableInstance
open ProphetSecretary.Model ProphetSecretary.Probability

noncomputable def normalizedDirectCloudScore (B : CountableInstance) (hZero : B.terminal=0)
    (J : ℕ) (S : Set ℝ) (m : ℕ) : Fin (B.shiftedDirectSize hZero J m) → ℝ → ℝ :=
  fun j y => -fixedBaseNormalizedScore (B.shiftedDirectMean hZero J m)
    (B.directScheduledCloudScore hZero S (m+J)) j y

lemma normalizedDirectCloudScore_properties (B : CountableInstance) (hZero : B.terminal=0)
    (hMean : B.expectedMaximum=1) {J : ℕ} (hJ : B.directNormalizationStart hZero hMean≤J)
    {S : Set ℝ} (hS : MeasurableSet S) {b : ℝ} (hb : (B.terminal:ℝ)<b) (hSub : S⊆Ioi b) (m : ℕ) :
    (∀ j, Measurable (B.normalizedDirectCloudScore hZero J S m j)) ∧
      (∀ j y, |B.normalizedDirectCloudScore hZero J S m j y|≤1) ∧
      (∀ j, (∫ y, B.normalizedDirectCloudScore hZero J S m j y
        ∂(B.normalizedDirectBase hZero hMean hJ m).law j)=0) ∧
      information (B.normalizedDirectBase hZero hMean hJ m).law
        (B.normalizedDirectCloudScore hZero J S m)≤2*B.intensity.real S := by
  have hS0 : (0:ℝ)∉S := fun h => not_lt_of_ge (B.terminal.property.trans hb.le) (hSub h)
  have hRaw := B.directScheduledCloudScore_properties hZero hS hS0 (m+J)
  have hRawInfo := B.directScheduledCloudScore_information_le hZero hS hb hSub (m+J)
  have hPos := B.shiftedDirectMean_positive hZero hMean hJ m
  let h := B.directScheduledCloudScore hZero S (m+J)
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
    change (∫ y, -fixedBaseNormalizedScore M h j y ∂(B.normalizedDirectBase hZero hMean hJ m).law j)=0
    rw [integral_neg]
    exact neg_eq_zero.mpr (hCenter j)
  · unfold information
    simp only [normalizedDirectCloudScore,neg_sq]
    exact hInfoEq.trans_le hRawInfo
end ProphetSecretary.Limiting.CountableInstance
