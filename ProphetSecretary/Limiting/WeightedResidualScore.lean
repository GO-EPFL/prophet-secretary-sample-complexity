import ProphetSecretary.Limiting.WeightedOrdering
import ProphetSecretary.Probability.CompensatedCloudScore
import ProphetSecretary.Model.FirstMomentTailCount

/-!
# Finite original-coordinate scores for an ordered residual cloud

Retained coordinates receive score zero. Residual coordinates compensate on
the full complement of the chosen band. The component functions are bounded
and centered under their own original marginal laws; their information bound
is explicit and independent of the number of distributions.
-/
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Classical BigOperators
namespace ProphetSecretary.Limiting
open ProphetSecretary.Probability
variable {n : ℕ}

noncomputable def weightedResidualScore (P : Model.Instance n) (wgt : ℝ →ᵇ ℝ) (N : ℕ) (B : Set ℝ)
    (i : Fin n) (x : ℝ) : ℝ :=
  if N ≤ ((weightedMeanPermutation P wgt).symm i).val then compensatedBandScore (P.law i) B x else 0

lemma measurable_weightedResidualScore (P : Model.Instance n) (wgt : ℝ →ᵇ ℝ) (N : ℕ)
    {B : Set ℝ} (hB : MeasurableSet B) (i : Fin n) : Measurable (weightedResidualScore P wgt N B i) := by
  unfold weightedResidualScore
  by_cases h : N ≤ ((weightedMeanPermutation P wgt).symm i).val
  · simp only [if_pos h]
    exact measurable_compensatedBandScore (P.law i) hB
  · simp only [if_neg h]
    exact measurable_const

lemma weightedResidualScore_centered_bounded (P : Model.Instance n) (wgt : ℝ →ᵇ ℝ) (N : ℕ)
    {B : Set ℝ} (hB : MeasurableSet B)
    (hHalf : ∀ i, N ≤ ((weightedMeanPermutation P wgt).symm i).val → (P.law i).real B≤1/2) :
    (∀ i x, |weightedResidualScore P wgt N B i x|≤1) ∧
      ∀ i, (∫ x, weightedResidualScore P wgt N B i x ∂P.law i)=0 := by
  constructor
  · intro i x
    by_cases h : N ≤ ((weightedMeanPermutation P wgt).symm i).val
    · simpa only [weightedResidualScore,if_pos h] using compensatedBandScore_abs_le_one (P.law i) (hHalf i h) x
    · simp only [weightedResidualScore,if_neg h,abs_zero,zero_le_one]
  · intro i
    by_cases h : N ≤ ((weightedMeanPermutation P wgt).symm i).val
    · simp only [weightedResidualScore,if_pos h]
      exact compensatedBandScore_mean (P.law i) hB (by linarith [hHalf i h])
    · simp only [weightedResidualScore,if_neg h,integral_zero]

lemma weightedResidualScore_information_le (P : Model.Instance n) (wgt : ℝ →ᵇ ℝ) (N : ℕ)
    {B : Set ℝ} (hB : MeasurableSet B)
    (hHalf : ∀ i, N ≤ ((weightedMeanPermutation P wgt).symm i).val → (P.law i).real B≤1/2) :
    information P.law (weightedResidualScore P wgt N B)≤2*(∑ i, (P.law i).real B) := by
  unfold information
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  by_cases h : N ≤ ((weightedMeanPermutation P wgt).symm i).val
  · simp only [weightedResidualScore,if_pos h]
    exact compensatedBandScore_secondMoment_le (P.law i) hB (hHalf i h)
  · simp only [weightedResidualScore,if_neg h,zero_pow (by norm_num : (2:ℕ)≠0),integral_zero]
    exact mul_nonneg (by norm_num) measureReal_nonneg

lemma weightedResidualScore_information_le_firstMoment (P : Model.Instance n)
    (hP : Integrable Model.Instance.maximum P.valuesLaw) (wgt : ℝ →ᵇ ℝ) (N : ℕ)
    {B : Set ℝ} (hB : MeasurableSet B) {b S0 : ℝ} (hb : 0<b) (hAbove : B⊆Ioi b)
    (hS : P.totalFirstMoment≤S0)
    (hHalf : ∀ i, N ≤ ((weightedMeanPermutation P wgt).symm i).val → (P.law i).real B≤1/2) :
    information P.law (weightedResidualScore P wgt N B)≤2*S0/b := by
  have hBand : (∑ i, (P.law i).real B)≤P.tailCount b := by
    change (∑ i, (P.law i).real B)≤∑ i, (P.law i).real (Ioi b)
    exact Finset.sum_le_sum (fun i _ => measureReal_mono (μ := P.law i) hAbove)
  calc
    _ ≤ 2*(∑ i, (P.law i).real B) := weightedResidualScore_information_le P wgt N hB hHalf
    _ ≤ 2*P.tailCount b := mul_le_mul_of_nonneg_left hBand (by norm_num)
    _ ≤ 2*(P.totalFirstMoment/b) := mul_le_mul_of_nonneg_left (P.tailCount_le_totalFirstMoment_div hP hb) (by norm_num)
    _ ≤ 2*(S0/b) := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hS hb.le) (by norm_num)
    _ = _ := by ring
end ProphetSecretary.Limiting
