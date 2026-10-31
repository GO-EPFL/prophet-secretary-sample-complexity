import ProphetSecretary.Probability.CompensatedBandScore

/-!
# Independent, nonidentical compensated cloud scores

The complete score has information Σpᵢ/(1−pᵢ). Its difference from the centered
positive-band count has squared L² norm at most Σpᵢ². These finite identities
supply `updual:scorecount` without requiring zero atoms or identical marginals.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators

namespace ProphetSecretary.Probability

variable {n : ℕ}

lemma compensatedCloudScore_information (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {B : Set ℝ} (hB : MeasurableSet B) (hp : ∀ i, (μ i).real B ≤ 1 / 2) :
    information μ (fun i => compensatedBandScore (μ i) B) =
      ∑ i, (μ i).real B / (1 - (μ i).real B) := by
  unfold information
  apply Finset.sum_congr rfl
  intro i _
  exact compensatedBandScore_secondMoment (μ i) hB (by linarith [hp i])

lemma compensatedCloudScore_information_le (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {B : Set ℝ} (hB : MeasurableSet B) (hp : ∀ i, (μ i).real B ≤ 1 / 2) :
    information μ (fun i => compensatedBandScore (μ i) B) ≤ 2 * ∑ i, (μ i).real B := by
  unfold information
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => compensatedBandScore_secondMoment_le (μ i) hB (hp i)

/-- Actual product-law L² approximation of the score by the centered band count. -/
theorem compensatedCloudScore_centeredCount_L2 (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {B : Set ℝ} (hB : MeasurableSet B) (hp : ∀ i, (μ i).real B ≤ 1 / 2) :
    (∫ x : Fin n → ℝ, (completeScore (fun i => compensatedBandScore (μ i) B) x -
      ((∑ i, B.indicator (fun _ => (1 : ℝ)) (x i)) - ∑ i, (μ i).real B)) ^ 2 ∂Measure.pi μ) ≤
      ∑ i, ((μ i).real B) ^ 2 := by
  let h : Fin n → ℝ → ℝ := fun i => compensatedBandScore (μ i) B
  let r : Fin n → ℝ → ℝ := fun i x => (μ i).real B * h i x
  have hh : ∀ i, Measurable (h i) := fun i => measurable_compensatedBandScore (μ i) hB
  have hr : ∀ i, Measurable (r i) := fun i => (hh i).const_mul _
  have hb (i : Fin n) (x : ℝ) : |h i x| ≤ 1 := compensatedBandScore_abs_le_one (μ i) (hp i) x
  have hrb : ∀ i, ∀ᵐ x ∂μ i, |r i x| ≤ 1 := by
    intro i
    exact Eventually.of_forall fun x => by
      change |(μ i).real B * h i x| ≤ 1
      rw [abs_mul, abs_of_nonneg measureReal_nonneg]
      have ht := mul_le_mul_of_nonneg_left (hb i x) (measureReal_nonneg : 0 ≤ (μ i).real B)
      simp only [mul_one] at ht
      exact ht.trans (by linarith [hp i])
  have hm : ∀ i, (∫ x, r i x ∂μ i) = 0 := by
    intro i
    change (∫ x, (μ i).real B * h i x ∂μ i) = _
    rw [integral_const_mul, compensatedBandScore_mean (μ i) hB (by linarith [hp i]), mul_zero]
  have hpoint (x : Fin n → ℝ) : completeScore r x = completeScore h x -
      ((∑ i, B.indicator (fun _ => (1 : ℝ)) (x i)) - ∑ i, (μ i).real B) := by
    calc
      _ = ∑ i, (h i (x i) - (B.indicator (fun _ => (1 : ℝ)) (x i) - (μ i).real B)) := by
        apply Finset.sum_congr rfl
        intro i _
        exact (compensatedBandScore_centered_difference (μ i) (by linarith [hp i]) (x i)).symm
      _ = _ := by rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]; rfl
  have hmoment := completeScore_secondMoment μ r hr hrb hm
  have hinfo : information μ r ≤ ∑ i, ((μ i).real B) ^ 2 := by
    unfold information
    apply Finset.sum_le_sum
    intro i _
    have heq : (fun x => r i x ^ 2) = fun x => ((μ i).real B) ^ 2 * h i x ^ 2 := by
      funext x
      dsimp [r]
      ring
    rw [heq, integral_const_mul, compensatedBandScore_secondMoment (μ i) hB (by linarith [hp i])]
    have hratio : (μ i).real B / (1 - (μ i).real B) ≤ 1 := by
      apply (div_le_one (by linarith [hp i])).mpr
      linarith [hp i]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hratio (sq_nonneg ((μ i).real B))
  have hbound := hmoment.le.trans hinfo
  simpa only [hpoint] using hbound

end ProphetSecretary.Probability
