import ProphetSecretary.Probability.BandScore

/-!
# Exact centered band-count moments for independent nonidentical offers

The complete count includes every coordinate. Its variance is the sum of
Bernoulli variances, so its second moment is at most the expected count,
with no factor depending on the number of distributions.
-/
open MeasureTheory Set Filter
open scoped Classical BigOperators
namespace ProphetSecretary.Probability
variable {n : ℕ}

noncomputable def centeredIndependentBandCount (μ : Fin n → Measure ℝ) (B : Set ℝ) (x : Fin n → ℝ) : ℝ :=
  countIn B x-∑ i, (μ i).real B

lemma centeredIndependentBandCount_eq_completeScore (μ : Fin n → Measure ℝ) (B : Set ℝ) :
    centeredIndependentBandCount μ B=completeScore (fun i => centeredIndicator B ((μ i).real B)) := by
  funext x
  simp only [centeredIndependentBandCount,countIn,completeScore,centeredIndicator,
    Set.indicator,Finset.sum_sub_distrib]

lemma centeredIndependentBandCount_moments (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {B : Set ℝ} (hB : MeasurableSet B) :
    MemLp (centeredIndependentBandCount μ B) 2 (Measure.pi μ) ∧
      (∫ x, centeredIndependentBandCount μ B x ∂Measure.pi μ)=0 ∧
      (∫ x, (centeredIndependentBandCount μ B x)^2 ∂Measure.pi μ)=
        ∑ i, ((μ i).real B-((μ i).real B)^2) := by
  let h := fun i => centeredIndicator B ((μ i).real B)
  have hm (i : Fin n) : Measurable (h i) := centeredIndicator_measurable hB _
  have hb (i : Fin n) : ∀ᵐ x ∂μ i, |h i x|≤1 := Eventually.of_forall
    (centeredIndicator_abs_le_one B measureReal_nonneg measureReal_le_one)
  have h0 (i : Fin n) : (∫ x, h i x ∂μ i)=0 := centeredIndicator_mean hB
  rw [centeredIndependentBandCount_eq_completeScore]
  refine ⟨(memLp_two_iff_integrable_sq (measurable_completeScore hm).aestronglyMeasurable).mpr
    (completeScore_integrable_pow μ h hm hb 2),completeScore_mean μ h hm hb h0,?_⟩
  rw [completeScore_secondMoment μ h hm hb h0]
  unfold information
  apply Finset.sum_congr rfl
  intro i _
  exact centeredIndicator_secondMoment hB

lemma centeredIndependentBandCount_secondMoment_le (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {B : Set ℝ} (hB : MeasurableSet B) :
    (∫ x, (centeredIndependentBandCount μ B x)^2 ∂Measure.pi μ)≤∑ i, (μ i).real B := by
  rw [(centeredIndependentBandCount_moments μ hB).2.2]
  exact Finset.sum_le_sum (fun i _ => sub_le_self _ (sq_nonneg _))
end ProphetSecretary.Probability
