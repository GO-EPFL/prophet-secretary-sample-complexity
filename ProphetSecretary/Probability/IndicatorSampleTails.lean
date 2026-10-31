import ProphetSecretary.Probability.UnitSumChernoff
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Actual iid sample-count tails for the outer pilot

Mapping each observation to a measurable event indicator proves the independent
unit-coordinate law used by the already verified Chernoff estimates. Atoms of
the original real law are allowed.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators
namespace ProphetSecretary.Probability

noncomputable def sampleEventIndicator (A : Set ℝ) : ℝ → ℝ := A.indicator (fun _ => 1)

lemma sampleEventIndicator_measurable {A : Set ℝ} (hA : MeasurableSet A) : Measurable (sampleEventIndicator A) :=
  measurable_const.indicator hA

noncomputable def indicatorSampleLaw (μ : Measure ℝ) (A : Set ℝ) : Measure ℝ := μ.map (sampleEventIndicator A)

lemma indicatorSampleLaw_unit (μ : Measure ℝ) [IsProbabilityMeasure μ] {A : Set ℝ} (hA : MeasurableSet A) :
    ∀ᵐ x ∂indicatorSampleLaw μ A, x∈Icc (0:ℝ) 1 := by
  apply (ae_map_iff (sampleEventIndicator_measurable hA).aemeasurable measurableSet_Icc).mpr
  exact Eventually.of_forall fun x => by
    simp only [sampleEventIndicator,Set.indicator_apply]
    split_ifs <;> norm_num

lemma integral_indicatorSampleLaw (μ : Measure ℝ) {A : Set ℝ} (hA : MeasurableSet A) :
    (∫ x, x ∂indicatorSampleLaw μ A)=μ.real A := by
  have h := integral_map (μ:=μ) (sampleEventIndicator_measurable hA).aemeasurable aestronglyMeasurable_id
  exact h.trans (by simpa only [sampleEventIndicator,smul_eq_mul,mul_one,id_eq] using integral_indicator_const (1:ℝ) hA)

noncomputable def sampleEventCount {q : ℕ} (A : Set ℝ) (a : Fin q → ℝ) : ℕ :=
  (Finset.univ.filter (fun i => a i∈A)).card

lemma sampleEventIndicator_sum {q : ℕ} (A : Set ℝ) (a : Fin q → ℝ) :
    coordinateSum (fun i => sampleEventIndicator A (a i))=(sampleEventCount A a:ℝ) := by
  simp only [coordinateSum,sampleEventIndicator,Set.indicator_apply,sampleEventCount]
  rw [Finset.sum_boole]

lemma indicatorSamples_measurePreserving (μ : Measure ℝ) [IsProbabilityMeasure μ] {A : Set ℝ} (hA : MeasurableSet A) (q : ℕ) :
    MeasurePreserving (fun a : Fin q → ℝ => fun i => sampleEventIndicator A (a i))
      (Measure.pi (fun _ => μ)) (Measure.pi (fun _ : Fin q => indicatorSampleLaw μ A)) := by
  haveI : IsProbabilityMeasure (indicatorSampleLaw μ A) := Measure.isProbabilityMeasure_map (sampleEventIndicator_measurable hA).aemeasurable
  exact ⟨measurable_pi_lambda _ (fun i => (sampleEventIndicator_measurable hA).comp (measurable_pi_apply i)),
    Measure.pi_map_pi (fun _ => (sampleEventIndicator_measurable hA).aemeasurable)⟩

lemma iid_count_ge_eq_indicator_sum (μ : Measure ℝ) [IsProbabilityMeasure μ] {A : Set ℝ} (hA : MeasurableSet A) (q r : ℕ) :
    (Measure.pi (fun _ : Fin q => μ)).real {a | r≤sampleEventCount A a}=
      (Measure.pi (fun _ : Fin q => indicatorSampleLaw μ A)).real {b | (r:ℝ)≤coordinateSum b} := by
  have hMap := indicatorSamples_measurePreserving μ hA q
  have hE : MeasurableSet {b : Fin q → ℝ | (r:ℝ)≤coordinateSum b} :=
    measurableSet_le measurable_const (Finset.measurable_sum Finset.univ (fun i _ => measurable_pi_apply i))
  rw [←hMap.map_eq,map_measureReal_apply hMap.measurable hE]
  congr 1
  ext a
  simp only [Set.mem_setOf_eq,Set.mem_preimage,sampleEventIndicator_sum,Nat.cast_le]

lemma iid_count_le_eq_indicator_sum (μ : Measure ℝ) [IsProbabilityMeasure μ] {A : Set ℝ} (hA : MeasurableSet A) (q r : ℕ) :
    (Measure.pi (fun _ : Fin q => μ)).real {a | sampleEventCount A a≤r}=
      (Measure.pi (fun _ : Fin q => indicatorSampleLaw μ A)).real {b | coordinateSum b≤(r:ℝ)} := by
  have hMap := indicatorSamples_measurePreserving μ hA q
  have hE : MeasurableSet {b : Fin q → ℝ | coordinateSum b≤(r:ℝ)} :=
    measurableSet_le (Finset.measurable_sum Finset.univ (fun i _ => measurable_pi_apply i)) measurable_const
  rw [←hMap.map_eq,map_measureReal_apply hMap.measurable hE]
  congr 1
  ext a
  simp only [Set.mem_setOf_eq,Set.mem_preimage,sampleEventIndicator_sum,Nat.cast_le]

/-- q=500r, probability≤.001, and upper-count exponent q/3000. -/
theorem iid_sample_count_upper (μ : Measure ℝ) [IsProbabilityMeasure μ] {A : Set ℝ}
    (hA : MeasurableSet A) (r : ℕ) (hp : μ.real A≤1/1000) :
    (Measure.pi (fun _ : Fin (500*r) => μ)).real {a | r≤sampleEventCount A a}≤Real.exp (-(r:ℝ)/6) := by
  let ν := indicatorSampleLaw μ A
  haveI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map (sampleEventIndicator_measurable hA).aemeasurable
  have hMean : (∑ _i : Fin (500*r), ∫ x, x ∂ν)≤(r:ℝ)/2 := by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    rw [integral_indicatorSampleLaw μ hA]
    have h := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg (500*r))
    norm_num at h ⊢
    nlinarith only [h]
  have hBound := coordinateSum_upper_classifier_tail (fun _ : Fin (500*r) => ν)
    (fun _ => indicatorSampleLaw_unit μ hA) (show (0:ℝ)≤(r:ℝ)/2 by positivity) hMean
  have hThreshold : 2*((r:ℝ)/2)=(r:ℝ) := by ring
  rw [hThreshold] at hBound
  rw [iid_count_ge_eq_indicator_sum μ hA (500*r) r]
  exact hBound.trans (Real.exp_le_exp.mpr (by nlinarith only [(Nat.cast_nonneg r : (0:ℝ)≤(r:ℝ))]))

/-- q=500r, probability≥.003, and lower-count exponent q/6000. -/
theorem iid_sample_count_lower (μ : Measure ℝ) [IsProbabilityMeasure μ] {A : Set ℝ}
    (hA : MeasurableSet A) (r : ℕ) (hp : 3/1000≤μ.real A) :
    (Measure.pi (fun _ : Fin (500*r) => μ)).real {a | sampleEventCount A a<r}≤Real.exp (-(r:ℝ)/12) := by
  let ν := indicatorSampleLaw μ A
  haveI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map (sampleEventIndicator_measurable hA).aemeasurable
  have hMean : 3*((r:ℝ)/2)≤∑ _i : Fin (500*r), ∫ x, x ∂ν := by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    rw [integral_indicatorSampleLaw μ hA]
    have h := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg (500*r))
    norm_num at h ⊢
    nlinarith only [h]
  have hBound := coordinateSum_lower_classifier_tail (fun _ : Fin (500*r) => ν)
    (fun _ => indicatorSampleLaw_unit μ hA) (show (0:ℝ)≤(r:ℝ)/2 by positivity) hMean
  have hThreshold : 2*((r:ℝ)/2)=(r:ℝ) := by ring
  rw [hThreshold] at hBound
  apply le_trans (b:=(Measure.pi (fun _ : Fin (500*r) => μ)).real {a | sampleEventCount A a≤r})
  · exact measureReal_mono (fun a ha => (show sampleEventCount A a<r from ha).le) (measure_ne_top _ _)
  · rw [iid_count_le_eq_indicator_sum μ hA (500*r) r]
    convert hBound using 1
    congr 1
    norm_num [div_div,neg_div]

end ProphetSecretary.Probability
