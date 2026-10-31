import ProphetSecretary.Limiting.CountableBenchmark
import ProphetSecretary.Limiting.CountablePositiveTail
import ProphetSecretary.Limiting.BoundedIntensityMoment
import ProphetSecretary.Model.Truncation
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# First moments of cap excess in a countable instance

Individual excess expectations are summed and anonymous excess is integrated
against the actual intensity. A cutoff strictly above reserve makes these
moments finite even when total intensity and the unrestricted first-moment
sum near zero are infinite. Atoms at the cutoff contribute zero excess.
-/
open MeasureTheory Set Filter
open scoped Classical NNReal ENNReal
namespace ProphetSecretary.Limiting.CountableInstance

noncomputable def individualCapExcess (B : CountableInstance) (K : ℝ≥0) (i : ℕ) : ℝ :=
  ∫ x, Model.tailValue K x ∂(B.individuals i : Measure ℝ)

noncomputable def poissonCapExcess (B : CountableInstance) (K : ℝ≥0) : ℝ :=
  ∫ x, Model.tailValue K x ∂B.intensity

noncomputable def totalCapExcess (B : CountableInstance) (K : ℝ≥0) : ℝ :=
  (∑' i, B.individualCapExcess K i)+B.poissonCapExcess K

lemma individualCapExcess_nonnegative (B : CountableInstance) (K : ℝ≥0) (i : ℕ) :
    0 ≤ B.individualCapExcess K i := integral_nonneg (Model.tailValue_nonnegative K)

lemma poissonCapExcess_nonnegative (B : CountableInstance) (K : ℝ≥0) :
    0 ≤ B.poissonCapExcess K := integral_nonneg (Model.tailValue_nonnegative K)

lemma totalCapExcess_nonnegative (B : CountableInstance) (K : ℝ≥0) : 0 ≤ B.totalCapExcess K :=
  add_nonneg (tsum_nonneg (B.individualCapExcess_nonnegative K)) (B.poissonCapExcess_nonnegative K)

private lemma tailValue_le_cap_indicator (H K : ℝ≥0) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) H) :
    Model.tailValue K x ≤ (Ioi (K : ℝ)).indicator (fun _ => (H : ℝ)) x := by
  by_cases hKx : (K : ℝ) < x
  · rw [Set.indicator_of_mem (show x ∈ Ioi (K : ℝ) from hKx)]
    exact (Model.tailValue_le_abs K x).trans ((abs_of_nonneg hx.1).le.trans hx.2)
  · rw [Set.indicator_of_notMem (show x ∉ Ioi (K : ℝ) from hKx)]
    unfold Model.tailValue
    rw [max_eq_right (sub_nonpos.mpr (le_of_not_gt hKx))]

private lemma integrable_capTail (μ : Measure ℝ) (H K : ℝ≥0)
    (hSupp : ∀ᵐ x ∂μ, x ∈ Icc (0 : ℝ) H) (hFinite : μ (Ioi (K : ℝ)) ≠ ⊤) :
    Integrable (Model.tailValue K) μ := by
  have hI : Integrable ((Ioi (K : ℝ)).indicator (fun _ => (H : ℝ))) μ :=
    (integrable_indicator_iff measurableSet_Ioi).mpr (integrableOn_const hFinite)
  apply hI.mono' (Model.measurable_tailValue K).aestronglyMeasurable
  filter_upwards [hSupp] with x hx
  rw [Real.norm_eq_abs,abs_of_nonneg (Model.tailValue_nonnegative K x)]
  exact tailValue_le_cap_indicator H K hx

private lemma integral_capTail_le (μ : Measure ℝ) (H K : ℝ≥0)
    (hSupp : ∀ᵐ x ∂μ, x ∈ Icc (0 : ℝ) H) (hFinite : μ (Ioi (K : ℝ)) ≠ ⊤) :
    (∫ x, Model.tailValue K x ∂μ) ≤ (H : ℝ)*μ.real (Ioi (K : ℝ)) := by
  have hI : Integrable ((Ioi (K : ℝ)).indicator (fun _ => (H : ℝ))) μ :=
    (integrable_indicator_iff measurableSet_Ioi).mpr (integrableOn_const hFinite)
  have h := integral_mono_ae (integrable_capTail μ H K hSupp hFinite) hI
    (hSupp.mono (fun _ hx => tailValue_le_cap_indicator H K hx))
  rw [integral_indicator_const (H : ℝ) measurableSet_Ioi] at h
  simpa only [smul_eq_mul,mul_comm] using h

lemma individualCapExcess_integrable (B : CountableInstance) (K : ℝ≥0) (i : ℕ) :
    Integrable (Model.tailValue K) (B.individuals i : Measure ℝ) :=
  integrable_capTail _ B.cap K (B.individual_supported i) (measure_ne_top _ _)

lemma individualCapExcess_le_cap_mul_tail (B : CountableInstance) (K : ℝ≥0) (i : ℕ) :
    B.individualCapExcess K i ≤ (B.cap : ℝ)*(B.individuals i : Measure ℝ).real (Ioi (K : ℝ)) :=
  integral_capTail_le _ B.cap K (B.individual_supported i) (measure_ne_top _ _)

lemma poissonCapExcess_integrable (B : CountableInstance) (K : ℝ≥0) (hK : (B.terminal : ℝ) < K) :
    Integrable (Model.tailValue K) B.intensity :=
  integrable_capTail _ B.cap K
    (B.intensity_supported.mono (fun _ hx => ⟨B.terminal.property.trans hx.1.le,hx.2⟩))
    (B.intensity_tail_finite _ hK).ne

lemma poissonCapExcess_le_cap_mul_tail (B : CountableInstance) (K : ℝ≥0) (hK : (B.terminal : ℝ) < K) :
    B.poissonCapExcess K ≤ (B.cap : ℝ)*B.intensity.real (Ioi (K : ℝ)) :=
  integral_capTail_le _ B.cap K
    (B.intensity_supported.mono (fun _ hx => ⟨B.terminal.property.trans hx.1.le,hx.2⟩))
    (B.intensity_tail_finite _ hK).ne

lemma summable_individualCapExcess (B : CountableInstance) (K : ℝ≥0) (hK : (B.terminal : ℝ) < K) :
    Summable (B.individualCapExcess K) :=
  Summable.of_nonneg_of_le (B.individualCapExcess_nonnegative K) (B.individualCapExcess_le_cap_mul_tail K)
    ((ENNReal.summable_toReal (B.individual_tail_finite _ hK).ne).mul_left (B.cap : ℝ))

lemma hasSum_bandCapExcess (B : CountableInstance) (K : ℝ≥0) (hK : (B.terminal : ℝ) < K) :
    HasSum (fun k => ∫ x, Model.tailValue K x ∂(B.bandIntensity k : Measure ℝ)) (B.poissonCapExcess K) := by
  have hI : Integrable (Model.tailValue K) (Measure.sum (fun k => (B.bandIntensity k : Measure ℝ))) := by
    rw [B.sum_bandIntensity]
    exact B.poissonCapExcess_integrable K hK
  have h := hasSum_integral_measure hI
  rw [B.sum_bandIntensity] at h
  exact h

end ProphetSecretary.Limiting.CountableInstance
