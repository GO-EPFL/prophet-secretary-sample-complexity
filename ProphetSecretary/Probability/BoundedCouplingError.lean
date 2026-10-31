import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Bounded observable error on a coupling

Two observables agreeing outside a measurable exceptional event differ in
expectation by at most their total range times that event's probability.
-/
open MeasureTheory Set Filter
namespace ProphetSecretary.Probability
variable {Ω : Type*} [MeasurableSpace Ω]
lemma integral_sub_abs_le_of_eq_off (μ : Measure Ω) [IsFiniteMeasure μ]
    (f g : Ω → ℝ) (hf : Measurable f) (hg : Measurable g) {D : ℝ} (_hD : 0≤D)
    (hfb : ∀ q, |f q|≤D) (hgb : ∀ q, |g q|≤D) (E : Set Ω) (hE : MeasurableSet E)
    (hEq : ∀ q, q∉E → f q=g q) :
    |(∫ q, f q ∂μ)-(∫ q, g q ∂μ)| ≤ 2*D*μ.real E := by
  have hfi : Integrable f μ := Integrable.of_bound hf.aestronglyMeasurable D (Eventually.of_forall hfb)
  have hgi : Integrable g μ := Integrable.of_bound hg.aestronglyMeasurable D (Eventually.of_forall hgb)
  rw [← integral_sub hfi hgi]
  calc
    _ ≤ ∫ q, |f q-g q| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ q, E.indicator (fun _ => 2*D) q ∂μ := by
      apply integral_mono (hfi.sub hgi).abs ((integrable_const (2*D)).indicator hE)
      intro q
      change |f q-g q| ≤ E.indicator (fun _ => 2*D) q
      by_cases hq : q∈E
      · rw [Set.indicator_of_mem hq]
        exact (abs_sub (f q) (g q)).trans (by linarith [hfb q,hgb q])
      · rw [Set.indicator_of_notMem hq,hEq q hq,sub_self,abs_zero]
    _ = _ := by rw [integral_indicator_const _ hE,smul_eq_mul]; ring
end ProphetSecretary.Probability
