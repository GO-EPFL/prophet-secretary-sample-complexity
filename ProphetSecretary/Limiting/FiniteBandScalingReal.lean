import ProphetSecretary.Limiting.FiniteBandScaling

/-!
# Real-valued set probabilities after finite intensity scaling

The original measure of a measurable set changes by (r−1) times the mass
of its intersection with the scaled band. This identity includes zero mass.
-/
open MeasureTheory Set
open scoped Classical NNReal
namespace ProphetSecretary.Limiting

lemma bandScaledIntensity_real_apply (μ : FiniteMeasure ℝ) {B S : Set ℝ}
    (hB : MeasurableSet B) (hS : MeasurableSet S) (r : ℝ≥0) :
    (bandScaledIntensity μ B r:Measure ℝ).real S=(μ:Measure ℝ).real S+((r:ℝ)-1)*(μ:Measure ℝ).real (S∩B) := by
  have hSplit := measureReal_sdiff_add_inter (μ := (μ:Measure ℝ)) (s := S) hB
  change (μ:Measure ℝ).real (S∩Bᶜ)+(μ:Measure ℝ).real (S∩B)=(μ:Measure ℝ).real S at hSplit
  change ((μ.restrict Bᶜ+r • μ.restrict B) S:ℝ)=_
  rw [FiniteMeasure.coeFn_add,Pi.add_apply,FiniteMeasure.smul_apply,
    FiniteMeasure.restrict_apply μ Bᶜ hS,FiniteMeasure.restrict_apply μ B hS]
  simp only [NNReal.coe_add,NNReal.coe_mul,smul_eq_mul]
  change (μ:Measure ℝ).real (S∩Bᶜ)+(r:ℝ)*(μ:Measure ℝ).real (S∩B)=_
  rw [← hSplit]
  ring
end ProphetSecretary.Limiting
