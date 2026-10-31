import ProphetSecretary.Limiting.FiniteBandScaling
import ProphetSecretary.Probability.FiniteProductDensity

/-!
# Actual normalized mark and array densities under band scaling

For a nonzero finite intensity, normalizing contributes exactly the ratio of
old and new total mass. The independent uniform clocks are unchanged. Finite
array densities are derived from the actual product law, including empty arrays.
-/

open MeasureTheory Set
open scoped Classical NNReal ENNReal BigOperators

namespace ProphetSecretary.Limiting

lemma finiteMeasure_normalize_density (μ ν : FiniteMeasure ℝ) (hμ : μ ≠ 0) (hν : ν ≠ 0)
    (f : ℝ → ℝ) (hf : Measurable f)
    (hDensity : (ν : Measure ℝ)=(μ : Measure ℝ).withDensity (fun x => ENNReal.ofReal (f x))) :
    (ν.normalize : Measure ℝ)=(μ.normalize : Measure ℝ).withDensity
      (fun x => ENNReal.ofReal (((μ.mass/ν.mass : ℝ≥0) : ℝ)*f x)) := by
  let c : ℝ≥0 := μ.mass/ν.mass
  have hm := μ.mass_nonzero_iff.mpr hμ
  have hCoefficientNN : μ.mass⁻¹*c=ν.mass⁻¹ := by
    dsimp only [c]
    rw [div_eq_mul_inv,← mul_assoc,inv_mul_cancel₀ hm,one_mul]
  have hCoefficient : ((μ.mass⁻¹ : ℝ≥0) : ℝ≥0∞)*(c : ℝ≥0∞)=((ν.mass⁻¹ : ℝ≥0) : ℝ≥0∞) := by
    rw [← ENNReal.coe_mul]
    exact congrArg (fun q : ℝ≥0 => (q : ℝ≥0∞)) hCoefficientNN
  have hfE : Measurable (fun x => ENNReal.ofReal (f x)) := ENNReal.measurable_ofReal.comp hf
  have hFunction : (fun x => ENNReal.ofReal ((c : ℝ)*f x))=
      (c : ℝ≥0∞) • (fun x => ENNReal.ofReal (f x)) := by
    funext x
    change ENNReal.ofReal ((c : ℝ)*f x)=(c : ℝ≥0∞)*ENNReal.ofReal (f x)
    simpa only [ENNReal.ofReal_coe_nnreal] using
      (ENNReal.ofReal_mul (p := (c : ℝ)) (q := f x) c.property)
  rw [ν.toMeasure_normalize_eq_of_nonzero hν,μ.toMeasure_normalize_eq_of_nonzero hμ,hDensity]
  change ((ν.mass⁻¹ : ℝ≥0) : ℝ≥0∞) • (μ : Measure ℝ).withDensity (fun x => ENNReal.ofReal (f x))=
    (((μ.mass⁻¹ : ℝ≥0) : ℝ≥0∞) • (μ : Measure ℝ)).withDensity (fun x => ENNReal.ofReal ((c : ℝ)*f x))
  rw [hFunction,withDensity_smul_measure,withDensity_smul (c : ℝ≥0∞) hfE,
    smul_smul,hCoefficient]

noncomputable def bandNormalizedDensity (μ : FiniteMeasure ℝ) (S : Set ℝ) (r : ℝ≥0) (x : ℝ) : ℝ :=
  ((μ.mass/(bandScaledIntensity μ S r).mass : ℝ≥0) : ℝ)*bandScaleFactor S r x

lemma measurable_bandNormalizedDensity (μ : FiniteMeasure ℝ) {S : Set ℝ}
    (hS : MeasurableSet S) (r : ℝ≥0) : Measurable (bandNormalizedDensity μ S r) :=
  (measurable_bandScaleFactor hS r).const_mul _

lemma bandNormalizedDensity_nonnegative (μ : FiniteMeasure ℝ) (S : Set ℝ) (r : ℝ≥0) (x : ℝ) :
    0 ≤ bandNormalizedDensity μ S r x := mul_nonneg (by positivity) (bandScaleFactor_nonnegative S r x)

lemma bandScaleFactor_le (S : Set ℝ) (r : ℝ≥0) (x : ℝ) : bandScaleFactor S r x ≤ (r : ℝ)+1 := by
  have hr0 : 0 ≤ (r : ℝ) := r.property
  unfold bandScaleFactor
  split_ifs
  · exact le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)
  · exact le_add_of_nonneg_left hr0

lemma integrable_bandNormalizedPointDensity (μ : FiniteMeasure ℝ) {S : Set ℝ}
    (hS : MeasurableSet S) (r : ℝ≥0) :
    Integrable (fun p : Point => bandNormalizedDensity μ S r p.2) (pointLaw μ) := by
  let c : ℝ≥0 := μ.mass/(bandScaledIntensity μ S r).mass
  apply Integrable.of_bound ((measurable_bandNormalizedDensity μ hS r).comp measurable_snd).aestronglyMeasurable
    ((c : ℝ)*((r : ℝ)+1))
  apply Filter.Eventually.of_forall
  intro p
  change ‖bandNormalizedDensity μ S r p.2‖ ≤ _
  rw [Real.norm_eq_abs,abs_of_nonneg (bandNormalizedDensity_nonnegative μ S r p.2)]
  exact mul_le_mul_of_nonneg_left (bandScaleFactor_le S r p.2) c.property

lemma normalizedMarkLaw_bandScale_density (μ : FiniteMeasure ℝ) {S : Set ℝ}
    (hS : MeasurableSet S) {r : ℝ≥0} (hr : 0 < r) (hμ : μ ≠ 0) :
    ((bandScaledIntensity μ S r).normalize : Measure ℝ)=(μ.normalize : Measure ℝ).withDensity
      (fun x => ENNReal.ofReal (bandNormalizedDensity μ S r x)) :=
  finiteMeasure_normalize_density μ (bandScaledIntensity μ S r) hμ
    (bandScaledIntensity_ne_zero μ hS hr hμ) (bandScaleFactor S r) (measurable_bandScaleFactor hS r)
    (bandScaledIntensity_toMeasure μ hS r)

lemma pointLaw_bandScale_density (μ : FiniteMeasure ℝ) {S : Set ℝ}
    (hS : MeasurableSet S) {r : ℝ≥0} (hr : 0 < r) (hμ : μ ≠ 0) :
    pointLaw (bandScaledIntensity μ S r)=(pointLaw μ).withDensity
      (fun p => ENNReal.ofReal (bandNormalizedDensity μ S r p.2)) := by
  have hfE : Measurable (fun x => ENNReal.ofReal (bandNormalizedDensity μ S r x)) :=
    ENNReal.measurable_ofReal.comp (measurable_bandNormalizedDensity μ hS r)
  unfold pointLaw
  rw [normalizedMarkLaw_bandScale_density μ hS hr hμ]
  exact prod_withDensity_right hfE

lemma arrayLaw_bandScale_density (μ : FiniteMeasure ℝ) {S : Set ℝ}
    (hS : MeasurableSet S) {r : ℝ≥0} (hr : 0 < r) (hμ : μ ≠ 0) (N : ℕ) :
    arrayLaw (bandScaledIntensity μ S r) N=(arrayLaw μ N).withDensity
      (fun v => ENNReal.ofReal (∏ j : Fin N, bandNormalizedDensity μ S r (v j).2)) := by
  unfold arrayLaw
  simp_rw [pointLaw_bandScale_density μ hS hr hμ]
  exact ProphetSecretary.Probability.pi_withDensity_ofReal (fun _ : Fin N => pointLaw μ)
    (fun _ p => bandNormalizedDensity μ S r p.2)
    (fun _ => integrable_bandNormalizedPointDensity μ hS r)
    (fun _ => Filter.Eventually.of_forall (fun p => bandNormalizedDensity_nonnegative μ S r p.2))

end ProphetSecretary.Limiting
