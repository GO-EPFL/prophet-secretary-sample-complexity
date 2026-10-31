import ProphetSecretary.Limiting.FiniteIntensityPoisson
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Scaling a measurable band of a finite mark intensity

Only the chosen band is multiplied by r. The complement is retained, and the
actual mark measure has the stated density before any Poisson process is built.
-/

open MeasureTheory Set Filter
open scoped Classical NNReal ENNReal

namespace ProphetSecretary.Limiting

noncomputable def bandScaledIntensity (μ : FiniteMeasure ℝ) (S : Set ℝ) (r : ℝ≥0) : FiniteMeasure ℝ :=
  μ.restrict Sᶜ+r • μ.restrict S

noncomputable def bandScaleFactor (S : Set ℝ) (r : ℝ≥0) (x : ℝ) : ℝ :=
  if x ∈ S then (r : ℝ) else 1

lemma measurable_bandScaleFactor {S : Set ℝ} (hS : MeasurableSet S) (r : ℝ≥0) :
    Measurable (bandScaleFactor S r) := Measurable.ite hS measurable_const measurable_const

lemma bandScaleFactor_nonnegative (S : Set ℝ) (r : ℝ≥0) (x : ℝ) : 0 ≤ bandScaleFactor S r x := by
  unfold bandScaleFactor
  split_ifs
  · exact r.property
  · norm_num

lemma bandScaleFactor_positive (S : Set ℝ) {r : ℝ≥0} (hr : 0 < r) (x : ℝ) :
    0 < bandScaleFactor S r x := by
  unfold bandScaleFactor
  split_ifs
  · exact hr
  · norm_num

lemma bandScaledIntensity_toMeasure (μ : FiniteMeasure ℝ) {S : Set ℝ} (hS : MeasurableSet S) (r : ℝ≥0) :
    (bandScaledIntensity μ S r : Measure ℝ)=(μ : Measure ℝ).withDensity
      (fun x => ENNReal.ofReal (bandScaleFactor S r x)) := by
  have hFunction : (fun x => ENNReal.ofReal (bandScaleFactor S r x))=
      S.indicator (fun _ => (r : ℝ≥0∞))+Sᶜ.indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext x
    by_cases hx : x ∈ S <;> simp [bandScaleFactor,hx]
  rw [hFunction,withDensity_add_left (measurable_const.indicator hS),
    withDensity_indicator hS,withDensity_indicator hS.compl,withDensity_const,withDensity_const,one_smul]
  change (μ : Measure ℝ).restrict Sᶜ+r • (μ : Measure ℝ).restrict S=
    (r : ℝ≥0∞) • (μ : Measure ℝ).restrict S+(μ : Measure ℝ).restrict Sᶜ
  exact add_comm _ _

lemma bandScaledIntensity_mass (μ : FiniteMeasure ℝ) (S : Set ℝ) (r : ℝ≥0) :
    (bandScaledIntensity μ S r).mass=μ Sᶜ+r*μ S := by
  change (μ.restrict Sᶜ+r • μ.restrict S) univ=_
  rw [FiniteMeasure.coeFn_add,Pi.add_apply,FiniteMeasure.smul_apply]
  simp only [FiniteMeasure.restrict_apply μ Sᶜ MeasurableSet.univ,
    FiniteMeasure.restrict_apply μ S MeasurableSet.univ,univ_inter,smul_eq_mul]

lemma bandScaledIntensity_mass_difference (μ : FiniteMeasure ℝ) {S : Set ℝ}
    (hS : MeasurableSet S) (r : ℝ≥0) :
    ((bandScaledIntensity μ S r).mass : ℝ)-(μ.mass : ℝ)=((r : ℝ)-1)*(μ S : ℝ) := by
  have hSplit := measureReal_add_measureReal_compl (μ := (μ : Measure ℝ)) hS
  change (μ S : ℝ)+(μ Sᶜ : ℝ)=(μ.mass : ℝ) at hSplit
  rw [bandScaledIntensity_mass,NNReal.coe_add,NNReal.coe_mul]
  linarith only [hSplit]

lemma bandScaledIntensity_ne_zero (μ : FiniteMeasure ℝ) {S : Set ℝ} (hS : MeasurableSet S)
    {r : ℝ≥0} (hr : 0 < r) (hμ : μ ≠ 0) : bandScaledIntensity μ S r ≠ 0 := by
  have hAC : (μ : Measure ℝ) ≪ (bandScaledIntensity μ S r : Measure ℝ) := by
    rw [bandScaledIntensity_toMeasure μ hS r]
    apply withDensity_absolutelyContinuous'
      (ENNReal.measurable_ofReal.comp (measurable_bandScaleFactor hS r)).aemeasurable
    exact Eventually.of_forall (fun x => ENNReal.ofReal_ne_zero_iff.mpr (bandScaleFactor_positive S hr x))
  intro hZero
  have hNull : (μ : Measure ℝ) univ=0 := hAC (s := univ) (by rw [hZero]; rfl)
  apply hμ
  apply FiniteMeasure.toMeasure_injective
  exact Measure.measure_univ_eq_zero.mp hNull

end ProphetSecretary.Limiting
