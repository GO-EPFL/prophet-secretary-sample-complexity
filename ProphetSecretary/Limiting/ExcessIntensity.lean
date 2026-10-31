import ProphetSecretary.Limiting.PositiveOfferIntensity
import ProphetSecretary.Model.ExcessMeasure

/-!
# The actual positive Poisson intensity after a reserve shift

The excess pushforward may have an atom at zero. It is restricted to positive
values before any hybrid model is constructed. Normalized mark laws below are
analytical probability laws; their zero-intensity fallback is the point mass at
zero, and it does not create an observed zero-mark Poisson process.
-/

open MeasureTheory Set Filter
open scoped Classical NNReal

namespace ProphetSecretary.Limiting

noncomputable def excessIntensity (μ : FiniteMeasure ℝ) (a : ℝ) : FiniteMeasure ℝ :=
  ⟨(Model.excessLaw (μ : Measure ℝ) a).restrict (Ioi 0), by
    unfold Model.excessLaw
    infer_instance⟩

lemma excessIntensity_supported (μ : FiniteMeasure ℝ) {H a : ℝ} (ha : 0 ≤ a)
    (hsupport : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Ioc (0 : ℝ) H) :
    ∀ᵐ x ∂(excessIntensity μ a : Measure ℝ), x ∈ Ioc (0 : ℝ) H := by
  have hupper : ∀ᵐ y ∂Model.excessLaw (μ : Measure ℝ) a, y ≤ H := by
    apply (ae_map_iff (Model.measurable_excessValueMap a).aemeasurable measurableSet_Iic).mpr
    filter_upwards [hsupport] with x hx
    have hn : 0 ≤ min a (max x 0) := le_min ha (le_max_right _ _)
    change x - min a (max x 0) ≤ H
    linarith only [hx.2,hn]
  filter_upwards [ae_restrict_mem measurableSet_Ioi,ae_restrict_of_ae hupper] with x hx hH
  exact ⟨hx,hH⟩

lemma excessIntensity_premium (μ : FiniteMeasure ℝ) {w v : ℝ} (hw : 0 ≤ w) (hv : 0 ≤ v) (a : ℝ) :
    (∫ y, max (w * y - v) 0 ∂(excessIntensity μ a : Measure ℝ)) =
      (μ : Measure ℝ).real univ * Model.positivePremium (Model.excessLaw (μ.normalize : Measure ℝ) a) w v := by
  have h := positivePremium_eq_positiveRestriction (Model.excessLaw (μ : Measure ℝ) a) w v hw hv
  change (∫ y, max (w * y - v) 0 ∂(Model.excessLaw (μ : Measure ℝ) a).restrict (Ioi 0)) = _
  rw [← h, Model.positivePremium_excessLaw, finiteMeasure_integral_normalize]
  rw [Model.positivePremium_excessLaw]

noncomputable def normalizedMarkOrZero (μ : FiniteMeasure ℝ) : Measure ℝ :=
  if μ = 0 then Measure.dirac 0 else (μ.normalize : Measure ℝ)

instance normalizedMarkOrZero_probability (μ : FiniteMeasure ℝ) : IsProbabilityMeasure (normalizedMarkOrZero μ) := by
  by_cases hμ : μ = 0
  · rw [normalizedMarkOrZero,if_pos hμ]
    infer_instance
  · rw [normalizedMarkOrZero,if_neg hμ]
    infer_instance

lemma normalizedMarkOrZero_bounds (μ : FiniteMeasure ℝ) {H : ℝ} (hH : 0 ≤ H)
    (hsupport : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Ioc (0 : ℝ) H) :
    ∀ᵐ x ∂normalizedMarkOrZero μ, x ∈ Icc (0 : ℝ) H := by
  by_cases hμ : μ = 0
  · rw [normalizedMarkOrZero,if_pos hμ]
    exact (ae_dirac_iff measurableSet_Icc).mpr ⟨le_rfl,hH⟩
  · rw [normalizedMarkOrZero,if_neg hμ]
    exact (normalized_ae μ hμ hsupport).mono fun _ hx => ⟨hx.1.le,hx.2⟩

lemma normalizedMarkOrZero_integrable (μ : FiniteMeasure ℝ) {H : ℝ} (hH : 0 ≤ H)
    (hsupport : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Ioc (0 : ℝ) H) :
    Integrable id (normalizedMarkOrZero μ) := by
  apply Integrable.of_bound aestronglyMeasurable_id H
  filter_upwards [normalizedMarkOrZero_bounds μ hH hsupport] with x hx
  simpa only [id_eq,Real.norm_eq_abs,abs_of_nonneg hx.1] using hx.2

lemma normalizedMarkOrZero_premium (μ : FiniteMeasure ℝ) (w v : ℝ) :
    (μ : Measure ℝ).real univ * Model.positivePremium (normalizedMarkOrZero μ) w v =
      ∫ x, max (w * x - v) 0 ∂(μ : Measure ℝ) := by
  by_cases hμ : μ = 0
  · rw [hμ]
    simp [Measure.real]
  · rw [normalizedMarkOrZero,if_neg hμ,finiteMeasure_integral_normalize]
    rfl

lemma excessIntensity_normalized_premium (μ : FiniteMeasure ℝ) {w v : ℝ} (hw : 0 ≤ w) (hv : 0 ≤ v) (a : ℝ) :
    (excessIntensity μ a : Measure ℝ).real univ * Model.positivePremium (normalizedMarkOrZero (excessIntensity μ a)) w v =
      (μ : Measure ℝ).real univ * Model.positivePremium (Model.excessLaw (μ.normalize : Measure ℝ) a) w v := by
  rw [normalizedMarkOrZero_premium,excessIntensity_premium μ hw hv]

end ProphetSecretary.Limiting
