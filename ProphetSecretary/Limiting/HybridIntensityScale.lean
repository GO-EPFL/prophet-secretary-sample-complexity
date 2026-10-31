import ProphetSecretary.Limiting.HybridHorizon

/-!
# A uniform Lipschitz bound in the finite intensity multiplier

Only the anonymous intensity changes here; the duration coefficient is held
fixed. The actual added measure is (v−u)μ. Its first moment gives the explicit
value error, independently of the retained dimension and duration weight.
-/
open MeasureTheory Set Filter
open scoped Topology NNReal Classical
namespace ProphetSecretary.Limiting
variable {n : ℕ}

lemma FiniteIntensityHybridInstance.intensityScale_value_sub_bounds
    (B : FiniteIntensityHybridInstance n) {u v : ℝ≥0} (huv : u ≤ v)
    {w d : ℝ} (hw : 0 ≤ w) (hd : 0 ≤ d) :
    0 ≤ (B.remainingHorizon v).optimalScalarValue w d-(B.remainingHorizon u).optimalScalarValue w d ∧
      (B.remainingHorizon v).optimalScalarValue w d-(B.remainingHorizon u).optimalScalarValue w d ≤
        w*((v : ℝ)-(u : ℝ))*(∫ x, x ∂(B.intensity : Measure ℝ)) := by
  have hI : (B.remainingHorizon v).intensity = (B.remainingHorizon u).intensity+(v-u) • B.intensity := by
    change v • B.intensity = u • B.intensity+(v-u) • B.intensity
    rw [← add_smul,add_tsub_cancel_of_le huv]
  have hρ : ∀ᵐ x ∂(((v-u) • B.intensity : FiniteMeasure ℝ) : Measure ℝ), x ∈ Ioc (0 : ℝ) (B.remainingHorizon u).cap :=
    Measure.ae_smul_measure B.intensity_supported (v-u)
  have h := (B.remainingHorizon u).value_intensity_add (B.remainingHorizon v) rfl rfl
    ((v-u) • B.intensity) hρ hI hw hd
  refine ⟨h.1,h.2.trans_eq ?_⟩
  change w*(∫ x, x ∂((v-u) • (B.intensity : Measure ℝ))) = _
  rw [integral_smul_nnreal_measure]
  change w*((((v-u : ℝ≥0) : ℝ))*(∫ x, x ∂(B.intensity : Measure ℝ))) = _
  rw [NNReal.coe_sub huv]
  ring

/-- The fixed-duration-coefficient value is globally Lipschitz in the
nonnegative intensity multiplier, with explicit first-moment constant. -/
theorem FiniteIntensityHybridInstance.intensityScale_value_abs_sub_le
    (B : FiniteIntensityHybridInstance n) (u v : ℝ≥0) {w d : ℝ} (hw : 0 ≤ w) (hd : 0 ≤ d) :
    |(B.remainingHorizon v).optimalScalarValue w d-(B.remainingHorizon u).optimalScalarValue w d| ≤
      w * |(v : ℝ)-(u : ℝ)| * (∫ x, x ∂(B.intensity : Measure ℝ)) := by
  rcases le_total u v with huv | hvu
  · have h := B.intensityScale_value_sub_bounds huv hw hd
    rw [abs_of_nonneg h.1,abs_of_nonneg (sub_nonneg.mpr (show (u : ℝ) ≤ (v : ℝ) by exact_mod_cast huv))]
    exact h.2
  · have h := B.intensityScale_value_sub_bounds hvu hw hd
    rw [abs_sub_comm ((B.remainingHorizon v).optimalScalarValue w d),abs_of_nonneg h.1,
      abs_sub_comm (v : ℝ),abs_of_nonneg (sub_nonneg.mpr (show (v : ℝ) ≤ (u : ℝ) by exact_mod_cast hvu))]
    exact h.2

end ProphetSecretary.Limiting
