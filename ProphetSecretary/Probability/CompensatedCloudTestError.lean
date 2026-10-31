import ProphetSecretary.Probability.CompensatedBandTilt
import ProphetSecretary.Probability.CenteredBoundedScore

/-!
# Test-function error of a complementary intensity compensation

The finite residual labels are retained explicitly. On the chosen band the
likelihood is the intended intensity multiplier; its only error is the small
compensating density on the complement. The estimate is uniform over bounded
continuous tests and does not require an atom at zero.
-/

open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Classical BigOperators
namespace ProphetSecretary.Probability

lemma compensatedBandTilt_setIntegral_difference (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {S D : Set ℝ} (hS : MeasurableSet S) (hD : MeasurableSet D) (f : ℝ →ᵇ ℝ)
    (hp : μ.real S≤1/2) {θ : ℝ} (hθ : |θ|≤1/4) :
    (∫ x in D, f x ∂tiltLaw μ (compensatedBandScore μ S) θ)-
      (∫ x in D, (1+θ*S.indicator (fun _ => (1:ℝ)) x)*f x ∂μ)=
      -θ*(μ.real S/(1-μ.real S))*(∫ x in D, Sᶜ.indicator f x ∂μ) := by
  let q := μ.real S/(1-μ.real S)
  have hf : Integrable (f : ℝ → ℝ) (μ.restrict D) :=
    (integrable_boundedObservable μ f).integrableOn
  have hfS := hf.indicator hS
  have hfC := hf.indicator hS.compl
  have hPos : ∀ᵐ x ∂μ.restrict D, 0≤tiltFactor (compensatedBandScore μ S) θ x :=
    ae_restrict_of_ae (tiltFactor_ae_nonnegative
      (Eventually.of_forall (compensatedBandScore_abs_le_one μ hp)) hθ)
  have hTilt : (∫ x in D, f x ∂tiltLaw μ (compensatedBandScore μ S) θ)=
      ∫ x in D, (1+θ*compensatedBandScore μ S x)*f x ∂μ := by
    change (∫ x, f x ∂(μ.withDensity (fun x => ENNReal.ofReal
      (tiltFactor (compensatedBandScore μ S) θ x))).restrict D)=_
    rw [restrict_withDensity hD]
    exact integral_tiltLaw (measurable_compensatedBandScore μ hS) hPos f
  have hValue (x : ℝ) : (1+θ*compensatedBandScore μ S x)*f x=
      f x+θ*S.indicator f x-(θ*q)*Sᶜ.indicator f x := by
    by_cases hx : x∈S <;> (simp [compensatedBandScore,hx,q]; ring)
  have hTarget (x : ℝ) : (1+θ*S.indicator (fun _ => (1:ℝ)) x)*f x=
      f x+θ*S.indicator f x := by
    rw [add_mul,one_mul,mul_assoc]
    by_cases hx : x∈S <;> simp [hx]
  rw [hTilt]
  simp_rw [hValue,hTarget]
  have hSub : (∫ x in D, f x+θ*S.indicator f x-(θ*q)*Sᶜ.indicator f x ∂μ)=
      (∫ x in D, f x+θ*S.indicator f x ∂μ)-(∫ x in D, (θ*q)*Sᶜ.indicator f x ∂μ) :=
    integral_sub (hf.add (hfS.const_mul θ)) (hfC.const_mul (θ*q))
  rw [hSub,integral_const_mul]
  dsimp only [q]
  ring

lemma compensatedBandTilt_setIntegral_error_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {S D : Set ℝ} (hS : MeasurableSet S) (hD : MeasurableSet D) (f : ℝ →ᵇ ℝ)
    {p θ : ℝ} (hp0 : 0≤p) (hp : p≤1/2) (hpi : μ.real S≤p) (hθ : |θ|≤1/4) :
    |(∫ x in D, f x ∂tiltLaw μ (compensatedBandScore μ S) θ)-
      (∫ x in D, (1+θ*S.indicator (fun _ => (1:ℝ)) x)*f x ∂μ)|≤
      2 * |θ| * p * ‖f‖ * μ.real D := by
  have hHalf : μ.real S≤1/2 := hpi.trans hp
  have hRatioNonneg : 0≤μ.real S/(1-μ.real S) :=
    div_nonneg measureReal_nonneg (by linarith only [hHalf])
  have hRatio : μ.real S/(1-μ.real S)≤2*p := by
    have hSecond := compensatedBandScore_secondMoment_le μ hS hHalf
    rw [compensatedBandScore_secondMoment μ hS (by linarith only [hHalf])] at hSecond
    linarith only [hSecond,hpi]
  have hIntegral : |∫ x in D, Sᶜ.indicator f x ∂μ|≤‖f‖*μ.real D := by
    have hBound : ∀ x : ℝ, ‖Sᶜ.indicator f x‖≤‖f‖ := by
      intro x
      by_cases hx : x∈Sᶜ
      · simpa only [Set.indicator_of_mem hx] using f.norm_coe_le_norm x
      · simp only [Set.indicator_of_notMem hx,norm_zero]
        exact norm_nonneg f
    simpa only [Real.norm_eq_abs] using
      norm_setIntegral_le_of_norm_le_const (measure_lt_top μ D) (fun x _ => hBound x)
  rw [compensatedBandTilt_setIntegral_difference μ hS hD f hHalf hθ,
    abs_mul,abs_mul,abs_neg,abs_of_nonneg hRatioNonneg]
  calc
    _ ≤ |θ| * (2*p) * (‖f‖*μ.real D) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hRatio (abs_nonneg θ)) hIntegral
        (abs_nonneg _) (mul_nonneg (abs_nonneg θ) (mul_nonneg (by norm_num) hp0))
    _ = _ := by ring

/-- The filtered finite residual estimate used in paper `lem:closure`.
The constant is independent of the number of retained or residual variables. -/
theorem compensatedCloud_test_error_le {ι : Type*} (μ : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (I : Finset ι)
    {S D : Set ℝ} (hS : MeasurableSet S) (hD : MeasurableSet D) (f : ℝ →ᵇ ℝ)
    {p θ : ℝ} (hp0 : 0≤p) (hp : p≤1/2) (hpi : ∀ i∈I, (μ i).real S≤p) (hθ : |θ|≤1/4) :
    |(∑ i∈I, ∫ x in D, f x ∂tiltLaw (μ i) (compensatedBandScore (μ i) S) θ)-
      (∑ i∈I, ∫ x in D, (1+θ*S.indicator (fun _ => (1:ℝ)) x)*f x ∂μ i)|≤
      2 * |θ| * p * ‖f‖ * (∑ i∈I, (μ i).real D) := by
  rw [←Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ i∈I, 2 * |θ| * p * ‖f‖ * (μ i).real D := by
      exact Finset.sum_le_sum (fun i hi => compensatedBandTilt_setIntegral_error_le
        (μ i) hS hD f hp0 hp (hpi i hi) hθ)
    _ = _ := (Finset.mul_sum _ _ _).symm

end ProphetSecretary.Probability
