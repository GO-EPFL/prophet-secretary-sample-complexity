import ProphetSecretary.Limiting.PositiveIntensityFromWeight
import ProphetSecretary.Probability.WeakFiniteAlmostContinuousIntegral
import Mathlib.Topology.Algebra.Indicator

/-!
# Unweighting weak finite measures on a positive continuity band

The reciprocal factor is uniformly bounded above a fixed b>0. A bounded
continuous test function divided by max(b,x), then restricted to x>b, is
continuous away from b. The actual finite-measure almost-continuous integral
theorem therefore proves weak convergence of the corresponding positive-band
intensities when the limiting weighted measure has no atom at b.
-/
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Topology NNReal Classical
namespace ProphetSecretary.Limiting

noncomputable def positiveCutoffTest (b : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  (Ioi b).indicator (fun x => f x / max b x)

lemma continuous_div_max_cutoff {b : ℝ} (hb : 0 < b) (f : ℝ →ᵇ ℝ) :
    Continuous (fun x => f x / max b x) :=
  f.continuous.div (continuous_const.max continuous_id) (fun x => ne_of_gt (lt_of_lt_of_le hb (le_max_left b x)))

lemma measurable_positiveCutoffTest {b : ℝ} (hb : 0 < b) (f : ℝ →ᵇ ℝ) :
    Measurable (positiveCutoffTest b f) :=
  (continuous_div_max_cutoff hb f).measurable.indicator measurableSet_Ioi

lemma positiveCutoffTest_bound {b : ℝ} (hb : 0 < b) (f : ℝ →ᵇ ℝ) (x : ℝ) :
    |positiveCutoffTest b f x| ≤ ‖f‖ / b := by
  by_cases hx : x ∈ Ioi b
  · rw [positiveCutoffTest,Set.indicator_of_mem hx,abs_div,abs_of_pos (lt_of_lt_of_le hb (le_max_left b x))]
    have hf : |f x| ≤ ‖f‖ := by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm x
    exact (div_le_div_of_nonneg_right hf (by positivity : 0 ≤ max b x)).trans
      (div_le_div_of_nonneg_left (norm_nonneg f) hb (le_max_left b x))
  · rw [positiveCutoffTest,Set.indicator_of_notMem hx,abs_zero]
    positivity

lemma positiveCutoffTest_continuousAt_ae (η : FiniteMeasure ℝ) {b : ℝ} (hb : 0 < b)
    (hatom : (η : Measure ℝ) {b} = 0) (f : ℝ →ᵇ ℝ) :
    ∀ᵐ x ∂(η : Measure ℝ), ContinuousAt (positiveCutoffTest b f) x := by
  have hfront : (η : Measure ℝ) (frontier (Ioi b)) = 0 := by rw [frontier_Ioi]; exact hatom
  exact (measure_eq_zero_iff_ae_notMem.mp hfront).mono fun x hx =>
    (continuous_div_max_cutoff hb f).continuousOn.continuousAt_indicator hx

/-- The actual cutoff intensity is evaluated by a bounded almost-continuous
observable of the finite weighted measure. -/
lemma positiveMarkIntensityAbove_integral (η : FiniteMeasure ℝ) {b : ℝ} (hb : 0 < b) (f : ℝ → ℝ) :
    (∫ x, f x ∂(positiveMarkIntensityAbove η b hb : Measure ℝ)) =
      ∫ x, positiveCutoffTest b f x ∂(η : Measure ℝ) := by
  change (∫ x, f x ∂(positiveMarkIntensity η).restrict (Ioi b)) = _
  rw [← integral_indicator measurableSet_Ioi]
  change (∫ x, (Ioi b).indicator f x ∂(η : Measure ℝ).withDensity positiveReciprocalWeight) = _
  rw [integral_withDensity_eq_integral_toReal_smul measurable_positiveReciprocalWeight
    (Eventually.of_forall fun x => by unfold positiveReciprocalWeight; split_ifs <;> simp) ((Ioi b).indicator f)]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    dsimp only
    by_cases hx : b < x
    · simp only [positiveCutoffTest,Set.indicator_apply,Set.mem_Ioi,if_pos hx]
      have hx0 : 0 < x := hb.trans hx
      rw [positiveReciprocalWeight,if_pos hx0,ENNReal.toReal_ofReal (by positivity : 0 ≤ 1/x),smul_eq_mul,max_eq_right hx.le]
      ring
    · simp only [positiveCutoffTest,Set.indicator_apply,Set.mem_Ioi,if_neg hx,smul_zero]

/-- Weak unweighting preserves every positive continuity cutoff, including a
zero limiting weighted measure. -/
theorem positiveMarkIntensityAbove_tendsto {Γ : Type*} {l : Filter Γ} [l.IsCountablyGenerated]
    {ηs : Γ → FiniteMeasure ℝ} {η : FiniteMeasure ℝ} (hweak : Tendsto ηs l (𝓝 η))
    {b : ℝ} (hb : 0 < b) (hatom : (η : Measure ℝ) {b} = 0) :
    Tendsto (fun m => positiveMarkIntensityAbove (ηs m) b hb) l (𝓝 (positiveMarkIntensityAbove η b hb)) := by
  apply FiniteMeasure.tendsto_of_forall_integral_tendsto
  intro f
  simp_rw [positiveMarkIntensityAbove_integral]
  exact ProphetSecretary.Probability.finite_integral_tendsto_of_weak_ae_continuous_bounded hweak
    (measurable_positiveCutoffTest hb f) (positiveCutoffTest_bound hb f)
    (positiveCutoffTest_continuousAt_ae η hb hatom f)

end ProphetSecretary.Limiting
