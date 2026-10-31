import ProphetSecretary.Limiting.ReserveIntensityFromWeight
import ProphetSecretary.Probability.WeakFiniteAlmostContinuousIntegral
import Mathlib.Topology.Algebra.Indicator

/-!
# Weak unweighting strictly above a reserve

The reciprocal ordering weight is bounded on each upper band. The only test
function discontinuity is at the cutoff, so actual finite-measure almost-
continuous integral convergence proves weak convergence on every continuity
band, including zero limiting weighted mass.
-/
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Topology NNReal Classical
namespace ProphetSecretary.Limiting

noncomputable def reserveCutoffTest (w : ℝ →ᵇ ℝ) (b : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  (Ioi b).indicator (fun x => f x / max (w b) (w x))
lemma continuous_div_max_weight (w : ℝ →ᵇ ℝ) {b : ℝ} (hwb : 0 < w b) (f : ℝ →ᵇ ℝ) :
    Continuous (fun x => f x / max (w b) (w x)) :=
  f.continuous.div (continuous_const.max w.continuous)
    (fun _x => ne_of_gt (hwb.trans_le (le_max_left _ _)))
lemma measurable_reserveCutoffTest (w : ℝ →ᵇ ℝ) {b : ℝ} (hwb : 0 < w b) (f : ℝ →ᵇ ℝ) :
    Measurable (reserveCutoffTest w b f) :=
  (continuous_div_max_weight w hwb f).measurable.indicator measurableSet_Ioi
lemma reserveCutoffTest_bound (w : ℝ →ᵇ ℝ) {b : ℝ} (hwb : 0 < w b) (f : ℝ →ᵇ ℝ) (x : ℝ) :
    |reserveCutoffTest w b f x| ≤ ‖f‖ / w b := by
  by_cases hx : x ∈ Ioi b
  · rw [reserveCutoffTest,Set.indicator_of_mem hx,abs_div,abs_of_pos (hwb.trans_le (le_max_left _ _))]
    have hf : |f x| ≤ ‖f‖ := by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm x
    exact (div_le_div_of_nonneg_right hf (by positivity : 0 ≤ max (w b) (w x))).trans
      (div_le_div_of_nonneg_left (norm_nonneg f) hwb (le_max_left _ _))
  · rw [reserveCutoffTest,Set.indicator_of_notMem hx,abs_zero]
    positivity
lemma reserveCutoffTest_continuousAt_ae (η : FiniteMeasure ℝ) (w : ℝ →ᵇ ℝ) {b : ℝ}
    (hwb : 0 < w b) (hatom : (η : Measure ℝ) {b} = 0) (f : ℝ →ᵇ ℝ) :
    ∀ᵐ x ∂(η : Measure ℝ), ContinuousAt (reserveCutoffTest w b f) x := by
  have hfront : (η : Measure ℝ) (frontier (Ioi b)) = 0 := by rw [frontier_Ioi]; exact hatom
  exact (measure_eq_zero_iff_ae_notMem.mp hfront).mono fun x hx =>
    (continuous_div_max_weight w hwb f).continuousOn.continuousAt_indicator hx

lemma reserveMarkIntensityAbove_integral (η : FiniteMeasure ℝ) (w : ℝ →ᵇ ℝ) (a : ℝ)
    (hw : Monotone w) {b : ℝ} (hb : a < b) (hwb : 0 < w b) (f : ℝ → ℝ) :
    (∫ x, f x ∂(reserveMarkIntensityAbove η w a b hw hb hwb : Measure ℝ)) =
      ∫ x, reserveCutoffTest w b f x ∂(η : Measure ℝ) := by
  change (∫ x, f x ∂(reserveMarkIntensity η w a).restrict (Ioi b)) = _
  rw [← integral_indicator measurableSet_Ioi]
  change (∫ x, (Ioi b).indicator f x ∂(η : Measure ℝ).withDensity (reserveReciprocalWeight w a)) = _
  rw [integral_withDensity_eq_integral_toReal_smul (measurable_reserveReciprocalWeight w a)
    (Eventually.of_forall fun x => by unfold reserveReciprocalWeight; split_ifs <;> simp) ((Ioi b).indicator f)]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    dsimp only
    by_cases hx : b < x
    · simp only [reserveCutoffTest,Set.indicator_apply,Set.mem_Ioi,if_pos hx]
      have hwx : 0 < w x := hwb.trans_le (hw hx.le)
      rw [reserveReciprocalWeight,if_pos (hb.trans hx),ENNReal.toReal_ofReal (by positivity : 0 ≤ 1 / w x),
        smul_eq_mul,max_eq_right (hw hx.le)]
      ring
    · simp only [reserveCutoffTest,Set.indicator_apply,Set.mem_Ioi,if_neg hx,smul_zero]

theorem reserveMarkIntensityAbove_tendsto {Γ : Type*} {l : Filter Γ} [l.IsCountablyGenerated]
    {ηs : Γ → FiniteMeasure ℝ} {η : FiniteMeasure ℝ} (hweak : Tendsto ηs l (𝓝 η))
    (w : ℝ →ᵇ ℝ) (a : ℝ) (hw : Monotone w) {b : ℝ} (hb : a < b) (hwb : 0 < w b)
    (hatom : (η : Measure ℝ) {b} = 0) :
    Tendsto (fun m => reserveMarkIntensityAbove (ηs m) w a b hw hb hwb) l
      (𝓝 (reserveMarkIntensityAbove η w a b hw hb hwb)) := by
  apply FiniteMeasure.tendsto_of_forall_integral_tendsto
  intro f
  simp_rw [reserveMarkIntensityAbove_integral]
  exact ProphetSecretary.Probability.finite_integral_tendsto_of_weak_ae_continuous_bounded hweak
    (measurable_reserveCutoffTest w hwb f) (reserveCutoffTest_bound w hwb f)
    (reserveCutoffTest_continuousAt_ae η w hwb hatom f)

end ProphetSecretary.Limiting
