import ProphetSecretary.Statistics.PremiumKac

/-!
# Premium increments in the scalar coefficient

Normalized differences of positive premiums are nonnegative and bounded by the
remaining horizon. Their mean is the complementary difference quotient of the
actual optimal scalar value. These are deterministic design-law identities.
-/

open MeasureTheory Set
open scoped BigOperators Classical

namespace ProphetSecretary.Model

lemma positivePremium_threshold_difference (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable id μ) (w : ℝ) {a b : ℝ} (hab : a ≤ b) :
    0 ≤ positivePremium μ w a - positivePremium μ w b ∧
      positivePremium μ w a - positivePremium μ w b ≤ b - a := by
  have hIa := integrable_positivePart μ hμ w a
  have hIb := integrable_positivePart μ hμ w b
  constructor
  · exact sub_nonneg.mpr (integral_mono hIb hIa (fun x => max_le_max (by linarith) le_rfl))
  · have hp (x : ℝ) : max (w * x - a) 0 ≤ max (w * x - b) 0 + (b - a) := by
      apply max_le
      · linarith [le_max_left (w * x - b) 0]
      · linarith [le_max_right (w * x - b) 0]
    have h := integral_mono hIa (hIb.add (integrable_const (b - a))) hp
    simp only [Pi.add_apply] at h
    rw [integral_add hIb (integrable_const (b - a)), integral_const, probReal_univ, one_smul] at h
    change (∫ x, max (w * x - a) 0 ∂μ) - (∫ x, max (w * x - b) 0 ∂μ) ≤ b - a
    linarith

variable {n : ℕ}

noncomputable def Instance.clockPremiumSlope (Q : Instance n) (z z' : ℝ) (u : Fin n → ℝ) (i : Fin n) : ℝ :=
  (Q.clockPremium 1 z u i - Q.clockPremium 1 z' u i) / (z' - z)

noncomputable def Instance.premiumSlopeSum (Q : Instance n) (z z' : ℝ) (u : Fin n → ℝ) : ℝ :=
  (Q.unstoppedPremium 1 z u - Q.unstoppedPremium 1 z' u) / (z' - z)

lemma Instance.premiumSlopeSum_eq_sum (Q : Instance n) (z z' : ℝ) (u : Fin n → ℝ) :
    Q.premiumSlopeSum z z' u = ∑ i, Q.clockPremiumSlope z z' u i := by
  simp only [Instance.premiumSlopeSum, Instance.clockPremiumSlope, Instance.unstoppedPremium,
    ← Finset.sum_sub_distrib, ← Finset.sum_div]

lemma Instance.clockPremiumSlope_bounds (Q : Instance n)
    (hQ : Integrable Instance.maximum Q.valuesLaw) {z z' : ℝ} (hz : 0 ≤ z) (hzz : z < z')
    (u : Fin n → ℝ) (i : Fin n) :
    0 ≤ Q.clockPremiumSlope z z' u i ∧ Q.clockPremiumSlope z z' u i ≤ max 0 (1 - u i) := by
  let A := (unseen (history Finset.univ (fun _ => 0) u (u i))).erase i
  let s := max 0 (1 - u i)
  have hs : 0 ≤ s := le_max_left _ _
  have hz' : 0 ≤ z' := hz.trans hzz.le
  have hD := Q.restrictTo_integrable_maximum A hQ
  have hmono : optimalScalarValue (Q.restrictTo A) 1 (z * s) ≤
      optimalScalarValue (Q.restrictTo A) 1 (z' * s) :=
    optimalScalarValue_mono _ hD zero_le_one (mul_nonneg hz hs) le_rfl (mul_le_mul_of_nonneg_right hzz.le hs)
  have hLip := optimalScalarValue_durationWeight_lipschitz (Q.restrictTo A) hD zero_le_one
    (mul_nonneg hz' hs) (mul_nonneg hz hs)
  rw [abs_of_nonneg (sub_nonneg.mpr hmono), ← sub_mul, abs_of_nonneg (mul_nonneg (sub_nonneg.mpr hzz.le) hs)] at hLip
  have hp := positivePremium_threshold_difference (Q.law i) (Q.integrable_maximum_iff.mp hQ i) 1 hmono
  change 0 ≤ (positivePremium (Q.law i) 1 (optimalScalarValue (Q.restrictTo A) 1 (z * s)) -
    positivePremium (Q.law i) 1 (optimalScalarValue (Q.restrictTo A) 1 (z' * s))) / (z' - z) ∧
    (positivePremium (Q.law i) 1 (optimalScalarValue (Q.restrictTo A) 1 (z * s)) -
    positivePremium (Q.law i) 1 (optimalScalarValue (Q.restrictTo A) 1 (z' * s))) / (z' - z) ≤ s
  exact ⟨div_nonneg hp.1 (sub_nonneg.mpr hzz.le), (div_le_iff₀ (sub_pos.mpr hzz)).mpr (hp.2.trans (by nlinarith [hLip]))⟩

lemma Instance.measurable_premiumSlopeSum (Q : Instance n)
    (hQ : Integrable Instance.maximum Q.valuesLaw) {z z' : ℝ} (hz : 0 ≤ z) (hz' : 0 ≤ z') :
    Measurable (Q.premiumSlopeSum z z') :=
  ((Q.measurable_unstoppedPremium hQ (by norm_num : (0 : ℝ) < 1) hz).sub
    (Q.measurable_unstoppedPremium hQ (by norm_num : (0 : ℝ) < 1) hz')).div_const _

lemma Instance.premiumSlopeSum_bounds (Q : Instance n)
    (hQ : Integrable Instance.maximum Q.valuesLaw) {z z' : ℝ} (hz : 0 ≤ z) (hzz : z < z')
    (u : Fin n → ℝ) (hu : ∀ i, u i ∈ Icc (0 : ℝ) 1) :
    0 ≤ Q.premiumSlopeSum z z' u ∧ Q.premiumSlopeSum z z' u ≤ n := by
  rw [Q.premiumSlopeSum_eq_sum]
  constructor
  · exact Finset.sum_nonneg (fun i _ => (Q.clockPremiumSlope_bounds hQ hz hzz u i).1)
  · calc
      _ ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum (fun i _ =>
        (Q.clockPremiumSlope_bounds hQ hz hzz u i).2.trans (max_le (by norm_num) (by linarith [(hu i).1])))
      _ = _ := by simp

lemma Instance.integrable_premiumSlopeSum_pow (Q : Instance n)
    (hQ : Integrable Instance.maximum Q.valuesLaw) {z z' : ℝ} (hz : 0 ≤ z) (hzz : z < z') (p : ℕ) :
    Integrable (fun u => Q.premiumSlopeSum z z' u ^ p) (Instance.clocksLaw n) := by
  apply Integrable.of_bound ((Q.measurable_premiumSlopeSum hQ hz (hz.trans hzz.le)).pow_const p).aestronglyMeasurable ((n : ℝ) ^ p)
  filter_upwards [Instance.clocks_mem_unitInterval (n := n)] with u hu
  have h := Q.premiumSlopeSum_bounds hQ hz hzz u hu
  simpa only [Real.norm_eq_abs, abs_pow, abs_of_nonneg h.1] using pow_le_pow_left₀ h.1 h.2 p

lemma Instance.integral_premiumSlopeSum (Q : Instance n)
    (hQ : Integrable Instance.maximum Q.valuesLaw) {z z' : ℝ} (hz : 0 ≤ z) (hzz : z < z') :
    (∫ u, Q.premiumSlopeSum z z' u ∂Instance.clocksLaw n) =
      1 - (optimalScalarValue Q 1 z' - optimalScalarValue Q 1 z) / (z' - z) := by
  have hI (c : ℝ) (hc : 0 ≤ c) : Integrable (Q.unstoppedPremium 1 c) (Instance.clocksLaw n) := by
    simpa only [pow_one] using Q.integrable_unstoppedPremium_pow hQ (by norm_num : (0 : ℝ) < 1) hc 1
  simp only [Instance.premiumSlopeSum, integral_div]
  rw [integral_sub (hI z hz) (hI z' (hz.trans hzz.le)),
    Q.integral_unstoppedPremium hQ (by norm_num : (0 : ℝ) < 1) hz,
    Q.integral_unstoppedPremium hQ (by norm_num : (0 : ℝ) < 1) (hz.trans hzz.le)]
  field_simp [ne_of_gt (sub_pos.mpr hzz)]; ring

lemma Instance.integral_premiumSlopeSum_bounds (Q : Instance n)
    (hQ : Integrable Instance.maximum Q.valuesLaw) {z z' : ℝ} (hz : 0 ≤ z) (hzz : z < z') :
    0 ≤ (∫ u, Q.premiumSlopeSum z z' u ∂Instance.clocksLaw n) ∧
      (∫ u, Q.premiumSlopeSum z z' u ∂Instance.clocksLaw n) ≤ 1 := by
  rw [Q.integral_premiumSlopeSum hQ hz hzz]
  have hm := optimalScalarValue_mono Q hQ zero_le_one hz le_rfl hzz.le
  have hl := optimalScalarValue_durationWeight_lipschitz Q hQ zero_le_one (hz.trans hzz.le) hz
  rw [abs_of_nonneg (sub_nonneg.mpr hm), abs_of_nonneg (sub_nonneg.mpr hzz.le)] at hl
  constructor
  · have h := (div_le_one (sub_pos.mpr hzz)).mpr hl
    linarith
  · have h := div_nonneg (sub_nonneg.mpr hm) (sub_nonneg.mpr hzz.le)
    linarith

end ProphetSecretary.Model
