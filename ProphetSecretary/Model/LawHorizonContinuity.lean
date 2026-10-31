import ProphetSecretary.Model.LawThresholdVariation
import ProphetSecretary.Model.ContinuationODE

/-!
# Joint law and duration-coefficient continuity

Actual value Lipschitz bounds hold even at coefficient zero. The Bellman ODE
then identifies the coefficient derivative as a continuous expression at every
positive coefficient, using only finitely many marginal expected maxima.
-/

open MeasureTheory Set Filter
open scoped Topology BigOperators NNReal

namespace ProphetSecretary.Model

open ProphetSecretary.Probability

variable {n : ℕ}

lemma Instance.likelihoodValue_joint_bound (P : Instance n) {w H d e : ℝ}
    (hw : 0 ≤ w) (hH : 0 ≤ H) (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    {θ ρ : ℝ} (hθ : θ ∈ Ioo (-(1 / 2) : ℝ) (1 / 2)) (hρ : ρ ∈ Ioo (-(1 / 2) : ℝ) (1 / 2))
    (hd : 0 ≤ d) (he : 0 ≤ e) :
    |optimalScalarValue (P.likelihoodWidePath h hh hb hm ρ) w e - optimalScalarValue (P.likelihoodWidePath h hh hb hm θ) w d| ≤
      |e - d| + (2 * (w * H + d) * (n : ℝ)) * |ρ - θ| := by
  let Q := P.likelihoodWidePath h hh hb hm ρ
  have hQ := Q.integrable_maximum_of_bounded (P.likelihoodWidePath_bounded h hh hb hm ρ hbound)
  exact (abs_sub_le (optimalScalarValue Q w e) (optimalScalarValue Q w d)
    (optimalScalarValue (P.likelihoodWidePath h hh hb hm θ) w d)).trans
    (add_le_add (optimalScalarValue_durationWeight_lipschitz Q hQ hw he hd)
      (P.optimalScalarValue_likelihoodWidePath_lipschitz hw hd hH hbound h hh hb hm hθ hρ))

theorem Instance.likelihoodValue_joint_continuousOn (P : Instance n) {w H : ℝ}
    (hw : 0 ≤ w) (hH : 0 ≤ H) (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0) :
    ContinuousOn (fun v : ℝ × ℝ ↦ optimalScalarValue (P.likelihoodWidePath h hh hb hm v.1) w v.2)
      ((Ioo (-(1 / 2) : ℝ) (1 / 2)) ×ˢ Ici (0 : ℝ)) := by
  intro v hv
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let K := 2 * (w * H + v.2) * (n : ℝ)
  have hc : Continuous (fun z : ℝ × ℝ ↦ |z.2 - v.2| + K * |z.1 - v.1|) :=
    (continuous_snd.sub continuous_const).abs.add (continuous_const.mul (continuous_fst.sub continuous_const).abs)
  have ht : Tendsto (fun z : ℝ × ℝ ↦ |z.2 - v.2| + K * |z.1 - v.1|)
      (𝓝[((Ioo (-(1 / 2) : ℝ) (1 / 2)) ×ˢ Ici (0 : ℝ))] v) (𝓝 0) := by
    have ht' := hc.tendsto v
    simpa only [sub_self, abs_zero, mul_zero, add_zero] using ht'.mono_left nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, ht (Iio_mem_nhds hε)] with z hz hsmall
  have hbnd := P.likelihoodValue_joint_bound hw hH hbound h hh hb hm hv.1 hz.1 hv.2 hz.2
  simpa only [Real.dist_eq] using hbnd.trans_lt hsmall

noncomputable def scoredExpectedMax (μ : Measure ℝ) (h : ℝ → ℝ) (w v : ℝ) : ℝ :=
  ∫ a, h a * max (w * a) v ∂μ

lemma scoredExpectedMax_lipschitz (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable id μ) (h : ℝ → ℝ) (hh : Measurable h) (hb : ∀ᵐ a ∂μ, |h a| ≤ 1) (w : ℝ) :
    LipschitzWith 1 (scoredExpectedMax μ h w) := by
  have hInt (v : ℝ) : Integrable (fun a ↦ h a * max (w * a) v) μ :=
    (integrable_max_with μ hμ w v).bdd_mul hh.aestronglyMeasurable (by simpa only [Real.norm_eq_abs] using hb)
  rw [lipschitzWith_iff_dist_le_mul]
  intro v v'
  simp only [Real.dist_eq, NNReal.coe_one, one_mul]
  unfold scoredExpectedMax
  rw [← integral_sub (hInt v) (hInt v')]
  have hn := norm_integral_le_of_norm_le_const (μ := μ)
    (f := fun a ↦ h a * max (w * a) v - h a * max (w * a) v') (C := |v - v'|) (by
      filter_upwards [hb] with a ha
      rw [← mul_sub, Real.norm_eq_abs, abs_mul]
      have hMax : |max (w * a) v - max (w * a) v'| ≤ |v - v'| := by
        simpa only [sub_self, abs_zero, max_eq_right (abs_nonneg (v - v'))] using
          abs_max_sub_max_le_max (w * a) v (w * a) v'
      exact (mul_le_mul_of_nonneg_left hMax (abs_nonneg _)).trans
        (by simpa only [one_mul] using mul_le_mul_of_nonneg_right ha (abs_nonneg (v - v'))))
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using hn

lemma expectedMaxWith_tiltLaw_half (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable id μ) (h : ℝ → ℝ) (hh : Measurable h) (hb : ∀ᵐ a ∂μ, |h a| ≤ 1)
    {θ : ℝ} (hθ : |θ| ≤ 1 / 2) (w v : ℝ) :
    expectedMaxWith (tiltLaw μ h θ) w v = expectedMaxWith μ w v + θ * scoredExpectedMax μ h w v := by
  have h0 : ∀ᵐ a ∂μ, 0 ≤ tiltFactor h θ a := hb.mono (fun a ha ↦
    (by norm_num : (0 : ℝ) ≤ 1 / 2).trans (tiltFactor_half_bounds hθ ha).1)
  have hInt := integrable_max_with μ hμ w v
  have hProd : Integrable (fun a ↦ h a * max (w * a) v) μ :=
    hInt.bdd_mul hh.aestronglyMeasurable (by simpa only [Real.norm_eq_abs] using hb)
  unfold expectedMaxWith scoredExpectedMax
  rw [integral_tiltLaw hh h0]
  have he : (fun a ↦ tiltFactor h θ a * max (w * a) v) =
      (fun a ↦ max (w * a) v + θ * (h a * max (w * a) v)) := by
    funext a
    unfold tiltFactor
    ring
  rw [he, integral_add (f := fun a ↦ max (w * a) v)
    (g := fun a ↦ θ * (h a * max (w * a) v)) hInt (hProd.const_mul θ), integral_const_mul]

theorem Instance.childMaximum_likelihoodWidePath_continuousOn (P : Instance (n + 1)) {w H : ℝ}
    (hw : 0 ≤ w) (hH : 0 ≤ H) (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin (n + 1) → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0) (i : Fin (n + 1)) :
    ContinuousOn (fun v : ℝ × ℝ ↦ (P.likelihoodWidePath h hh hb hm v.1).childMaximum i w 1 v.2)
      ((Ioo (-(1 / 2) : ℝ) (1 / 2)) ×ˢ Ici (0 : ℝ)) := by
  let A := remainingSet i
  let child := fun v : ℝ × ℝ ↦ optimalScalarValue
    ((P.restrictTo A).likelihoodWidePath (fun j ↦ h (stateEmbedding A j))
      (fun j ↦ hh (stateEmbedding A j)) (fun j ↦ hb (stateEmbedding A j))
      (fun j ↦ hm (stateEmbedding A j)) v.1) w v.2
  have hChild : ContinuousOn child ((Ioo (-(1 / 2) : ℝ) (1 / 2)) ×ˢ Ici (0 : ℝ)) :=
    (P.restrictTo A).likelihoodValue_joint_continuousOn hw hH (fun j ↦ hbound (stateEmbedding A j))
      (fun j ↦ h (stateEmbedding A j)) (fun j ↦ hh (stateEmbedding A j))
      (fun j ↦ hb (stateEmbedding A j)) (fun j ↦ hm (stateEmbedding A j))
  have hμ := P.integrable_maximum_iff.mp (P.integrable_maximum_of_bounded hbound) i
  have hRhs : ContinuousOn (fun v : ℝ × ℝ ↦ expectedMaxWith (P.law i) w (child v) +
      v.1 * scoredExpectedMax (P.law i) (h i) w (child v))
      ((Ioo (-(1 / 2) : ℝ) (1 / 2)) ×ˢ Ici (0 : ℝ)) :=
    ((expectedMaxWith_continuous (P.law i) hμ w).comp_continuousOn hChild).add
      (continuous_fst.continuousOn.mul (((scoredExpectedMax_lipschitz (P.law i) hμ (h i) (hh i) (hb i) w).continuous).comp_continuousOn hChild))
  apply hRhs.congr
  intro v hv
  have hAbs : |v.1| ≤ 1 / 2 := abs_le.mpr ⟨hv.1.1.le, hv.1.2.le⟩
  have hLaw : (P.likelihoodWidePath h hh hb hm v.1).law i = tiltLaw (P.law i) (h i) v.1 := by
    rw [P.likelihoodWidePath_of_mem h hh hb hm hAbs]
    rfl
  change expectedMaxWith ((P.likelihoodWidePath h hh hb hm v.1).law i) w
      (remainingScalarValue ((P.likelihoodWidePath h hh hb hm v.1).restrictTo A) w 1 v.2) = _
  rw [hLaw]
  simp only [remainingScalarValue, one_mul]
  rw [P.likelihoodWidePath_restrictTo h hh hb hm v.1 A]
  exact expectedMaxWith_tiltLaw_half (P.law i) hμ (h i) (hh i) (hb i) hAbs w (child v)

/-- The horizon derivative varies continuously with the likelihood-law parameter
and every positive duration coefficient. This is derived from the actual ODE. -/
theorem Instance.likelihoodValue_coefficientDeriv_continuousOn (P : Instance n) {w H : ℝ}
    (hw : 0 < w) (hH : 0 ≤ H) (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0) :
    ContinuousOn (fun v : ℝ × ℝ ↦ deriv (remainingScalarValue (P.likelihoodWidePath h hh hb hm v.1) w 1) v.2)
      ((Ioo (-(1 / 2) : ℝ) (1 / 2)) ×ˢ Ioi (0 : ℝ)) := by
  cases n with
  | zero =>
    have he : (fun v : ℝ × ℝ ↦ deriv (remainingScalarValue (P.likelihoodWidePath h hh hb hm v.1) w 1) v.2) =
        (fun _ ↦ (1 : ℝ)) := by
      funext v
      exact (remainingScalarValue_empty_hasDerivAt _ w 1 v.2).deriv
    rw [he]
    exact continuousOn_const
  | succ m =>
    have hValue : ContinuousOn (fun v : ℝ × ℝ ↦ optimalScalarValue (P.likelihoodWidePath h hh hb hm v.1) w v.2)
        ((Ioo (-(1 / 2) : ℝ) (1 / 2)) ×ˢ Ioi (0 : ℝ)) :=
      (P.likelihoodValue_joint_continuousOn hw.le hH hbound h hh hb hm).mono
        (fun v hv ↦ ⟨hv.1, Ioi_subset_Ici_self hv.2⟩)
    have hSum : ContinuousOn (fun v : ℝ × ℝ ↦ ∑ i : Fin (m + 1),
        (P.likelihoodWidePath h hh hb hm v.1).childMaximum i w 1 v.2)
        ((Ioo (-(1 / 2) : ℝ) (1 / 2)) ×ˢ Ioi (0 : ℝ)) := by
      apply continuousOn_finsetSum
      intro i _
      exact (P.childMaximum_likelihoodWidePath_continuousOn hw.le hH hbound h hh hb hm i).mono
        (fun v hv ↦ ⟨hv.1, Ioi_subset_Ici_self hv.2⟩)
    have hRhs : ContinuousOn (fun v : ℝ × ℝ ↦
        (v.2 + (∑ i : Fin (m + 1), (P.likelihoodWidePath h hh hb hm v.1).childMaximum i w 1 v.2) -
          (m + 1 : ℝ) * optimalScalarValue (P.likelihoodWidePath h hh hb hm v.1) w v.2) / v.2)
        ((Ioo (-(1 / 2) : ℝ) (1 / 2)) ×ˢ Ioi (0 : ℝ)) :=
      ((continuous_snd.continuousOn.add hSum).sub (continuousOn_const.mul hValue)).div
        continuous_snd.continuousOn (fun v hv ↦ hv.2.ne')
    apply hRhs.congr
    intro v hv
    let Q := P.likelihoodWidePath h hh hb hm v.1
    have hQ := Q.integrable_maximum_of_bounded (P.likelihoodWidePath_bounded h hh hb hm v.1 hbound)
    have hODE := Q.remainingScalarValue_ode hQ hw zero_le_one hv.2
    have hVal : remainingScalarValue Q w 1 v.2 = optimalScalarValue Q w v.2 := by simp only [remainingScalarValue, one_mul]
    have hS : (∑ i : Fin (m + 1), (Q.childMaximum i w 1 v.2 - remainingScalarValue Q w 1 v.2)) =
        (∑ i : Fin (m + 1), Q.childMaximum i w 1 v.2) - (m + 1 : ℝ) * optimalScalarValue Q w v.2 := by
      simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_add, Nat.cast_one, hVal]
    rw [one_mul, hS] at hODE
    change deriv (remainingScalarValue Q w 1) v.2 =
      (v.2 + (∑ i : Fin (m + 1), Q.childMaximum i w 1 v.2) - (m + 1 : ℝ) * optimalScalarValue Q w v.2) / v.2
    apply (eq_div_iff hv.2.ne').mpr
    nlinarith

end ProphetSecretary.Model
