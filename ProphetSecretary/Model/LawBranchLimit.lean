import ProphetSecretary.Model.LawRootDerivative
import ProphetSecretary.Model.WeightedSaturatedValue
import ProphetSecretary.Analysis.RootActionLoss

/-!
# The actual continuation-state triangular law limit

A positive finite continuation root is differentiated using the proved value
equation and ODE. The resulting triangular coefficient is its squared actual
law derivative divided by twice the physical time slope `cT`.
-/

open MeasureTheory Set Filter
open scoped Topology NNReal

namespace ProphetSecretary.Model

open ProphetSecretary.Probability

variable {n : ℕ}

theorem Instance.weightedLawRootActionLoss_limit (P : Instance n) {w c H x : ℝ}
    (hw : 0 < w) (hc : 0 < c) (hH : 0 ≤ H) (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H) (hxCap : x ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    {θ : ℝ} (hθ : θ ∈ Ioo (-(1 / 2) : ℝ) (1 / 2))
    (hx : optimalScalarValue (P.likelihoodWidePath h hh hb hm θ) 1 0 < x) (m : ℝ → ℝ)
    (hLocal : ∀ᶠ t : ℝ in 𝓝 (1 - (w * P.lawDurationRoot hbound h hh hb hm θ x) / c),
      m t = m (1 - (w * P.lawDurationRoot hbound h hh hb hm θ x) / c)) :
    let d := w * P.lawDurationRoot hbound h hh hb hm θ x
    let G := deriv (fun q ↦ optimalScalarValue (P.likelihoodWidePath h hh hb hm q) w d) θ
    let T := deriv (remainingScalarValue (P.likelihoodWidePath h hh hb hm θ) w 1) d
    Tendsto (fun δ : ℝ ↦ (∫ t : ℝ, m t * ProphetSecretary.Analysis.rootActionLoss
      ((P.likelihoodWidePath h hh hb hm (θ + δ)).weightedSaturatedValue w) (w * x) c d t) / δ ^ 2)
      (𝓝[≠] 0) (𝓝 (m (1 - d / c) * G ^ 2 / (2 * c * T))) := by
  let Q := fun q ↦ P.likelihoodWidePath h hh hb hm q
  have hQ (q : ℝ) := (Q q).integrable_maximum_of_bounded (P.likelihoodWidePath_bounded h hh hb hm q hbound)
  let r := fun q ↦ w * P.lawDurationRoot hbound h hh hb hm q x
  let d := r θ
  let F := fun q z ↦ (Q q).weightedSaturatedValue w z
  let T := fun q z ↦ deriv (remainingScalarValue (Q q) w 1) z
  let G := deriv (fun q ↦ optimalScalarValue (Q q) w d) θ
  have hdPos : 0 < d := mul_pos hw ((Q θ).durationRoot_positive (hQ θ) hx)
  have hdCap : d ≤ w * H := mul_le_mul_of_nonneg_left ((Q θ).durationRoot_le_cap (hQ θ) hH hxCap) hw.le
  have hdJ : d ∈ Ioo (0 : ℝ) (w * H + 1) := ⟨hdPos, by linarith⟩
  have hR : HasDerivAt r (-G / T θ d) θ :=
    P.weightedLawDurationRoot_hasDerivAt hw hH hbound hxCap h hh hb hm hθ hx
  have hLip (q : ℝ) (_hq : q ∈ Ioo (-(1 / 2) : ℝ) (1 / 2)) : LipschitzWith 1 (F q) :=
    (Q q).weightedSaturatedValue_lipschitz (hQ q) hw.le
  have hD (q : ℝ) (_hq : q ∈ Ioo (-(1 / 2) : ℝ) (1 / 2)) (z : ℝ) (hz : z ∈ Ioo (0 : ℝ) (w * H + 1)) :
      HasDerivAt (F q) (T q z) z := (Q q).weightedSaturatedValue_hasDerivAt (hQ q) hw hz.1
  have hT : ContinuousAt (fun v : ℝ × ℝ ↦ T v.1 v.2) (θ, d) :=
    (P.likelihoodValue_coefficientDeriv_continuousOn hw hH hbound h hh hb hm).continuousAt
      ((isOpen_Ioo.prod isOpen_Ioi).mem_nhds ⟨hθ, hdPos⟩)
  have hLevel (q : ℝ) (_hq : q ∈ Ioo (-(1 / 2) : ℝ) (1 / 2)) (s : ℝ) : F q s ≤ F q (r q) ↔ s ≤ r q :=
    (Q q).weightedSaturatedValue_level_iff (hQ q) hw
      (mul_nonneg hw.le (P.lawDurationRoot_nonnegative hbound h hh hb hm q x)) s
  have hTimePos : 0 < T θ d := lt_of_lt_of_le
    (by positivity : (0 : ℝ) < 1 / (4 * (1 + (n : ℝ))))
    (remainingScalarValue_deriv_ge_card_bound (Q θ) (hQ θ) hw zero_le_one hdPos)
  have hLimit := ProphetSecretary.Analysis.tendsto_weighted_rootActionLoss hθ hdJ hc hdPos rfl hR hLip hD hT hLevel hLocal
  have hCoeff : m (1 - d / c) * T θ d * (-G / T θ d) ^ 2 / (2 * c) =
      m (1 - d / c) * G ^ 2 / (2 * c * T θ d) := by field_simp [hc.ne', hTimePos.ne']
  rw [hCoeff] at hLimit
  apply hLimit.congr'
  have hAdd : Tendsto (fun δ : ℝ ↦ θ + δ) (𝓝 0) (𝓝 θ) := by
    have hc' : Continuous (fun δ : ℝ ↦ θ + δ) := continuous_const.add continuous_id
    simpa only [add_zero] using hc'.tendsto 0
  have hRootPos : ∀ᶠ δ : ℝ in 𝓝 0, 0 < r (θ + δ) :=
    (hR.continuousAt.tendsto.comp hAdd) (Ioi_mem_nhds hdPos)
  filter_upwards [hRootPos.filter_mono nhdsWithin_le_nhds] with δ hpos
  have hlevel : optimalScalarValue (Q (θ + δ)) 1 0 < x := by
    by_contra hn
    have hz := (Q (θ + δ)).durationRoot_eq_zero_of_le (hQ (θ + δ)) (le_of_not_gt hn)
    have hr0 : r (θ + δ) = 0 := by
      change w * (Q (θ + δ)).durationRoot (hQ (θ + δ)) x = 0
      rw [hz, mul_zero]
    exact hpos.ne' hr0
  have hRootValue : F (θ + δ) (r (θ + δ)) = w * x := by
    change optimalScalarValue (Q (θ + δ)) w (max 0 (w * (Q (θ + δ)).durationRoot (hQ (θ + δ)) x)) = _
    rw [max_eq_right (mul_nonneg hw.le ((Q (θ + δ)).durationRoot_nonnegative (hQ (θ + δ)) x))]
    exact (Q (θ + δ)).weightedDurationRoot_value (hQ (θ + δ)) hw hlevel
  simp only [hRootValue]
  rfl

end ProphetSecretary.Model
