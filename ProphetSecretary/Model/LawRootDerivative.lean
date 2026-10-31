import ProphetSecretary.Model.LawRoots
import ProphetSecretary.Model.LawHorizonContinuity
import ProphetSecretary.Model.ContinuationSlope
import ProphetSecretary.Stability.WideLikelihoodEnvelope
import ProphetSecretary.Analysis.MovingRoot

/-!
# Actual law derivatives of positive continuation roots

The duration coefficient is held fixed when the parameter derivative of the
value is taken. The root derivative is then derived from the value equation,
joint coefficient-derivative continuity, and the proved positive duration floor.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace ProphetSecretary.Model

open ProphetSecretary.Probability

variable {n : ℕ}

theorem Instance.weightedLawDurationRoot_hasDerivAt (P : Instance n) {w H x : ℝ}
    (hw : 0 < w) (hH : 0 ≤ H) (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H) (hxCap : x ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    {θ : ℝ} (hθ : θ ∈ Ioo (-(1 / 2) : ℝ) (1 / 2))
    (hx : optimalScalarValue (P.likelihoodWidePath h hh hb hm θ) 1 0 < x) :
    let d := w * P.lawDurationRoot hbound h hh hb hm θ x
    HasDerivAt (fun q ↦ w * P.lawDurationRoot hbound h hh hb hm q x)
      (-deriv (fun q ↦ optimalScalarValue (P.likelihoodWidePath h hh hb hm q) w d) θ /
        deriv (remainingScalarValue (P.likelihoodWidePath h hh hb hm θ) w 1) d) θ := by
  let Q := P.likelihoodWidePath h hh hb hm θ
  have hQ := Q.integrable_maximum_of_bounded (P.likelihoodWidePath_bounded h hh hb hm θ hbound)
  let r := fun q ↦ w * P.lawDurationRoot hbound h hh hb hm q x
  let d := r θ
  let F := fun q z ↦ optimalScalarValue (P.likelihoodWidePath h hh hb hm q) w z
  let T := fun q z ↦ deriv (remainingScalarValue (P.likelihoodWidePath h hh hb hm q) w 1) z
  have hdPos : 0 < d := mul_pos hw (Q.durationRoot_positive hQ hx)
  have hdCap : d ≤ w * H := mul_le_mul_of_nonneg_left (Q.durationRoot_le_cap hQ hH hxCap) hw.le
  have hdJ : d ∈ Ioo (0 : ℝ) (w * H + 1) := ⟨hdPos, by linarith⟩
  have hCont : ContinuousAt r θ :=
    continuous_const.continuousAt.mul
      ((P.lawDurationRoot_continuousOn hH hbound hxCap h hh hb hm).continuousAt (Ioo_mem_nhds hθ.1 hθ.2))
  have hr : Tendsto r (𝓝 θ) (𝓝 d) := hCont.tendsto
  have hBase : F θ d = w * x := Q.weightedDurationRoot_value hQ hw hx
  have hRoot : ∀ᶠ q : ℝ in 𝓝 θ, F q (r q) = F θ d := by
    filter_upwards [hr (Ioi_mem_nhds hdPos)] with q hpos
    let Qq := P.likelihoodWidePath h hh hb hm q
    have hQq := Qq.integrable_maximum_of_bounded (P.likelihoodWidePath_bounded h hh hb hm q hbound)
    have hlevel : optimalScalarValue Qq 1 0 < x := by
      by_contra hn
      have hz := Qq.durationRoot_eq_zero_of_le hQq (le_of_not_gt hn)
      have hrq : r q = 0 := by
        change w * Qq.durationRoot hQq x = 0
        rw [hz, mul_zero]
      exact hpos.ne' hrq
    have hVal : F q (r q) = w * x := Qq.weightedDurationRoot_value hQq hw hlevel
    exact hVal.trans hBase.symm
  have hD : ∀ q ∈ Ioo (-(1 / 2) : ℝ) (1 / 2), ∀ z ∈ Ioo (0 : ℝ) (w * H + 1), HasDerivAt (F q) (T q z) z := by
    intro q _hq z hz
    let Qq := P.likelihoodWidePath h hh hb hm q
    have hQq := Qq.integrable_maximum_of_bounded (P.likelihoodWidePath_bounded h hh hb hm q hbound)
    have hv := (remainingScalarValue_differentiableAt_all Qq hQq hw zero_le_one hz.1).hasDerivAt
    apply hv.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (fun y ↦ by simp only [F, Qq, remainingScalarValue, one_mul])
  have hT : ContinuousAt (fun v : ℝ × ℝ ↦ T v.1 v.2) (θ, d) :=
    (P.likelihoodValue_coefficientDeriv_continuousOn hw hH hbound h hh hb hm).continuousAt
      ((isOpen_Ioo.prod isOpen_Ioi).mem_nhds ⟨hθ, hdPos⟩)
  have hPos : 0 < T θ d := by
    have hFloor := remainingScalarValue_deriv_ge_card_bound Q hQ (w := w) (c := 1) hw zero_le_one hdPos
    exact lt_of_lt_of_le (by positivity : (0 : ℝ) < 1 / (4 * (1 + (n : ℝ)))) hFloor
  have hParam : HasDerivAt (fun q ↦ F q d) (deriv (fun q ↦ F q d) θ) θ :=
    (P.hasDerivAt_optimalScalarValue_likelihoodWidePath hw hdPos hH hbound h hh hb hm hθ).differentiableAt.hasDerivAt
  exact ProphetSecretary.Analysis.hasDerivAt_movingRoot hθ hdJ rfl hr hRoot hD hT hPos hParam

/-- Elapsed crossing time has the opposite sign to the remaining duration
coefficient: a positive law derivative moves the elapsed root later. -/
theorem Instance.lawCrossingTime_hasDerivAt (P : Instance n) {w c H x : ℝ}
    (hw : 0 < w) (_hc : 0 < c) (hH : 0 ≤ H) (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H) (hxCap : x ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    {θ : ℝ} (hθ : θ ∈ Ioo (-(1 / 2) : ℝ) (1 / 2))
    (hx : optimalScalarValue (P.likelihoodWidePath h hh hb hm θ) 1 0 < x) :
    let d := w * P.lawDurationRoot hbound h hh hb hm θ x
    HasDerivAt (fun q ↦ 1 - (w * P.lawDurationRoot hbound h hh hb hm q x) / c)
      (deriv (fun q ↦ optimalScalarValue (P.likelihoodWidePath h hh hb hm q) w d) θ /
        (c * deriv (remainingScalarValue (P.likelihoodWidePath h hh hb hm θ) w 1) d)) θ := by
  have hr := ((P.weightedLawDurationRoot_hasDerivAt hw hH hbound hxCap h hh hb hm hθ hx).div_const c).const_sub 1
  simpa only [neg_div, neg_neg, div_div, mul_comm] using hr

end ProphetSecretary.Model
