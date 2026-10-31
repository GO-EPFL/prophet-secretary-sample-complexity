import ProphetSecretary.Model.CrossingRoots
import ProphetSecretary.Model.LawThresholdVariation

/-!
# Actual continuation roots along a likelihood-law path

Roots are constructed separately from each instance's scalar value. Strong
increase in the duration coefficient and the actual law-value Lipschitz bound
prove their continuity; no continuity of an optimizer is assumed.
-/

open MeasureTheory Set
open scoped Topology NNReal

namespace ProphetSecretary.Model

open ProphetSecretary.Probability

variable {n : ℕ}

lemma Instance.durationRoot_le_cap (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {H x : ℝ} (hH : 0 ≤ H) (hx : x ≤ H) :
    P.durationRoot hP x ≤ H := by
  by_cases hroot : optimalScalarValue P 1 0 < x
  · exact (P.durationRoot_le_level hP hroot).trans hx
  · rw [P.durationRoot_eq_zero_of_le hP (le_of_not_gt hroot)]
    exact hH

noncomputable def Instance.lawDurationRoot (P : Instance n) {H : ℝ}
    (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    (θ x : ℝ) : ℝ :=
  (P.likelihoodWidePath h hh hb hm θ).durationRoot
    ((P.likelihoodWidePath h hh hb hm θ).integrable_maximum_of_bounded
      (P.likelihoodWidePath_bounded h hh hb hm θ hbound)) x

lemma Instance.lawDurationRoot_nonnegative (P : Instance n) {H : ℝ}
    (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0) (θ x : ℝ) :
    0 ≤ P.lawDurationRoot hbound h hh hb hm θ x := Instance.durationRoot_nonnegative _ _ _

theorem Instance.lawDurationRoot_lipschitz (P : Instance n) {H x : ℝ}
    (hH : 0 ≤ H) (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H) (hx : x ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    {θ ρ : ℝ} (hθ : θ ∈ Ioo (-(1 / 2) : ℝ) (1 / 2)) (hρ : ρ ∈ Ioo (-(1 / 2) : ℝ) (1 / 2)) :
    |P.lawDurationRoot hbound h hh hb hm ρ x - P.lawDurationRoot hbound h hh hb hm θ x| ≤
      (16 * H * (n : ℝ) * (1 + (n : ℝ))) * |ρ - θ| := by
  have hDir (s t : ℝ) (hs : s ∈ Ioo (-(1 / 2) : ℝ) (1 / 2)) (ht : t ∈ Ioo (-(1 / 2) : ℝ) (1 / 2)) :
      P.lawDurationRoot hbound h hh hb hm t x - P.lawDurationRoot hbound h hh hb hm s x ≤
        (16 * H * (n : ℝ) * (1 + (n : ℝ))) * |t - s| := by
    let Q := P.likelihoodWidePath h hh hb hm s
    let T := P.likelihoodWidePath h hh hb hm t
    have hQ := Q.integrable_maximum_of_bounded (P.likelihoodWidePath_bounded h hh hb hm s hbound)
    have hT := T.integrable_maximum_of_bounded (P.likelihoodWidePath_bounded h hh hb hm t hbound)
    let dQ := Q.durationRoot hQ x
    let dT := T.durationRoot hT x
    have hdQ := Q.durationRoot_nonnegative hQ x
    have hdT := T.durationRoot_nonnegative hT x
    change dT - dQ ≤ _
    have hRhs : 0 ≤ (16 * H * (n : ℝ) * (1 + (n : ℝ))) * |t - s| := by positivity
    by_cases horder : dQ ≤ dT
    · by_cases hzero : dT = 0
      · rw [hzero]
        exact (by linarith : 0 - dQ ≤ 0).trans hRhs
      · have hpositive : 0 < dT := lt_of_le_of_ne hdT (Ne.symm hzero)
        have hlevel : optimalScalarValue T 1 0 < x := by
          by_contra hn
          have hz := T.durationRoot_eq_zero_of_le hT (le_of_not_gt hn)
          exact hzero hz
        have hg := T.remainingHorizon_growth hT (w := 1) (c := 1) zero_lt_one zero_le_one hdQ horder
        rw [one_mul, one_mul, T.durationRoot_value hT hlevel] at hg
        have hv := Q.durationRoot_value_ge hQ x
        have hL := P.optimalScalarValue_likelihoodWidePath_lipschitz zero_le_one hdQ hH hbound h hh hb hm hs ht
        have hcap : dQ ≤ H := Q.durationRoot_le_cap hQ hH hx
        have hCoeff : 2 * (1 * H + dQ) * (n : ℝ) ≤ 4 * H * (n : ℝ) := by
          nlinarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n]
        have hLarge := hL.trans (mul_le_mul_of_nonneg_right hCoeff (abs_nonneg (t - s)))
        have hAbs := neg_le_abs (optimalScalarValue T 1 dQ - optimalScalarValue Q 1 dQ)
        have he : (1 / (4 * (1 + (n : ℝ)))) * (dT - dQ) = (dT - dQ) / (4 * (1 + (n : ℝ))) := by ring
        rw [he] at hg
        have hquot : (dT - dQ) / (4 * (1 + (n : ℝ))) ≤ 4 * H * (n : ℝ) * |t - s| := by
          nlinarith
        have hmul := (div_le_iff₀ (by positivity : 0 < 4 * (1 + (n : ℝ)))).mp hquot
        nlinarith
    · exact (by linarith : dT - dQ ≤ 0).trans hRhs
  rw [abs_le]
  have h1 := hDir θ ρ hθ hρ
  have h2 := hDir ρ θ hρ hθ
  rw [abs_sub_comm θ ρ] at h2
  constructor <;> linarith

lemma Instance.lawDurationRoot_continuousOn (P : Instance n) {H x : ℝ}
    (hH : 0 ≤ H) (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H) (hx : x ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0) :
    ContinuousOn (fun θ ↦ P.lawDurationRoot hbound h hh hb hm θ x) (Ioo (-(1 / 2) : ℝ) (1 / 2)) := by
  have hC : 0 ≤ 16 * H * (n : ℝ) * (1 + (n : ℝ)) := by positivity
  have hLip : LipschitzOnWith (NNReal.mk (16 * H * (n : ℝ) * (1 + (n : ℝ))) hC)
      (fun θ ↦ P.lawDurationRoot hbound h hh hb hm θ x) (Ioo (-(1 / 2) : ℝ) (1 / 2)) := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro θ hθ ρ hρ
    simpa only [Real.dist_eq, NNReal.coe_mk] using P.lawDurationRoot_lipschitz hH hbound hx h hh hb hm hρ hθ
  exact hLip.continuousOn

/-- Positive reward scaling converts the normalized root into the actual
coefficient at which the continuation equals the candidate payoff `wx`. -/
lemma Instance.weightedDurationRoot_value (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w x : ℝ} (hw : 0 < w)
    (hx : optimalScalarValue P 1 0 < x) :
    optimalScalarValue P w (w * P.durationRoot hP x) = w * x := by
  have h := optimalScalarValue_smul P hP hw.le zero_le_one (P.durationRoot_nonnegative hP x)
  rw [mul_one, P.durationRoot_value hP hx] at h
  exact h

end ProphetSecretary.Model
