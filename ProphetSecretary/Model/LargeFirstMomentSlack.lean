import ProphetSecretary.Model.FirstMomentTheorem
import ProphetSecretary.Model.ScalarValueProperties

/-!
# Scalar slack for large total first moment

The interior lower bound is the contrapositive of `upmom:theorem`. Outside
that interval the endpoint slack remains an explicit hypothesis, to be
supplied by the boundary and clamp results. No global first-moment bound
is inferred merely from a small scalar gap.
-/

open MeasureTheory Set
namespace ProphetSecretary.Model

noncomputable def largeFirstMomentGapConstant (δ d : ℝ) : ℝ := min (firstMomentGapRadius δ) d

lemma largeFirstMomentGapConstant_positive {δ d : ℝ} (hδ : 0<δ) (hd : 0<d) :
    0<largeFirstMomentGapConstant δ d := lt_min (firstMomentGapRadius_positive hδ) hd

lemma Instance.largeFirstMoment_gap_lower_bound_of_outside_slack {n : ℕ} (P : Instance n)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x≤1) {δ d : ℝ} (hδ : 0<δ) (hd : 0<d)
    (hLarge : firstMomentUniformBound δ<P.totalFirstMoment)
    (hOutside : ∀ lam∈Icc (0 : ℝ) 1, lam<δ ∨ 1-δ<lam → d≤normalizedScalarGap P lam)
    {lam : ℝ} (hlam : lam∈Icc (0 : ℝ) 1) :
    largeFirstMomentGapConstant δ d/(1+P.positiveCount)^4≤normalizedScalarGap P lam := by
  have hL : 0≤P.positiveCount := P.tailCount_nonnegative 0
  have hDenOne : (1 : ℝ)≤(1+P.positiveCount)^4 := one_le_pow₀ (by linarith only [hL])
  have hDenPos : 0<(1+P.positiveCount)^4 := zero_lt_one.trans_le hDenOne
  have hκ := (largeFirstMomentGapConstant_positive hδ hd).le
  by_cases hBoundary : lam<δ ∨ 1-δ<lam
  · have hRatio : largeFirstMomentGapConstant δ d/(1+P.positiveCount)^4≤largeFirstMomentGapConstant δ d := by
      apply (div_le_iff₀ hDenPos).mpr
      have h := mul_nonneg hκ (sub_nonneg.mpr hDenOne)
      nlinarith only [h]
    exact hRatio.trans ((min_le_right _ _).trans (hOutside lam hlam hBoundary))
  · have hInterior : δ≤lam ∧ δ≤1-lam := by
      rcases not_or.mp hBoundary with ⟨hLeft,hRight⟩
      constructor
      · exact le_of_not_gt hLeft
      · linarith only [le_of_not_gt hRight]
    have hStrict : firstMomentGapRadius δ/(1+P.positiveCount)^4<normalizedScalarGap P lam := by
      apply lt_of_not_ge
      intro hGap
      have hBound := P.totalFirstMoment_le_of_small_scalarGap hcap hδ hInterior.1 hInterior.2
        (by ring : lam+(1-lam)=1) hGap
      exact (not_lt_of_ge hBound) hLarge
    exact (div_le_div_of_nonneg_right (min_le_left _ _) hDenPos.le).trans hStrict.le

end ProphetSecretary.Model
