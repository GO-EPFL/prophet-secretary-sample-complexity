import ProphetSecretary.Model.FirstMomentLayercake
import ProphetSecretary.Analysis.IntegrateLogTail

/-!
# The integrated first-moment estimate

This proves `upmom:integrated` for the actual finite independent instance.
Below a*=K(1+S)e_h the closed tail is bounded by L; above it the proved
logarithmic tail bound applies. If a*>1, the first term alone bounds S.
-/
open MeasureTheory Set
namespace ProphetSecretary.Model
variable {n : ℕ}

/-- Complete instance-level inequality `upmom:integrated`. -/
theorem Instance.firstMoment_integrated_bound (P : Instance n)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1)
    {δ h w c : ℝ} (hδ : 0 < δ) (hwδ : δ ≤ w) (hcδ : δ ≤ c) (hsum : w + c = 1)
    (hh : 0 < h) (hquarter : h ≤ 1 / 4)
    (he : P.firstMomentError δ h w c ≤ firstMomentSurvivalConstant) :
    P.totalFirstMoment ≤ firstMomentAtomScaleConstant δ * P.positiveCount *
      (1 + P.totalFirstMoment) * P.firstMomentError δ h w c +
      Real.log (firstMomentLogTailConstant δ * (1 + P.totalFirstMoment)) + 4 := by
  let α := P.firstMomentAtomScale δ h w c
  let T := firstMomentLogTailConstant δ * (1 + P.totalFirstMoment)
  have hP := P.integrable_maximum_of_bounded hcap
  have hw : 0 < w := hδ.trans_le hwδ
  have hc : 0 < c := hδ.trans_le hcδ
  have hα : 0 < α := P.firstMomentAtomScale_positive hP hδ hh hw hc.le
  have hS := P.totalFirstMoment_nonnegative
  have hL : 0 ≤ P.positiveCount := P.tailCount_nonnegative 0
  have hK₀ := firstMomentLogTailConstant_positive δ
  have hK₀1 : 1 ≤ firstMomentLogTailConstant δ := by
    have h := Real.add_one_le_exp (1 : ℝ)
    exact (by linarith only [h] : (1 : ℝ) ≤ Real.exp 1).trans (le_max_left _ _)
  have hT : 1 ≤ T := by
    have hm := mul_le_mul_of_nonneg_left (by linarith only [hS] : 1 ≤ 1 + P.totalFirstMoment) hK₀.le
    exact hK₀1.trans (by simpa only [mul_one] using hm)
  have hmain : P.totalFirstMoment ≤ P.positiveCount * α + Real.log T + 4 := by
    by_cases hα1 : α ≤ 1
    · rw [P.totalFirstMoment_eq_integral_closedTailCount hcap]
      apply ProphetSecretary.Analysis.integral_log_tail_envelope P.integrableOn_closedTailCount hα.le hα1 hT
      · intro t ht _
        exact P.closedTailCount_le_positiveCount ht.1
      · intro t ht hαt
        exact P.logarithmic_tailCount_bound hcap hδ hwδ hcδ hsum hh hquarter he hαt.le ht.2
    · have hαge : 1 ≤ α := le_of_not_ge hα1
      have hm := mul_le_mul_of_nonneg_left hαge hL
      have hSle := P.totalFirstMoment_le_positiveCount hcap
      have hlog := Real.log_nonneg hT
      nlinarith only [hm,hSle,hlog]
  change P.totalFirstMoment ≤ _
  convert hmain using 1
  dsimp [α,T,Instance.firstMomentAtomScale]
  ring

end ProphetSecretary.Model
