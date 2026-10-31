import ProphetSecretary.Analysis.PointwiseDerivativeRegularity
import Mathlib.Tactic.Positivity

/-!
# A gap bound retaining the information factor

When the negative derivative is proportional to the information itself, one
fixed step of size proportional to (1+S)⁻¹ gives a linear-in-gap bound. No
division by the information or a positive-gap assumption is needed.
-/

open Set

namespace ProphetSecretary.Analysis

lemma information_le_of_nonnegative_quadratic {s K S I : ℝ}
    (hK : 0 ≤ K) (hS : 0 ≤ S) (hI : 0 ≤ I)
    (hpay : ∀ t ∈ Icc (0 : ℝ) (1/4), 0 ≤ s-2*I*t+K*(1+S)*I*t^2) :
    I ≤ 4*(K+1)*(1+S)*s := by
  let B := (K+1)*(1+S)
  let t := 1/(4*B)
  have hB1 : 1 ≤ B := by dsimp only [B]; nlinarith only [hK,hS,mul_nonneg hK hS]
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one hB1
  have ht : 0 < t := by dsimp only [t]; positivity
  have ht4 : t ≤ 1/4 := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) (by nlinarith only [hB1])
  have hBt : B*t = 1/4 := by dsimp only [t]; field_simp [hB.ne']
  have hProd : 4*B*t = 1 := by nlinarith only [hBt]
  have hCoeff : K*(1+S) ≤ B := by dsimp only [B]; nlinarith only [hS]
  have hKt : K*(1+S)*t ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hCoeff ht.le
    nlinarith only [h,hBt]
  have hSmall := mul_le_of_le_one_left (mul_nonneg hI ht.le) hKt
  have hStep := hpay t ⟨ht.le,ht4⟩
  have hIt : I*t ≤ s := by nlinarith only [hSmall,hStep]
  have hMul := mul_le_mul_of_nonneg_left hIt (by positivity : 0 ≤ 4*B)
  have hEq : (4*B)*(I*t) = I := by
    calc
      _ = I*(4*B*t) := by ring
      _ = I := by rw [hProd,mul_one]
  rw [hEq] at hMul
  exact hMul.trans_eq (by dsimp only [B]; ring)

theorem information_le_of_nonnegative_smooth {f : ℝ → ℝ} {K S I : ℝ}
    (hK : 0 ≤ K) (hS : 0 ≤ S) (hI : 0 ≤ I)
    (hnonneg : ∀ t ∈ Icc (-(1/4) : ℝ) (1/4), 0 ≤ f t)
    (hf : ∀ t ∈ Icc (-(1/4) : ℝ) (1/4), HasDerivAt f (deriv f t) t)
    (hLip : ∀ t ∈ Icc (-(1/4) : ℝ) (1/4), ∀ u ∈ Icc (-(1/4) : ℝ) (1/4),
      |deriv f u-deriv f t| ≤ (K*(1+S)*I)*|u-t|)
    (hDerivative : deriv f 0 = -2*I) : I ≤ 4*(K+1)*(1+S)*f 0 := by
  let Q := K*(1+S)*I
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hZero : (0 : ℝ) ∈ Icc (-(1/4) : ℝ) (1/4) := by norm_num
  have hL : LipschitzOnWith ⟨Q,hQ⟩ (deriv f) (Icc (-(1/4) : ℝ) (1/4)) := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro t ht u hu
    change |deriv f t-deriv f u| ≤ Q*|t-u|
    exact hLip u hu t ht
  apply information_le_of_nonnegative_quadratic hK hS hI
  intro t ht
  have hMem : t ∈ Icc (-(1/4) : ℝ) (1/4) := ⟨by linarith only [ht.1],ht.2⟩
  have hRem := quadratic_remainder_of_lipschitz_derivative hf hL hZero hMem
  simp only [sub_zero,hDerivative] at hRem
  have hUpper := (abs_le.mp hRem).2
  have hn := hnonneg t hMem
  change f t-f 0-(-2*I)*t ≤ (K*(1+S)*I)*t^2 at hUpper
  nlinarith only [hUpper,hn]

end ProphetSecretary.Analysis
