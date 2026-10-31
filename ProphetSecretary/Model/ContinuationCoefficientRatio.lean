import ProphetSecretary.Model.ClockNearLoss

/-!
# Comparing continuation values across a positive scalar interval

For R₀=hi/lo≥1 and lo≤z≤hi, positive homogeneity and coefficient monotonicity
of the unrestricted stopping value give V(1,hi u)≤R₀V(1,z u). This is the
actual comparison used for the early dyadic bands in `upstat:selected`.
-/

open MeasureTheory Set

namespace ProphetSecretary.Model

variable {n : ℕ}

lemma remainingScalarValue_coefficient_ratio (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {R z hi u : ℝ}
    (hR : 1 ≤ R) (hz : 0 ≤ z) (hhi : 0 ≤ hi) (hu : 0 ≤ u) (hcoef : hi ≤ R * z) :
    remainingScalarValue P 1 hi u ≤ R * remainingScalarValue P 1 z u := by
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hc := mul_le_mul_of_nonneg_right hcoef hu
  have hc' : hi * u ≤ R * (z * u) := by simpa only [mul_assoc] using hc
  have hmono := optimalScalarValue_mono P hP zero_le_one (mul_nonneg hhi hu) hR hc'
  have hscale := optimalScalarValue_smul P hP hR0 zero_le_one (mul_nonneg hz hu)
  simp only [mul_one] at hscale
  exact hmono.trans_eq hscale

lemma Instance.continuationValue_coefficient_ratio (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {lo hi z u : ℝ}
    (hlo : 0 < lo) (hloz : lo ≤ z) (hzhi : z ≤ hi) (hu : 0 ≤ u) (A : Finset (Fin n)) :
    P.continuationValue A u 1 hi ≤ (hi / lo) * P.continuationValue A u 1 z := by
  have hz : 0 < z := hlo.trans_le hloz
  have hhi : 0 < hi := hz.trans_le hzhi
  have hR : 1 ≤ hi / lo := (le_div_iff₀ hlo).mpr (by linarith only [hloz, hzhi])
  have hR0 : 0 ≤ hi / lo := zero_le_one.trans hR
  have hcoef : hi ≤ (hi / lo) * z := by
    have hm := mul_le_mul_of_nonneg_left hloz hR0
    have heq : (hi / lo) * lo = hi := by field_simp
    rwa [heq] at hm
  exact remainingScalarValue_coefficient_ratio (P.restrictTo A) (P.restrictTo_integrable_maximum A hP)
    hR hz.le hhi.le hu hcoef

lemma Instance.clockContinuation_coefficient_ratio (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {lo hi z : ℝ}
    (hlo : 0 < lo) (hloz : lo ≤ z) (hzhi : z ≤ hi) (u : Fin n → ℝ) (t : ℝ) :
    P.clockContinuation hi u t ≤ (hi / lo) * P.clockContinuation z u t :=
  P.continuationValue_coefficient_ratio hP hlo hloz hzhi (le_max_left _ _) _

end ProphetSecretary.Model
