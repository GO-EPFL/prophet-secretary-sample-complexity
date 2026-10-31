import ProphetSecretary.Model.TerminalScalarValue
import ProphetSecretary.Model.TerminalBenchmark
import ProphetSecretary.Reach.Robust
import ProphetSecretary.Model.TwoOfferCompetitiveBound

/-!
# The positive scalar slack created by a fixed terminal reward

Exact reserve removal in both value and benchmark separates the terminal
contribution (1−C_PS)wa from the ordinary excess-instance gap. This finite
inequality is a quantitative precursor to `lem:no-reserve`; no limiting
instance or limiting policy conclusion is inferred here.
-/

open MeasureTheory

namespace ProphetSecretary.Model

variable {n : ℕ}

noncomputable def terminalScalarGap (P : Instance n) (a w c : ℝ) : ℝ :=
  optimalTerminalScalarValue P a w c - optimalCompetitiveRatio * (w * P.expectedTerminalMaximum a + c)

lemma terminalScalarGap_eq_excess (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw)
    {a w c : ℝ} (ha : 0 ≤ a) (hw : 0 < w) (hc : 0 ≤ c) :
    terminalScalarGap P a w c = (1 - optimalCompetitiveRatio) * w * a + scalarGap (P.excessOffers a) w c := by
  unfold terminalScalarGap
  rw [optimalTerminalScalarValue_eq_excessValue P hP ha hw hc,P.expectedTerminalMaximum_eq_excess hP ha]
  unfold scalarGap
  ring

/-- The bound is uniform in the instance size and does not require M>0. -/
theorem terminalScalarGap_ge_terminal (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw)
    {a w c : ℝ} (ha : 0 ≤ a) (hw : 0 < w) (hc : 0 ≤ c) :
    (1 - optimalCompetitiveRatio) * w * a ≤ terminalScalarGap P a w c := by
  rw [terminalScalarGap_eq_excess P hP ha hw hc]
  exact le_add_of_nonneg_right (scalarGap_nonnegative (P.excessOffers a)
    (P.excessOffers_integrable_maximum hP ha) hw.le hc)

/-- Exact finite criticality forces a zero terminal reward. The strict global
bound C_PS<1 is supplied by the proved two-offer instance. -/
theorem terminalScalarGap_nonpositive_forces_zero (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw)
    {a w c : ℝ} (ha : 0 ≤ a) (hw : 0 < w) (hc : 0 ≤ c) (hgap : terminalScalarGap P a w c ≤ 0) : a = 0 := by
  have hbound := (terminalScalarGap_ge_terminal P hP ha hw hc).trans hgap
  have hC : 0 < 1 - optimalCompetitiveRatio := by linarith [optimalCompetitiveRatio_le_threeQuarters]
  have hcoef : 0 < (1 - optimalCompetitiveRatio) * w := mul_pos hC hw
  have han : a ≤ 0 := by
    by_contra hn
    exact (not_lt_of_ge hbound) (mul_pos hcoef (not_le.mp hn))
  exact le_antisymm han ha

end ProphetSecretary.Model
