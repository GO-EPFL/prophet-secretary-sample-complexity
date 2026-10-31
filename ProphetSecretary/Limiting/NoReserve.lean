import ProphetSecretary.Limiting.HybridScalarGap
import ProphetSecretary.Limiting.CountableValueLimit
import ProphetSecretary.Limiting.CountableBenchmarkLimit

/-!
# A critical countable instance has zero terminal reserve

Paper correspondence: `lem:no-reserve`. The stronger quantitative inequality
is proved for every actual bounded countable instance, before imposing
criticality or positive expected maximum. Actual finite-hybrid truncations
satisfy the reserve inequality; their proved benchmark and full-policy value
limits pass it to the original instance. The global constant is bounded
strictly below one by the verified two-offer construction.
-/
open MeasureTheory Set Filter
open scoped Topology NNReal Classical
namespace ProphetSecretary.Limiting.CountableInstance
open ProphetSecretary.Model

noncomputable def scalarGap (B : CountableInstance) (w c : ℝ) : ℝ :=
  B.optimalScalarValue w c-optimalCompetitiveRatio*(w*B.expectedMaximum+c)

/-- Criticality includes the paper's positive-benchmark requirement. -/
def IsCritical (B : CountableInstance) (w c : ℝ) : Prop :=
  0 < B.expectedMaximum ∧ B.scalarGap w c = 0

/-- The reserve contribution is uniform over every nonnegative weight and
requires neither a positive benchmark nor a finite total Poisson intensity. -/
theorem scalarGap_ge_terminal (B : CountableInstance) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    (1-optimalCompetitiveRatio)*w*(B.terminal : ℝ) ≤ B.scalarGap w c := by
  have hM := B.truncation_expectedMaximum_tendsto id B.markCutoff B.terminal_lt_markCutoff tendsto_id B.markCutoff_tendsto
  have hV := B.truncation_value_tendsto id B.markCutoff B.terminal_lt_markCutoff tendsto_id B.markCutoff_tendsto hw hc
  have hGap : Tendsto (fun m => (B.truncation m (B.markCutoff m) (B.terminal_lt_markCutoff m)).scalarGap w c)
      atTop (𝓝 (B.scalarGap w c)) :=
    hV.sub (((hM.const_mul w).add_const c).const_mul optimalCompetitiveRatio)
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hGap
  apply Eventually.of_forall
  intro m
  exact (B.truncation m (B.markCutoff m) (B.terminal_lt_markCutoff m)).scalarGap_ge_terminal hw hc

lemma scalarGap_nonnegative (B : CountableInstance) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    0 ≤ B.scalarGap w c :=
  (mul_nonneg (mul_nonneg (sub_nonneg.mpr optimalCompetitiveRatio_le_one) hw) B.terminal.property).trans
    (B.scalarGap_ge_terminal hw hc)

lemma globalScalar_inequality (B : CountableInstance) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    optimalCompetitiveRatio*(w*B.expectedMaximum+c) ≤ B.optimalScalarValue w c :=
  sub_nonneg.mp (B.scalarGap_nonnegative hw hc)

/-- Even nonpositive scalar gap forces zero reserve when reward has positive
weight. This includes c=0 and does not need M>0. -/
theorem terminal_eq_zero_of_gap_nonpositive (B : CountableInstance) {w c : ℝ}
    (hw : 0 < w) (hc : 0 ≤ c) (hgap : B.scalarGap w c ≤ 0) : B.terminal = 0 := by
  have hbound := (B.scalarGap_ge_terminal hw.le hc).trans hgap
  have hC : 0 < 1-optimalCompetitiveRatio := by linarith [optimalCompetitiveRatio_le_threeQuarters]
  have hp : 0 < (1-optimalCompetitiveRatio)*w := mul_pos hC hw
  have ha : (B.terminal : ℝ) ≤ 0 := by
    by_contra h
    exact (not_lt_of_ge hbound) (mul_pos hp (not_le.mp h))
  apply Subtype.ext
  exact le_antisymm ha B.terminal.property

/-- `lem:no-reserve` for the genuine full admissible policy supremum.
The conclusion holds in particular for limits of finite instances. -/
theorem terminal_eq_zero_of_critical (B : CountableInstance) {w c : ℝ}
    (hw : 0 < w) (hc : 0 ≤ c) (hcritical : B.IsCritical w c) : B.terminal = 0 :=
  B.terminal_eq_zero_of_gap_nonpositive hw hc hcritical.2.le

end ProphetSecretary.Limiting.CountableInstance
