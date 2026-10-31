import ProphetSecretary.Statistics.EmpiricalMaximumVariance

/-!
# The explicit empirical-cap bad-event probability

Unbiasedness and the proved M/k variance bound give the actual one-sided
Chebyshev estimate M/[k(a−M)²]. The training law is the original independent
sample array; no independence from a sample-selected scalar is asserted or
needed for this event.
-/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal Classical
namespace ProphetSecretary.Model
variable {n k : ℕ} [NeZero k]

theorem Instance.empiricalExpectedMaximum_upper_tail (P : Instance n)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {a : ℝ} (ha : P.expectedMaximum < a) :
    (P.trainingCoordinateLaw k).real {y | a < empiricalExpectedMaximum (k := k) y} ≤
      P.expectedMaximum / ((k : ℝ)*(a-P.expectedMaximum)^2) := by
  have hc := meas_ge_le_variance_div_sq (P.memLp_empiricalExpectedMaximum (k := k) 1 hcap 2) (sub_pos.mpr ha)
  rw [P.integral_empiricalExpectedMaximum 1 hcap] at hc
  have hsub : {y : (Fin n × Fin k) → ℝ | a < empiricalExpectedMaximum (k := k) y} ⊆
      {y : (Fin n × Fin k) → ℝ | a-P.expectedMaximum ≤ |empiricalExpectedMaximum (k := k) y-P.expectedMaximum|} := by
    intro y hy
    change a < empiricalExpectedMaximum (k := k) y at hy
    exact (sub_le_sub_right hy.le _).trans (le_abs_self _)
  have hbound := (measure_mono hsub).trans hc
  have hReal := ENNReal.toReal_le_of_le_ofReal
    (div_nonneg (variance_nonneg _ _) (sq_nonneg (a-P.expectedMaximum))) hbound
  calc
    _ ≤ variance (empiricalExpectedMaximum (k := k)) (P.trainingCoordinateLaw k)/(a-P.expectedMaximum)^2 := hReal
    _ ≤ (P.expectedMaximum/(k : ℝ))/(a-P.expectedMaximum)^2 :=
      div_le_div_of_nonneg_right (P.variance_empiricalExpectedMaximum_le_mean_div_samples hcap) (sq_nonneg _)
    _ = _ := by rw [div_div]

lemma Instance.empirical_cap_bad_probability_le (P : Instance n)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) (hM : P.expectedMaximum ≤ 1/80) :
    (P.trainingCoordinateLaw k).real {y | (1/4 : ℝ) < empiricalExpectedMaximum (k := k) y} ≤
      (80/361 : ℝ)/(k : ℝ) := by
  have ha : P.expectedMaximum < (1/4 : ℝ) := by linarith
  apply (P.empiricalExpectedMaximum_upper_tail hcap ha).trans
  have hk : (0 : ℝ) < k := Nat.cast_pos.mpr (NeZero.pos k)
  have hg : 0 < (1/4 : ℝ)-P.expectedMaximum := sub_pos.mpr ha
  apply (div_le_iff₀ (mul_pos hk (sq_pos_of_pos hg))).mpr
  have hrat : (80/361 : ℝ)/(k : ℝ)*((k : ℝ)*((1/4 : ℝ)-P.expectedMaximum)^2) =
      (80/361 : ℝ)*((1/4 : ℝ)-P.expectedMaximum)^2 := by field_simp
  rw [hrat]
  have h0 := P.expectedMaximum_nonnegative
  nlinarith [sq_nonneg P.expectedMaximum]

/-- The same explicit bound in the reservoir representation supplied to the
learner by its actual sampling transcript. -/
theorem Instance.reservoir_empiricalExpectedMaximum_upper_tail (P : Instance n)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {a : ℝ} (ha : P.expectedMaximum < a) :
    (P.reservoirLaw k).real {y | a < (totalEmpiricalInstance y).expectedMaximum} ≤
      P.expectedMaximum / ((k : ℝ)*(a-P.expectedMaximum)^2) := by
  let E : Set ((Fin n × Fin k) → ℝ) := {y | a < empiricalExpectedMaximum (k := k) y}
  have hE : MeasurableSet E := measurableSet_lt measurable_const measurable_empiricalExpectedMaximum
  have hp := P.reservoirCoordinates_measurePreserving k
  have he := hp.measure_preimage hE.nullMeasurableSet
  have hset : reservoirCoordinates ⁻¹' E = {y | a < (totalEmpiricalInstance y).expectedMaximum} := by
    ext y
    simp only [E,mem_preimage,mem_setOf_eq,empiricalExpectedMaximum,MeasurableEquiv.symm_apply_apply]
  rw [hset] at he
  have heReal := congrArg ENNReal.toReal he
  change (P.reservoirLaw k).real {y | a < (totalEmpiricalInstance y).expectedMaximum} =
    (P.trainingCoordinateLaw k).real E at heReal
  rw [heReal]
  exact P.empiricalExpectedMaximum_upper_tail hcap ha

end ProphetSecretary.Model
