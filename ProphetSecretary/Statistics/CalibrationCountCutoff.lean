import ProphetSecretary.Statistics.CalibrationNumericalTarget
import ProphetSecretary.Probability.IndicatorSampleTails
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The empirical positive-count cutoff

Counting positive observations gives independent Bernoulli coordinates.
Their product moment-generating bound controls the one cutoff shared by
all target and policy computations in `con:calibrated-learner`.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical BigOperators

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model ProphetSecretary.Probability

variable {n m : ℕ} [NeZero m]

lemma log_le_clog_two (m : ℕ) (hm : 1 ≤ m) :
    Real.log (m : ℝ) ≤ (Nat.clog 2 m : ℝ) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hl : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hmR
  have h2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have h2le : Real.log (2 : ℝ) ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    Real.log (m : ℝ) ≤ Real.logb 2 (m : ℝ) := by
      rw [Real.logb]
      apply (le_div_iff₀ h2).mpr
      exact mul_le_of_le_one_right hl h2le
    _ ≤ (Nat.ceil (Real.logb 2 (m : ℝ)) : ℝ) := Nat.le_ceil _
    _ = (Nat.clog 2 m : ℝ) := congrArg (fun q : ℕ => (q : ℝ)) (Real.natCeil_logb_natCast 2 m)

/-- The MGF is for the actual complete independent empirical block. -/
theorem empiricalPositiveCount_mgf_le (P : Instance n) :
    (∫ y, Real.exp ((m : ℝ)*empiricalPositiveCount y) ∂P.trainingCoordinateLaw m) ≤
      Real.exp ((Real.exp 1-1)*(m : ℝ)*P.positiveCount) := by
  let ν : (Fin n × Fin m) → Measure ℝ := fun q => indicatorSampleLaw (P.law q.1) (Ioi 0)
  let T : ((Fin n × Fin m) → ℝ) → (Fin n × Fin m) → ℝ :=
    fun y q => sampleEventIndicator (Ioi 0) (y q)
  letI (q : Fin n × Fin m) : IsProbabilityMeasure (ν q) :=
    Measure.isProbabilityMeasure_map (sampleEventIndicator_measurable measurableSet_Ioi).aemeasurable
  have hunit (q : Fin n × Fin m) : ∀ᵐ x ∂ν q, x ∈ Icc (0 : ℝ) 1 :=
    indicatorSampleLaw_unit (P.law q.1) measurableSet_Ioi
  have hp : MeasurePreserving T (P.trainingCoordinateLaw m) (Measure.pi ν) := by
    refine ⟨measurable_pi_lambda _ (fun q =>
      (sampleEventIndicator_measurable measurableSet_Ioi).comp (measurable_pi_apply q)), ?_⟩
    exact Measure.pi_map_pi (fun _ => (sampleEventIndicator_measurable measurableSet_Ioi).aemeasurable)
  have hcount (y : (Fin n × Fin m) → ℝ) :
      (m : ℝ)*empiricalPositiveCount y = coordinateSum (T y) := by
    unfold empiricalPositiveCount coordinateSum T sampleEventIndicator
    simp only [Set.indicator_apply, Set.mem_Ioi]
    rw [← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast NeZero.ne m : (m : ℝ) ≠ 0), one_mul]
  have hsum : (∑ q : Fin n × Fin m, ∫ x, x ∂ν q) = (m : ℝ)*P.positiveCount := by
    simp only [ν, integral_indicatorSampleLaw _ measurableSet_Ioi, Fintype.sum_prod_type,
      Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    unfold Instance.positiveCount Instance.tailCount
    rw [← Finset.mul_sum]
    rfl
  have hmeas : Measurable (fun a : (Fin n × Fin m) → ℝ => Real.exp (coordinateSum a)) :=
    (Finset.measurable_sum Finset.univ (fun q _ => measurable_pi_apply q)).exp
  have hmap := integral_map (μ := P.trainingCoordinateLaw m)
    hp.measurable.aemeasurable hmeas.aestronglyMeasurable
  rw [hp.map_eq] at hmap
  have hbound := coordinateSum_mgf_le ν hunit 1
  simp only [mgf, one_mul] at hbound
  rw [hsum] at hbound
  calc
    (∫ y, Real.exp ((m : ℝ)*empiricalPositiveCount y) ∂P.trainingCoordinateLaw m) =
        ∫ a, Real.exp (coordinateSum a) ∂Measure.pi ν := by
      rw [hmap]
      exact integral_congr_ae (Eventually.of_forall (fun y => congrArg Real.exp (hcount y)))
    _ ≤ _ := by simpa only [mul_assoc] using hbound

/-- The single empirical count cutoff fails with exponentially small probability. -/
theorem empiricalPositiveCount_cutoff_probability (P : Instance n)
    (hCount : P.positiveCount ≤ 2*Real.log (m : ℝ)) :
    (P.trainingCoordinateLaw m).real {y | targetCountCutoff m < empiricalPositiveCount y} ≤
      Real.exp (-2*(m : ℝ)) := by
  have hm : 1 ≤ m := NeZero.pos m
  have hmR : (0 : ℝ) < m := by exact_mod_cast NeZero.pos m
  have hlog : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by exact_mod_cast hm)
  have hclog := log_le_clog_two m hm
  have hE : 0 ≤ Real.exp 1-1 := by linarith [Real.one_le_exp_iff.mpr (by norm_num : (0 : ℝ) ≤ 1)]
  have hE2 : Real.exp 1-1 ≤ 2 := by linarith [Real.exp_one_lt_three]
  have hnum : (Real.exp 1-1)*P.positiveCount ≤ 4*Real.log (m : ℝ) := by
    calc
      _ ≤ (Real.exp 1-1)*(2*Real.log (m : ℝ)) := mul_le_mul_of_nonneg_left hCount hE
      _ ≤ 2*(2*Real.log (m : ℝ)) := mul_le_mul_of_nonneg_right hE2 (by positivity)
      _ = _ := by ring
  have hraw (y : (Fin n × Fin m) → ℝ) :
      (m : ℝ)*empiricalPositiveCount y ≤ (n : ℝ)*(m : ℝ) := by
    unfold empiricalPositiveCount
    rw [← mul_assoc, mul_inv_cancel₀ hmR.ne', one_mul]
    calc
      (∑ q : Fin n × Fin m, if 0 < y q then (1 : ℝ) else 0) ≤ ∑ _q : Fin n × Fin m, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro q _
        split_ifs <;> norm_num
      _ = _ := by simp
  have hi : Integrable (fun y => Real.exp (1*((m : ℝ)*empiricalPositiveCount y)))
      (P.trainingCoordinateLaw m) := by
    apply Integrable.of_bound
      (((measurable_empiricalPositiveCount.const_mul (m : ℝ)).const_mul 1).exp).aestronglyMeasurable
      (Real.exp ((n : ℝ)*(m : ℝ)))
    filter_upwards [] with y
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), one_mul]
    exact Real.exp_le_exp.mpr (hraw y)
  have ht := measure_ge_le_exp_mul_mgf (X := fun y => (m : ℝ)*empiricalPositiveCount y)
    (μ := P.trainingCoordinateLaw m) (t := 1) ((m : ℝ)*targetCountCutoff m) zero_le_one hi
  have hmgf := empiricalPositiveCount_mgf_le P (m := m)
  change (∫ y, Real.exp ((m : ℝ)*empiricalPositiveCount y) ∂P.trainingCoordinateLaw m) ≤ _ at hmgf
  have hsub : {y : (Fin n × Fin m) → ℝ | targetCountCutoff m < empiricalPositiveCount y} ⊆
      {y : (Fin n × Fin m) → ℝ | (m : ℝ)*targetCountCutoff m ≤ (m : ℝ)*empiricalPositiveCount y} := by
    intro y hy
    exact (mul_lt_mul_of_pos_left hy hmR).le
  calc
    _ ≤ (P.trainingCoordinateLaw m).real
        {y | (m : ℝ)*targetCountCutoff m ≤ (m : ℝ)*empiricalPositiveCount y} := measureReal_mono hsub
    _ ≤ Real.exp (-(1 : ℝ)*((m : ℝ)*targetCountCutoff m))*
        Real.exp ((Real.exp 1-1)*(m : ℝ)*P.positiveCount) := by
      apply ht.trans
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      simpa only [mgf, one_mul] using hmgf
    _ = Real.exp ((m : ℝ)*((Real.exp 1-1)*P.positiveCount-targetCountCutoff m)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-2*(m : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have hinner : (Real.exp 1-1)*P.positiveCount-targetCountCutoff m ≤ -2 := by
        unfold targetCountCutoff
        linarith
      have hmul := mul_le_mul_of_nonneg_left hinner hmR.le
      nlinarith

end ProphetSecretary.Statistics.Calibration
