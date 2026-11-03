import ProphetSecretary.Statistics.CalibrationNumericalTarget

/-!
# Integrating the target queries' confidence bounds

The empirical first block and query seeds have their actual product law.
Conditional single-query confidence holds almost everywhere in the training
array, so no condition is imposed on impossible raw inputs. A finite union
bound needs no independence between the different grid queries.
-/

open MeasureTheory Set
open scoped BigOperators Classical

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model

variable {n m : ℕ} [NeZero m] {Seed : Type*} [MeasurableSpace Seed]

/-- Conditional fixed-grid query confidence controls the actual guarded failure event. -/
theorem queryFailure_probability_le
    (μ : Measure ((Fin n × Fin m) → ℝ)) [IsProbabilityMeasure μ]
    (ν : Measure Seed) [IsProbabilityMeasure ν] (mu : ℝ)
    (out : (((Fin n × Fin m) → ℝ) × Seed) → TargetGrid m → ℝ) (ho : Measurable out)
    (hConf : ∀ᵐ a ∂μ, targetEligible mu a → ∀ j : TargetGrid m,
      ν.real {r | 1/(m : ℝ) < |out (a,r) j-optimalScalarValue (trainingInstance a) 1 (targetGrid j)|} ≤
        1/((m : ℝ)^2*(4*(m : ℝ)+1))) :
    (μ.prod ν).real {p | queryFailure mu p.1 (out p)} ≤ 1/(m : ℝ)^2 := by
  let Ω := (((Fin n × Fin m) → ℝ) × Seed)
  let B : Set Ω := {p | queryFailure mu p.1 (out p)}
  have hBm : MeasurableSet B := (measurableSet_queryFailure mu).preimage (measurable_fst.prodMk ho)
  have hBI : Integrable (B.indicator (fun _ : Ω => (1 : ℝ))) (μ.prod ν) :=
    (integrable_const 1).indicator hBm
  have hMean : (μ.prod ν).real B = ∫ a, (∫ r, B.indicator (fun _ : Ω => (1 : ℝ)) (a,r) ∂ν) ∂μ := by
    have hI := integral_indicator_const (μ := μ.prod ν) (1 : ℝ) hBm
    rw [smul_eq_mul, mul_one] at hI
    rw [← hI, integral_prod _ hBI]
  rw [hMean]
  have hBound : (∫ a, (∫ r, B.indicator (fun _ : Ω => (1 : ℝ)) (a,r) ∂ν) ∂μ) ≤
      ∫ _a, 1/(m : ℝ)^2 ∂μ := by
    apply integral_mono_ae hBI.integral_prod_left (integrable_const _)
    filter_upwards [hConf] with a hA
    have hSection : MeasurableSet {r | queryFailure mu a (out (a,r))} :=
      hBm.preimage (measurable_const.prodMk measurable_id)
    have hSec : (∫ r, B.indicator (fun _ : Ω => (1 : ℝ)) (a,r) ∂ν) =
        ν.real {r | queryFailure mu a (out (a,r))} := by
      simpa only [B, Set.indicator_apply, Set.mem_setOf_eq, smul_eq_mul, mul_one] using
        integral_indicator_const (μ := ν) (1 : ℝ) hSection
    rw [hSec]
    by_cases he : targetEligible mu a
    · let E : TargetGrid m → Set Seed := fun j =>
        {r | 1/(m : ℝ) < |out (a,r) j-optimalScalarValue (trainingInstance a) 1 (targetGrid j)|}
      have hSub : {r | queryFailure mu a (out (a,r))} ⊆ ⋃ j : TargetGrid m, E j := by
        intro r hr
        have h := Classical.not_forall.mp hr.2
        obtain ⟨j, hj⟩ := h
        exact Set.mem_iUnion.mpr ⟨j, lt_of_not_ge hj⟩
      calc
        _ ≤ ν.real (⋃ j : TargetGrid m, E j) := measureReal_mono hSub
        _ ≤ ∑ j : TargetGrid m, ν.real (E j) := measureReal_iUnion_fintype_le E
        _ ≤ ∑ _j : TargetGrid m, 1/((m : ℝ)^2*(4*(m : ℝ)+1)) :=
          Finset.sum_le_sum (fun j _ => hA he j)
        _ = 1/(m : ℝ)^2 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          have hm : (m : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne m
          have hN : (4*(m : ℝ)+1) ≠ 0 := by positivity
          field_simp
    · have hEmpty : {r | queryFailure mu a (out (a,r))} = ∅ := by
        ext r
        simp [queryFailure, he]
      rw [hEmpty, measureReal_empty]
      positivity
  simpa only [integral_const, probReal_univ, one_smul] using hBound

/-- The implemented target satisfies the lower clause after integrating query confidence. -/
theorem numericalTarget_expected_lower_of_query_confidence
    (μ : Measure ((Fin n × Fin m) → ℝ)) [IsProbabilityMeasure μ]
    (ν : Measure Seed) [IsProbabilityMeasure ν] (mu : ℝ) (hmu : 0 < mu)
    (out : (((Fin n × Fin m) → ℝ) × Seed) → TargetGrid m → ℝ) (ho : Measurable out)
    (hConf : ∀ᵐ a ∂μ, targetEligible mu a → ∀ j : TargetGrid m,
      ν.real {r | 1/(m : ℝ) < |out (a,r) j-optimalScalarValue (trainingInstance a) 1 (targetGrid j)|} ≤
        1/((m : ℝ)^2*(4*(m : ℝ)+1))) :
    optimalCompetitiveRatio-1/(m : ℝ)^2 ≤
      ∫ p, numericalTarget mu p.1 (out p) ∂μ.prod ν := by
  have hLow := numericalTarget_expected_lower (μ.prod ν) mu hmu Prod.fst out measurable_fst ho
  have hFail := queryFailure_probability_le μ ν mu out ho hConf
  linarith

end ProphetSecretary.Statistics.Calibration
