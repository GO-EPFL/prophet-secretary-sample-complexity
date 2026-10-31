import ProphetSecretary.Statistics.ReverseCandidateRate
import ProphetSecretary.Statistics.ReverseCandidateReduction
import ProphetSecretary.Statistics.FixedPolicyEmpiricalUnbiased
import ProphetSecretary.Statistics.EmpiricalOptimismLower

/-!
# Fixed-weight upward bias (`upstat:optimism`)

The true canonical optimizer is fixed while training varies. Its evaluation
under the empirical product law is unbiased. Expected empirical regret equals
expected upward bias; dropping empirical reach and restoring each independent
candidate row gives the same inverse-linear rate as for selected weights.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

/-- The separate fixed-weight statement; no sample-selected centering appears. -/
theorem empiricalScalarValue_expected_optimism_bound (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x≤1) {z lo hi : ℝ}
    (hlo : 0<lo) (hlohi : lo≤hi) (hz : z∈Icc lo hi) :
    0 ≤ (∫ a : (Fin n × Fin k) → ℝ,
      optimalScalarValue (totalEmpiricalInstance (reservoirCoordinates.symm a)) 1 z ∂P.trainingCoordinateLaw k)-
        optimalScalarValue P 1 z ∧
    (∫ a : (Fin n × Fin k) → ℝ,
      optimalScalarValue (totalEmpiricalInstance (reservoirCoordinates.symm a)) 1 z ∂P.trainingCoordinateLaw k)-
        optimalScalarValue P 1 z ≤
      empiricalCandidateRegretConstant lo hi * P.totalFirstMoment*(1+P.totalFirstMoment)/(k:ℝ) := by
  have hz0 := (hlo.trans_le hz.1).le
  have hP := P.integrable_maximum_of_bounded hbound
  let π := P.valuePolicy hP zero_le_one hz0
  have hVI := integrable_empiricalScalarValue_unit (k:=k) P hbound hz0
  have hJI : Integrable (fun a : (Fin n × Fin k) → ℝ =>
      π.scalarObjective (totalEmpiricalInstance (reservoirCoordinates.symm a)) 1 z) (P.trainingCoordinateLaw k) :=
    (P.reservoirCoordinates_symm_measurePreserving k).integrable_comp_of_integrable
    (π.integrable_empiricalScalarObjective (k:=k) P hbound z)
  have hmeanJ : (∫ a : (Fin n × Fin k) → ℝ,
      π.scalarObjective (totalEmpiricalInstance (reservoirCoordinates.symm a)) 1 z ∂P.trainingCoordinateLaw k) =
        optimalScalarValue P 1 z := by
    calc
      _ = ∫ y : Reservoir n k, π.scalarObjective (totalEmpiricalInstance y) 1 z ∂P.reservoirLaw k :=
        (P.reservoirCoordinates_symm_measurePreserving k).integral_comp' _
      _ = π.scalarObjective P 1 z := π.integral_empiricalScalarObjective P hbound z
      _ = _ := P.valuePolicy_optimal hP zero_lt_one hz0
  have hCI (i : Fin n) := integrable_reverseCandidateContribution (k:=k) P hbound hz0 hz.2 i
  have hregret : (∫ a : (Fin n × Fin k) → ℝ,
      optimalScalarValue (totalEmpiricalInstance (reservoirCoordinates.symm a)) 1 z-
        π.scalarObjective (totalEmpiricalInstance (reservoirCoordinates.symm a)) 1 z ∂P.trainingCoordinateLaw k) ≤
      ∑ i : Fin n, ∫ a, reverseCandidateContribution P z i a ∂P.trainingCoordinateLaw k := by
    rw [←integral_finsetSum _ (fun i _ => hCI i)]
    apply integral_mono_ae (hVI.sub hJI) (integrable_finsetSum _ (fun i _ => hCI i))
    exact (P.trainingCoordinates_bounded (k:=k) hbound).mono fun a ha =>
      trueCanonical_empirical_regret_le_candidates P hbound hz0 hz.2 a ha
  rw [integral_sub hVI hJI,hmeanJ] at hregret
  refine ⟨empiricalScalarValue_expected_optimism_nonnegative P hbound hz0,hregret.trans ?_⟩
  calc
    _ ≤ ∑ i : Fin n, empiricalCandidateRegretConstant lo hi*(1+P.totalFirstMoment)*
        (∫ x, x ∂P.law i)/(k:ℝ) :=
      Finset.sum_le_sum fun i _ => integral_reverseCandidateContribution_rate_full P hbound hlo hlohi hz i
    _ = ∑ i : Fin n, (empiricalCandidateRegretConstant lo hi*(1+P.totalFirstMoment)/(k:ℝ))*
        (∫ x, x ∂P.law i) := Finset.sum_congr rfl fun _ _ => by ring
    _ = _ := by rw [←Finset.mul_sum]; unfold Instance.totalFirstMoment; ring

/-- Reservoir coordinates give the same statement in the paper's training
array notation. The true instance optimum remains separate from global C_PS. -/
theorem empiricalScalarValue_expected_optimism_bound_reservoir (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x≤1) {z lo hi : ℝ}
    (hlo : 0<lo) (hlohi : lo≤hi) (hz : z∈Icc lo hi) :
    0 ≤ (∫ y : Reservoir n k, optimalScalarValue (totalEmpiricalInstance y) 1 z ∂P.reservoirLaw k)-
        optimalScalarValue P 1 z ∧
    (∫ y : Reservoir n k, optimalScalarValue (totalEmpiricalInstance y) 1 z ∂P.reservoirLaw k)-
        optimalScalarValue P 1 z ≤
      empiricalCandidateRegretConstant lo hi * P.totalFirstMoment*(1+P.totalFirstMoment)/(k:ℝ) := by
  have he := (P.reservoirCoordinates_symm_measurePreserving k).integral_comp'
    (fun y : Reservoir n k => optimalScalarValue (totalEmpiricalInstance y) 1 z)
  rw [←he]
  exact empiricalScalarValue_expected_optimism_bound P hbound hlo hlohi hz

end ProphetSecretary.Model
