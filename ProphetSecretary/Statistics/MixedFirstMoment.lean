import ProphetSecretary.Statistics.EmpiricalFirstMoment
import ProphetSecretary.Model.MixedEmpiricalInstance

/-!
# Actual mixed marginal means are unbiased

A declared known marginal retains its fixed true first moment. Every unknown
marginal is the actual independent empirical average. Thus independent training
averaging restores each true mean, without centering any selected coefficient.
-/

open MeasureTheory
open scoped Classical BigOperators
namespace ProphetSecretary.Model
variable {n k : ℕ} [NeZero k]

lemma Instance.integrable_mixed_coordinate_firstMoment (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (known : Finset (Fin n)) (i : Fin n) :
    Integrable (fun a : (Fin n × Fin k) → ℝ =>
      ∫ x, x ∂(mixedEmpiricalInstance P known (reservoirCoordinates.symm a)).law i) (P.trainingCoordinateLaw k) := by
  by_cases hi : i∈known
  · simpa only [mixedEmpiricalInstance_law_known P known _ hi] using
      (integrable_const (μ:=P.trainingCoordinateLaw k) (∫ x, x ∂P.law i))
  · simpa only [mixedEmpiricalInstance_law_unknown P known _ hi] using
      P.integrable_empirical_coordinate_firstMoment (k:=k) hP i

lemma Instance.integral_mixed_coordinate_firstMoment (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (known : Finset (Fin n)) (i : Fin n) :
    (∫ a : (Fin n × Fin k) → ℝ, (∫ x, x ∂(mixedEmpiricalInstance P known (reservoirCoordinates.symm a)).law i)
      ∂P.trainingCoordinateLaw k) = ∫ x, x ∂P.law i := by
  by_cases hi : i∈known
  · simp only [mixedEmpiricalInstance_law_known P known _ hi,integral_const,probReal_univ,one_smul]
  · simpa only [mixedEmpiricalInstance_law_unknown P known _ hi] using
      P.integral_empirical_coordinate_firstMoment (k:=k) hP i

end ProphetSecretary.Model
