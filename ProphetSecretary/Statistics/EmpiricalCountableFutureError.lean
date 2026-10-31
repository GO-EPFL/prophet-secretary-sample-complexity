import ProphetSecretary.Statistics.EmpiricalFutureValueError
import ProphetSecretary.Probability.CountableConditionalMaximum

/-!
# A common empirical future error at countably many times

Twice the actual conditional-expectation maximum bounds all scalar coefficients
at all supplied observation times on one common probability-one event. Its
second and sixth moments have universal Doob factors 16 and 832. Extension
from a rational enumeration to every elapsed time is a separate pathwise step.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

lemma Instance.empiricalUniformResidualEnvelope_bounded (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) (lo hi : ℝ) :
    ∀ᵐ q ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n),
      P.empiricalUniformResidualEnvelope k lo hi q ≤ (n : ℝ) := by
  have hb := P.empiricalIntervalEnvelope_bounded (k := k) hbound lo hi
  exact hb.mono fun q hq => (ProphetSecretary.Analysis.dyadicSupremum_mem_Icc
    (Nat.cast_nonneg n) q (fun t _ => hq t)).2

noncomputable def Instance.empiricalCountableFutureError (P : Instance n) (k : ℕ) [NeZero k]
    (lo hi : ℝ) (τ : ℕ → ℝ) : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) → ℝ :=
  fun q => 2 * ProphetSecretary.Probability.countableConditionalMaximum
    ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n))
    (ProphetSecretary.Probability.dataClockHistoryFiltration ((Fin n × Fin k) → ℝ) n)
    (P.empiricalUniformResidualEnvelope k lo hi) τ q

lemma Instance.measurable_empiricalCountableFutureError (P : Instance n)
    (lo hi : ℝ) (τ : ℕ → ℝ) : Measurable (P.empiricalCountableFutureError k lo hi τ) :=
  (ProphetSecretary.Probability.measurable_countableConditionalMaximum _ _ _ _).const_mul 2

lemma Instance.empiricalCountableFutureError_nonnegative (P : Instance n)
    (lo hi : ℝ) (τ : ℕ → ℝ) (q : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ))) :
    0 ≤ P.empiricalCountableFutureError k lo hi τ q :=
  mul_nonneg (by norm_num) (ProphetSecretary.Probability.countableConditionalMaximum_nonnegative _ _ _ _ _)

/-- Common domination also applies when z is selected from the training array. -/
theorem Instance.empiricalCountableFutureError_dominates (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {lo hi : ℝ} (hlo : 0 ≤ lo) (hlohi : lo ≤ hi)
    (τ : ℕ → ℝ) (hτ : ∀ j, τ j ∈ Ico (0 : ℝ) 1) :
    ∀ᵐ q ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n), ∀ j, ∀ z ∈ Icc lo hi,
      |(totalEmpiricalInstance (reservoirCoordinates.symm q.1)).continuationValue
          (ProphetSecretary.Probability.pendingClockSet (τ j) q.2) (1-τ j) 1 z -
        P.continuationValue (ProphetSecretary.Probability.pendingClockSet (τ j) q.2) (1-τ j) 1 z| ≤
      P.empiricalCountableFutureError k lo hi τ q := by
  let μ := (P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)
  let ℱ := ProphetSecretary.Probability.dataClockHistoryFiltration ((Fin n × Fin k) → ℝ) n
  let E := P.empiricalUniformResidualEnvelope k lo hi
  have hb : ∀ᵐ q ∂μ, ‖E q‖ ≤ (n : ℝ) := by
    filter_upwards [P.empiricalUniformResidualEnvelope_bounded (k := k) hbound lo hi] with q hq
    rw [Real.norm_eq_abs, abs_of_nonneg (P.empiricalUniformResidualEnvelope_nonnegative lo hi q)]
    exact hq
  have hmax := ProphetSecretary.Probability.countableConditionalMaximum_dominates μ ℱ E τ (Nat.cast_nonneg n) hb
  have hevery : ∀ᵐ q ∂μ, ∀ j, ∀ z ∈ Icc lo hi,
      |(totalEmpiricalInstance (reservoirCoordinates.symm q.1)).continuationValue
          (ProphetSecretary.Probability.pendingClockSet (τ j) q.2) (1-τ j) 1 z -
        P.continuationValue (ProphetSecretary.Probability.pendingClockSet (τ j) q.2) (1-τ j) 1 z| ≤
        2 * μ[E | ℱ (τ j)] q :=
    ae_all_iff.mpr fun j => P.empirical_future_value_error_le_condExp hbound hlo hlohi (hτ j).1 (hτ j).2
  filter_upwards [hmax, hevery] with q hq herror
  intro j z hz
  exact (herror j z hz).trans (mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hq j)) (by norm_num))

/-- The only remaining dependence is the already proved complete-path moment;
the factors are 16 for p=2 and 832 for p=6. -/
theorem Instance.empiricalCountableFutureError_moment (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) (lo hi : ℝ) (τ : ℕ → ℝ)
    {p : ℕ} (hp : p=2 ∨ p=6) :
    Integrable (fun q => P.empiricalCountableFutureError k lo hi τ q ^ p)
      ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ∧
    (∫ q, P.empiricalCountableFutureError k lo hi τ q ^ p
      ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ≤
      (2 : ℝ)^p * (if p=2 then 4 else 13) * ∫ q, P.empiricalUniformResidualEnvelope k lo hi q ^ p
        ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n) := by
  let μ := (P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)
  let ℱ := ProphetSecretary.Probability.dataClockHistoryFiltration ((Fin n × Fin k) → ℝ) n
  let E := P.empiricalUniformResidualEnvelope k lo hi
  have hnorm (q) : ‖E q‖ = E q := by
    rw [Real.norm_eq_abs, abs_of_nonneg (P.empiricalUniformResidualEnvelope_nonnegative lo hi q)]
  have hb : ∀ᵐ q ∂μ, ‖E q‖ ≤ (n : ℝ) := by
    simpa only [hnorm] using P.empiricalUniformResidualEnvelope_bounded (k := k) hbound lo hi
  have hI : Integrable (fun q => ‖E q‖^p) μ := by
    simpa only [hnorm] using (P.empiricalUniformResidualEnvelope_moment (k := k) hbound hp lo hi).1
  have hm := ProphetSecretary.Probability.countableConditionalMaximum_moment μ ℱ E τ (Nat.cast_nonneg n) hb hp hI
  have hfun : (fun q => P.empiricalCountableFutureError k lo hi τ q ^ p) =
      fun q => (2 : ℝ)^p * ProphetSecretary.Probability.countableConditionalMaximum μ ℱ E τ q ^ p := by
    funext q
    exact mul_pow _ _ _
  rw [hfun]
  refine ⟨hm.1.const_mul _, ?_⟩
  rw [integral_const_mul]
  have hi := mul_le_mul_of_nonneg_left hm.2 (by positivity : (0 : ℝ) ≤ 2^p)
  simpa only [hnorm, mul_assoc] using hi

end ProphetSecretary.Model
