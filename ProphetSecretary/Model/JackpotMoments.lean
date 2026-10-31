import ProphetSecretary.Model.Jackpot
import ProphetSecretary.Model.ScalarObjectiveBounds

/-!
# First moments of a one-marginal jackpot perturbation

The perturbed instance still has a finite first moment. Its prophet benchmark is at
least the added jackpot's first moment, even when the bounded base benchmark is zero.
-/

open MeasureTheory ProbabilityTheory Set unitInterval

namespace ProphetSecretary.Model

lemma jackpotLaw_integrable {μ : Measure ℝ} {f : ℝ → ℝ} (hf : Integrable f μ)
    (p : unitInterval) (A : ℝ) : Integrable f (jackpotLaw μ p A) := by
  exact ((integrable_dirac (by simp) : Integrable f (Measure.dirac A)).smul_measure_nnreal).add_measure
    hf.smul_measure_nnreal

lemma integral_jackpotLaw {μ : Measure ℝ} {f : ℝ → ℝ} (hf : Integrable f μ)
    (p : unitInterval) (A : ℝ) :
    (∫ x, f x ∂jackpotLaw μ p A) = (p : ℝ) * f A + (1 - (p : ℝ)) * ∫ x, f x ∂μ := by
  unfold jackpotLaw
  rw [integral_add_measure
    ((integrable_dirac (by simp) : Integrable f (Measure.dirac A)).smul_measure_nnreal)
    hf.smul_measure_nnreal, integral_smul_nnreal_measure, integral_smul_nnreal_measure,
    integral_dirac]
  rfl

namespace Instance

variable {n : ℕ} (P : Instance n)

lemma jackpot_integrable_maximum (hP : Integrable maximum P.valuesLaw) (i : Fin n)
    (p : unitInterval) {A : ℝ} (hA : 0 ≤ A) :
    Integrable maximum (P.jackpot i p A hA).valuesLaw := by
  apply Instance.integrable_maximum
  intro j
  by_cases hj : j = i
  · subst j
    simpa only [jackpot, Function.update_self] using
      jackpotLaw_integrable (P.integrable_maximum_iff.mp hP i) p A
  · simpa only [jackpot, Function.update_of_ne hj] using P.integrable_maximum_iff.mp hP j

/-- The jackpot alone supplies first moment `p*A` to the prophet benchmark. -/
lemma jackpot_expectedMaximum_ge (hP : Integrable maximum P.valuesLaw) (i : Fin n)
    (p : unitInterval) {A : ℝ} (hA : 0 ≤ A) :
    (p : ℝ) * A ≤ (P.jackpot i p A hA).expectedMaximum := by
  let Q := P.jackpot i p A hA
  have hQ := P.jackpot_integrable_maximum hP i p hA
  have he : ∫ x, x ∂Q.law i = (p : ℝ) * A + (1 - (p : ℝ)) * ∫ x, x ∂P.law i :=
    by simpa only [Q, jackpot, Function.update_self, id_eq] using
      integral_jackpotLaw (P.integrable_maximum_iff.mp hP i) p A
  have hm : 0 ≤ ∫ x, x ∂P.law i := integral_nonneg_of_ae (P.nonnegative i)
  calc
    (p : ℝ) * A ≤ ∫ x, x ∂Q.law i := by
      rw [he]
      exact le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr p.2.2) hm)
    _ = ∫ x, x i ∂Q.valuesLaw := (Q.integral_coordinate i).symm
    _ ≤ Q.expectedMaximum := integral_mono (Q.integrable_coordinate_of_maximum hQ i) hQ
      (fun x => le_maximum x i)

lemma jackpot_positiveFinite (hP : Integrable maximum P.valuesLaw) (i : Fin n)
    (p : unitInterval) (hp : 0 < (p : ℝ)) {A : ℝ} (hA : 0 < A) :
    (P.jackpot i p A hA.le).HasPositiveFiniteMaximum :=
  ⟨P.jackpot_integrable_maximum hP i p hA.le,
    (mul_pos hp hA).trans_le (P.jackpot_expectedMaximum_ge hP i p hA.le)⟩

end Instance
end ProphetSecretary.Model
